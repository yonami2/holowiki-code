#!/usr/bin/env python3
"""Advertisement blocking for the hololive wiki reader (Python 3.9+, stdlib only).

The reader downloads one HTML document per page and never runs JavaScript or
fetches images, scripts or frames, so ad creatives are never loaded. This
module makes that guarantee explicit and checkable at three points:

1. Network: only HTTPS requests to seesaawiki.jp are allowed. `guard_request`
   raises BlockedRequest for anything else and names ad hosts as such.
   `NetworkLog` can additionally record the destination host of every HTTP(S)
   connection the process opens (through a proxy too: the CONNECT target),
   plus DNS lookups and TCP connections, and optionally refuse any host but
   the wiki. This is how audits prove zero ad-network traffic.
2. Markup: `classify_element` names the ad slots and page chrome that Seesaa
   places around an article (ad boxes, overlay banners, video ad player,
   reader comments, share buttons). The reader skips such an element and its
   whole subtree while parsing, so no extra parsing pass is needed.
3. Output: `scan_output` looks for ad-network URLs and affiliate links in the
   extracted article, including nested metadata and embedded media. If an
   ad URL remains, the reader refuses to return the page in strict mode.

Words such as 広告, PR or product names are never used to delete text: the
wiki legitimately documents sponsorships and collaborations.

Command line (no network):
  python hololive_adblock.py rules                         the rule lists
  python hololive_adblock.py audit page.html --url URL     where a saved page's ads are
"""

from __future__ import annotations

import http.client
import re
import socket
import threading
from html import unescape
from html.parser import HTMLParser
from urllib.parse import parse_qsl, urlsplit

VERSION = "1.0.0+skill.2"
ALLOWED_HOSTS = frozenset({"seesaawiki.jp"})

# Ad serving and ad-tech hosts. A URL matches its exact host or a subdomain,
# never a substring, so "adventure.example" or a path containing "ad" is safe.
# The first seven were observed on seesaawiki.jp/hololivetv pages (2026-09-23).
AD_HOSTS = frozenset({
    "ad-stir.com", "microad.net", "microad.jp", "criteo.net", "criteo.com",
    "creativecarrer.com", "browsiprod.com", "gliacloud.com",
    "doubleclick.net", "googlesyndication.com", "googleadservices.com",
    "googletagservices.com", "adservice.google.com", "amazon-adsystem.com",
    "adnxs.com", "adsrvr.org", "pubmatic.com", "rubiconproject.com", "openx.net",
    "taboola.com", "outbrain.com", "i-mobile.co.jp", "imobile.co.jp", "nend.net",
    "zucks.net", "fluct.jp", "adingo.jp", "gmossp-sp.jp", "geniee.jp", "gsspat.jp",
    "logly.co.jp", "popin.cc", "ad-generation.jp", "impact-ad.jp",
    "yads.yahoo.co.jp", "yads.c.yimg.jp", "uncn.jp", "smartnews-ads.com",
})
# Analytics, counters and share widgets: not ads, and never article content.
TRACKING_HOSTS = frozenset({
    "googletagmanager.com", "google-analytics.com", "rainman.seesaawiki.jp",
    "b.st-hatena.com", "platform.twitter.com", "connect.facebook.net",
})
# Affiliate redirectors. Reported, never removed: the wiki also links to
# official hololive goods this way, and deleting a source would lose facts.
AFFILIATE_HOSTS = frozenset({
    "a8.net", "moshimo.com", "valuecommerce.com", "accesstrade.net", "afi-b.com",
    "linksynergy.com", "afl.rakuten.co.jp", "amzn.to", "felmat.net", "rentracks.jp",
    "affiliate.dmm.com", "al.dmm.com",
})
AFFILIATE_QUERY = {"amazon.co.jp": "tag", "amazon.com": "tag", "dmm.com": "af_id", "dmm.co.jp": "af_id"}

# Seesaa's ad slots. Class and id tokens are compared whole, never by substring.
AD_CLASSES = frozenset({
    "adsense-box", "adsense-main-top", "adsense-main-inner", "side-adsense", "ad-extra",
    "ads-box", "adsbygoogle", "gliaplayer-container", "header-banner",
})
AD_IDS = frozenset({"adsense-location-top", "seesaa-bnr", "seesaa-bnr-close", "browsi-tag"})
AD_ID_PREFIXES = ("crt-",)                     # Criteo ad containers
AD_DATA_ATTRIBUTES = frozenset({"data-revive-zoneid", "data-ad-client", "data-ad-slot"})
# Page chrome inside #page-body-inner: reader comments, the comment form, edit
# and attachment links, share buttons. Never article text; the reader only
# reaches them when a page lacks .user-area and it falls back to the container.
CHROME_IDS = frozenset({
    "comment-box", "pageroot-form-box", "information-box", "page-social-link-top",
    "page-social-link-bottom", "page-posted", "page-attachedfile", "page-extra",
    "page-toplink", "page-tag-outer",
})
CHROME_CLASSES = frozenset({"comment-form-box"})
# Containers that hold the article itself. A rule that matched one of these
# would delete the article, so it is refused instead (see classify_element).
ARTICLE_CLASSES = frozenset({"user-area", "footer-footnote"})
ARTICLE_IDS = frozenset({"page-body-inner", "page-body"})

URL_ATTRIBUTES = ("href", "src", "data-src", "data-original", "data", "poster", "srcset", "data-srcset", "action")
_URL_IN_TEXT = re.compile(r"(?:https?:)?//[^\s<>\"'`\\|\]\[)(]+", re.I)


class BlockedRequest(PermissionError):
    """A request outside the wiki (for example to an ad network) was refused.

    A PermissionError, so HTTP clients report it as a failed, non-retryable
    connection instead of crashing.
    """

    def __init__(self, url, reason):
        super().__init__(f"Blocked request to {url}: {reason}")
        self.url, self.reason = url, reason


def _host(url):
    try:
        parts = urlsplit(url)
    except (TypeError, ValueError):
        return None
    if parts.scheme.lower() not in {"", "http", "https"} or not parts.netloc:
        return None
    try:
        host = parts.hostname
    except ValueError:
        return None
    return host.lower().rstrip(".") if host else None


def _suffix_match(host, suffixes):
    """The member of `suffixes` that is `host` or a parent domain of it."""
    labels = host.split(".")
    return next((candidate for candidate in (".".join(labels[i:]) for i in range(len(labels)))
                 if candidate in suffixes), None)


# Host of an absolute or protocol-relative URL, without urlsplit's full parse.
_FAST_HOST = re.compile(r"\s*(?:[A-Za-z][A-Za-z0-9+.-]*:)?//(?:[^@/?#\s]*@)?(\[[^\]]*\]|[^:/?#\s]+)")


def _fast_host(value):
    # urlsplit and browser URL parsing remove these ASCII characters even
    # inside a host. Apply the same rule before a fast host classification.
    if "\t" in value or "\r" in value or "\n" in value:
        value = value.translate({9: None, 10: None, 13: None})
    match = _FAST_HOST.match(value)
    return match.group(1).lower().rstrip(".") if match else None


_CATEGORY = {**{h: "affiliate" for h in AFFILIATE_HOSTS}, **{h: "tracking" for h in TRACKING_HOSTS},
             **{h: "ad" for h in AD_HOSTS}}


def host_category(host):
    """'ad', 'tracking', 'affiliate' or None for a host name."""
    host = host.lower().rstrip(".") if host else None
    return _host_record(host)[0] if host and host not in ALLOWED_HOSTS else None


def url_category(url):
    """Category of an absolute or protocol-relative URL ('ad', 'tracking', 'affiliate')."""
    host = _fast_host(url)
    if not host or host in ALLOWED_HOSTS:
        return None
    category, _, domain = _host_record(host)
    if category:
        return category
    if domain:
        try:
            if any(name == AFFILIATE_QUERY[domain] and value for name, value in parse_qsl(urlsplit(url).query)):
                return "affiliate"
        except ValueError:
            return None
    return None


def guard_request(url):
    """Allow only HTTPS to the wiki host; otherwise raise BlockedRequest."""
    host = _host(url)
    if urlsplit(url).scheme.lower() != "https" or host not in ALLOWED_HOSTS:
        category = host_category(host)
        reason = {"ad": "advertising host", "tracking": "tracking host",
                  "affiliate": "affiliate host"}.get(category, "not the wiki host")
        raise BlockedRequest(url, reason)
    return url


def _tokens(attrs, name):
    return set((attrs.get(name) or "").split())


_URL_ATTRIBUTE_SET = frozenset(URL_ATTRIBUTES)
# token -> 'article' | 'ad' | 'chrome', so one lookup per class token or id.
_CLASS_KIND = {**{name: "chrome" for name in CHROME_CLASSES}, **{name: "ad" for name in AD_CLASSES},
               **{name: "article" for name in ARTICLE_CLASSES}}
_ID_KIND = {**{name: "chrome" for name in CHROME_IDS}, **{name: "ad" for name in AD_IDS},
            **{name: "article" for name in ARTICLE_IDS}}


_RULE_CACHE = {}


def _ad_rule_of(url):
    """The AD_HOSTS rule an absolute URL loads from, or None.

    Memoized by the URL's scheme and authority (everything before the path):
    an article repeats a few hosts across thousands of links and images.
    """
    end = url.find("/", url.find("//") + 2)
    key = url[:end] if end > 0 else url
    rule = _RULE_CACHE.get(key, False)
    if rule is False:
        if len(_RULE_CACHE) > 4096:
            _RULE_CACHE.clear()
        host = _fast_host(key)
        record = _host_record(host) if host and host not in ALLOWED_HOSTS else None
        rule = _RULE_CACHE[key] = record[1] if record and record[0] == "ad" else None
    return rule


def _ad_rule_in(name, value):
    """The AD_HOSTS rule matched by a URL attribute's value, or None."""
    if "srcset" not in name:
        return _ad_rule_of(value)
    return next((rule for rule in map(_ad_rule_of, value.split(",")) if rule), None)


def classify_element(tag, attrs, base_url=None):
    """Why an element must be skipped, as (kind, reason); None to keep it.

    kind is 'ad' (ad slot or anything loading from an ad host) or 'chrome'
    (reader comments, share buttons and other page furniture). `attrs` is a
    dict or the (name, value) list HTMLParser passes. The reader calls this
    for every start tag of the article, so it reads the attributes once,
    allocates nothing for an ordinary tag and never builds a URL for a
    relative or wiki link. `base_url` is accepted for compatibility: a
    relative URL resolves to the wiki, never to an ad host.
    An element that is (or holds) the article is never classified.
    """
    if not attrs:
        return None
    ad_class = chrome_class = ident = data = ad_rule = None
    for name, value in (attrs.items() if isinstance(attrs, dict) else attrs):
        if name == "class":
            if value:
                for token in value.split():
                    kind = _CLASS_KIND.get(token)
                    if kind is None:
                        continue
                    if kind == "article":
                        return None
                    if kind == "ad":
                        ad_class = token if ad_class is None or token < ad_class else ad_class
                    else:
                        chrome_class = token if chrome_class is None or token < chrome_class else chrome_class
        elif name == "id":
            if value:
                if _ID_KIND.get(value) == "article":
                    return None
                ident = value
        elif name in AD_DATA_ATTRIBUTES:
            data = data or name
        elif (ad_rule is None and value and name in _URL_ATTRIBUTE_SET and "//" in value):
            ad_rule = _ad_rule_in(name, value)
    if ad_class:
        return "ad", "ad_class:" + ad_class
    id_kind = _ID_KIND.get(ident) if ident else None
    if id_kind == "ad":
        return "ad", "ad_id:" + ident
    if ident and ident.startswith(AD_ID_PREFIXES):
        return "ad", "ad_id_prefix:" + ident
    if data:
        return "ad", "ad_attribute:" + data
    if ad_rule:
        return "ad", "ad_host:" + ad_rule
    if id_kind == "chrome":
        return "chrome", "chrome_id:" + ident
    if chrome_class:
        return "chrome", "chrome_class:" + chrome_class
    return None


_HOST_CACHE = {}


def _host_record(host):
    """(category, matched rule, affiliate-query domain) of a host; memoized, since pages repeat hosts."""
    record = _HOST_CACHE.get(host)
    if record is None:
        if len(_HOST_CACHE) > 4096:
            _HOST_CACHE.clear()
        matched = _suffix_match(host, _CATEGORY)
        record = _HOST_CACHE[host] = (_CATEGORY.get(matched), matched, _suffix_match(host, AFFILIATE_QUERY))
    return record


def _host_category_cached(host):
    """(category, matched rule) or None."""
    if not host or host in ALLOWED_HOSTS:
        return None
    record = _host_record(host)
    return record[:2] if record[0] else None


def article_guard(tag, attrs):
    """True when an element is (or holds) the article; rules must never remove it."""
    attrs = dict(attrs)
    return bool(_tokens(attrs, "class") & ARTICLE_CLASSES) or (attrs.get("id") or "") in ARTICLE_IDS


class SkipLog:
    """What a parser skipped: counts by kind/reason plus a few samples."""
    SAMPLE_LIMIT = 40

    def __init__(self):
        self.counts, self.samples = {}, []

    def add(self, kind, reason, tag, line):
        key = kind + "/" + reason
        self.counts[key] = self.counts.get(key, 0) + 1
        if len(self.samples) < self.SAMPLE_LIMIT:
            self.samples.append({"kind": kind, "reason": reason, "tag": tag, "source_line": line})

    def report(self):
        by_kind = {}
        for key, count in self.counts.items():
            kind = key.split("/", 1)[0]
            by_kind[kind] = by_kind.get(kind, 0) + count
        return {"skipped_elements": sum(self.counts.values()), "by_kind": by_kind,
                "by_reason": dict(sorted(self.counts.items())), "samples": self.samples,
                "samples_truncated": sum(self.counts.values()) > len(self.samples)}


# --- output scan -------------------------------------------------------------

def _strings(value, path):
    """(path, text) for every string under `value` that could hold a URL.

    path is a tuple of keys and indexes, formatted only for a hit.
    """
    if isinstance(value, str):
        # Nearly every string is plain text; only one containing '//' can hold a URL.
        if "//" in value:
            yield path, value
    elif isinstance(value, dict):
        for key, item in value.items():
            if isinstance(item, str):
                if "//" in item:
                    yield path + (key,), item
            elif isinstance(item, (dict, list, tuple)):
                yield from _strings(item, path + (key,))
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            if isinstance(item, str):
                if "//" in item:
                    yield path + (index,), item
            elif isinstance(item, (dict, list, tuple)):
                yield from _strings(item, path + (index,))


def _field_strings(name, value):
    """(path, text) pairs of one reader field, without walking derived data."""
    if name == "lines" and isinstance(value, list):
        for index, line in enumerate(value):
            text = line.get("text", "") if isinstance(line, dict) else line
            if isinstance(text, str) and "//" in text:
                yield (name, index), text
    else:
        yield from _strings(value, (name,))


def _format_path(parts):
    return "$" + "".join(f"[{part}]" if isinstance(part, int) else f".{part}" for part in parts)


_WIKI_PREFIX = "https://seesaawiki.jp/"


def _url_hits(text):
    """[(url, 'ad' | 'affiliate')] for the URLs written in one string."""
    # A wiki URL (percent-encoded, one '//') holds no other URL: the common case.
    if text.startswith(_WIKI_PREFIX) and text.find("//", 8) < 0:
        return ()
    text = unescape(text) if "&" in text else text
    variants = [text]
    if "\t" in text or "\r" in text or "\n" in text:
        # Also examine URL-parser normalization, but retain the original
        # text scan: joining whitespace can merge two independent URLs.
        variants.append(text.translate({9: None, 10: None, 13: None}))
    hits, seen_urls = [], set()
    for variant in variants:
        for match in _URL_IN_TEXT.finditer(variant):
            url = match.group().rstrip(",;.")
            if url in seen_urls:
                continue
            seen_urls.add(url)
            category = url_category(url if not url.startswith("//") else "https:" + url)
            if category in {"ad", "affiliate"}:
                hits.append((url, category))
    return hits


def scan_output(fields):
    """Ad and affiliate URLs in extracted fields ({name: value}).

    'structural' hits come from link and media URL fields. Other fields,
    including image alt text and all nested footnote representations, are
    textual. Both categories are rejected by the reader in strict mode;
    neither causes a network request. Pass every extracted content field,
    before line selection or optional output fields are applied.
    """
    buckets = {"ad_urls_structural": {}, "ad_urls_textual": {}, "affiliate_urls": {}}
    seen = {}
    for name, value in fields.items():
        for path, text in _field_strings(name, value):
            structural = (name in {"links", "link_original_hrefs"}
                          or ((name == "images" or "embedded_media" in path)
                              and path[-1] in {"url", "src", "srcset"}))
            # The same URL is usually in several fields (a link and its
            # original href, an image and its link); classify it once.
            hits = seen.get(text)
            if hits is None:
                hits = seen[text] = _url_hits(text)
            for url, category in hits:
                if category == "ad":
                    bucket = "ad_urls_structural" if structural else "ad_urls_textual"
                else:
                    bucket = "affiliate_urls"
                # Count a URL once however many fields or lines repeat it.
                buckets[bucket].setdefault(url[:300], []).append(_format_path(path))
    result = {}
    for bucket, urls in buckets.items():
        result[bucket] = [{"url": url, "paths": paths[:5]} for url, paths in list(urls.items())[:40]]
        result[bucket + "_count"] = len(urls)
    # A URL counted as structural is not also a textual mention.
    textual = set(buckets["ad_urls_textual"]) - set(buckets["ad_urls_structural"])
    result["ad_urls_textual"] = [item for item in result["ad_urls_textual"] if item["url"] in textual]
    result["ad_urls_textual_count"] = len(textual)
    return result


# --- network audit --------------------------------------------------------------

class NetworkLog:
    """Record every connection made inside the block; optionally refuse them.

    Used by audits, not by normal reading. Three views are kept because a
    proxy hides the real destination from the socket layer:
      http_destinations  host of every HTTP(S) connection, including the
                         target of a proxy CONNECT tunnel (the real site)
      dns_lookups        names resolved (with a proxy: the proxy's name)
      tcp_connections    socket.create_connection addresses
    With block=True an HTTP destination outside ALLOWED_HOSTS raises
    BlockedRequest before any byte is sent.
    """

    def __init__(self, block=False):
        self.block = block
        self.lookups, self.connections, self.destinations, self.blocked = [], [], [], []
        self._lock = threading.Lock()

    def _add(self, bucket, value):
        with self._lock:
            bucket.append(value)

    def __enter__(self):
        self._getaddrinfo = socket.getaddrinfo
        self._create_connection = socket.create_connection
        self._http_connect = http.client.HTTPConnection.connect
        log = self

        def getaddrinfo(host, *args, **kwargs):
            log._add(log.lookups, host.decode() if isinstance(host, bytes) else str(host))
            return log._getaddrinfo(host, *args, **kwargs)

        def create_connection(address, *args, **kwargs):
            log._add(log.connections, f"{address[0]}:{address[1]}")
            return log._create_connection(address, *args, **kwargs)

        def http_connect(connection):
            destination = (getattr(connection, "_tunnel_host", None) or connection.host or "").lower().rstrip(".")
            log._add(log.destinations, destination)
            if log.block and destination not in ALLOWED_HOSTS:
                log._add(log.blocked, destination)
                raise BlockedRequest(destination, host_category(destination) or "not the wiki host")
            return log._http_connect(connection)

        socket.getaddrinfo, socket.create_connection = getaddrinfo, create_connection
        http.client.HTTPConnection.connect = http_connect
        return self

    def __exit__(self, *exc):
        socket.getaddrinfo, socket.create_connection = self._getaddrinfo, self._create_connection
        http.client.HTTPConnection.connect = self._http_connect
        return False

    def summary(self):
        destinations = sorted(set(self.destinations))
        return {"http_connections": len(self.destinations), "http_destinations": destinations,
                "non_wiki_destinations": [h for h in destinations if h not in ALLOWED_HOSTS],
                "ad_destinations": [h for h in destinations if host_category(h) == "ad"],
                "dns_lookups": sorted(set(self.lookups)), "tcp_connections": len(self.connections),
                "blocked": sorted(set(self.blocked))}


# --- whole-page inventory (audits and the command line) -----------------------

class _Inventory(HTMLParser):
    """Every ad element on a page and whether it sits inside the article.

    The open elements are kept with the positions of each tag name and with counts of the open article
    containers, so an end tag and the zone of an element cost the same at any depth (a page that nested 16,000
    <div> took the square of that)."""
    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
            "param", "source", "track", "wbr"}

    def __init__(self, base_url):
        super().__init__(convert_charrefs=True)
        self.base_url, self.stack, self.items = base_url, [], []
        self.open_at = {}                  # tag -> positions in self.stack, ascending
        self.inner = self.article = 0      # open #page-body-inner elements / open article containers
        self.raw_tag = None
        self.script_hosts = {}

    def _zone(self):
        if self.inner and self.article:
            return "article"
        return "article_container_other" if self.inner else "outside_article_container"

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        found = classify_element(tag, attrs, self.base_url)
        if found:
            self.items.append({"kind": found[0], "reason": found[1], "tag": tag,
                               "zone": self._zone(), "source_line": self.getpos()[0]})
        if tag in {"script", "style"}:
            self.raw_tag = tag
        if tag not in self.VOID:
            inner, article = attrs.get("id") == "page-body-inner", bool(_tokens(attrs, "class") & ARTICLE_CLASSES)
            self.open_at.setdefault(tag, []).append(len(self.stack))
            self.stack.append((tag, inner, article))
            self.inner += inner
            self.article += article

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in self.VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if tag == self.raw_tag:
            self.raw_tag = None
        positions = self.open_at.get(tag)
        if not positions:
            return                         # nothing of this name is open
        position = positions[-1]
        for name, inner, article in self.stack[position:]:
            self.open_at[name].pop()
            self.inner -= inner
            self.article -= article
        del self.stack[position:]

    def handle_data(self, data):
        if self.raw_tag == "script":
            for match in _URL_IN_TEXT.finditer(data):
                url = match.group()
                url = "https:" + url if url.startswith("//") else url
                if url_category(url) == "ad":
                    host = _host(url)
                    self.script_hosts[host] = self.script_hosts.get(host, 0) + 1


def inventory(html, base_url):
    """Ad and chrome elements of a whole page, grouped by zone.

    zone 'article' is .user-area/.footer-footnote inside #page-body-inner,
    the only part the reader returns.
    """
    parser = _Inventory(base_url)
    parser.feed(html)
    parser.close()
    zones = {}
    for item in parser.items:
        zone = zones.setdefault(item["zone"], {"ad": 0, "chrome": 0})
        zone[item["kind"]] += 1
    hosts = {}
    for item in parser.items:
        if item["reason"].startswith("ad_host:"):
            host = item["reason"].split(":", 1)[1]
            hosts[host] = hosts.get(host, 0) + 1
    return {"elements": len(parser.items), "by_zone": zones, "ad_hosts_in_markup": hosts,
            "ad_hosts_in_inline_scripts": parser.script_hosts,
            "article_ad_elements": [item for item in parser.items
                                    if item["zone"] == "article" and item["kind"] == "ad"][:40],
            "samples": parser.items[:40]}


def main(argv=None):
    import argparse
    import json
    import sys
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, OSError, ValueError):
            pass
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = cli.add_subparsers(dest="command", required=True)
    sub.add_parser("rules", help="print the rule lists")
    audit = sub.add_parser("audit", help="locate ad elements in a saved HTML page (no network)")
    audit.add_argument("html", help="saved page, e.g. from the reader's --save-html")
    audit.add_argument("--url", default="https://seesaawiki.jp/hololivetv/", help="page URL (for relative links)")
    audit.add_argument("--encoding", default="euc_jis_2004", help="decoding of the saved bytes (default: euc_jis_2004)")
    args = cli.parse_args(argv)
    if args.command == "rules":
        print(json.dumps({"version": VERSION, "allowed_hosts": sorted(ALLOWED_HOSTS), "ad_hosts": sorted(AD_HOSTS),
                          "tracking_hosts": sorted(TRACKING_HOSTS), "affiliate_hosts": sorted(AFFILIATE_HOSTS),
                          "affiliate_query": AFFILIATE_QUERY, "ad_classes": sorted(AD_CLASSES), "ad_ids": sorted(AD_IDS),
                          "ad_id_prefixes": list(AD_ID_PREFIXES), "ad_data_attributes": sorted(AD_DATA_ATTRIBUTES),
                          "chrome_ids": sorted(CHROME_IDS), "chrome_classes": sorted(CHROME_CLASSES)},
                         ensure_ascii=False, indent=1))
        return 0
    with open(args.html, "rb") as stream:
        html = stream.read().decode(args.encoding, errors="replace")
    print(json.dumps(inventory(html, args.url), ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
