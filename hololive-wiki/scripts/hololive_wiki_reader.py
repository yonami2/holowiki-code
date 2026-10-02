#!/usr/bin/env python3
"""Read one public Seesaa hololive wiki page; Python 3.9+, standard library only."""

import argparse
import base64
import bisect
import codecs
import difflib
import gzip
import hashlib
import http.client
import importlib.util
import io
import json
import math
import os
import re
import socket
import ssl
import sys
import tempfile
import time
import zlib
from datetime import datetime, timezone
from email.message import Message
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote, quote_from_bytes, unquote_to_bytes, urljoin, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

MAX_BYTES = 24 * 1024 * 1024
MAX_GRID_CELLS = 1_000_000
MAX_PAGE_GRID_CELLS = 4_000_000
MAX_PAGE_GRID_WORK = 4_000_000
VERSION = "3.9.0+skill.6"
DEFAULT_UA = "HololiveWikiReader/3.9.0 (Python urllib; public single-page reader)"
DESKTOP_UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/130.0.0.0 Safari/537.36 HololiveWikiReader/3.2"
REDIRECT_CODES = {301, 302, 303, 307, 308}
RETRY_CODES = {408, 429, 500, 502, 503, 504}
# Seconds. A socket timeout the platform cannot hold makes urllib raise OverflowError (about 9e9 s on Linux, 2**31
# milliseconds = 2.1e6 s on Windows), and a Retry-After of 400 digits is infinity, which JSON cannot carry: neither
# is taken above this (11.6 days).
MAX_SECONDS = 10 ** 6
# Bytes per read. One read(n) allocates n bytes before it reads any (a limit of 1 TiB is a MemoryError, one beyond
# the C index limit an OverflowError), so a file or a decompressed body is read in pieces up to the limit.
READ_CHUNK = 1 << 20

# How the caller named the page. These describe one invocation, not the stored
# response, so a cache record must not carry them into a later run.
REQUEST_RESOLUTION_KEYS = frozenset({
    "requested_title", "title_used", "title_source", "title_url_source",
    "title_observed_urls", "title_encoding", "title_normalized"})

# Cached metadata describes the response, never parsed output or display mode.
# Restrict replayed fields so an unknown/stale field cannot override the result.
RESPONSE_METADATA_KEYS = frozenset({
    "requested_url", "url", "http_status", "content_type", "content_encoding",
    "vary", "user_agent", "wire_bytes", "html_bytes", "http_requests",
    "redirects", "retry_history", "fetched_at", "layout_fallback",
    "fetch_warnings", "source", "from_cache", "network_hosts"})

# A nickname cell holding only one of these is a placeholder for "none", not a
# name. Only an entire cell value is compared; text is never edited.
PLACEHOLDER_CELL_VALUES = frozenset({
    "-", "‐", "–", "—", "―", "−", "－", "ー"})


class ReaderError(Exception):
    def __init__(self, code, message, **details):
        super().__init__(message)
        self.code, self.details = code, details


AD_FILTER_MODES = ("strict", "report", "off")


def load_adblock():
    """The ad-filter module stored next to this reader (hololive_adblock.py)."""
    path = Path(__file__).resolve().with_name("hololive_adblock.py")
    if not path.is_file():
        raise ReaderError("ad_filter_missing", "hololive_adblock.py must sit next to the reader. "
                          "Use --ad-filter off only to read without advertisement filtering.", path=str(path))
    module = sys.modules.get("hololive_adblock")
    if module is not None and Path(getattr(module, "__file__", "")).resolve() == path:
        return module
    spec = importlib.util.spec_from_file_location("hololive_adblock", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["hololive_adblock"] = module
    # The skill runs this reader from its scripts/ folder, which stays as shipped: no __pycache__ beside it.
    writes, sys.dont_write_bytecode = sys.dont_write_bytecode, True
    try:
        spec.loader.exec_module(module)
    except Exception:
        del sys.modules["hololive_adblock"]
        raise
    finally:
        sys.dont_write_bytecode = writes
    return module


def validate_wiki_name(name):
    """Accept a literal Seesaa wiki slug, never a URL or encoded path."""
    if (not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,128}", name)
            or "hololive" not in name.lower()):
        raise ReaderError("invalid_wiki", "Use a literal Seesaa wiki name containing hololive, such as hololivetv or hololivedreams.")
    return name


def wiki_base(wiki="hololivetv"):
    return "https://seesaawiki.jp/" + validate_wiki_name(wiki) + "/"


def wiki_from_url(url):
    """Return the wiki of an already validated or explicitly supplied URL."""
    return urlsplit(check_url(url)).path.split("/", 2)[1]


def check_url(url, *, wiki=None):
    """Validate WITHOUT decoding/re-encoding the URL that will be requested."""
    if not isinstance(url, str) or not url:
        raise ReaderError("invalid_url", "URL must be a nonempty string.")
    # A fragment is browser navigation, never part of an HTTP request. Split
    # before transport validation so observed Japanese headings remain usable.
    # Literal '#' only: %23 belongs to the request path/query and is preserved.
    url = url.partition("#")[0]
    if "\ufffd" in url or "%ef%bf%bd" in url.lower():
        raise ReaderError("corrupted_url", "Replacement characters cannot be recovered. Use the original link or --title with an observed title.")
    if not url.isascii() or re.search(r"[\x00-\x20\x7f\\]", url):
        raise ReaderError("invalid_url", "Keep the original ASCII percent-encoded URL; use --title for an observed Japanese title.")
    if re.search(r"%(?![0-9A-Fa-f]{2})", url):
        raise ReaderError("invalid_url", "Malformed percent escape in URL.")
    try:
        parts = urlsplit(url)
    except ValueError as exc:
        raise ReaderError("invalid_url", str(exc)) from exc
    if parts.scheme != "https" or parts.netloc != "seesaawiki.jp":
        raise ReaderError("url_out_of_scope", "Only HTTPS URLs on seesaawiki.jp may be fetched.")
    slug = parts.path.split("/", 2)[1] if parts.path.startswith("/") else ""
    try:
        validate_wiki_name(slug)
    except ReaderError as exc:
        raise ReaderError("url_out_of_scope", "The literal wiki name must contain hololive.") from exc
    if wiki is not None and slug != validate_wiki_name(wiki):
        raise ReaderError("url_out_of_scope", "The URL belongs to a different wiki; select its exact --wiki name.", selected_wiki=wiki, url_wiki=slug)
    prefix = "/" + slug + "/"
    # Decode a COPY for structural validation only. Never use this copy as a URL.
    path = unquote_to_bytes(parts.path)
    if b"\\" in path or any(c < 32 or c == 127 for c in path) or any(p in {b".", b".."} for p in path.split(b"/")):
        raise ReaderError("invalid_url", "Control characters or dot traversal in the URL path.")
    if parts.path != prefix and not parts.path.startswith(prefix + "d/"):
        raise ReaderError("url_out_of_scope", "This reader fetches only the wiki root and /d/ articles; it does not fetch listing, search, API or editing routes.")
    return url


def url_identity(url):
    """Equality/cache key only: percent-escape hex digits are case-insensitive.

    Keep observed spellings for requests and provenance. Do not decode percent
    escapes, change literal path/query case, reorder queries, or fold titles.
    """
    return re.sub(r"%[0-9A-Fa-f]{2}", lambda match: match.group().upper(), check_url(url))


def article_url(url):
    """The wiki article path, retaining its observed percent-escape spelling.

    Query parameters select a representation of a /d/ article. A title lookup
    requests its unfiltered article path; an explicit --url retains the query.
    """
    return urlsplit(check_url(url))._replace(query="", fragment="").geturl()


def article_identity(url):
    """Title equality: omit the query and fold RFC 3986 unreserved escapes.

    Reserved escapes such as %2F stay encoded. This key never replaces an
    observed URL in a request or the full-URI HTTP cache key.
    """
    plain = url_identity(article_url(url))
    return re.sub(r"%[0-9A-F]{2}",
                  lambda match: chr(int(match.group()[1:], 16))
                  if chr(int(match.group()[1:], 16)) in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~"
                  else match.group(), plain)


def encode_title(title):
    """Encode an exact title, preserving EUC-JP bytes before adding extensions.

    JIS2004 decoding agrees with strict EUC-JP, but its encoder may choose
    different bytes for the same character (for example, copyright sign).
    Re-encode individual decoded EUC units through EUC-JP when possible.
    A unit can contain two Unicode code points, such as kana + handakuten;
    splitting such a unit into individual characters would lose its mapping.
    """
    if not title or not title.strip() or re.search(r"[\x00-\x1f\x7f]", title):
        raise ReaderError("invalid_title", "Use a nonempty, exact, previously observed page title.")
    message = ("This title cannot be encoded exactly using EUC-JP with supported "
               "JIS2004 extensions. Use its observed original URL; the title "
               "will not be silently normalized or replaced.")
    try:
        encoded = title.encode("euc-jp")
    except UnicodeEncodeError:
        pass
    else:
        # EUC-JP's yen/overline aliases otherwise change the page title into
        # backslash/ASCII tilde even though encoding succeeds.
        if encoded.decode("euc-jp") != title:
            raise ReaderError("title_not_euc_jp", message)
        return encoded, "euc_jp"
    try:
        extended = title.encode("euc_jis_2004")
        if extended.decode("euc_jis_2004") != title:
            raise ReaderError("title_not_euc_jp", message)
        pieces = []
        offset = 0
        while offset < len(extended):
            lead = extended[offset]
            width = 1 if lead < 0x80 else 3 if lead == 0x8F else 2
            unit = extended[offset:offset + width]
            text = unit.decode("euc_jis_2004")
            try:
                legacy = text.encode("euc-jp")
            except UnicodeEncodeError:
                pieces.append(unit)
            else:
                pieces.append(legacy if legacy.decode("euc-jp") == text else unit)
            offset += width
        encoded = b"".join(pieces)
        if encoded.decode("euc_jis_2004") != title:
            raise ReaderError("title_not_euc_jp", message)
        return encoded, "euc_jp_with_jis2004_extensions"
    except UnicodeError as exc:
        raise ReaderError("title_not_euc_jp", message) from exc


def encoded_title_url(encoded, wiki="hololivetv"):
    """The one place an article URL is built from encoded title bytes."""
    return check_url(wiki_base(wiki) + "d/" + quote_from_bytes(encoded, safe="/"), wiki=wiki)


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None

    # urllib's usual redirect handler drains bodies without a size bound.
    # Return the response untouched and let fetch_page validate each next hop.
    def http_error_302(self, req, fp, code, msg, headers):
        return fp

    http_error_301 = http_error_303 = http_error_307 = http_error_308 = http_error_302


def redirect_url(current, location):
    if not location:
        raise ReaderError("invalid_redirect", "Redirect Location is missing or contains whitespace/control characters.")
    location = location.partition("#")[0]
    if re.search(r"[\x00-\x20\x7f\\]", location):
        raise ReaderError("invalid_redirect", "Redirect Location is missing or contains whitespace/control characters.")
    # HTTP header fields are exposed by http.client using ISO-8859-1.
    # Quoting raw bytes preserves unescaped EUC-JP bytes in a Location header.
    try:
        location = quote(location, safe="!#$%&'()*+,-./:;=?@[]_~", encoding="iso-8859-1", errors="strict")
    except UnicodeError as exc:
        raise ReaderError("invalid_redirect", "Redirect Location contains unsupported unencoded characters.") from exc
    try:
        target = urljoin(current, location)
    except ValueError as exc:
        raise ReaderError("invalid_redirect", str(exc)) from exc
    return check_url(target, wiki=wiki_from_url(current))


def remaining(deadline):
    value = deadline - time.monotonic()
    if value <= 0:
        raise ReaderError("time_budget_exceeded", "The network time budget was exhausted.")
    return value


def read_response(response, limit, deadline):
    if response.headers.get("Content-Range"):
        raise ReaderError("partial_response", "A partial response cannot be treated as the whole page.")
    lengths = response.headers.get_all("Content-Length", [])
    expected = None
    if lengths:
        values = [v.strip() for header in lengths for v in header.split(",")]
        if not values or any(not re.fullmatch(r"[0-9]+", v) for v in values) or len(set(values)) != 1:
            raise ReaderError("invalid_content_length", "Invalid or conflicting Content-Length values.")
        expected = int(values[0])
        if expected > limit:
            raise ReaderError("page_too_large", "Response exceeds the byte limit.", limit=limit)
    if expected is not None and response.headers.get("Transfer-Encoding"):
        raise ReaderError("ambiguous_framing", "Both Transfer-Encoding and Content-Length were supplied.")
    chunks, total = [], 0
    read = getattr(response, "read1", response.read)
    while True:
        remaining(deadline)
        block = read(min(65536, limit + 1 - total))
        if not block:
            break
        total += len(block)
        if total > limit:
            raise ReaderError("page_too_large", "Response exceeds the byte limit.", limit=limit)
        chunks.append(block)
    remaining(deadline)
    if expected is not None and total != expected:
        raise ReaderError("truncated_response", "Response length differs from Content-Length.", expected_bytes=expected, received_bytes=total)
    return b"".join(chunks)


def path_exists(path):
    """Path.exists(), False (as in Python 3.14) for a name no file system can look up: Python before 3.14 raises
    OSError for a name that is too long, so a long --cache-dir or --index-file was a traceback."""
    try:
        return path.exists()
    except (OSError, ValueError):
        return False


def read_up_to(stream, size):
    """At most `size` bytes of a binary stream, read READ_CHUNK at a time."""
    chunks, total = [], 0
    while total < size:
        block = stream.read(min(READ_CHUNK, size - total))
        if not block:
            break
        chunks.append(block)
        total += len(block)
    return b"".join(chunks)


def decompress_body(raw, content_encoding, limit):
    encoding = (content_encoding or "identity").strip().lower()
    if encoding in {"", "identity"}:
        return raw
    if encoding not in {"gzip", "x-gzip", "deflate"}:
        raise ReaderError("unsupported_compression", "Unsupported Content-Encoding.", content_encoding=encoding)
    try:
        if encoding in {"gzip", "x-gzip"}:
            with gzip.GzipFile(fileobj=io.BytesIO(raw)) as stream:
                decoded = read_up_to(stream, limit + 1)
        else:
            decoded = None
            for window in (zlib.MAX_WBITS, -zlib.MAX_WBITS):
                try:
                    decoder = zlib.decompressobj(window)
                    candidate = decoder.decompress(raw, min(limit + 1, sys.maxsize))
                except zlib.error:
                    if window == -zlib.MAX_WBITS:
                        raise
                    continue
                if len(candidate) > limit or decoder.unconsumed_tail:
                    raise ReaderError("page_too_large", "Decompressed page exceeds the byte limit.", limit=limit)
                if not decoder.eof or decoder.unused_data:
                    if window == zlib.MAX_WBITS:
                        # A raw stream can also begin with a valid zlib header.
                        # Try its complete raw interpretation before rejecting.
                        continue
                    raise ReaderError("invalid_compression", "Incomplete deflate stream or unexpected trailing data.")
                decoded = candidate
                break
        if len(decoded) > limit:
            raise ReaderError("page_too_large", "Decompressed page exceeds the byte limit.", limit=limit)
        return decoded
    except (EOFError, OSError, zlib.error) as exc:
        raise ReaderError("invalid_compression", "The compressed response is damaged or incomplete.") from exc


def retry_after_seconds(value):
    if not value:
        return None
    if re.fullmatch(r"[0-9]+", value.strip()):
        return min(float(value.strip()), float(MAX_SECONDS))
    try:
        parsed = parsedate_to_datetime(value)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=timezone.utc)
        return min(max(0.0, (parsed - datetime.now(timezone.utc)).total_seconds()), float(MAX_SECONDS))
    except (ValueError, TypeError, OverflowError):
        return None


def transient_network_error(error):
    cause = error.reason if isinstance(error, URLError) else error
    if isinstance(cause, (ssl.SSLCertVerificationError, ssl.SSLError)):
        return False
    if isinstance(cause, socket.gaierror):
        return cause.errno == socket.EAI_AGAIN
    return isinstance(cause, (TimeoutError, ConnectionError, http.client.IncompleteRead, http.client.RemoteDisconnected))


class RateLimiter:
    """Minimum start-to-start interval within one process, including redirects."""
    def __init__(self, interval=0.5):
        self.interval = interval
        self.last = None

    def wait(self, deadline):
        if self.last is not None:
            delay = self.interval - (time.monotonic() - self.last)
            if delay > 0:
                if delay >= remaining(deadline):
                    raise ReaderError("time_budget_exceeded", "The rate-limit wait exceeds the network budget.")
                time.sleep(delay)
        self.last = time.monotonic()


def fetch_page(url, *, timeout=20.0, retries=2, time_budget=90.0, max_bytes=MAX_BYTES, opener=None,
               user_agent=DEFAULT_UA, rate_limiter=None):
    requested_url = check_url(url)
    opener = opener or build_opener(NoRedirect())
    deadline = time.monotonic() + time_budget
    attempts = 0
    history = []
    for attempt in range(retries + 1):
        current, visited, redirects = requested_url, {requested_url}, []
        retry_hint = None
        try:
            for hop in range(6):
                if rate_limiter is not None:
                    rate_limiter.wait(deadline)
                request = Request(current, headers={
                    "User-Agent": user_agent,
                    "Accept": "text/html, application/xhtml+xml;q=0.9",
                    "Accept-Encoding": "gzip, deflate",
                    "Accept-Language": "ja,en;q=0.5",
                })
                socket_timeout = min(timeout, remaining(deadline), MAX_SECONDS)     # a request that has no time is not counted
                attempts += 1
                try:
                    response = opener.open(request, timeout=socket_timeout)
                except HTTPError as exc:
                    response = exc
                with response:
                    status = response.getcode()
                    final_url = check_url(response.geturl(), wiki=wiki_from_url(requested_url))
                    if status in REDIRECT_CODES:
                        target = redirect_url(final_url, response.headers.get("Location"))
                        if target in visited:
                            raise ReaderError("redirect_loop", "A redirect loop was detected.")
                        if hop == 5:
                            raise ReaderError("too_many_redirects", "More than five redirects were requested.")
                        redirects.append({"status": status, "from": final_url, "to": target})
                        visited.add(target)
                        current = target
                        continue
                    if status != 200:
                        retry_hint = retry_after_seconds(response.headers.get("Retry-After"))
                        raise ReaderError("http_error", "HTTP request failed; a 404 alone does not establish URL corruption.", http_status=status, url=final_url)
                    content_type = response.headers.get("Content-Type", "")
                    media = response.headers.get_content_type()
                    if content_type and media not in {"text/html", "application/xhtml+xml"}:
                        raise ReaderError("not_html", "Response has a non-HTML Content-Type.", content_type=content_type)
                    wire = read_response(response, max_bytes, deadline)
                    raw = decompress_body(wire, response.headers.get("Content-Encoding"), max_bytes)
                    if not content_type and not has_html_evidence(raw):
                        raise ReaderError("not_html", "Missing Content-Type and no recognizable HTML prefix.")
                    return raw, {
                        "requested_url": requested_url, "url": final_url,
                        "network_hosts": sorted({urlsplit(item).hostname for item in visited}),
                        "http_status": status, "content_type": content_type,
                        "content_encoding": response.headers.get("Content-Encoding", "identity"),
                        "vary": response.headers.get("Vary", ""), "user_agent": user_agent,
                        "wire_bytes": len(wire), "html_bytes": len(raw),
                        "http_requests": attempts, "redirects": redirects,
                        "retry_history": history,
                        "fetched_at": datetime.now(timezone.utc).isoformat(),
                    }
        except (ReaderError, URLError, OSError, http.client.HTTPException) as exc:
            if isinstance(exc, ReaderError):
                retryable = (exc.code == "http_error" and exc.details.get("http_status") in RETRY_CODES) or exc.code == "truncated_response"
                failure = exc
            else:
                retryable = transient_network_error(exc)
                failure = ReaderError("network_error", "Public HTTP access failed.", exception=type(exc).__name__, reason=str(exc))
                if isinstance(exc, URLError) and isinstance(exc.reason, BaseException):
                    # What urllib wrapped: gaierror for a failed name lookup, TimeoutError, ConnectionRefusedError, ...
                    failure.details["reason_exception"] = type(exc.reason).__name__
            if not retryable or attempt == retries:
                failure.details.update(http_requests=attempts, retry_history=history)
                raise failure from exc
            delay = max(0.5 * (2 ** attempt), retry_hint or 0)
            left = deadline - time.monotonic()
            if left <= 0:
                raise ReaderError("time_budget_exceeded", "The network time budget was exhausted.",
                                  http_requests=attempts, retry_history=history) from exc
            if delay > 30 or delay >= left:
                raise ReaderError("retry_deferred", "Retry-After/backoff exceeds the remaining budget. Try again later.",
                                  retry_after_seconds=delay, last_error=failure.code,
                                  http_requests=attempts, retry_history=history) from exc
            history.append({"error_code": failure.code, "http_status": failure.details.get("http_status"), "wait_seconds": delay})
            time.sleep(delay)
    raise ReaderError("network_error", "No response was obtained.")


class MetaCharset(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.charsets = []
        self.in_body = False
        self.skip = []

    def handle_starttag(self, tag, attrs):
        if tag == "body":
            self.in_body = True
        if tag in {"script", "style", "noscript", "template"}:
            self.skip.append(tag)
        if self.in_body or self.skip or tag != "meta":
            return
        attrs = dict(attrs)
        if attrs.get("charset"):
            self.charsets.append(attrs["charset"].strip())
        elif (attrs.get("http-equiv") or "").lower() == "content-type":      # a bare attribute parses to None
            msg = Message()
            msg["Content-Type"] = attrs.get("content") or ""
            value = msg.get_content_charset()
            if value:
                self.charsets.append(value)

    def handle_endtag(self, tag):
        if self.skip and self.skip[-1] == tag:
            self.skip.pop()


def text_codec(label):
    if not label:
        return None
    try:
        info = codecs.lookup(label.strip())
        if info.name in {"idna", "punycode", "unicode-escape", "raw-unicode-escape", "undefined"}:
            return None
        sample = b"x".decode(info.name, errors="replace")
        if not isinstance(sample, str):
            return None
        return info.name
    except (LookupError, TypeError, ValueError, UnicodeError):
        return None


def audit_euc_extensions(raw, limit=40):
    """Audit every non-ASCII unit; limit examples, never aggregate counts.

    Agreement of Python's strict JIS2004 and CP932 decoders for an exact NEC
    row-13 unit is useful evidence for common symbols such as ① and Ⅱ. It is
    not proof of the source's encoding. Neither the whole AD row nor SS3 (8F)
    units are automatically trusted, and F5-FE is not inherently unmappable.
    """
    pattern = rb"\x8e[\xa1-\xdf]|\x8f[\xa1-\xfe]{2}|[\xa1-\xfe]{2}|[\x80-\xff]"
    known, counts = {}, {}
    newlines = [i for i, value in enumerate(raw) if value == 10]
    total = 0
    for match in re.finditer(pattern, raw):
        unit = match.group()
        if unit not in known:
            try:
                unit.decode("euc_jp", errors="strict")
                known[unit] = False
            except UnicodeError:
                known[unit] = True
        if not known[unit]:
            continue
        total += 1
        if unit not in counts:
            category = "source_mapping_unconfirmed"
            basis = "EUC-JIS-2004 fallback; source extension mapping not established."
            try:
                rendered = unit.decode("euc_jis_2004", errors="strict")
            except UnicodeError:
                rendered = unit.decode("euc_jis_2004", errors="replace")
                category = "undecodable_unit"
                basis = "Neither strict EUC-JP nor strict EUC-JIS-2004 decodes this unit."
            else:
                if len(unit) == 2 and unit[0] == 0xAD:
                    trail = unit[1] - 0x61 + (unit[1] >= 0xE0)
                    try:
                        common = bytes((0x87, trail)).decode("cp932", errors="strict")
                    except UnicodeError:
                        common = None
                    if common == rendered:
                        category = "common_nec_mapping_agrees"
                        basis = "Python JIS2004 and CP932 row-13 decoders agree; this does not verify the source encoding."
            counts[unit] = {"bytes_hex": unit.hex(), "rendered": rendered,
                            "count": 0, "byte_offsets": [], "html_lines": [],
                            "status": "outside_declared_euc_jp; " + category,
                            "category": category, "mapping_basis": basis}
        entry = counts[unit]
        entry["count"] += 1
        if len(entry["byte_offsets"]) < 5:
            entry["byte_offsets"].append(match.start())
            entry["html_lines"].append(bisect.bisect_right(newlines, match.start()) + 1)
    entries = sorted(counts.values(), key=lambda e: (-e["count"], e["bytes_hex"]))
    categories = {name: {"occurrences": 0, "distinct_units": 0} for name in (
        "common_nec_mapping_agrees", "source_mapping_unconfirmed", "undecodable_unit")}
    for entry in entries:
        category = categories[entry["category"]]
        category["occurrences"] += entry["count"]
        category["distinct_units"] += 1
    return {"occurrences": total, "distinct_units": len(entries), "samples": entries[:limit],
            "samples_truncated": len(entries) > limit, "byte_offsets_base": 0, "html_lines_base": 1,
            "categories": categories}


def audit_byte_replacements(raw, html, encoding, lossy):
    total = html.count("\ufffd")
    literal, introduced = total, 0
    method = "strict_decode"
    if lossy:
        literal = 0
        replay_encoding = encoding
        boms = {"utf-16": (codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE),
                "utf-32": (codecs.BOM_UTF32_LE, codecs.BOM_UTF32_BE)}
        if encoding in boms and not raw.startswith(boms[encoding]):
            replay_encoding += "-le" if sys.byteorder == "little" else "-be"
        decoder = codecs.getincrementaldecoder(replay_encoding)(errors="ignore")
        for start in range(0, len(raw), 65536):
            literal += decoder.decode(raw[start:start + 65536], final=False).count("\ufffd")
        literal += decoder.decode(b"", final=True).count("\ufffd")
        introduced = total - literal
        method = "replace_total_minus_literal_count_from_ignore_replay"
    return {
        "scope": "whole_decoded_html_before_html_parsing",
        "encoding": encoding,
        "replacement_characters": total,
        "decoder_introduced_replacements": introduced,
        "source_literal_replacements": literal,
        "method": method,
        "limitation": (
            "Counts describe decoding under the selected encoding, not the intended text, "
            "the cause of invalid bytes, or whether a later response will change. "
            "Source literals are bytes that decode to U+FFFD without error handling. "
            "HTML numeric references are excluded; see html_reference_audit."
        ),
    }


def decode_page(raw, content_type="", override=None):
    warnings = []
    message = Message()
    message["Content-Type"] = content_type
    declared = message.get_content_charset()
    parser = MetaCharset()
    parser.feed(_LONG_DECIMAL_REFERENCE.sub(lambda m: " " * len(m.group()), raw[:65536].decode("latin-1")))
    meta = next((value for value in parser.charsets if text_codec(value)), None)
    for label in [declared] + parser.charsets:
        if label and not text_codec(label):
            warnings.append("Unsupported charset declaration ignored: " + label)
    header_codec, meta_codec = text_codec(declared), text_codec(meta)
    if header_codec and meta_codec and header_codec != meta_codec:
        warnings.append("HTTP and HTML meta charsets disagree; the HTTP declaration takes priority.")
    if override:
        chosen, source = text_codec(override), "explicit_override"
        if not chosen:
            raise ReaderError("invalid_encoding", "The requested encoding is not a supported text codec.")
        warnings.append("Character encoding was explicitly overridden.")
    elif header_codec:
        chosen, source = header_codec, "http_header"
    elif raw.startswith(codecs.BOM_UTF8):
        chosen, source = "utf-8-sig", "bom"
    elif raw.startswith((codecs.BOM_UTF32_LE, codecs.BOM_UTF32_BE)):
        chosen, source = "utf-32", "bom"
    elif raw.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)):
        chosen, source = "utf-16", "bom"
    elif meta_codec:
        chosen, source = meta_codec, "html_meta"
    else:
        chosen, source = "euc_jp", "site_default"
        warnings.append("No supported HTTP/meta charset was found; using the site's EUC-JP default.")
    if chosen == "utf-8" and raw.startswith(codecs.BOM_UTF8):
        chosen = "utf-8-sig"
    used, replaced = chosen, False
    try:
        html = raw.decode(chosen, errors="strict")
    except UnicodeError as first:
        if chosen == "euc_jp":
            try:
                html = raw.decode("euc_jis_2004", errors="strict")
                used = "euc_jis_2004"
                warnings.append("Strict EUC-JP failed; decoded with EUC-JIS-2004. See encoding_audit for extension classification.")
            except UnicodeError as fallback_error:
                used = "euc_jis_2004"
                html = raw.decode(used, errors="replace")
                replaced = True
                first = fallback_error
        else:
            html = raw.decode(chosen, errors="replace")
            replaced = True
        if replaced:
            warnings.append(
                "Undecodable bytes were replaced under the selected encoding. "
                "This does not establish transfer damage, permanently invalid source data, "
                "or whether the charset declaration is correct. Do not rely on affected "
                "names, quotations, or cells. First error in the selected decoder: " + str(first)
            )
    byte_replacements = audit_byte_replacements(raw, html, used, replaced)
    if byte_replacements["source_literal_replacements"]:
        warnings.append(
            f"The raw response decodes to {byte_replacements['source_literal_replacements']} "
            "literal U+FFFD character(s) without error replacement. These are separate from "
            "decoder-introduced replacements; their intended text and cause are unknown. "
            "See byte_replacement_audit."
        )
    audit = audit_euc_extensions(raw) if chosen == "euc_jp" and (used != chosen or replaced) else {
        "occurrences": 0, "distinct_units": 0, "samples": [], "samples_truncated": False,
        "byte_offsets_base": 0, "html_lines_base": 1,
        "categories": {name: {"occurrences": 0, "distinct_units": 0} for name in (
            "common_nec_mapping_agrees", "source_mapping_unconfirmed", "undecodable_unit")}}
    unconfirmed = audit["categories"]["source_mapping_unconfirmed"]
    if unconfirmed["occurrences"]:
        warnings.append(f"{unconfirmed['occurrences']} occurrence(s) in {unconfirmed['distinct_units']} byte-unit type(s) use extension mappings not confirmed for the source. See encoding_audit (samples may be limited).")
    return html, {
        "encoding_declared": declared, "encoding_meta": meta,
        "encoding_source": source, "encoding_used": used,
        "decode_lossy": replaced, "replacement_characters": byte_replacements["replacement_characters"],
        "byte_replacement_audit": byte_replacements,
        "encoding_audit": audit,
        "warnings": warnings,
    }


_NUMERIC_REFERENCE = re.compile(r"&#(?:[xX][0-9a-fA-F]+|[0-9]+);?")
_LONG_DECIMAL_REFERENCE = re.compile(r"&#[0-9]{129,};?")
_RAW_ATTRIBUTE = re.compile(r'''([^\s/>=]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+)))?''')


def _bounded_reference_value(token):
    hexadecimal = token[2:3] in {"x", "X"}
    digits = token[3 if hexadecimal else 2:].rstrip(";").lstrip("0") or "0"
    if len(digits) > (6 if hexadecimal else 7):
        return 0x110000
    return int(digits, 16 if hexadecimal else 10)


class _CharrefContexts(HTMLParser):
    """Locate source text and attribute values without unescaping their bytes."""
    def __init__(self, source):
        super().__init__(convert_charrefs=False)
        self.source, self.ranges, self.raw_tag = source, [], None
        self.line_starts = [0] + [m.end() for m in re.finditer("\n", source)]

    def source_offset(self):
        line, column = self.getpos()
        return self.line_starts[line - 1] + column

    def add(self, start, end, context, pair_allowed=True):
        if end <= start:
            return
        if (self.ranges and self.ranges[-1][1] == start
                and self.ranges[-1][2:] == (context, pair_allowed)):
            previous = self.ranges[-1]
            self.ranges[-1] = (previous[0], end, context, pair_allowed)
        else:
            self.ranges.append((start, end, context, pair_allowed))

    def handle_data(self, data):
        if self.raw_tag is None:
            start = self.source_offset()
            self.add(start, start + len(data), "text")

    def handle_charref(self, name):
        if self.raw_tag is None:
            start = self.source_offset()
            match = _NUMERIC_REFERENCE.match(self.source, start)
            if match:
                self.add(start, match.end(), "text")

    def handle_starttag(self, tag, attrs):
        if self.raw_tag is not None:
            return
        raw_element = tag in {"script", "style"}
        if raw_element:
            self.raw_tag = tag
        start = self.source_offset()
        raw = self.source[start:start + len(self.get_starttag_text())]
        tag_match = re.match(r"<\s*[^\s/>]+", raw)
        if not tag_match:
            return
        for attr in _RAW_ATTRIBUTE.finditer(raw, tag_match.end()):
            name = attr.group(1).lower()
            group = next((i for i in (2, 3, 4) if attr.group(i) is not None), None)
            if group is not None:
                self.add(start + attr.start(group), start + attr.end(group), "attribute:" + name, not raw_element and name in {"title", "alt"})

    def handle_endtag(self, tag):
        if self.raw_tag == tag:
            self.raw_tag = None


def prepare_surrogate_charrefs(html, mode="html"):
    if mode not in {"html", "utf16"}:
        raise ReaderError("invalid_charref_mode", "Use html or utf16 for surrogate character references.")
    report = {
        "mode": mode, "raw_source_preserved": True, "scoped_scan_performed": False,
        "scope": "whole_document_text_and_title_alt_attributes",
        "policy": "HTML replacement semantics" if mode == "html" else "Explicit nonstandard UTF-16 compatibility interpretation",
        "eligible_surrogate_pairs": 0, "joined_surrogate_pairs": 0,
        "unpaired_surrogate_refs": 0, "numeric_reference_normalizations": 0,
        "samples": [], "samples_truncated": False, "sample_limit": 40,
        "character_offsets_base": 0, "html_lines_base": 1,
    }
    has_long_decimal = _LONG_DECIMAL_REFERENCE.search(html) is not None
    if mode == "html" and not has_long_decimal:
        return html, report
    if not has_long_decimal and not any(0xD800 <= _bounded_reference_value(m.group()) <= 0xDFFF
                                       for m in _NUMERIC_REFERENCE.finditer(html)):
        return html, report
    contexts = _CharrefContexts(html)
    report["scoped_scan_performed"] = True
    discovery = _LONG_DECIMAL_REFERENCE.sub(lambda m: " " * len(m.group()), html)
    contexts.feed(discovery)
    contexts.close()
    edits = []
    sample_line, sample_offset = 1, 0

    def sample(start, end, after, action, context):
        nonlocal sample_line, sample_offset
        if len(report["samples"]) >= report["sample_limit"]:
            report["samples_truncated"] = True
            return
        sample_line += html.count("\n", sample_offset, start)
        sample_offset = start
        before = html[start:end]
        report["samples"].append({
            "before": before[:160], "before_truncated": len(before) > 160,
            "after": after, "action": action, "context": context,
            "character_offset": start, "html_line": sample_line,
        })

    def normalize(match, value, context):
        token = match.group()
        if token[2:3] not in {"x", "X"} and len(token.rstrip(";")) - 2 > 128:
            replacement = "&#" + str(value) + ";"
            edits.append((match.start(), match.end(), replacement))
            report["numeric_reference_normalizations"] += 1
            sample(match.start(), match.end(), replacement, "equivalent_decimal_syntax", context)

    def unpaired(match, value, context):
        report["unpaired_surrogate_refs"] += 1
        sample(match.start(), match.end(), "\ufffd", "left_for_standard_html_replacement", context)
        normalize(match, value, context)

    for start, end, context, pair_allowed in contexts.ranges:
        pending = None
        for match in _NUMERIC_REFERENCE.finditer(html, start, end):
            value = _bounded_reference_value(match.group())
            if pending is not None:
                high_match, high = pending
                pending = None
                if (0xDC00 <= value <= 0xDFFF and high_match.end() == match.start()
                        and match.group().endswith(";")):
                    report["eligible_surrogate_pairs"] += 1
                    glyph = chr(0x10000 + ((high - 0xD800) << 10) + value - 0xDC00)
                    if mode == "utf16":
                        edits.append((high_match.start(), match.end(), glyph))
                        report["joined_surrogate_pairs"] += 1
                        sample(high_match.start(), match.end(), glyph, "joined_utf16_pair", context)
                    else:
                        normalize(high_match, high, context)
                        normalize(match, value, context)
                    continue
                unpaired(high_match, high, context)
            if pair_allowed and 0xD800 <= value <= 0xDBFF and match.group().endswith(";"):
                pending = (match, value)
            elif pair_allowed and 0xD800 <= value <= 0xDFFF:
                unpaired(match, value, context)
            else:
                normalize(match, value, context)
        if pending is not None:
            unpaired(pending[0], pending[1], context)
    if not edits:
        return html, report
    parts, cursor = [], 0
    for start, end, replacement in edits:
        parts.extend((html[cursor:start], replacement))
        cursor = end
    parts.append(html[cursor:])
    return "".join(parts), report


class _Node:
    def __init__(self, tag, attrs=None, source_line=0):
        self.tag = tag
        self.attrs = attrs or {}
        self.source_line = source_line
        self.children = []


class _OpenElements:
    """The stack of open elements, with the positions of each tag name in it.

    Which element an end tag closes (the nearest open one of its name, unless a barrier such as a table lies
    between), and whether one is open at all, are answered from the positions: no walk down the stack. A page
    that nests 16,000 <div> and then sends 16,000 end tags that close nothing cost the square of that (13 s);
    every operation is now constant time, or proportional to the elements it closes."""

    def _reset_open(self):
        self.stack = []
        self.open_at = {}            # tag -> positions in self.stack, ascending

    def _push(self, node):
        self.open_at.setdefault(node.tag, []).append(len(self.stack))
        self.stack.append(node)

    def _pop_to(self, position):
        """Close the element at `position` and every element opened inside it."""
        for node in self.stack[position:]:
            self.open_at[node.tag].pop()
        del self.stack[position:]

    def _last(self, tag):
        """Position of the nearest open element named `tag`, or -1."""
        positions = self.open_at.get(tag)
        return positions[-1] if positions else -1

    def _close_optional(self, tags, barriers):
        """Close the nearest open element of `tags` (never the container at position 0) unless an element of
        `barriers` is nearer: what an implied end tag of <p>, <li>, <td>... closes."""
        found = max(self._last(tag) for tag in tags)
        if found > 0 and found > max(self._last(tag) for tag in barriers):
            self._pop_to(found)


class ArticleParser(_OpenElements, HTMLParser):
    """Parse only the requested article container, keeping collapsed HTML data."""

    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}
    SKIP = {"script", "style", "noscript", "iframe", "form", "textarea", "select", "button"}
    BLOCKS = {"p", "div", "section", "article", "li", "ul", "ol", "dl", "dt", "dd", "blockquote", "pre", "table", "tr", "hr", "details", "summary"}

    def __init__(self, url, target_id="page-body-inner", ad_filter=None):
        super().__init__(convert_charrefs=True)
        self.url = url
        self.target_id = target_id
        # hololive_adblock module, or None: skip ad slots and page chrome.
        self.ad_filter = ad_filter
        self.ad_skips = ad_filter.SkipLog() if ad_filter else None
        self.root = None
        self.root_closed = False
        self._reset_open()
        self.title = []
        self.in_title = False
        self.title_seen = False
        self.head_closed = False
        self.foreign_depth = 0
        self.skip_tag = None
        self.skip_depth = 0
        self.links = {}
        self.link_ids = {}
        self.warnings = []

    @property
    def found_article(self):
        return self.root is not None

    def handle_starttag(self, tag, attrs):
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth += 1
            return
        if self.stack and self.ad_filter is not None:
            # Inside the article container, an ad slot or page chrome is
            # skipped with its whole subtree, like script: no extra pass.
            found = self.ad_filter.classify_element(tag, attrs, self.url)
            if found:
                self.ad_skips.add(found[0], found[1], tag, self.getpos()[0])
                if tag not in self.VOID:
                    self.skip_tag, self.skip_depth = tag, 1
                return
        if tag in self.SKIP:
            if tag == "iframe" and self.stack:
                # Preserve only the embed's existence/source. Its document and
                # fallback markup remain skipped and are never fetched.
                self.stack[-1].children.append(_Node(tag, dict(attrs), self.getpos()[0]))
            self.skip_tag, self.skip_depth = tag, 1
            return
        attrs = dict(attrs)
        if tag in {"svg", "math"}:
            self.foreign_depth += 1
        if tag == "body":
            self.head_closed = True
        if (tag == "title" and self.root is None and not self.head_closed
                and not self.foreign_depth and not self.title_seen):
            self.in_title = True
            self.title_seen = True
        if not self.stack:
            if self.root is None and attrs.get("id") == self.target_id:
                self.root = _Node(tag, attrs, self.getpos()[0])
                self._push(self.root)
            return
        if tag in {"td", "th"}:
            self._close_optional({"td", "th"}, {"tr", "table"})
            if self._last("table") > self._last("tr"):           # a cell straight in a table: the row is implied
                row = _Node("tr", source_line=self.getpos()[0])
                self.stack[-1].children.append(row)
                self._push(row)
        elif tag == "tr":
            self._close_optional({"tr"}, {"table"})
        elif tag in {"thead", "tbody", "tfoot"}:
            self._close_optional({"tr"}, {"table"})
            self._close_optional({"thead", "tbody", "tfoot"}, {"table"})
        elif tag == "li":
            self._close_optional({"li"}, {"ul", "ol"})
        elif tag in {"dt", "dd"}:
            self._close_optional({"dt", "dd"}, {"dl"})
        if tag in self.BLOCKS or re.fullmatch(r"h[1-6]", tag):
            self._close_optional({"p"}, {"td", "th", "table", "div"})
        node = _Node(tag, attrs, self.getpos()[0])
        if tag == "a" and attrs.get("href"):
            try:
                href = urljoin(self.url, attrs["href"])
                if urlsplit(href).scheme.lower() in {"http", "https"}:
                    node.absolute_href = href
                    key = self.link_ids.get(href)
                    if key is None:
                        key = str(len(self.links) + 1)
                        self.links[key], self.link_ids[href] = href, key
                    node.link_id = key
            except ValueError:
                self.warnings.append("An invalid article link was retained as text.")
        self.stack[-1].children.append(node)
        if tag not in self.VOID:
            self._push(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in self.VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth -= 1
                if not self.skip_depth:
                    self.skip_tag = None
            return
        if tag == "title":
            self.in_title = False
        elif tag == "head":
            self.head_closed = True
        elif tag in {"svg", "math"}:
            self.foreign_depth = max(0, self.foreign_depth - 1)
        position = self._last(tag)
        if position < 0:
            return                       # nothing of this name is open: the end tag closes nothing
        if tag in {"td", "th", "tr"} and self._last("table") > position:
            return                       # a table opened inside the cell or row: the end tag stays inside it
        if position == 0:
            self.root_closed = True
        self._pop_to(position)

    def handle_data(self, data):
        if self.skip_tag:
            return
        if self.in_title:
            self.title.append(data)
        if self.stack:
            self.stack[-1].children.append(data)

    def lines(self):
        return _node_text(self.root, references=True, article=True).splitlines() if self.root else []


def _walk(node):
    pending = [node]
    while pending:
        current = pending.pop()
        if isinstance(current, _Node):
            yield current
            pending.extend(reversed(current.children))


def _footnote_number(node, footer=False):
    if node.tag != "a":
        return None
    values = [node.attrs.get(key) or "" for key in ("name", "id")] if footer else [node.attrs.get("href") or ""]
    pattern = r"footer-footnote([0-9]+)" if footer else r"#footer-footnote([0-9]+)"
    for value in values:
        match = re.fullmatch(pattern, value)
        if match:
            return match.group(1)
    return None


def _is_footnote_label(node, number):
    pieces, size, visits, pending = [], 0, 0, [node]
    while pending:
        visits += 1
        if visits > 64:
            return False
        item = pending.pop()
        if isinstance(item, str):
            size += len(item)
            if size > 128:
                return False
            pieces.append(item)
        else:
            if item is not node and item.tag not in {"span", "sup", "sub", "b", "i", "em", "strong", "small"}:
                return False
            pending.extend(reversed(item.children))
    label = re.sub(r"\s+", "", "".join(pieces))
    return label in {"", number, "*" + number, "※" + number, "[" + number + "]"}


def _wiki_link_title(href):
    try:
        parts = urlsplit(href)
        path_url = parts._replace(query="", fragment="").geturl()
        prefix = "/" + wiki_from_url(path_url) + "/d/"
        if not parts.path.startswith(prefix):
            return None
        raw = unquote_to_bytes(parts.path[len(prefix):])
        try:
            return raw.decode("euc-jp")
        except UnicodeDecodeError:
            return raw.decode("euc_jis_2004")
    except (ReaderError, ValueError, UnicodeError):
        return None


def _node_text(node, references=False, article=False, omit_footnotes=False, *,
               link_mode=None, footnotes=None, footnote_mode="markers",
               omit_footer_labels=False, expand_short_urls=False, omit_classes=(),
               line_footnotes=None, heading_lines=None, line_links=None,
               leave_out=()):
    # leave_out: elements inside node that are read on their own (nested tables, headings, list items). Each is a
    # block, so a line break in its place keeps the lines around it as they were.
    if node is None:
        return ""
    pieces = []
    marker_positions = []
    heading_positions = []
    link_positions = []
    link_mode = link_mode or ("references" if references else "off")
    pending = [(node, False, 0, None, None)]
    while pending:
        item, closing, cell_depth, mark, anchor_position = pending.pop()
        if isinstance(item, str):
            pieces.append(re.sub(r"\s+", " ", item))
            continue
        tag = item.tag
        if set((item.attrs.get("class") or "").split()).intersection(omit_classes):
            continue
        if not closing and item is not node and item in leave_out:
            pieces.append("\n")
            continue
        number = _footnote_number(item)
        fragment_only = tag == "a" and (item.attrs.get("href") or "").strip().startswith("#")
        if (omit_footnotes or footnote_mode == "off") and number and _is_footnote_label(item, number):
            continue
        footer_number = _footnote_number(item, footer=True) if omit_footer_labels else None
        if footer_number and _is_footnote_label(item, footer_number):
            continue
        is_heading = bool(re.fullmatch(r"h[1-6]", tag))
        boundary = " / " if article and cell_depth else "\n"
        if closing:
            if number and footnote_mode == "inline" and footnotes and number in footnotes:
                note = footnotes[number]
                note_text = note.get("display_text", note.get("text", ""))
                if note_text:
                    # The note carries its own line breaks; inside a cell they
                    # must not split the row the marker sits on.
                    if article and cell_depth:
                        note_text = re.sub(r"\r\n|[\n\v\f\r\x1c-\x1e\x85\u2028\u2029]", boundary, note_text)
                    pieces.append("(" + note_text + ")")
            elif mark is not None:
                # The resolved URL is rendered as running text. urlsplit strips
                # only tab/CR/LF, so collapse the rest the way alt text is
                # collapsed; links and link_original_hrefs keep the exact URL.
                href = re.sub(r"\s+", " ", getattr(item, "absolute_href", ""))
                title = _wiki_link_title(href)
                label = "".join(pieces[mark + 1:]).strip() if len(pieces) - mark <= 64 else None
                short_prefix = label[:-3] if label and label.endswith("...") else (label[:-1] if label and label.endswith("…") else None)
                if (expand_short_urls and short_prefix and len(label) <= 300
                        and re.fullmatch(r"https?://\S+", label) and href.startswith(short_prefix)):
                    pieces[mark:] = [href]
                elif link_mode == "inline" and title:
                    if label:
                        pieces[mark] = "[[" if label == title else "[[" + title + "|"
                        pieces.append("]]")
                    elif label is None:
                        pieces[mark] = "[[" + title + "|"
                        pieces.append("]]")
                elif link_mode == "inline" and href and (label or label is None):
                    pieces.append(" (" + href + ")")
                elif link_mode == "references" and getattr(item, "link_id", None):
                    pieces.append(f" [{item.link_id}] ")
            elif link_mode == "references" and not number and not fragment_only and getattr(item, "link_id", None):
                pieces.append(f" [{item.link_id}] ")
            if tag in {"del", "s", "strike"}:
                pieces.append("~~")
            if tag in {"td", "th"} and article:
                pieces.append(" ")
            elif tag == "tr" and article:
                # A row nested inside a cell must not break its parent's line;
                # every other block already ends on the cell-aware boundary.
                pieces.append("|" + boundary)
            elif tag in ArticleParser.BLOCKS or is_heading:
                pieces.append(boundary)
            if anchor_position is not None:
                anchor_position[1] = len(pieces)
            continue
        mark = None
        anchor_position = None
        if number and line_footnotes is not None:
            anchor_position = [len(pieces), None, number]
            marker_positions.append(anchor_position)
        elif (line_links is not None and not fragment_only
              and getattr(item, "link_id", None)):
            anchor_position = [len(pieces), None, item.link_id]
            link_positions.append(anchor_position)
        if tag == "a" and not number and not fragment_only and getattr(item, "absolute_href", None) and (link_mode == "inline" or expand_short_urls):
            mark = len(pieces)
            pieces.append("")
        if tag in {"td", "th"} and article:
            pieces.append("| ")
            for span in ("rowspan", "colspan"):
                if item.attrs.get(span) not in {None, "1"}:
                    # This annotation is not validated here, so an attribute
                    # holding a line separator would split the row it labels.
                    # The exact value stays in the cell's rowspan/colspan_raw.
                    value = re.sub(r"\s+", " ", item.attrs[span])
                    pieces.append("[" + span + "=" + value + "] ")
            cell_depth += 1
        elif tag == "br":
            pieces.append(boundary)
        elif tag in ArticleParser.BLOCKS or is_heading:
            pieces.append(boundary)
            if article and is_heading:
                # One entry per heading, in the same order _walk() yields them.
                if heading_lines is not None:
                    heading_positions.append(len(pieces))
                pieces.append("#" * int(tag[1]) + " ")
        elif tag == "img" and item.attrs.get("alt"):
            pieces.append(re.sub(r"\s+", " ", item.attrs["alt"]))
        elif tag in {"del", "s", "strike"}:
            pieces.append("~~")
        pending.append((item, True, cell_depth, mark, anchor_position))
        pending.extend((child, False, cell_depth, None, None) for child in reversed(item.children))
    raw_lines = "".join(pieces).splitlines(keepends=True)
    if line_footnotes is not None or heading_lines is not None or line_links is not None:
        piece_offsets, offset = [], 0
        for piece in pieces:
            piece_offsets.append(offset)
            offset += len(piece)
        # A marker that emits nothing and is followed by nothing sits one past
        # the last piece; give that position the end offset instead of failing.
        piece_offsets.append(offset)
        # Blank lines are dropped from the returned text, so they number 0.
        ends, line_numbers, previous_numbers, line_number, offset = [], [], [], 0, 0
        for line in raw_lines:
            offset += len(line)
            if line.strip():
                line_number += 1
            ends.append(offset)
            line_numbers.append(line_number if line.strip() else 0)
            previous_numbers.append(line_number)

        def line_at(position, previous_visible=False, next_visible=False):
            index = bisect.bisect_right(ends, piece_offsets[position])
            if index < len(ends) and line_numbers[index]:
                return line_numbers[index]
            if previous_visible:
                # Empty markers can sit on a blank line that rendering drops.
                # Their preceding visible line still needs its footnote.
                previous = previous_numbers[index] if index < len(ends) else line_number
                if previous:
                    return previous
                if next_visible:
                    # No visible line precedes this position, so the next one
                    # is necessarily line 1 if any exist. Do not rescan the
                    # article for each leading empty footnote marker.
                    return 1 if line_number else 0
            return 0

        if line_footnotes is not None:
            for position, end, number in marker_positions:
                empty = not any(piece.strip() for piece in pieces[position:end])
                line = line_at(position, previous_visible=empty, next_visible=empty)
                if line and number not in line_footnotes.setdefault(line, []):
                    line_footnotes[line].append(number)
        if heading_lines is not None:
            heading_lines.extend(line_at(position) or None for position in heading_positions)
        if line_links is not None:
            seen_links = {line: set(keys) for line, keys in line_links.items()}
            for position, end, key in link_positions:
                start_offset, end_offset = piece_offsets[position], piece_offsets[end]
                first = bisect.bisect_right(ends, start_offset)
                last = min(len(ends), bisect.bisect_left(ends, end_offset) + 1)
                occupied = []
                for index in range(first, last):
                    line_start = ends[index - 1] if index else 0
                    overlap = raw_lines[index][max(start_offset - line_start, 0):end_offset - line_start]
                    if overlap.strip() and line_numbers[index]:
                        occupied.append(line_numbers[index])
                if not occupied:
                    line = line_at(position, previous_visible=True)
                    if line:
                        occupied.append(line)
                for line in occupied:
                    seen = seen_links.setdefault(line, set())
                    if key not in seen:
                        seen.add(key)
                        line_links.setdefault(line, []).append(key)
    return "\n".join(line.strip() for line in raw_lines if line.strip())


def _table_descendants(table, tag):
    pending = list(reversed(table.children))
    while pending:
        child = pending.pop()
        if not isinstance(child, _Node) or child.tag == "table":
            continue
        if child.tag == tag:
            yield child
        pending.extend(reversed(child.children))


def _span(cell, attr, warnings):
    raw = cell.attrs.get(attr, "1")
    if not re.fullmatch(r"[0-9]{1,5}", raw or "") or not 1 <= int(raw) <= 10000:
        warnings.append(f"Unsupported {attr}={raw!r} at HTML line {cell.source_line}; table grid omitted.")
        return None
    return int(raw)


def _table_references(node):
    """The link ids and footnote numbers in `node` in source order, and the tables directly inside it. A table
    inside it is read as a table of its own, so what that table holds is not counted here."""
    links, notes, tables, pending = {}, {}, [], [node]
    while pending:
        current = pending.pop()
        if not isinstance(current, _Node):
            continue
        if current is not node and current.tag == "table":
            tables.append(current)
            continue
        key = getattr(current, "link_id", None)
        if key:
            links[key] = None
        number = _footnote_number(current)
        if number:
            notes[number] = None
        pending.extend(reversed(current.children))
    return list(links), list(notes), tables


def _own_texts(root, wanted):
    """{element: its text} for the elements under `root` that `wanted` accepts, in source order.

    An element of the same kind inside one is left out of its text (it is a
    block, so the lines around it stay as they were): it has an entry of its
    own. Taking it in repeated the innermost text once for every element
    around it, the square of their nesting in time and size (2,000 list
    items nested in a tag list: 19 s).
    """
    nodes = [node for node in _walk(root) if wanted(node)]
    inner = set(nodes)
    return {node: _node_text(node, leave_out=inner) for node in nodes}


def _extract_table(node, index, headings, warnings, *, max_grid_cells=MAX_GRID_CELLS,
                   grid_budget=None, table_numbers=None):
    """One table's rows and cells. A table inside a cell is read as a table of its own: the cell's text, links
    and notes leave it out, and nested_tables gives its index (`table_numbers`: {table: index} on the page)."""
    table_numbers = table_numbers if table_numbers is not None else {}
    result = {"index": index, "source_line": node.source_line, "headings": list(headings), "rows": []}
    captions = list(_table_descendants(node, "caption"))
    if captions:
        result["caption"] = _node_text(captions[0], leave_out=set(_table_references(captions[0])[2]))
    unsupported_span = False
    for row_index, row in enumerate(_table_descendants(node, "tr"), 1):
        row_data = {"index": row_index, "source_line": row.source_line, "cells": []}
        # Cells belong to this row only; nested table rows are extracted separately.
        cells = [child for child in row.children if isinstance(child, _Node) and child.tag in {"td", "th"}]
        for cell_index, cell in enumerate(cells, 1):
            rowspan, colspan = _span(cell, "rowspan", warnings), _span(cell, "colspan", warnings)
            unsupported_span |= rowspan is None or colspan is None
            link_ids, note_numbers, nested = _table_references(cell)
            inner = set(nested)
            value = {"index": cell_index, "tag": cell.tag, "text": _node_text(cell, leave_out=inner), "source_line": cell.source_line,
                     "rowspan": rowspan, "colspan": colspan,
                     "link_ids": link_ids}
            if note_numbers:
                value["footnote_numbers"] = note_numbers
            if any(table in table_numbers for table in nested):
                value["nested_tables"] = [table_numbers[table] for table in nested if table in table_numbers]
            clean_text = (_node_text(cell, omit_footnotes=True, leave_out=inner)
                          if note_numbers else value["text"])
            if clean_text != value["text"]:
                value["text_without_footnotes"] = clean_text
            for attr in ("rowspan", "colspan"):
                if attr in cell.attrs:
                    value[attr + "_raw"] = cell.attrs[attr]
            row_data["cells"].append(value)
        result["rows"].append(row_data)
    grid = None if unsupported_span else _expand_grid(
        result["rows"], warnings, index, max_grid_cells=max_grid_cells, grid_budget=grid_budget)
    result["grid"] = grid
    return result


def _expand_grid(rows, warnings, table_index, *, max_grid_cells=MAX_GRID_CELLS,
                 grid_budget=None):
    """Bounded logical cells map back to physical row/cell coordinates (1-based).

    A shared page budget bounds retained rectangular slots and expansion work.
    Work counts row allocation plus attempted span slots, including failed
    tables; a late overlap or rectangular-limit failure never refunds work.
    """
    if len(rows) > 50000:
        warnings.append(f"Table {table_index}: too many rows for grid expansion.")
        return None
    if grid_budget is not None:
        if len(rows) > grid_budget["work_remaining"]:
            warnings.append(f"Table {table_index}: page grid work limit reached; raw cells retained.")
            return None
        grid_budget["work_remaining"] -= len(rows)
    grid = [{} for _ in rows]
    total = 0
    for ri, row in enumerate(rows):
        col = 0
        for cell in row["cells"]:
            while col in grid[ri]:
                col += 1
            height, width = cell["rowspan"], cell["colspan"]
            area = height * width
            if col + width > 256 or total + area > max_grid_cells:
                warnings.append(f"Table {table_index}: span expansion limit reached; raw cells retained.")
                return None
            if ri + height > len(rows):
                warnings.append(f"Table {table_index}: rowspan extends beyond final row; grid omitted.")
                return None
            if grid_budget is not None:
                if area > grid_budget["work_remaining"]:
                    warnings.append(f"Table {table_index}: page grid work limit reached; raw cells retained.")
                    return None
                grid_budget["work_remaining"] -= area
            source = {"row": ri + 1, "cell": cell["index"]}
            for target_row in range(ri, ri + height):
                for target_col in range(col, col + width):
                    if target_col in grid[target_row]:
                        warnings.append(f"Table {table_index}: overlapping spans; grid omitted.")
                        return None
                    grid[target_row][target_col] = source
            total += area
            col += width
    width = max((max(row, default=-1) + 1 for row in grid), default=0)
    rectangular_cells = len(rows) * width
    if rectangular_cells > max_grid_cells:
        warnings.append(f"Table {table_index}: rectangular grid limit reached; raw cells retained.")
        return None
    if grid_budget is not None:
        if rectangular_cells > grid_budget["cells_remaining"]:
            warnings.append(f"Table {table_index}: page rectangular grid limit reached; raw cells retained.")
            return None
        grid_budget["cells_remaining"] -= rectangular_cells
    return [[row.get(col) for col in range(width)] for row in grid]


def _normalize_cell(text, multiple=False):
    values = []
    for line in text.splitlines():
        line = re.sub(r"(?:\s*(?:\*|※)\d+)+\s*$", "", line).strip()
        line = re.sub(r"\s+", " ", line)
        if line:
            values.append(line)
    value = ("、" if multiple else " ").join(values)
    return "" if value in PLACEHOLDER_CELL_VALUES else value


def _nickname_records(table):
    if table["grid"] is None:
        return []
    records, columns = [], None
    wanted = {"相手": "counterpart", "呼び方": "calls", "呼ばれ方": "called_by"}
    for row_index, logical_row in enumerate(table["grid"], 1):
        def cell_at(column):
            source = logical_row[column]
            if source is None:
                return None
            return table["rows"][source["row"] - 1]["cells"][source["cell"] - 1]
        headers = {}
        for column in range(len(logical_row)):
            cell = cell_at(column)
            header_text = cell.get("text_without_footnotes", cell["text"]) if cell else ""
            first_line = header_text.splitlines()[0] if header_text else ""
            label = re.sub(r"\s+", "", _normalize_cell(first_line))
            if label in wanted:
                headers[wanted[label]] = column
        if len(headers) == 3:
            columns = headers
            continue
        if columns is None or any(cell_at(col) is None for col in columns.values()):
            continue
        sources = {key: logical_row[col] for key, col in columns.items()}
        if len({(src["row"], src["cell"]) for src in sources.values()}) < 3:
            continue
        record = {key: _normalize_cell(cell_at(col).get("text_without_footnotes", cell_at(col)["text"]), multiple=key != "counterpart") for key, col in columns.items()}
        if not record["counterpart"] or record["counterpart"] in wanted:
            continue
        record["source"] = {"table": table["index"], "row": row_index, "cells": sources}
        records.append(record)
    return records


def _footnote_body_without_separator(node, marker_titles=()):
    """Remove one observed site separator immediately after a compact marker.

    The separator is a colon followed by whitespace or the text node's end,
    immediately following the marker, with optional leading whitespace. If
    the unchanged note already matches a marker title, that leading colon
    is body text and stays. Never trim punctuation from the assembled note.
    Do not cross a new element, since it may already be the note's body.
    Clone only the changed ancestor path, leaving the source tree intact.
    """
    pending, parents = [(node, None, None)], {}
    after_marker = False
    while pending:
        item, parent, index = pending.pop()
        if isinstance(item, str):
            if not after_marker:
                continue
            if not item.strip():
                continue
            match = re.match(r"\s*[:：](?=\s|$)", item)
            if not match:
                return node
            normalize = lambda value: re.sub(r"\s+", " ", value).strip()
            if marker_titles and normalize(_footnote_source_text(node)) in {
                    normalize(title) for title in marker_titles}:
                return node
            replacement = item[match.end():]
            while parent is not None:
                clone = _Node(parent.tag)
                clone.__dict__.update(parent.__dict__)
                clone.children = list(parent.children)
                clone.children[index] = replacement
                replacement = clone
                parent, index = parents[parent]
            return replacement
        if after_marker:
            return node
        parents[item] = (parent, index)
        number = _footnote_number(item, footer=True)
        if number and _is_footnote_label(item, number):
            after_marker = True
            continue
        pending.extend((child, item, i) for i, child in reversed(list(enumerate(item.children))))
    return node


def _footnote_source_text(node):
    pieces, pending = [], [node]
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            pieces.append(item)
            continue
        number = _footnote_number(item, footer=True)
        if number and _is_footnote_label(item, number):
            continue
        pending.extend(reversed(item.children))
    return "".join(pieces).strip()


def _footer_rows(box, covered):
    """[(row, numbers)]: the rows (li) of a footnote list that hold a footer note number, in source order.

    A row holding one number defines that note with everything inside it: the
    rows within it are part of its text, not more definitions of the note. A
    row holding several (a malformed or nested list) comes with two of them,
    and the rows within it are read. Footnote lists nested in `box` are added
    to `covered`, since their rows are read here once. Numbers are gathered
    from the inside out, so nesting costs no more than the list's size;
    reading each row's whole subtree cost its square (2,000 nested rows, 51 s).
    """
    nodes = list(_walk(box))
    found = {}
    for node in reversed(nodes):
        own = _footnote_number(node, footer=True)
        numbers = [own] if own else []
        for child in node.children:
            if len(numbers) > 1:
                break
            if isinstance(child, _Node):
                for number in found[child]:
                    if number not in numbers:
                        numbers.append(number)
        found[node] = numbers[:2]
        if node is not box and "footer-footnote" in (node.attrs.get("class") or "").split():
            covered.add(node)
    rows, pending = [], [box]
    while pending:
        node = pending.pop()
        if not found[node]:
            continue
        if node.tag == "li":
            rows.append((node, found[node]))
            if len(found[node]) == 1:
                continue
        pending.extend(child for child in reversed(node.children) if isinstance(child, _Node))
    return rows


def _extract_footnotes(root, warnings, link_mode="references"):
    """Compare two representations from the SAME page, preserving each source."""
    notes = {}
    # Gather titles before processing definitions: malformed/source-edited
    # pages may place their footer before the body marker.
    marker_titles = {}
    for node in _walk(root):
        number = _footnote_number(node)
        if number and node.attrs.get("title"):
            marker_titles.setdefault(number, []).append(node.attrs["title"])

    def entry(number):
        return notes.setdefault(number, {"number": number, "text": "", "marker_titles": [],
                                         "footer_entries": [], "agreement": "unavailable",
                                         "marker_references": []})

    covered = set()          # footnote lists inside one already read
    for node in _walk(root):
        number = _footnote_number(node)
        if number:
            record = entry(number)
            record["marker_references"].append({
                "source_line": node.source_line,
                "title_present": "title" in node.attrs,
                "title_empty": "title" in node.attrs and not (node.attrs.get("title") or "").strip(),
            })
            if not _is_footnote_label(node, number):
                warnings.append(f"Footnote {number}: unexpected marker content at HTML line {node.source_line}; text retained even when markers are hidden.")
            title = node.attrs.get("title")
            if title:
                record["marker_titles"].append({"text": title, "source_line": node.source_line})
        footer_number = _footnote_number(node, footer=True)
        if footer_number and not _is_footnote_label(node, footer_number):
            warnings.append(f"Footnote {footer_number}: unexpected footer label content at HTML line {node.source_line}; text retained.")
        if "footer-footnote" not in (node.attrs.get("class") or "").split() or node in covered:
            continue
        for row, numbers in _footer_rows(node, covered):
            # A malformed or nested list must not attach several notes to one number.
            if len(numbers) != 1:
                warnings.append(f"Ambiguous footer footnote at HTML line {row.source_line}; raw text retained.")
                continue
            body = _footnote_body_without_separator(row, marker_titles.get(numbers[0], ()))
            raw_text = _node_text(body, omit_footer_labels=True)
            full_text = _node_text(body, omit_footer_labels=True, expand_short_urls=True)
            display_text = _node_text(body, omit_footer_labels=True, link_mode=link_mode,
                                      expand_short_urls=link_mode != "off")
            source_links = list(dict.fromkeys(child.link_id for child in _walk(row)
                                               if getattr(child, "link_id", None) and not _footnote_number(child, footer=True)))
            non_text_content = bool(source_links) or any(
                child.tag in {"img", "iframe", "svg", "canvas", "video", "audio", "object", "embed", "table", "hr"}
                for child in _walk(row))
            embedded_media = [{"tag": child.tag, "src": child.attrs.get("src"),
                               "source_line": child.source_line}
                              for child in _walk(row) if child.tag == "iframe"]
            entry(numbers[0])["footer_entries"].append({
                "body_state": "text" if full_text else ("non_text" if non_text_content else "empty"),
                "embedded_media": embedded_media,
                "text": full_text, "raw_text": raw_text, "display_text": display_text,
                "comparison_text": _footnote_source_text(body),
                "source_line": row.source_line,
                "link_ids": source_links})
    normalize = lambda value: re.sub(r"\s+", " ", value).strip()
    for number, record in notes.items():
        markers, footers = record["marker_titles"], record["footer_entries"]
        representations = {normalize(item["text"]) for item in markers}
        # The site's title removes tags, whereas rendered footer text inserts
        # line breaks for <br>, <p>, blockquotes, etc. Compare the source text
        # nodes; preserve raw/rendered versions separately for source review.
        representations.update(normalize(item["comparison_text"]) for item in footers)
        if len(representations) > 1:
            record["agreement"] = "conflict"
            warnings.append(f"Footnote {number}: marker title and/or footer text disagree within this page; all versions retained.")
        elif markers and footers:
            record["agreement"] = "match"
        elif markers:
            record["agreement"] = "marker_only"
        elif footers:
            record["agreement"] = "footer_only"
        record["text"] = footers[0]["text"] if footers else (markers[0]["text"] if markers else "")
        record["display_text"] = footers[0]["display_text"] if footers else record["text"]
        record["reference_state"] = "referenced" if record["marker_references"] else "unreferenced"
        states = {item["body_state"] for item in footers}
        record["definition_state"] = ("missing" if not footers else "text" if "text" in states
                                      else "non_text" if "non_text" in states else "empty")
        record["empty_footer_entries"] = sum(item["body_state"] == "empty" for item in footers)
        if not footers and record["marker_references"]:
            warnings.append(f"Footnote {number}: a body marker has no footer definition in the extracted article; any marker title is retained.")
        if record["empty_footer_entries"]:
            warnings.append(f"Footnote {number}: {record['empty_footer_entries']} footer definition(s) contain no extracted text, source link or visible media; empty entries are retained.")
        if footers and not record["marker_references"]:
            warnings.append(f"Footnote {number}: a footer definition has no body marker in the extracted article; the definition is retained.")
    return notes


class _MetadataParser(_OpenElements, HTMLParser):
    """Keep only three narrow metadata blocks instead of a second full DOM."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self._reset_open()
        self.results = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if not self.stack:
            kind = None
            if tag == "p" and "update" in (attrs.get("class") or "").split():
                kind = "updated"
            elif tag == "ul" and attrs.get("id") in {"page-category", "page-tags"}:
                kind = "categories" if attrs["id"] == "page-category" else "tags"
            if kind is None or kind in self.results:
                return
            root = _Node(tag, attrs, self.getpos()[0])
            self.results[kind] = root
            self._push(root)
            return
        if tag == "li":
            self._close_optional({"li"}, {"ul", "ol"})
        node = _Node(tag, attrs, self.getpos()[0])
        self.stack[-1].children.append(node)
        if tag not in ArticleParser.VOID:
            self._push(node)

    def handle_endtag(self, tag):
        position = self._last(tag)
        if position >= 0:
            self._pop_to(position)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in ArticleParser.VOID:
            self.handle_endtag(tag)

    def handle_data(self, data):
        if self.stack and not any(self.open_at.get(tag) for tag in ArticleParser.SKIP):
            self.stack[-1].children.append(data)

    def metadata(self):
        result = {"last_updated": None, "categories": [], "tags": []}
        updated = self.results.get("updated")
        if updated:
            for node in _walk(updated):
                if node.tag == "img":
                    node.attrs.pop("alt", None)
            text = _node_text(updated, omit_classes={"history"})
            result["last_updated"] = re.sub(r"^最終更新\s*[:：]?\s*", "", text).strip() or None
            result["updated_source_line"] = updated.source_line
        for key in ("categories", "tags"):
            root = self.results.get(key)
            if root:
                texts = _own_texts(root, lambda node: node.tag == "li")
                result[key] = list(dict.fromkeys(text for node, text in texts.items()
                                                 if "title" not in (node.attrs.get("class") or "").split() and text))
        return result


class _EmptyArticleEvidence(HTMLParser):
    MEDIA = {"img", "iframe", "svg", "canvas", "video", "audio", "object", "embed", "table", "hr"}
    UI = {"form", "textarea", "select", "button", "input"}

    def __init__(self, target_id):
        super().__init__(convert_charrefs=True)
        self.target_id = target_id
        self.div_depth = 0
        self.root_depth = None
        self.area_depth = None
        self.skip_tag = None
        self.skip_depth = 0
        self.areas = self.closed_areas = 0
        self.source_text_present = self.non_text_content_present = self.ui_present = False

    def handle_starttag(self, tag, attrs):
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth += 1
            return
        attrs = dict(attrs)
        if tag == "div":
            self.div_depth += 1
            if attrs.get("id") == self.target_id and self.root_depth is None:
                self.root_depth = self.div_depth
            if (self.root_depth is not None and self.area_depth is None
                    and "user-area" in (attrs.get("class") or "").split()):
                self.area_depth = self.div_depth
                self.areas += 1
        if self.area_depth is not None:
            self.non_text_content_present |= tag in self.MEDIA
            self.ui_present |= tag in self.UI
        if tag in ArticleParser.SKIP:
            self.skip_tag, self.skip_depth = tag, 1

    def handle_endtag(self, tag):
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth -= 1
                if not self.skip_depth:
                    self.skip_tag = None
            return
        if tag == "div":
            if self.area_depth == self.div_depth:
                self.closed_areas += 1
                self.area_depth = None
            if self.root_depth == self.div_depth:
                self.root_depth = None
            self.div_depth = max(0, self.div_depth - 1)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in ArticleParser.VOID:
            self.handle_endtag(tag)

    def handle_data(self, data):
        if self.area_depth is not None and not self.skip_tag and data.strip():
            self.source_text_present = True

    def evidence(self):
        return {"user_area_count": self.areas, "closed_user_area_count": self.closed_areas,
                "source_text_present": self.source_text_present,
                "non_text_content_present": self.non_text_content_present,
                "ui_present": self.ui_present}


FEED_CHUNK = 65536


def _feed_until(parser, html, done):
    """Feed `html` in chunks and stop as soon as `done(parser)` holds.

    The article container and the page metadata end well before Seesaa's
    sidebar and footer (about 160,000 characters on every page), which
    neither parser reads. A parser that never finishes gets the whole
    document and is closed, exactly as a single feed() would.

    A chunk ends where markup starts ("<"): HTMLParser passes on the text it
    has at the end of a chunk, so text cut in two there was two pieces, and a
    run of spaces cut in two kept two spaces. The parser also keeps back what
    it cannot finish yet, such as a start tag whose ">" has not come, and reads
    it again with the next chunk. A chunk is never shorter than what is kept
    back, so a start tag left open over megabytes is read a few times instead
    of once for every 64 KB (4 MB took 39 s).
    """
    start = 0
    while start < len(html):
        end = html.find("<", start + max(FEED_CHUNK, len(getattr(parser, "rawdata", ""))))
        end = len(html) if end < 0 else end
        parser.feed(html[start:end])
        start = end
        if done(parser):
            return True
    parser.close()
    return False


def parse_article(html, url, *, link_mode="references", footnote_mode="markers", max_grid_cells=MAX_GRID_CELLS,
                  ad_filter="strict"):
    if isinstance(max_grid_cells, bool) or not isinstance(max_grid_cells, int) or not 1 <= max_grid_cells <= MAX_GRID_CELLS:
        raise ValueError(f"max_grid_cells must be an integer in 1..{MAX_GRID_CELLS}.")
    grid_budget = {"cells_remaining": MAX_PAGE_GRID_CELLS, "work_remaining": MAX_PAGE_GRID_WORK}
    if link_mode not in {"references", "inline", "off"}:
        raise ValueError("link_mode must be references, inline, or off.")
    if footnote_mode not in {"markers", "inline", "off"}:
        raise ValueError("footnote_mode must be markers, inline, or off.")
    if ad_filter not in AD_FILTER_MODES:
        raise ValueError("ad_filter must be strict, report, or off.")
    adblock = load_adblock() if ad_filter != "off" else None
    # Nothing after the container's end tag can change the extracted article.
    article_done = lambda parser: parser.root_closed  # noqa: E731
    parser = ArticleParser(url, ad_filter=adblock)
    _feed_until(parser, html, article_done)
    if not parser.found_article:
        parser = ArticleParser(url, target_id="page-body", ad_filter=adblock)
        _feed_until(parser, html, article_done)
        if parser.found_article:
            parser.warnings.append("page-body-inner was absent; extracted the page-body fallback container.")
    if not parser.found_article:
        raise ValueError("Article body was not found; inspect page structure or access status.")
    article_selector = "#" + parser.target_id
    unclosed_container = parser.root.tag == "div" and not parser.root_closed
    article_integrity = {
        "container_selector": article_selector, "container_tag": parser.root.tag,
        "closing_tag_observed": parser.root_closed,
        "unclosed_required_container": unclosed_container,
        "reason": "missing_required_div_end_tag" if unclosed_container else None,
        "limitation": "Container closure alone does not establish transfer or semantic completeness.",
    }
    if unclosed_container:
        parser.warnings.append(
            "The article div container was not closed in the supplied HTML. "
            "Recovered text is retained, but the page will not be cached. "
            "This can reflect incomplete input or malformed source markup; it does not prove a failed transfer."
        )
    areas, pending = [], [parser.root]
    while pending:
        node = pending.pop()
        if not isinstance(node, _Node):
            continue
        classes = (node.attrs.get("class") or "").split()
        if "user-area" in classes or "footer-footnote" in classes:
            areas.append(node)
        else:
            pending.extend(reversed(node.children))
    user_area_count = sum("user-area" in (node.attrs.get("class") or "").split() for node in areas)
    if user_area_count:
        selected_root = _Node("article", source_line=parser.root.source_line)
        selected_root.children = areas
        parser.root = selected_root
        article_selector += " .user-area"
        if user_area_count > 1:
            parser.warnings.append("Multiple article .user-area containers were combined in source order.")
        used_ids = {node.link_id for node in _walk(parser.root) if getattr(node, "link_id", None)}
        parser.links = {key: value for key, value in parser.links.items() if key in used_ids}
    footnotes = _extract_footnotes(parser.root, parser.warnings, link_mode=link_mode)
    line_footnotes, heading_lines, line_links = {}, [], {}
    lines = _node_text(parser.root, article=True, link_mode=link_mode,
                       footnotes=footnotes, footnote_mode=footnote_mode,
                       line_footnotes=line_footnotes, heading_lines=heading_lines,
                       line_links=line_links).splitlines()
    article_state, article_content = "content", None
    if not lines:
        evidence = _EmptyArticleEvidence(parser.target_id)
        evidence.feed(html)
        evidence.close()
        article_content = evidence.evidence()
        if (not user_area_count or unclosed_container
                or evidence.areas != user_area_count or evidence.closed_areas != user_area_count
                or (evidence.ui_present and not evidence.source_text_present and not evidence.non_text_content_present)):
            raise ValueError("The article body is empty or unconfirmed; an explicit, closed .user-area is required to identify an empty article.")
        article_state = ("no_extractable_text" if evidence.source_text_present or evidence.non_text_content_present else "empty")
    footnote_diagnostics = {
        "scope": "extracted_article", "note_count": len(footnotes),
        "missing_definitions": [n for n, note in footnotes.items() if note["definition_state"] == "missing"],
        "empty_definitions": [n for n, note in footnotes.items() if note["empty_footer_entries"]],
        "unreferenced_definitions": [n for n, note in footnotes.items()
                                     if note["footer_entries"] and note["reference_state"] == "unreferenced"],
        "non_text_definitions": [n for n, note in footnotes.items() if note["definition_state"] == "non_text"],
    }
    headings, tables, current_headings = [], [], []
    table_numbers = {node: number for number, node in enumerate((node for node in _walk(parser.root) if node.tag == "table"), 1)}
    heading_texts = _own_texts(parser.root, lambda node: re.fullmatch(r"h[1-6]", node.tag))
    for node in _walk(parser.root):
        if re.fullmatch(r"h[1-6]", node.tag):
            # article_line ties this heading to the rendered line it starts, so
            # selection never has to guess from text that merely looks like one.
            entry = {"level": int(node.tag[1]), "text": heading_texts[node], "source_line": node.source_line,
                     "article_line": heading_lines[len(headings)] if len(headings) < len(heading_lines) else None}
            headings.append(entry)
            start = entry["article_line"]
            match = re.match(r"^(#{1,6})\s+(.*)$", lines[start - 1]) if start else None
            # Match the section selector's own-line rule. A heading embedded
            # in a table cell is retained above, but cannot end an article
            # section or reassign subsequent tables to an unselectable one.
            if match and len(match.group(1)) == entry["level"]:
                current_headings = [item for item in current_headings if item["level"] < entry["level"]] + [entry]
        elif node.tag == "table":
            tables.append(_extract_table(node, len(tables) + 1, current_headings, parser.warnings,
                                         max_grid_cells=max_grid_cells, grid_budget=grid_budget,
                                         table_numbers=table_numbers))
    nicknames = [record for table in tables for record in _nickname_records(table)]
    images = []
    for node in _walk(parser.root):
        if node.tag != "img":
            continue
        src = node.attrs.get("src")
        image_url = None
        if src:
            try:
                image_url = urljoin(url, src)
            except ValueError:
                parser.warnings.append(
                    f"An invalid image URL at HTML line {node.source_line} was retained in src; resolved URL is unavailable.")
        images.append({
            "url": image_url,
            "src": src,
            "alt": node.attrs.get("alt"),
            "width": node.attrs.get("width"),
            "height": node.attrs.get("height"),
            "srcset": node.attrs.get("srcset"),
            "source_line": node.source_line,
        })
    metadata_parser = _MetadataParser()
    # The first update note, category list and tag list are kept; once all
    # three are closed, later markup cannot change the metadata.
    _feed_until(metadata_parser, html, lambda parser: len(parser.results) == 3 and not parser.stack)
    original_hrefs = {}
    for node in _walk(parser.root):
        key = getattr(node, "link_id", None)
        if key:
            sources = original_hrefs.setdefault(key, [])
            if node.attrs["href"] not in sources:
                sources.append(node.attrs["href"])
    page_title = "".join(parser.title).strip()
    article_title = _wiki_link_title(url)
    page_metadata = metadata_parser.metadata()
    ad_report = {"mode": ad_filter}
    if adblock is not None:
        # Scan all content before selection and output switches. Structured
        # fields can retain alternate text and media URLs absent from lines.
        # Diagnostics are deliberately outside this input: their examples
        # name the very URLs that the filter reports or removes.
        embedded_media = [{"tag": node.tag, "src": node.attrs.get("src")}
                          for node in _walk(parser.root) if node.tag == "iframe"]
        scan = adblock.scan_output({"lines": lines, "links": parser.links, "link_original_hrefs": original_hrefs,
                                    "footnotes": footnotes, "images": images, "embedded_media": embedded_media,
                                    "headings": headings, "tables": tables, "nicknames": nicknames,
                                    "page_title": page_title, "article_title": article_title,
                                    "metadata": page_metadata})
        ad_report.update(version=adblock.VERSION, skipped=parser.ad_skips.report(), output_scan=scan,
                         scan_scope="whole_extracted_content_before_selection",
                         network="Only the HTML of seesaawiki.jp pages is requested; scripts, images and frames are never fetched.")
        ad_urls = scan["ad_urls_structural_count"] + scan["ad_urls_textual_count"]
        if ad_urls:
            message = (f"{ad_urls} advertising URL(s) remain in extracted content "
                       f"({scan['ad_urls_structural_count']} link/media, "
                       f"{scan['ad_urls_textual_count']} text/metadata); an ad element was not recognized "
                       "or an advertising-host URL is written in the article.")
            if ad_filter == "strict":
                raise ReaderError("ad_content_detected", message + " The page was not returned (--ad-filter strict).",
                                  ad_filter=ad_report)
            parser.warnings.append(message + " Kept because --ad-filter report was selected.")
        if scan["affiliate_urls_count"]:
            parser.warnings.append(f"{scan['affiliate_urls_count']} affiliate link(s) are retained as article sources, "
                                   "not treated as ads. See ad_filter.output_scan.")
    return {"page_title": page_title,
            "document_title": page_title,
            "article_title": article_title, "article_selector": article_selector,
            "article_integrity": article_integrity,
            "article_state": article_state, "article_content": article_content,
            "footnote_diagnostics": footnote_diagnostics,
            "lines": lines, "links": parser.links,
            "link_original_hrefs": original_hrefs,
            "headings": headings, "tables": tables, "nicknames": nicknames,
            "images": images,
            "footnotes": footnotes, "line_footnotes": line_footnotes, "line_links": line_links,
            "metadata": page_metadata, "ad_filter": ad_report,
            "warnings": list(dict.fromkeys(parser.warnings))}


def _structured_replacement_audit(parsed):
    fields = ("page_title", "article_title", "links", "link_original_hrefs", "headings", "tables",
              "nicknames", "footnotes", "images", "metadata")
    audit = {
        "scope": "whole_parsed_structured_fields_before_selection",
        "fields": list(fields), "replacement_characters": 0, "affected_values": 0,
        "counting": "Occurrences in overlapping parsed representations; not unique source glyphs and not additive with article or byte-decoding counts.",
        "sample_paths": "JSON pointers into parse_article output, before selection and CLI output filtering; list indexes are zero-based.",
        "samples": [], "samples_truncated": False, "sample_limit": 40,
    }
    pending = [("", iter((key, parsed[key]) for key in fields if key in parsed))]
    while pending:
        parent_path, items = pending[-1]
        try:
            key, value = next(items)
        except StopIteration:
            pending.pop()
            continue
        if not isinstance(value, (str, dict, list)):
            continue
        path = parent_path + "/" + str(key).replace("~", "~0").replace("/", "~1")
        if isinstance(value, dict):
            pending.append((path, iter(value.items())))
        elif isinstance(value, list):
            pending.append((path, iter(enumerate(value))))
        elif "\ufffd" in value:
            count = value.count("\ufffd")
            audit["replacement_characters"] += count
            audit["affected_values"] += 1
            if len(audit["samples"]) < audit["sample_limit"]:
                first = value.index("\ufffd")
                start = max(0, first - 40)
                end = min(len(value), start + 160)
                audit["samples"].append({
                    "path": path, "replacement_characters": count,
                    "text_excerpt": value[start:end], "excerpt_character_offset": start,
                    "excerpt_truncated": start > 0 or end < len(value),
                })
            else:
                audit["samples_truncated"] = True
    return audit


class ResponseProbe(HTMLParser):
    def __init__(self):
        super().__init__()
        self.inner = False
        self.mobile_style = False

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        self.inner |= attrs.get("id") == "page-body-inner"
        if tag == "link":
            self.mobile_style |= (attrs.get("href") or "").startswith("https://static.seesaawiki.jp/css/wiki/lite/")


_LINK_TAG = r'''(?is)<link(?=[\s/>])(?:[^>"']|"[^"]*"|'[^']*')*>'''
_LINK_TAG_BYTES, _LINK_TAG_TEXT = re.compile(_LINK_TAG.encode("ascii")), re.compile(_LINK_TAG)
_HTML_EVIDENCE = r"(?i)<(?:!doctype\s+html|html\b|head\b|div\b)"
_HTML_EVIDENCE_BYTES, _HTML_EVIDENCE_TEXT = re.compile(_HTML_EVIDENCE.encode("ascii")), re.compile(_HTML_EVIDENCE)


def wide_text(raw, content_type=""):
    """The response decoded as text when its bytes do not keep ASCII markup as it is: UTF-16 or UTF-32 (a byte
    order mark, or NUL bytes between the letters) or a charset in the Content-Type that encodes ASCII otherwise.
    None for every other response. The checks below search the raw bytes for ASCII markup; for such a response
    they search this text instead."""
    head = raw[:4096]
    wide = head.startswith((codecs.BOM_UTF32_LE, codecs.BOM_UTF32_BE, codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)) or b"\x00" in head
    if not wide and content_type:
        message = Message()
        message["Content-Type"] = content_type
        codec = text_codec(message.get_content_charset())
        try:
            wide = bool(codec) and "<a>".encode(codec) != b"<a>"
        except (UnicodeError, LookupError):
            wide = False
    if not wide:
        return None
    try:
        return decode_page(raw, content_type or "")[0]
    except (ReaderError, ValueError, LookupError):
        return None


def has_html_evidence(raw, content_type=""):
    """Whether the start of a response that names no Content-Type looks like an HTML document."""
    if _HTML_EVIDENCE_BYTES.search(raw[:8192]):
        return True
    text = wide_text(raw[:8192], content_type)
    return text is not None and _HTML_EVIDENCE_TEXT.search(text) is not None


def is_mobile_response(raw, metadata):
    if metadata.get("http_status") != 200:
        return False
    text = wide_text(raw, metadata.get("content_type"))
    if text is None:
        data, marker, ampersand, closer, link_tag = raw, b"/css/wiki/lite/", b"&", b">", _LINK_TAG_BYTES
    else:
        data, marker, ampersand, closer, link_tag = text, "/css/wiki/lite/", "&", ">", _LINK_TAG_TEXT
    if marker not in data:
        # HTML entities can encode any part of the stylesheet URL. Inspect
        # candidate link tags before rejecting, including > inside quotes.
        # A tag ends at a >, so none can begin after the last one: the scan stops
        # there (a page of unterminated <link tags would cost the square of its size).
        if not any(ampersand in match.group() for match in link_tag.finditer(data, 0, data.rfind(closer) + 1)):
            return False
    probe = ResponseProbe()
    probe.feed(_LONG_DECIMAL_REFERENCE.sub(lambda m: " " * len(m.group()), raw.decode("latin-1") if text is None else text))
    return probe.mobile_style and not probe.inner


def read_page_with_layout(url, args, limiter):
    started = time.monotonic()
    def get(ua):
        budget = args.time_budget - (time.monotonic() - started)
        if budget <= 0:
            raise ReaderError("time_budget_exceeded", "No time remains for the desktop layout request.")
        return fetch_page(url, timeout=args.timeout, retries=args.retries, time_budget=budget,
                          max_bytes=args.max_bytes, user_agent=ua, rate_limiter=limiter)
    raw, metadata = get(args.user_agent)
    if is_mobile_response(raw, metadata):
        previous = metadata
        if args.user_agent == DESKTOP_UA:
            raise ReaderError("mobile_layout", "The server returned a mobile layout without the full article.",
                              http_requests=metadata["http_requests"])
        try:
            raw, metadata = get(DESKTOP_UA)
        except ReaderError as exc:
            exc.details["http_requests"] = exc.details.get("http_requests", 0) + previous["http_requests"]
            exc.details["retry_history"] = previous.get("retry_history", []) + exc.details.get("retry_history", [])
            exc.details["layout_fallback"] = "Initial HTTP 200 mobile representation was incomplete; the single desktop request failed."
            raise
        metadata["http_requests"] += previous["http_requests"]
        metadata["retry_history"] = previous.get("retry_history", []) + metadata.get("retry_history", [])      # as the count above
        metadata["layout_fallback"] = {"reason": "HTTP 200 with observed wiki/lite stylesheet and no page-body-inner", "initial_user_agent": args.user_agent}
        metadata["fetch_warnings"] = ["A successful mobile-layout response lacked the full article; fetched the desktop representation once."]
        if is_mobile_response(raw, metadata):
            raise ReaderError("mobile_layout", "The desktop request also lacks the full article.",
                              http_requests=metadata["http_requests"])
    return raw, metadata


def cache_diagnostic_reasons(result):
    reasons = [name for key, name in (
        ("decode_lossy", "byte_decode_replacements"),
        ("article_replacement_characters", "article_replacements"),
        ("structured_replacement_characters", "structured_replacements"),
    ) if result.get(key)]
    charrefs = result.get("charref_repairs", {})
    if charrefs.get("joined_surrogate_pairs") or charrefs.get("numeric_reference_normalizations"):
        reasons.append("character_reference_preprocessing")
    return reasons


class PageCache:
    """Explicit task-scoped cache; one bounded, checksummed, atomic JSON record."""
    def __init__(self, directory, max_bytes=MAX_BYTES, ttl=21600, policy="clean"):
        if policy not in {"clean", "diagnostic"}:
            raise ValueError("Cache policy must be clean or diagnostic.")
        self.directory = Path(directory) if directory else None
        self.max_bytes, self.ttl = max_bytes, ttl
        self.policy = policy
        self.warnings = []

    def path(self, url, user_agent):
        # Reader-version changes intentionally invalidate old parsed responses;
        # percent-case aliases within this version reuse one cache record.
        key = hashlib.sha256((VERSION + "\n" + url_identity(url) + "\n" + user_agent).encode()).hexdigest()
        return self.directory / (key + ".json")

    def read_snapshot(self, path, *, allow_old_version=False):
        """Validate stored raw bytes; age/version exceptions never imply freshness."""
        limit = 4 * ((self.max_bytes + 2) // 3) + 131072
        with path.open("rb") as stream:
            data = read_up_to(stream, limit + 1)
        if len(data) > limit:
            raise ValueError("record exceeds limit")
        record = json.loads(data)
        if (not isinstance(record, dict) or record.get("schema") != 1
                or not isinstance(record.get("reader_version"), str)
                or (not allow_old_version and record["reader_version"] != VERSION)):
            raise ValueError("schema/version mismatch")
        try:
            age = time.time() - float(record["stored_at"])
        except OverflowError as exc:
            raise ValueError("invalid timestamp") from exc
        if not math.isfinite(age) or age < -60:
            raise ValueError("invalid timestamp")
        requested = check_url(record["requested_url"])
        if not isinstance(record.get("requested_user_agent"), str):
            raise ValueError("invalid request user agent")
        raw = base64.b64decode(record["html_base64"], validate=True)
        if len(raw) > self.max_bytes or hashlib.sha256(raw).hexdigest() != record.get("sha256"):
            raise ValueError("size or checksum mismatch")
        meta = record["metadata"]
        if (not isinstance(meta, dict) or meta.get("http_status") != 200
                or url_identity(meta.get("requested_url")) != url_identity(requested)):
            raise ValueError("invalid metadata")
        check_url(meta["url"], wiki=wiki_from_url(requested))
        if not isinstance(meta.get("content_type"), str) or not isinstance(meta.get("fetched_at"), str):
            raise ValueError("invalid source metadata")
        if "fetch_warnings" in meta and (not isinstance(meta["fetch_warnings"], list)
                or any(not isinstance(warning, str) for warning in meta["fetch_warnings"])):
            raise ValueError("invalid fetch warnings")
        media = Message()
        media["Content-Type"] = meta["content_type"]
        if meta["content_type"]:
            if media.get_content_type() not in {"text/html", "application/xhtml+xml"}:
                raise ValueError("non-HTML content type")
        elif not has_html_evidence(raw):
            raise ValueError("missing HTML evidence")
        response_meta = {key: value for key, value in meta.items() if key in RESPONSE_METADATA_KEYS}
        # JSON permits escaped lone surrogates; UTF-8 output does not. Reject
        # corrupt retained provenance before reuse, after dropping unknown and
        # invocation-only fields so discarded fields cannot poison good HTML.
        json.dumps(response_meta, ensure_ascii=False).encode("utf-8")
        return raw, response_meta, record, age

    def load(self, url, user_agent, *, ad_filter="strict", max_grid_cells=MAX_GRID_CELLS):
        """A reusable snapshot's bytes and metadata, or None. The snapshot is checked with the settings the page
        will be read with (the ad filter and the grid budget), so what is accepted here is what is then parsed."""
        if self.directory is None:
            return None
        path = self.path(url, user_agent)
        if not path_exists(path):
            return None
        try:
            raw, meta, record, age = self.read_snapshot(path)
            if age > self.ttl:
                return None
            identity = url_identity(url)
            if url_identity(record.get("requested_url")) != identity or record.get("requested_user_agent") != user_agent:
                raise ValueError("request identity mismatch")
            html, decoded = decode_page(raw, meta["content_type"])
            prepared, charrefs = prepare_surrogate_charrefs(html, "html")
            parsed = parse_article(prepared, meta["url"], max_grid_cells=max_grid_cells, ad_filter=ad_filter)
            if (parsed["article_integrity"]["unclosed_required_container"]
                    or is_mobile_response(raw, meta) or not parsed["article_selector"].startswith("#page-body-inner")):
                raise ValueError("incomplete article")
            reasons = cache_diagnostic_reasons({
                "decode_lossy": decoded["decode_lossy"],
                "article_replacement_characters": sum(line.count("\ufffd") for line in parsed["lines"]),
                "structured_replacement_characters": _structured_replacement_audit(parsed)["replacement_characters"],
                "charref_repairs": charrefs,
            })
            # Recompute quality from raw bytes; never trust a stored clean label.
            if reasons and self.policy == "clean":
                self.warnings.append("A cache snapshot has content diagnostics and was ignored under the clean policy.")
                return None
            if reasons:
                self.warnings.append("Reused a diagnostic raw snapshot under the explicit diagnostic cache policy. Content warnings are recalculated on every read; this does not establish the cause or permanence of the damage. Use --refresh for a new response.")
            return raw, {**meta, "from_cache": True, "cache_age_seconds": max(0, age),
                         "cache_quality": "diagnostic" if reasons else "clean", "cache_diagnostics": reasons,
                         "original_http_requests": meta.get("http_requests"), "http_requests": 0}
        except (OSError, ValueError, KeyError, TypeError, ReaderError, RecursionError):
            self.warnings.append("An invalid cache record was ignored; obtaining a fresh response.")
            return None

    def store(self, url, user_agent, raw, metadata, result):
        if self.directory is None:
            return
        charrefs = result.get("charref_repairs", {})
        reasons = cache_diagnostic_reasons(result)
        if reasons and self.policy == "clean":
            if charrefs.get("joined_surrogate_pairs") or charrefs.get("numeric_reference_normalizations"):
                self.warnings.append("The response required character-reference preprocessing and was not cached; raw cache records must remain readable under the default HTML policy.")
            else:
                self.warnings.append("Content diagnostics prevented clean caching. --cache-policy diagnostic can retain the original response with warnings; it does not certify the content.")
            return
        if (len(raw) > self.max_bytes or result.get("article_integrity", {}).get("unclosed_required_container")
                or metadata.get("http_status") != 200):
            return
        if not result.get("article_selector", "").startswith("#page-body-inner") or is_mobile_response(raw, metadata):
            return
        if result.get("encoding_source") == "explicit_override":
            return
        record = {"schema": 1, "reader_version": VERSION, "stored_at": time.time(),
                  "quality": "diagnostic" if reasons else "clean",
                  "requested_url": url, "requested_user_agent": user_agent,
                  "metadata": {key: value for key, value in metadata.items()
                               if key not in REQUEST_RESOLUTION_KEYS},
                  "sha256": hashlib.sha256(raw).hexdigest(), "html_base64": base64.b64encode(raw).decode("ascii")}
        try:
            self.directory.mkdir(parents=True, exist_ok=True)
            write_atomic(self.path(url, user_agent), json.dumps(record, ensure_ascii=False).encode("utf-8"))
            result.update(cache_saved=True, cache_quality=record["quality"], cache_diagnostics=reasons)
            if reasons:
                self.warnings.append("Saved the original response as a diagnostic raw snapshot. Content warnings remain applicable; storage does not establish the cause or permanence of the damage.")
        except OSError as exc:
            self.warnings.append("The page was read, but its cache record could not be saved. "
                                 + write_failure_reason(self.path(url, user_agent), exc))


class ObservedLinks(HTMLParser):
    def __init__(self, base_url):
        super().__init__(convert_charrefs=True)
        self.base_url = check_url(base_url)
        self.wiki = wiki_from_url(self.base_url)
        self.article_prefix = "/" + self.wiki + "/d/"
        self.entries = {}

    def handle_starttag(self, tag, attrs):
        if tag != "a":
            return
        href = dict(attrs).get("href")
        if not href or href.strip().startswith("#"):
            return
        try:
            url = check_url(urljoin(self.base_url, href), wiki=self.wiki)
            path = urlsplit(url).path
            if not path.startswith(self.article_prefix):
                return
            raw = unquote_to_bytes(path[len(self.article_prefix):])
            try:
                title, encoding = raw.decode("euc_jp"), "euc_jp"
            except UnicodeError:
                title, encoding = raw.decode("euc_jis_2004"), "euc_jis_2004"
            if not title or len(title) > 1024 or "\ufffd" in title:
                return
            self.entries.setdefault(url_identity(url), {
                "title": title, "url": url, "title_encoding": encoding, "observed_on": self.base_url})
        except (ReaderError, ValueError, UnicodeError):
            return


class TitleIndex:
    """Observed article paths with their original URL variants as provenance.

    HTTP/cache identity includes query parameters, while title identity does
    not. Schema 1 records are merged on load and saved as schema 2 at the next
    harvest. Searching never fetches a seed page.
    """
    LIMIT = 4 * 1024 * 1024

    def __init__(self, path=None, *, wiki="hololivetv"):
        self.path = Path(path) if path else None
        self.wiki = validate_wiki_name(wiki)
        self.base = wiki_base(self.wiki)
        self.article_prefix = "/" + self.wiki + "/d/"
        self.write_enabled = True
        self.entries = {}
        self.warnings = []
        self._serialized_size = None
        if self.path and path_exists(self.path):
            try:
                with self.path.open("rb") as stream:
                    raw = stream.read(self.LIMIT + 1)
                if len(raw) > self.LIMIT:
                    raise ValueError("index exceeds limit")
                data = json.loads(raw)
                if not isinstance(data, dict) or data.get("schema") not in {1, 2} or not isinstance(data.get("entries"), list):
                    raise ValueError("index schema")
                if data.get("wiki", self.wiki) != self.wiki:
                    self.write_enabled = False
                    raise ValueError("index belongs to a different wiki")
                for item in data["entries"]:
                    if not isinstance(item, dict) or not isinstance(item.get("title"), str) or not isinstance(item.get("url"), str):
                        raise ValueError("invalid index entry")
                    if wiki_from_url(item["url"]) != self.wiki:
                        self.write_enabled = False
                        raise ValueError("index contains a different wiki")
                    identity = article_identity(item["url"])
                    observed_on = item.get("observed_on", self.base)
                    if not isinstance(observed_on, str):
                        raise ValueError("invalid observation provenance")
                    observed_on.encode("utf-8")
                    urls = [item["url"]] if data["schema"] == 1 else item.get("observed_urls")
                    if not isinstance(urls, list) or not urls:
                        raise ValueError("missing observed URLs")
                    for url in urls:
                        if not isinstance(url, str):
                            raise ValueError("invalid observed URL")
                        probe = ObservedLinks(self.base)
                        probe.handle_starttag("a", [("href", url)])
                        observed = probe.entries.get(url_identity(url))
                        if observed is None or observed["title"] != item["title"] or article_identity(url) != identity:
                            raise ValueError("index title/URL mismatch")
                        observed["observed_on"] = observed_on
                        self._merge(observed)
                    if data["schema"] == 2 and check_url(item["url"]) != article_url(item["url"]):
                        raise ValueError("schema 2 article URL contains a query")
            except (OSError, ValueError, TypeError, ReaderError, RecursionError):
                self.entries = {}
                self.warnings.append("The invalid local title index was ignored." if self.write_enabled else
                                     "The title index belongs to a different wiki; it was ignored and will not be overwritten. Use a separate --index-file.")

    def _merge(self, item):
        """Merge a validated observed URL, preferring an observed plain URL."""
        observed_url = check_url(item["url"], wiki=self.wiki)
        identity = article_identity(observed_url)
        plain_url = article_url(observed_url)
        source = "observed_url" if observed_url == plain_url else "query_removed_from_observed_url"
        current = self.entries.get(identity)
        previous_size = (len(json.dumps(current, ensure_ascii=False).encode("utf-8"))
                         if self._serialized_size is not None and current is not None else 0)
        if current is None:
            self.entries[identity] = {**item, "url": plain_url, "url_source": source,
                                      "observed_urls": [observed_url]}
        else:
            observed_identity = url_identity(observed_url)
            if not any(url_identity(url) == observed_identity for url in current["observed_urls"]):
                current["observed_urls"].append(observed_url)
            if source == "observed_url" and current["url_source"] != "observed_url":
                current.update({key: item[key] for key in ("url", "title_encoding", "observed_on")})
                current["url_source"] = source
        if self._serialized_size is not None:
            self._serialized_size += (len(json.dumps(self.entries[identity], ensure_ascii=False).encode("utf-8"))
                                      - previous_size)
            if current is None and len(self.entries) > 1:
                self._serialized_size += 2  # json.dumps separates entries with ", ".

    def harvest(self, html, url, *, include_page=False):
        probe = ObservedLinks(check_url(url, wiki=self.wiki))
        if include_page:
            # A successfully parsed page is itself an observed URL, even if
            # its HTML contains no ordinary self-link. Never guess its title
            # from display text; decode only the supplied final article URL.
            probe.handle_starttag("a", [("href", url)])
        probe.feed(html)
        probe.close()
        for item in probe.entries.values():
            self._merge(item)
        self.save()

    def serialized(self):
        return json.dumps({"schema": 2, "wiki": self.wiki, "entries": list(self.entries.values())}, ensure_ascii=False).encode("utf-8")

    def save(self, *, strict=False):
        if self.path and self.write_enabled:
            data = self.serialized()
            if len(data) > self.LIMIT:
                if strict:
                    raise ReaderError("index_too_large", "The rebuilt index exceeds its byte limit; existing index was not overwritten.")
                self.warnings.append("The title index exceeds its size limit and was not saved.")
                return False
            try:
                self.path.parent.mkdir(parents=True, exist_ok=True)
                write_atomic(self.path, data)
            except OSError as exc:
                if strict:
                    raise ReaderError("output_write_failed", "The title index could not be saved. "
                                      + write_failure_reason(self.path, exc), path=str(self.path)) from exc
                self.warnings.append("The page was read, but its title index could not be saved. " + write_failure_reason(self.path, exc))
                return False
            return True
        return False

    def exact(self, title):
        return [item for item in self.entries.values() if item["title"] == title]

    def search(self, wanted, limit=8):
        pool = sorted(self.entries.values(), key=lambda item: (item["title"], item["url"]))
        close = set(difflib.get_close_matches(wanted, [x["title"] for x in pool], n=limit, cutoff=0.6))
        direct = [x for x in pool if wanted in x["title"]]
        rest = [x for x in pool if x not in direct and (x["title"] in close or x["title"].replace("～", "〜") == wanted.replace("～", "〜"))]
        return (sorted(direct, key=lambda x: x["title"] != wanted) + rest)[:limit]

    def corrupt_candidates(self, url, limit=8):
        try:
            parts = urlsplit(url)
            if parts.scheme != "https" or parts.netloc != "seesaawiki.jp" or not parts.path.startswith(self.article_prefix):
                return []
            damaged = unquote_to_bytes(parts.path[len(self.article_prefix):])
        except (ValueError, TypeError):
            return []
        if len(damaged) > 2048 or b"\xef\xbf\xbd" not in damaged:
            return []
        pieces = re.split(rb"(?:\xef\xbf\xbd)+", damaged)
        if sum(map(len, pieces)) < 2:
            return []
        matches = []
        for item in self.entries.values():
            original = unquote_to_bytes(urlsplit(item["url"]).path[len(self.article_prefix):])
            if not original.startswith(pieces[0]) or not original.endswith(pieces[-1]):
                continue
            cursor, valid = len(pieces[0]), True
            for piece in pieces[1:]:
                hit = original.find(piece, cursor + 1)
                if hit < 0:
                    valid = False
                    break
                cursor = hit + len(piece)
            if valid:
                matches.append(item)
        return sorted(matches, key=lambda x: (x["title"], x["url"]))[:limit]


def rebuild_title_index(cache, index, *, ad_filter="strict", max_grid_cells=MAX_GRID_CELLS):
    """Recollect observed links from raw snapshots, without HTTP or freshness claims.

    Valid existing observations are kept: deleted/invalid cache files do not
    establish that an indexed article disappeared. Old reader versions and
    expired snapshots are usable only for this explicit offline index operation.
    """
    if cache.directory is None or not cache.directory.is_dir():
        raise ReaderError("cache_directory_missing", "--rebuild-index requires an existing --cache-dir.")
    if index.path is None or not index.write_enabled:
        raise ReaderError("index_not_writable", "Use a separate index file belonging to the selected wiki.")
    report = {"reader_version": VERSION, "wiki": index.wiki, "http_requests": 0,
              "operation": "rebuild_index", "mode": "merge_observed_links",
              "cache_records_seen": 0, "pages_reindexed": 0, "other_wiki_records": 0,
              "invalid_records": 0, "expired_snapshots": 0, "old_reader_snapshots": 0,
              "skipped_samples": [], "sample_limit": 40,
              "known_articles_before": len(index.entries),
              "warnings": list(index.warnings),
              "limitation": "Offline link observations only; no target was fetched or checked for current existence. Valid existing observations are preserved."}
    # Merge privately and save once, so a failed scan/write leaves disk intact.
    rebuilt = TitleIndex(wiki=index.wiki)
    rebuilt.entries = json.loads(json.dumps(index.entries))
    # Track exact UTF-8 bytes by changed entry; repeated whole-index dumps would
    # remain quadratic even when performed only once per fixed-size batch.
    rebuilt._serialized_size = len(rebuilt.serialized())
    for path in sorted(cache.directory.glob("*.json")):
        if not re.fullmatch(r"[0-9a-fA-F]{64}\.json", path.name) or path.resolve() == index.path.resolve():
            continue
        report["cache_records_seen"] += 1
        try:
            raw, meta, record, age = cache.read_snapshot(path, allow_old_version=True)
            if wiki_from_url(meta["url"]) != index.wiki:
                report["other_wiki_records"] += 1
                continue
            html, decoded = decode_page(raw, meta["content_type"])
            if decoded["decode_lossy"]:
                raise ValueError("lossy byte decoding; index not harvested")
            prepared = prepare_surrogate_charrefs(html, "html")[0]
            parsed = parse_article(prepared, meta["url"], max_grid_cells=max_grid_cells, ad_filter=ad_filter)
            if (parsed["article_integrity"]["unclosed_required_container"]
                    or is_mobile_response(raw, meta)
                    or not parsed["article_selector"].startswith("#page-body-inner")):
                raise ValueError("incomplete or unsupported article layout")
            rebuilt.harvest(prepared, meta["url"], include_page=True)
            report["pages_reindexed"] += 1
            report["expired_snapshots"] += int(age > cache.ttl)
            report["old_reader_snapshots"] += int(record["reader_version"] != VERSION)
        except (OSError, ValueError, KeyError, TypeError, ReaderError, UnicodeError, LookupError, RecursionError) as exc:
            report["invalid_records"] += 1
            if len(report["skipped_samples"]) < report["sample_limit"]:
                report["skipped_samples"].append({"file": path.name, "reason": str(exc)[:300]})
        if rebuilt._serialized_size > index.LIMIT:
            raise ReaderError("index_too_large", "The rebuilt index exceeds its byte limit; existing index was not overwritten.", rebuild_index=report)
    if not report["pages_reindexed"]:
        raise ReaderError("no_usable_cache_snapshots", "No usable snapshots for this wiki; existing index was not overwritten.", rebuild_index=report)
    if len(rebuilt.serialized()) > index.LIMIT:
        raise ReaderError("index_too_large", "The rebuilt index exceeds its byte limit; existing index was not overwritten.", rebuild_index=report)
    rebuilt.path = index.path
    try:
        rebuilt.save(strict=True)
    except ReaderError as exc:
        exc.details["rebuild_index"] = report
        raise
    index.entries = rebuilt.entries
    report.update(index_saved=True, known_articles=len(index.entries),
                  added_articles=len(index.entries) - report["known_articles_before"],
                  known_urls=sum(len(item["observed_urls"]) for item in index.entries.values()),
                  skipped_samples_truncated=report["invalid_records"] > len(report["skipped_samples"]))
    if report["invalid_records"]:
        report["warnings"].append("Some cache records were skipped; valid existing index entries were retained. See skipped_samples.")
    return report


def resolve_source(args, index):
    wiki = getattr(args, "wiki", "hololivetv")
    if index.wiki != wiki:
        raise ReaderError("index_wiki_mismatch", "The title index must use the selected wiki.")
    if args.url is not None:
        try:
            return check_url(args.url, wiki=wiki), {}
        except ReaderError as exc:
            if exc.code == "corrupted_url":
                exc.details["candidates"] = index.corrupt_candidates(args.url)
                exc.details["candidate_policy"] = "Suggestions only; choose an observed URL explicitly. Lost bytes cannot be recovered uniquely from a partial index."
            raise
    title = args.title
    exact = index.exact(title)
    if len(exact) == 1:
        entry = exact[0]
        return entry["url"], {"requested_title": title, "title_used": title,
                              "title_source": "observed_url_index",
                              "title_url_source": entry.get("url_source", "observed_url"),
                              "title_observed_urls": entry.get("observed_urls", [entry["url"]]),
                              "title_encoding": entry.get("title_encoding")}
    if len(exact) > 1:
        raise ReaderError("ambiguous_title", "Several distinct article paths share this title; use an exact --url.", candidates=exact[:8])
    normalized = title.replace("～", "〜") if args.normalize_title else title
    notes = {"requested_title": title, "title_used": normalized, "title_normalized": normalized != title}
    try:
        encoded, mode = encode_title(normalized)
        notes["title_encoding"] = mode
        notes["title_source"] = "encoded_exact_title"
        return encoded_title_url(encoded, wiki), notes
    except ReaderError as exc:
        if exc.code == "title_not_euc_jp":
            exc.details["candidates"] = index.search(title)
            if "～" in title:
                exc.details["normalization_hint"] = "After confirming the title, --normalize-title explicitly maps fullwidth tilde ～ to wave dash 〜; original URLs remain unchanged."
        raise


def positive_int(value):
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("Use a positive integer.") from exc
    if parsed < 1:
        raise argparse.ArgumentTypeError("Use a positive integer.")
    return parsed


def positive_seconds(value):
    try:
        parsed = float(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("Use a positive finite number.") from exc
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("Use a positive finite number.")
    return parsed


def build_cli():
    def wiki_name(value):
        try:
            return validate_wiki_name(value)
        except ReaderError as exc:
            raise argparse.ArgumentTypeError(str(exc)) from exc
    def grid_cells(value):
        parsed = positive_int(value)
        if parsed > MAX_GRID_CELLS:
            raise argparse.ArgumentTypeError(f"Use at most {MAX_GRID_CELLS} cells per table.")
        return parsed
    cli = argparse.ArgumentParser(description=__doc__)
    source = cli.add_mutually_exclusive_group(required=True)
    source.add_argument("--title", help="Exact, observed wiki title; preserves EUC-JP bytes with JIS2004 extensions when needed")
    source.add_argument("--url", help="Original ASCII percent-encoded HTTPS URL inside the selected wiki")
    source.add_argument("--search", help="Search the collected local title index; never fetches a seed page")
    source.add_argument("--rebuild-index", action="store_true", help="Recollect links from validated cache snapshots without HTTP; preserve existing observations")
    cli.add_argument("--wiki", type=wiki_name, default="hololivetv", help="Exact Seesaa wiki name containing hololive (default: hololivetv; e.g. hololivedreams)")
    cli.add_argument("--index-file", type=Path, help="Task-local index for this wiki; defaults to cache-dir/titles.json, or titles-WIKI.json for other wikis")
    cli.add_argument("--normalize-title", action="store_true", help="Explicitly normalize title ～ to 〜; exact indexed titles and original URLs take priority")
    cli.add_argument("--find", help="Literal substring filter over article lines")
    cli.add_argument("--context", type=int, choices=range(0, 21), default=0, help="Context lines around --find matches (0..20)")
    cli.add_argument("--section", help="Select a unique heading section; ambiguity is reported")
    cli.add_argument("--start", type=positive_int, default=1, help="1-based offset in all lines, or in matching lines with --find")
    cli.add_argument("--lines", type=positive_int, default=80, help="Maximum displayed article lines (default: 80)")
    cli.add_argument("--all", action="store_true", help="Return all article lines, or all matches; ignore --start/--lines")
    cli.add_argument("--all-links", action="store_true", help="Include links from the whole article")
    cli.add_argument("--tables", action="store_true", help="Include structured tables from the whole article")
    cli.add_argument("--nicknames", action="store_true", help="Include normalized nickname records from the whole article")
    cli.add_argument("--images", action="store_true", help="Include image URLs, alt text and dimensions from the article")
    cli.add_argument("--format", choices=("json", "text", "md"), default="json", help="Output format (default: JSON, compatible with earlier versions)")
    cli.add_argument("--links", choices=("references", "inline", "off"), help="Link display; default references for JSON, inline for text/Markdown")
    cli.add_argument("--footnotes", choices=("markers", "inline", "off"), default="markers", help="Footnote display; structured footnotes remain available except with off")
    cli.add_argument("--timeout", type=positive_seconds, default=20.0, help="Per-socket-operation timeout, seconds")
    cli.add_argument("--time-budget", type=positive_seconds, default=90.0, help="Network budget checked between reads/requests")
    cli.add_argument("--retries", type=int, choices=range(0, 4), default=2, help="Transient retries, 0..3 (default: 2)")
    cli.add_argument("--max-bytes", type=positive_int, default=MAX_BYTES, help="Limit for both transfer and decompressed HTML")
    cli.add_argument("--max-grid-cells", type=grid_cells, default=MAX_GRID_CELLS, help="Logical slots per table (default/max 1000000); page budgets remain bounded")
    cli.add_argument("--encoding", help="Explicit character encoding override, with a warning")
    cli.add_argument("--surrogate-charrefs", choices=("html", "utf16"), default="html", help="HTML semantics by default; utf16 explicitly recovers adjacent surrogate references in text/title/alt with source evidence")
    cli.add_argument("--ad-filter", choices=AD_FILTER_MODES, default="strict",
                     help="strict (default): skip ad slots/page chrome and refuse a page whose extracted content still "
                          "points at an ad network; report: skip and warn only; off: v3.8.3 behaviour")
    cli.add_argument("--user-agent", default=DEFAULT_UA, help="Request User-Agent; HTTP 403 never triggers a UA-switch retry")
    cli.add_argument("--cache-dir", type=Path, help="Enable validated disk caching in an explicit task directory (disabled by default)")
    cli.add_argument("--cache-policy", choices=("clean", "diagnostic"), default="clean", help="clean: reject character replacements/preprocessing (default); diagnostic: reuse raw snapshots with fresh warnings, never incomplete responses")
    cli.add_argument("--ttl", type=positive_seconds, default=21600.0, help="Cache TTL in seconds (default: 6 hours)")
    cli.add_argument("--refresh", action="store_true", help="Ignore the cached page and fetch a fresh response")
    cli.add_argument("--output", type=Path, help="Write UTF-8 output to this file instead of stdout")
    cli.add_argument("--save-html", type=Path, help="Save decompressed original HTML bytes for local replay")
    cli.add_argument("--html-file", type=Path, help="Parse a saved local HTML file instead of making an HTTP request")
    cli.add_argument("--content-type", help="Original Content-Type for --html-file, e.g. 'text/html; charset=euc-jp'")
    return cli


def select_article_lines(parsed, args):
    numbered = list(enumerate(parsed["lines"], 1))
    section = None
    if args.section is not None:
        marks = []
        for entry in parsed.get("headings", []):
            start = entry.get("article_line")
            if not start:
                continue
            match = re.match(r"^(#{1,6})\s+", parsed["lines"][start - 1])
            # A heading sharing a line with other content (inside a table cell)
            # has no line of its own to select. Match the parsed heading text,
            # not the rendered line: the line also carries whatever the chosen
            # link display added, so --links/--format would otherwise decide
            # which headings are selectable and which collide.
            if match and len(match.group(1)) == entry["level"]:
                marks.append({"line": start, "level": entry["level"], "text": entry["text"], "heading": entry})
        exact = [mark for mark in marks if mark["text"] == args.section]
        candidates = exact or [mark for mark in marks if args.section in mark["text"]]
        if not candidates:
            raise ReaderError("section_not_found", "No heading matched the requested section.", section=args.section)
        if len(candidates) != 1:
            raise ReaderError("ambiguous_section", "Multiple headings match; use a more specific heading.", candidates=[{"line": mark["line"], "heading": mark["text"]} for mark in candidates[:20]])
        chosen = candidates[0]
        # Headings are collected in document order, so their lines ascend.
        end = next((mark["line"] - 1 for mark in marks
                    if mark["line"] > chosen["line"] and mark["level"] <= chosen["level"]), len(numbered))
        section = {"heading": chosen["text"], "level": chosen["level"], "start_line": chosen["line"],
                   "end_line": end, "total_lines": end - chosen["line"] + 1,
                   "source_heading": chosen["heading"]}
        numbered = [(i, line) for i, line in numbered if chosen["line"] <= i <= end]
    matches = numbered if args.find is None else [(i, line) for i, line in numbered if args.find in line]
    selection = matches
    contextual = args.find is not None and args.context
    if contextual:
        wanted = {j for i, _ in matches for j in range(max(1, i - args.context), i + args.context + 1)}
        selection = [(i, line) for i, line in numbered if i in wanted]
    offset = 0 if args.all else args.start - 1
    selection_offset = offset
    if contextual and not args.all:
        if offset >= len(matches):
            selected = []
            selection_offset = len(selection)
        else:
            first_match = matches[offset][0]
            # --start indexes matches, not the expanded context. Do not bring
            # a skipped match back as the leading context of a later match.
            lower = max(first_match - args.context, matches[offset - 1][0] + 1 if offset else 1)
            selection_lines = [line for line, _ in selection]
            selection_offset = bisect.bisect_left(selection_lines, lower)
            first_position = bisect.bisect_left(selection_lines, first_match)
            # A small --lines must still include the requested first match.
            selection_offset = max(selection_offset, first_position - args.lines + 1)
            selected = selection[selection_offset:selection_offset + args.lines]
    else:
        selected = selection if args.all else selection[offset:offset + args.lines]
    info = {"more_before": selection_offset > 0 and bool(selection),
            "more_after": selection_offset + len(selected) < len(selection),
            "total_selection_lines": len(selection), "selection_offset": selection_offset + 1}
    if section:
        info["section"] = section
    if args.find is not None:
        last_line = selected[-1][0] if selected else float("inf")
        more_matches = any(line > last_line for line, _ in matches[offset:])
        info.update(total_matches=len(matches), more_matches=more_matches, match_offset=offset + 1, context=args.context)
    return selected, info


def decode_and_prepare(raw, metadata, args):
    html, decoded = decode_page(raw, metadata.get("content_type", ""), args.encoding)
    prepared, charrefs = prepare_surrogate_charrefs(html, getattr(args, "surrogate_charrefs", "html"))
    return html, decoded, prepared, charrefs


def make_result(raw, metadata, args, source=None):
    html, decode_info, prepared_html, charrefs = source or decode_and_prepare(raw, metadata, args)
    decoded = dict(decode_info)
    link_mode = args.links or ("references" if args.format == "json" else "inline")
    parsed = parse_article(prepared_html, metadata["url"], link_mode=link_mode, footnote_mode=args.footnotes,
                           max_grid_cells=getattr(args, "max_grid_cells", MAX_GRID_CELLS),
                           ad_filter=getattr(args, "ad_filter", "strict"))
    lines = parsed["lines"]
    if not lines and parsed.get("article_state") not in {"empty", "no_extractable_text"}:
        raise ReaderError("empty_article", "The article body is empty.")
    warnings = decoded.pop("warnings") + parsed.get("warnings", []) + metadata.get("fetch_warnings", [])
    if charrefs["mode"] == "utf16":
        warnings.append(f"Explicit UTF-16 character-reference compatibility mode joined {charrefs['joined_surrogate_pairs']} pair(s) in text/title/alt. This differs from standard HTML decoding; raw bytes and the source-reference audit are unchanged. See charref_repairs.")
    if charrefs["numeric_reference_normalizations"]:
        warnings.append(f"Canonicalized {charrefs['numeric_reference_normalizations']} oversized decimal reference(s) to equivalent HTML values to avoid the integer digit limit. See charref_repairs; raw source is unchanged.")
    article_replacements = sum(line.count("\ufffd") for line in lines)
    reference_audit = {
        "scope": "whole_decoded_html", "replacement_reference_occurrences": 0,
        "method": "numeric_reference_source_pattern_scan",
        "limitation": "Includes comments, script raw text, attributes and other skipped markup; source-pattern counts cannot be attributed directly to article replacement characters.",
        "invalid_numeric_references": 0, "explicit_replacement_references": 0,
        "counts_by_reason": {}, "samples": [], "samples_truncated": False,
        "sample_limit": 40, "html_lines_base": 1, "character_offsets_base": 0,
    }
    source_line, previous_offset = 1, 0
    for match in re.finditer(r"&#(?:[xX][0-9a-fA-F]+|[0-9]+);?", html):
        token = match.group()
        hexadecimal = token[2:3] in {"x", "X"}
        digits = token[3 if hexadecimal else 2:].rstrip(";").lstrip("0") or "0"
        value = 0x110000 if len(digits) > (6 if hexadecimal else 7) else int(digits, 16 if hexadecimal else 10)
        reason = ("null_code_point" if value == 0 else
                  "surrogate_code_point" if 0xD800 <= value <= 0xDFFF else
                  "out_of_unicode_range" if value > 0x10FFFF else
                  "explicit_replacement_code_point" if value == 0xFFFD else None)
        if reason is None:
            continue
        reference_audit["replacement_reference_occurrences"] += 1
        count_key = "explicit_replacement_references" if value == 0xFFFD else "invalid_numeric_references"
        reference_audit[count_key] += 1
        counts = reference_audit["counts_by_reason"]
        counts[reason] = counts.get(reason, 0) + 1
        if len(reference_audit["samples"]) < reference_audit["sample_limit"]:
            source_line += html.count("\n", previous_offset, match.start())
            previous_offset = match.start()
            reference_audit["samples"].append({
                "reference": token[:80], "reference_truncated": len(token) > 80,
                "reason": reason, "html_line": source_line, "character_offset": match.start(),
            })
        else:
            reference_audit["samples_truncated"] = True
    if reference_audit["explicit_replacement_references"]:
        warnings.append(
            f"Original HTML contains {reference_audit['explicit_replacement_references']} explicit U+FFFD numeric reference source pattern(s). "
            "These patterns are present in the source, not inserted by byte decoding. "
            "The scan includes markup outside the article; it does not identify who introduced them or recover any earlier characters."
        )
    if article_replacements:
        warnings.append(
            f"Article text contains {article_replacements} replacement character(s) after HTML parsing. "
            f"Byte decoding reported {decoded['replacement_characters']} replacement character(s); "
            f"the whole decoded HTML contains {reference_audit['replacement_reference_occurrences']} "
            "numeric reference source pattern(s) that would resolve to U+FFFD. See html_reference_audit; "
            "these counts have different scopes. See charref_repairs for the explicit compatibility-mode policy."
        )
    structured_audit = _structured_replacement_audit(parsed)
    if structured_audit["replacement_characters"]:
        warnings.append(
            f"Parsed structured fields contain {structured_audit['replacement_characters']} "
            f"replacement character occurrence(s) in {structured_audit['affected_values']} value(s). "
            "Overlapping representations are counted separately; this is not a count of unique source glyphs "
            "and must not be added to article or byte-decoding counts. See structured_replacement_audit "
            "for affected fields, including fields hidden by display options. Original source bytes are preserved."
        )
    if metadata.get("title_normalized"):
        warnings.append("Explicit title normalization changed ～ to 〜; the requested and used titles are recorded.")
    numbered = list(enumerate(lines, 1))
    selected, selection_info = select_article_lines(parsed, args)
    tables = parsed.get("tables", [])
    section = selection_info.get("section")
    table_scope = "whole_article"
    if section:
        anchor = section["source_heading"]
        tables = [table for table in tables if anchor in table.get("headings", [])]
        table_scope = "selected_section"
    used_ids = {key for line, _ in selected for key in parsed.get("line_links", {}).get(line, [])}
    if args.tables or args.nicknames:
        used_ids.update(str(key) for table in tables for row in table["rows"] for cell in row["cells"] for key in cell["link_ids"])
    if args.footnotes != "off":
        used_ids.update(str(key) for note in parsed.get("footnotes", {}).values()
                        for entry in note.get("footer_entries", []) for key in entry.get("link_ids", []))
    all_links = parsed["links"]
    links = all_links if args.all_links or link_mode == "inline" or (args.all and args.find is None and not section) else {k: v for k, v in all_links.items() if k in used_ids}
    result = {
        "reader_version": VERSION, **metadata, **decoded,
        "html_sha256": hashlib.sha256(raw).hexdigest(),
        "parsed_at": datetime.now(timezone.utc).isoformat(),
        "page_title": parsed["page_title"],
        "document_title": parsed["document_title"], "article_title": parsed["article_title"],
        "wiki": wiki_from_url(metadata["url"]),
        "article_selector": parsed.get("article_selector", "#page-body-inner"),
        "article_integrity": parsed["article_integrity"],
        "article_state": parsed.get("article_state", "content"),
        "article_content": parsed.get("article_content", {}),
        "footnote_diagnostics": parsed.get("footnote_diagnostics", {}),
        "warnings": warnings,
        "total_lines": len(lines), "returned_lines": len(selected),
        **selection_info,
        "lines": [{"line": i, "text": line} for i, line in selected],
        "links": links, "total_links": len(all_links),
        "links_scope": "whole_article" if links is all_links else "selected_lines_tables_and_footnotes",
        "link_original_hrefs": {k: v for k, v in parsed.get("link_original_hrefs", {}).items() if k in links},
        "link_display": link_mode, "page_metadata": parsed.get("metadata", {}),
        "headings": parsed.get("headings", []),
        "total_tables": len(parsed.get("tables", [])),
        "grid_limits": {"table_cells": getattr(args, "max_grid_cells", MAX_GRID_CELLS), "page_cells": MAX_PAGE_GRID_CELLS,
                        "page_work_units": MAX_PAGE_GRID_WORK, "table_rows": 50000, "table_columns": 256},
        "total_images": len(parsed.get("images", [])),
        "replacement_lines": [i for i, line in numbered if "\ufffd" in line],
        "article_replacement_characters": article_replacements,
        "structured_replacement_characters": structured_audit["replacement_characters"],
        "structured_replacement_audit": structured_audit,
        "html_reference_audit": reference_audit,
        "charref_repairs": charrefs,
        "ad_filter": parsed["ad_filter"],
    }
    if args.footnotes != "off":
        result["footnotes"] = parsed.get("footnotes", {})
        result["selected_footnote_numbers"] = list(dict.fromkeys(
            number for line, _ in selected for number in parsed.get("line_footnotes", {}).get(line, [])))
        if args.tables or args.nicknames:
            result["structured_footnote_numbers"] = list(dict.fromkeys(
                number for table in tables for row in table["rows"] for cell in row["cells"]
                for number in cell.get("footnote_numbers", [])))
    if args.tables:
        result.update(tables=tables, tables_scope=table_scope, returned_tables=len(tables))
    if args.nicknames:
        ids = {table["index"] for table in tables}
        result.update(nicknames=[r for r in parsed.get("nicknames", []) if r["source"]["table"] in ids], nicknames_scope=table_scope)
    if args.images:
        result["images"] = parsed.get("images", [])
        result["images_scope"] = "whole_article"
    return result


def render_result(result, args):
    if args.format == "json":
        return json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if result.get("operation") == "rebuild_index":
        output = ["Title index rebuilt from cached HTML (no HTTP).",
                  f"Pages: {result['pages_reindexed']}; added articles: {result['added_articles']}; known articles: {result['known_articles']}; skipped invalid records: {result['invalid_records']}",
                  result["limitation"]]
        if result["skipped_samples"]:
            output.append("skipped_samples: " + json.dumps(result["skipped_samples"], ensure_ascii=False))
    elif "search_results" in result:
        output = [f"Known articles: {result.get('known_articles', result['known_urls'])}; "
                  f"observed URLs: {result['known_urls']}; local index search (no HTTP)"]
        output += [f"{r['title']} — {r['url']}" for r in result["search_results"]]
    else:
        output = ["# " + result["page_title"], "url: " + result["url"],
                  f"Article lines: {result['total_lines']}; selection lines: {result['total_selection_lines']}; returned: {result['returned_lines']}; more_after: {result['more_after']}"]
        output.append(f"encoding: {result['encoding_used']}; fetched_at: {result.get('fetched_at')}; from_cache: {result.get('from_cache', False)}")
        ad = result.get("ad_filter") or {}
        if ad.get("mode") and ad["mode"] != "off":
            skipped = ad.get("skipped", {}).get("by_kind", {})
            output.append(f"ad_filter: {ad['mode']}; skipped ad slots {skipped.get('ad', 0)}, page chrome {skipped.get('chrome', 0)}; "
                          f"ad URLs in article links/images: {ad.get('output_scan', {}).get('ad_urls_structural_count', 0)}")
        if result.get("article_state") == "empty":
            output.append("Article state: empty. The explicit, closed article area contains no content.")
        elif result.get("article_state") == "no_extractable_text":
            output.append("Article state: no_extractable_text. The article has non-text or non-rendered content; zero text lines do not mean an empty page.")
        if result.get("cache_quality"):
            output.append("cache_quality: " + result["cache_quality"])
        meta = result.get("page_metadata", {})
        if meta:
            output.append("page_metadata: " + json.dumps(meta, ensure_ascii=False))
        output.extend(f"{item['line']}: {item['text']}" for item in result["lines"])
        if args.tables:
            output.append("Structured tables (" + result["tables_scope"] + "):")
            output.append(json.dumps(result["tables"], ensure_ascii=False))
        if args.nicknames:
            output.append("Nicknames (" + result["nicknames_scope"] + "):")
            output.append(json.dumps(result["nicknames"], ensure_ascii=False))
        if args.images:
            output.append("Images (" + result["images_scope"] + "):")
            output.append(json.dumps(result["images"], ensure_ascii=False))
        if args.all_links or result.get("link_display") == "references":
            output.append("links: " + json.dumps(result["links"], ensure_ascii=False))
        elif args.tables and result.get("link_display") != "off":
            table_ids = {key for table in result["tables"] for row in table["rows"]
                         for cell in row["cells"] for key in cell.get("link_ids", [])}
            table_links = {key: href for key, href in result["links"].items() if key in table_ids}
            if table_links:
                output.append("Table link URLs: " + json.dumps(table_links, ensure_ascii=False))
        note_numbers = list(dict.fromkeys(result.get("selected_footnote_numbers", [])
                                         + result.get("structured_footnote_numbers", [])))
        selected_notes = {number: result.get("footnotes", {})[number]
                          for number in note_numbers
                          if number in result.get("footnotes", {})}
        appendix_notes = {number: note for number, note in selected_notes.items()
                          if args.footnotes == "markers" or number not in result.get("selected_footnote_numbers", [])}
        if appendix_notes:
            output.append("Footnotes for displayed content:")
            output.extend("*" + number + ": " + note.get("display_text", note.get("text", ""))
                          for number, note in appendix_notes.items())
        if result.get("link_display") != "off" and selected_notes:
            shown = "\n".join(output)
            sources = {key: result["links"][key] for note in selected_notes.values()
                       for entry in note.get("footer_entries", []) for key in entry.get("link_ids", [])
                       if key in result["links"] and result["links"][key] not in shown}
            if sources:
                output.append("Footnote source URLs:")
                output.extend("[" + key + "] " + href for key, href in sources.items())
        conflicts = {k: v for k, v in result.get("footnotes", {}).items() if v.get("agreement") == "conflict"}
        if conflicts:
            output.append("Conflicting footnote representations: " + json.dumps(conflicts, ensure_ascii=False))
    output.extend("WARNING: " + warning for warning in result.get("warnings", []))
    audit = result.get("encoding_audit", {})
    if audit.get("occurrences"):
        output.append("encoding_audit: " + json.dumps(audit, ensure_ascii=False))
    byte_audit = result.get("byte_replacement_audit", {})
    if byte_audit.get("replacement_characters"):
        output.append("byte_replacement_audit: " + json.dumps(byte_audit, ensure_ascii=False))
    charrefs = result.get("charref_repairs", {})
    if charrefs.get("mode") == "utf16" or charrefs.get("numeric_reference_normalizations"):
        output.append("charref_repairs: " + json.dumps(charrefs, ensure_ascii=False))
    return "\n".join(output) + "\n"


def write_failure_reason(path, exc):
    # The exception names the temporary file, so state the requested target too.
    reason = f"Target: {path}. {type(exc).__name__}: {exc}"
    length = len(str(path))
    if os.name == "nt" and length > 240:
        reason += (f" The target path is {length} characters long; Windows rejects paths over 260 "
                   "unless long paths are enabled, so a shorter directory is required.")
    return reason


def write_requested_file(path, content, purpose):
    """Report the requested path, never the temporary name, when a write fails."""
    try:
        write_atomic(path, content)
    except OSError as exc:
        raise ReaderError("output_write_failed", purpose + " could not be written. "
                          + write_failure_reason(path, exc), path=str(path)) from exc


def write_atomic(path, content):
    name = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix="." + path.name[:8] + ".", delete=False) as stream:
            name = stream.name
            stream.write(content)
        os.replace(name, path)
        name = None
    finally:
        if name is not None:
            Path(name).unlink(missing_ok=True)


def main(argv=None):
    # UTF-8 before argparse can print: --help and usage errors hold Japanese text, which a redirected
    # stream in a legacy code page (cp1252, cp936, cp949 on Windows) cannot encode.
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, OSError, ValueError):
            pass
    cli = build_cli()
    args = cli.parse_args(argv)
    if args.content_type and not args.html_file:
        cli.error("--content-type requires --html-file")
    if args.html_file and args.save_html:
        cli.error("--save-html cannot be combined with --html-file")
    if args.search is not None and args.html_file:
        cli.error("--search cannot be combined with --html-file")
    if args.context and args.find is None:
        cli.error("--context requires --find")
    if args.normalize_title and args.title is None:
        cli.error("--normalize-title requires --title")
    if args.rebuild_index:
        if args.cache_dir is None:
            cli.error("--rebuild-index requires --cache-dir")
        if args.html_file or args.save_html or args.encoding or args.refresh:
            cli.error("--rebuild-index cannot be combined with HTML input/output, encoding override or refresh")
    index_name = "titles.json" if args.wiki == "hololivetv" else "titles-" + args.wiki + ".json"
    index_path = args.index_file or (args.cache_dir / index_name if args.cache_dir else None)
    try:
        paths = [p.resolve() for p in (args.output, args.save_html, args.html_file, index_path) if p is not None]
    except (OSError, ValueError, UnicodeError):
        cli.error("A path argument cannot be used (an invalid character, or a name the file system cannot look up).")
    if len(paths) != len(set(paths)):
        cli.error("Input HTML, output files and title index must use different paths")
    index = TitleIndex(index_path, wiki=args.wiki)
    cache = PageCache(args.cache_dir, max_bytes=args.max_bytes, ttl=args.ttl, policy=args.cache_policy)
    requests_made = None          # HTTP requests of a page that was fetched, for an error that comes after the fetch
    try:
        if args.rebuild_index:
            result = rebuild_title_index(cache, index, ad_filter=args.ad_filter, max_grid_cells=args.max_grid_cells)
        elif args.search is not None:
            result = {"reader_version": VERSION, "query": args.search, "wiki": args.wiki,
                      "known_articles": len(index.entries),
                      "known_urls": sum(len(item.get("observed_urls", [item["url"]])) for item in index.entries.values()),
                      "http_requests": 0, "search_results": index.search(args.search, limit=args.lines), "warnings": index.warnings}
        else:
            url, title_info = resolve_source(args, index)
            if args.html_file:
                with args.html_file.open("rb") as stream:
                    raw = read_up_to(stream, args.max_bytes + 1)
                if len(raw) > args.max_bytes:
                    raise ReaderError("page_too_large", "Local HTML exceeds the byte limit.")
                metadata = {"url": url, "requested_url": url, "source": "local_html", "fetched_at": None,
                            "content_type": args.content_type or "", "html_bytes": len(raw), "http_requests": 0, "from_cache": False}
            else:
                cached = None if args.refresh or args.encoding else cache.load(url, args.user_agent, ad_filter=args.ad_filter, max_grid_cells=args.max_grid_cells)
                if cached:
                    raw, metadata = cached
                    metadata["source"] = "cache"
                else:
                    raw, metadata = read_page_with_layout(url, args, RateLimiter())
                    requests_made = metadata["http_requests"]
                    metadata.update(source="http", from_cache=False)
                if args.save_html:
                    write_requested_file(args.save_html, raw, "The saved HTML")
            metadata.update(title_info)
            source = decode_and_prepare(raw, metadata, args)
            result = make_result(raw, metadata, args, source)
            if not args.html_file and not metadata.get("from_cache"):
                cache.store(url, args.user_agent, raw, metadata, result)
            html, decoded, prepared_html, charrefs = source
            if not decoded["decode_lossy"]:
                index_html = (prepared_html if charrefs["mode"] == "html" else
                              prepare_surrogate_charrefs(html, "html")[0]
                              if _LONG_DECIMAL_REFERENCE.search(html) else html)
                index.harvest(index_html, metadata["url"], include_page=True)
            result["known_articles"] = len(index.entries)
            result["cache_policy"] = args.cache_policy
            result["known_index_urls"] = sum(len(item.get("observed_urls", [item["url"]])) for item in index.entries.values())
            result["warnings"].extend(cache.warnings + index.warnings)
        output = render_result(result, args)
        if args.output:
            write_requested_file(args.output, output.encode("utf-8"), "The output file")
        else:
            print(output, end="")
        return 0
    except BrokenPipeError:
        try:
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, sys.stdout.fileno())
            os.close(devnull)
        except (OSError, ValueError, AttributeError):
            pass
        return 0
    except (ReaderError, ValueError, OSError, UnicodeError, LookupError) as exc:
        result = {"error": str(exc), "error_code": getattr(exc, "code", "processing_error")}
        result.update(getattr(exc, "details", {}))
        if requests_made is not None:
            result.setdefault("http_requests", requests_made)
        if isinstance(exc, ReaderError) and exc.code == "http_error" and exc.details.get("http_status") == 404:
            if args.title is not None:
                wanted = args.title
            else:
                probe = ObservedLinks(wiki_base(args.wiki))
                probe.handle_starttag("a", [("href", args.url)])
                wanted = next(iter(probe.entries.values()), {}).get("title", "")
            result["candidates"] = index.search(wanted) if wanted else []
            result["candidate_policy"] = "Suggestions only; no alternative page was fetched."
        print(json.dumps(result, ensure_ascii=False), file=sys.stderr)
        return 1


def run_cli():
    """Flush while BrokenPipeError is still catchable, including --help output."""
    try:
        try:
            return main()
        finally:
            sys.stdout.flush()
    except BrokenPipeError:
        # A second implicit flush at interpreter shutdown must not print a
        # traceback or replace the intended status with CPython's exit 120.
        with open(os.devnull, "w") as sink:
            os.dup2(sink.fileno(), sys.stdout.fileno())
        return 0


if __name__ == "__main__":
    raise SystemExit(run_cli())
