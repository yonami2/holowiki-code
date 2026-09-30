#!/usr/bin/env python3
"""Name resolution shared by the cache CLI and the skill's lookup script.

The same file is shipped twice, byte for byte: in the cache archive (used by
hololive_cache_core.py) and in the skill's scripts/ (used before the archive
is unpacked). A test checks that both copies are identical.

fold() makes spellings meet: NFKC, casefold, hiragana -> katakana, and
spaces, "_", "-", "・", apostrophes, dots and "@" removed. So 「ぺこら」,
「ペコラ」, 「ﾍﾟｺﾗ」 and "Gawr Gura", "gawr_gura", "@gawrgura" fold alike.

names.json (made by build_fast_cache.py) maps folded keys to people:
  strong keys    official name, slug, aliases, readings and X accounts
  nickname keys  how the wiki's nickname tables say others (or the person
                 themself) call someone; kept only when the key points at
                 exactly one person, is not a generic word and is not
                 another person's strong key. A role title (会長, 団長, 姫)
                 is generic too, except when the tables give it to exactly
                 one person in at least ROLE_SUPPORT rows (会長 → 桐生ココ);
                 one given to several people (社長) is recorded as ambiguous.
resolve() tries: a strong key, then a nickname key, then the start of a word
of a name or slug, then part of a name (never for a generic word such as 姉,
which is part of ルイ姉 but names no one by itself). Anything else is refused
with suggestions; an ambiguous query names every candidate.

Python 3.9+, standard library only.
"""

from __future__ import annotations

import difflib
import json
import re
import unicodedata

SCHEMA = "hololive-wiki-names/1"
FOLD_RULE = ("NFKC→casefold→ひらがなをカタカナへ→空白・_・-・中黒・アポストロフィ・ドット・@ を除去")
KIND_LABELS = {"name": "正式名", "slug": "slug", "alias": "別名", "reading": "読み", "handle": "Xアカウント",
               "nickname": "呼称表の呼び名"}
STRONG_KINDS = ("name", "slug", "alias", "reading", "handle")
_SEPARATORS = re.compile(r"[\s_\-・'’`.．。@]+")
_WORDS = re.compile(r"[\s_・]+")
# Words that name a role or a pronoun rather than one person.
_GENERIC = """私 わたし わたくし あたし あたい 僕 ぼく 俺 おれ おいら おら うち 自分 余 我 吾輩 わがはい ワイ 拙者 あーし
わっち あちき 小生 本人 先輩 せんぱい パイセン 後輩 同期 相方 ちゃん さん くん 君 きみ 様 さま たん 氏 殿 姉 姉さん
姉ちゃん お姉ちゃん おねえちゃん ねえさん 兄 兄貴 お兄ちゃん 妹 弟 ママ まま パパ 母 父 お母さん 母上 娘 息子 嫁 旦那
彼女 彼氏 先生 社長 会長 部長 団長 隊長 総帥 姫 王 女王 師匠 お嬢 お嬢様 あなた あんた お前 おまえ みんな 皆 全員
ホロメン リスナー 視聴者 ファン 友達 友人 あいつ こいつ そいつ""".split()
# Generic words that the tables may nevertheless give to one person only.
_ROLE_TITLES = "会長 社長 部長 団長 隊長 総帥 姫 王 女王 師匠 先生 お嬢 お嬢様".split()
ROLE_SUPPORT = 3


class NameError_(Exception):
    """A query that matches no one, or more than one person."""

    def __init__(self, message, candidates=(), ambiguous=False):
        super().__init__(message)
        self.candidates = list(candidates)
        self.ambiguous = ambiguous


def fold(text):
    text = unicodedata.normalize("NFKC", str(text)).casefold()
    text = "".join(chr(ord(ch) + 0x60) if "ぁ" <= ch <= "ゖ" else ch for ch in text)
    return _SEPARATORS.sub("", text)


GENERIC = frozenset(fold(word) for word in _GENERIC)
ROLE_TITLES = frozenset(fold(word) for word in _ROLE_TITLES)


def words(text):
    """Folded words of a name or slug ("Ninomae Ina'nis" -> ninomae, inanis)."""
    return [fold(part) for part in _WORDS.split(unicodedata.normalize("NFKC", str(text))) if fold(part)]


def split_names(value):
    """Nickname cell -> separate current nicknames.

    Struck-through entries (~~x~~) are not current and are dropped; notes in
    brackets such as （初期） are removed from the name itself.
    """
    value = re.sub(r"~~.*?~~", "", str(value or ""))
    value = re.sub(r"[（(][^）)]*[）)]", "", value)
    value = re.sub(r"[*＊]\d+", "", value)
    parts = re.split(r"[、,，/／;；]\s*|\s{2,}", value)
    return [part.strip(" 　「」『』\"'") for part in parts if part.strip(" 　「」『』\"'")]


_ACCOUNT_ROW = re.compile(r"^\|\s*X\s*(?:[（(]旧\s*Twitter[）)]|\(Twitter\)|（Twitter）)\s*\|(?P<cell>[^|]*)\|")
_ACCOUNT = re.compile(r"(?<![A-Za-z0-9_])@([A-Za-z0-9_]{1,15})(?![A-Za-z0-9_])")


def accounts_in_profile(lines):
    """X accounts in the 公式情報 row "| X（旧Twitter） | @main / @sub |" of a page."""
    found = []
    for line in lines:
        match = _ACCOUNT_ROW.match(line.strip())
        if match:
            for name in _ACCOUNT.findall(match.group("cell")):
                if "@" + name not in found:
                    found.append("@" + name)
    return found


_NAME_ROW = re.compile(r"^\|\s*\[colspan=\d+\]\s*(?P<name>[^|（(]+?)\s*[（(](?P<reading>[^|（()）]+)[）)]")


def readings_in_profile(lines, name):
    """The reading in the name row of a main page's profile table, "| [colspan=2] 戌神ころね（いぬがみころね）*1 |".

    Only the first row naming the person counts. A bracket that repeats the
    name (宝鐘マリン（宝鐘マリン）) or a row without one (大神ミオ / Ookami Mio)
    gives nothing.
    """
    for line in lines:
        match = _NAME_ROW.match(line.strip())
        if match and fold(match.group("name")) == fold(name):
            reading = match.group("reading").strip()
            return [reading] if fold(reading) != fold(name) else []
    return []


# --- building names.json -----------------------------------------------------------

def build_index(people, nicknames=None, handles=None):
    """names.json content.

    people: [{"slug", "name", "region", "generation", "aliases", "readings"}]
    nicknames: {slug: [{"counterpart_slug", "calls", "called_by"}]} (optional)
    handles: {slug: ["@account", ...]} (optional)
    """
    handles = handles or {}
    keys = {}

    def add(key_text, slug, kind, original):
        key = fold(key_text)
        if not key:
            return
        rows = keys.setdefault(key, [])
        if not any(row[0] == slug and row[1] == kind for row in rows):
            rows.append([slug, kind, original])

    for person in people:
        slug = person["slug"]
        add(person["name"], slug, "name", person["name"])
        add(slug, slug, "slug", slug)
        for alias in person.get("aliases") or []:
            add(alias, slug, "alias", alias)
        for reading in person.get("readings") or []:
            add(reading, slug, "reading", reading)
        for account in list(person.get("handles") or []) + list(handles.get(slug, [])):
            add(account, slug, "handle", account)
    strong = set(keys)

    nick_slugs, nick_originals = {}, {}
    ambiguous = {}
    if nicknames:
        by_slug = {person["slug"]: person for person in people}
        found = {}                       # folded -> {slug: original}
        support = {}                     # role title -> {slug: rows}
        for owner, records in nicknames.items():
            for record in records:
                target = record.get("counterpart_slug")
                if not target or target not in by_slug:
                    continue
                if target == owner:
                    values = [(owner, record.get("calls"))]             # the person's own row
                else:
                    values = [(target, record.get("calls")),           # owner -> target
                              (owner, record.get("called_by"))]        # target -> owner
                for slug, cell in values:
                    for name in split_names(cell):
                        key = fold(name)
                        role = key in ROLE_TITLES
                        if (len(key) < 2 and not role) or len(key) > 24 or (key in GENERIC and not role) or key in strong:
                            continue
                        if not re.search(r"\w", key):
                            continue
                        found.setdefault(key, {}).setdefault(slug, name)
                        if role:
                            support.setdefault(key, {})[slug] = support.get(key, {}).get(slug, 0) + 1
        for key, owners in found.items():
            if key in support and len(owners) == 1 and max(support[key].values()) < ROLE_SUPPORT:
                continue                 # a title one table gives in passing
            if len(owners) == 1:
                (slug, original), = owners.items()
                nick_slugs[key], nick_originals[key] = slug, original
            else:
                ambiguous[key] = sorted(owners)
        for key in sorted(nick_slugs):
            keys[key] = [[nick_slugs[key], "nickname", nick_originals[key]]]
    return {
        "schema": SCHEMA,
        "fold": FOLD_RULE,
        "note": ("強いキー（正式名・slug・別名・読み・Xアカウント）を優先し、呼称表の呼び名は1人だけを指す語に限る。"
                 "呼び名は資料の記載で、本人の現在の呼ばれ方を保証しない。"),
        "people": {person["slug"]: {"name": person["name"], "region": person.get("region"),
                                    "generation": person.get("generation"),
                                    "words": sorted(set(words(person["name"]) + words(person["slug"])))}
                   for person in people},
        "counts": {"strong_keys": len(strong), "nickname_keys": len(nick_slugs),
                   "ambiguous_nicknames": len(ambiguous)},
        "keys": {key: keys[key] for key in sorted(keys)},
        "ambiguous_nicknames": {key: ambiguous[key] for key in sorted(ambiguous)},
    }


def dumps(index):
    """names.json bytes: one key per line, so the file stays grep-able."""
    head = {k: v for k, v in index.items() if k not in {"keys", "ambiguous_nicknames", "people"}}
    parts = [json.dumps(k, ensure_ascii=False) + ":" + json.dumps(v, ensure_ascii=False, separators=(",", ":"))
             for k, v in head.items()]
    for name in ("people", "keys", "ambiguous_nicknames"):
        body = ",\n".join(json.dumps(k, ensure_ascii=False) + ":" + json.dumps(v, ensure_ascii=False, separators=(",", ":"))
                          for k, v in index[name].items())
        parts.append(json.dumps(name, ensure_ascii=False) + ":{\n" + body + "\n}")
    return ("{\n" + ",\n".join(parts) + "\n}\n").encode("utf-8")


def load(path):
    with open(path, "rb") as stream:
        index = json.loads(stream.read().decode("utf-8"))
    if index.get("schema") != SCHEMA:
        raise ValueError("unsupported names index: " + str(index.get("schema")))
    return index


# --- resolving ---------------------------------------------------------------------

def _names(index, slugs):
    return [index["people"][slug]["name"] for slug in slugs]


def resolve(index, query):
    """{"slug", "name", "via", "matched"} for one person, or NameError_."""
    key = fold(query)
    if not key:
        raise NameError_("名前が空です。")
    people = index["people"]
    rows = index["keys"].get(key, [])
    for kinds in (STRONG_KINDS, ("nickname",)):
        slugs = list(dict.fromkeys(row[0] for row in rows if row[1] in kinds))
        if len(slugs) == 1:
            row = next(row for row in rows if row[0] == slugs[0] and row[1] in kinds)
            return {"slug": slugs[0], "name": people[slugs[0]]["name"], "via": row[1], "matched": row[2]}
        if slugs:
            raise NameError_("複数の人物に一致します。正式名か slug を指定してください: " + "、".join(_names(index, slugs)),
                             _names(index, slugs), ambiguous=True)
    # A known ambiguous nickname must not be overridden by a weaker partial match.
    ambiguous = index.get("ambiguous_nicknames", {}).get(key, [])
    if ambiguous:
        names = _names(index, ambiguous)
        raise NameError_("複数の人物に一致します。正式名か slug を指定してください: " + "、".join(names),
                         names, ambiguous=True)
    # Start of a word of a name or slug ("Ina" -> Ninomae Ina'nis, "Mori" -> Mori Calliope).
    minimum = 3 if key.isascii() else 2
    if len(key) >= minimum:
        slugs = [slug for slug, person in people.items() if any(word.startswith(key) for word in person["words"])]
        if len(slugs) == 1:
            return {"slug": slugs[0], "name": people[slugs[0]]["name"], "via": "word_prefix", "matched": query}
        if slugs:
            raise NameError_("複数の人物に一致します。正式名か slug を指定してください: " + "、".join(_names(index, slugs)),
                             _names(index, slugs), ambiguous=True)
    # Part of a name, alias or reading ("宝鐘" -> 宝鐘マリン); not a generic word (姉 is part of ルイ姉).
    if key in GENERIC:
        raise NameError_(f"「{query}」は特定の1人を指す呼び方ではありません。正式名か slug を指定してください。")
    slugs = list(dict.fromkeys(row[0] for other, rows_ in index["keys"].items() if key in other
                               for row in rows_ if row[1] in {"name", "alias", "reading"}))
    if len(slugs) == 1:
        return {"slug": slugs[0], "name": people[slugs[0]]["name"], "via": "partial", "matched": query}
    if slugs:
        raise NameError_("複数の人物に一致します。正式名か slug を指定してください: " + "、".join(_names(index, slugs)),
                         _names(index, slugs), ambiguous=True)
    candidates = list(index.get("ambiguous_nicknames", {}).get(key, []))
    close = difflib.get_close_matches(key, list(index["keys"]), n=8, cutoff=0.7) if len(key) >= 2 else []
    for other in close:
        candidates += [row[0] for row in index["keys"][other]]
    names = list(dict.fromkeys(_names(index, [slug for slug in candidates if slug in people])))[:5]
    raise NameError_(f"該当する人物がいません: {query}" + (f"（候補: {'、'.join(names)}）" if names else ""), names)


if __name__ == "__main__":
    import sys
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, OSError, ValueError):
            pass
    if len(sys.argv) < 3:
        print("usage: hololive_names.py NAMES_JSON QUERY [QUERY ...]", file=sys.stderr)
        raise SystemExit(2)
    loaded = load(sys.argv[1])
    status = 0
    for query in sys.argv[2:]:
        try:
            print(json.dumps(resolve(loaded, query), ensure_ascii=False))
        except NameError_ as exc:
            print(json.dumps({"query": query, "error": str(exc), "candidates": exc.candidates}, ensure_ascii=False))
            status = 1
    raise SystemExit(status)
