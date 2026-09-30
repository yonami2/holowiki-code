#!/usr/bin/env python3
"""List or inspect the v3 person summaries without unpacking the full archive.

    python3 scripts/hololive_cache_lookup.py --list [--region JP|EN|ID]
    python3 scripts/hololive_cache_lookup.py NAME --summary     quick JSON record (no unpacking)
    python3 scripts/hololive_cache_lookup.py NAME               the summary card (unpacks the cache once)

Names resolve exactly as in the cache CLI (hololive_names.py with names_82.json):
official names, slugs, aliases, readings, X accounts and nicknames that the
wiki's tables use for one person; kana, width and spacing differences are
ignored. Output is UTF-8 on every platform.
"""

import argparse
import errno
import json
import os
import sys
from pathlib import Path

sys.dont_write_bytecode = True          # leave the skill folder as shipped (no scripts/__pycache__)
import hololive_names  # noqa: E402

CACHE = Path(__file__).resolve().parent.parent / "cache"


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, OSError, ValueError):
            pass
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("person", nargs="?", help="Name, nickname, reading, X account or slug")
    parser.add_argument("--region", choices=("JP", "EN", "ID"))
    parser.add_argument("--list", action="store_true", help="Show available names (region, name, slug, wiki listing)")
    parser.add_argument("--summary", action="store_true", help="Print the quick JSON record")
    args = parser.parse_args()

    data = json.loads((CACHE / "quick_profiles_82.json").read_text(encoding="utf-8"))
    people = data["people"]
    if args.region:
        people = [person for person in people if person["region"] == args.region]
    if args.list:
        for person in people:
            print("\t".join([person["region"], person["name"], person["slug"], person.get("wiki_status") or "—"]))
        return 0
    if not args.person:
        parser.error("specify a person or --list")

    names = hololive_names.load(CACHE / "names_82.json")
    try:
        found = hololive_names.resolve(names, args.person)
    except hololive_names.NameError_ as exc:
        print(str(exc), file=sys.stderr)
        return 1
    person = next((item for item in people if item["slug"] == found["slug"]), None)
    if person is None:
        print(f"{found['name']} is not in region {args.region}", file=sys.stderr)
        return 1
    if args.summary:
        record = dict(person)
        record["matched"] = {"query": args.person, "via": found["via"], "key": found["matched"]}
        if data.get("fictional_world_note"):
            record["fictional_world_note"] = data["fictional_world_note"]
        print(json.dumps(record, ensure_ascii=False, indent=2))
        return 0
    from hololive_cache import read_verified
    try:
        card = read_verified(person["card_path"])      # checked against the cache's manifest
    except (OSError, ValueError) as exc:
        print("Cache initialization failed: " + str(exc), file=sys.stderr)
        return 1
    print(card.decode("utf-8"))
    return 0


def _reader_left(exc):
    """The program reading our output stopped early (| head): EPIPE; a Windows pipe reports EINVAL instead."""
    return isinstance(exc, BrokenPipeError) or (os.name == "nt" and exc.errno == errno.EINVAL)


if __name__ == "__main__":
    try:
        code = main()
        sys.stdout.flush()
    except OSError as exc:
        if not _reader_left(exc):
            raise
        try:                       # nothing more can be written; keep the exit flush from failing too
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except (OSError, ValueError, AttributeError):
            pass
        code = 0
    raise SystemExit(code)
