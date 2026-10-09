"""Skill package checks: identical shipped copies, the wrapper, the lookup script and the story pack.

Run from the skill root (no network; the archive is unpacked into temporary folders):

    python3 -m unittest discover -s tests -v          (Windows: python or py -3)

Each run unpacks the archive a few times (about 2 seconds each on a desktop).
"""
import hashlib
import importlib.util
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SKILL = Path(__file__).resolve().parents[1]
SCRIPTS = SKILL / "scripts"
CACHE = SKILL / "cache"
ARCHIVE = CACHE / "hololive_wiki_person_cache.tar.xz"
WRAPPER = SCRIPTS / "hololive_cache.py"
LOOKUP = SCRIPTS / "hololive_cache_lookup.py"
ROOT = "hololive_wiki_person_cache/"
SPEC = importlib.util.spec_from_file_location("skill_wrapper_tests", WRAPPER)
wrapper = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(wrapper)


def archive_member(name):
    with tarfile.open(ARCHIVE, "r:xz") as archive:
        return archive.extractfile(ROOT + name).read()


def run(argv, cache_dir, extra_env=None, cwd=None):
    env = dict(os.environ)
    env["HOLOLIVE_WIKI_CACHE_DIR"] = str(cache_dir)
    env.update(extra_env or {})
    process = subprocess.run([sys.executable, *map(str, argv)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             env=env, cwd=str(cwd or SKILL))
    return process.returncode, process.stdout.decode("utf-8"), process.stderr.decode("utf-8", "replace")


def private_file(path, data):
    """A file of this user that the wrapper accepts whatever the umask of the test run (e.g. 002)."""
    path.write_bytes(data.encode("utf-8") if isinstance(data, str) else bytes(data))
    os.chmod(path, 0o600)


def private_folder(path):
    path.mkdir(mode=0o700)
    os.chmod(path, 0o700)


class ShippedCopiesTests(unittest.TestCase):
    def test_wrapper_names_the_archive_it_ships_with(self):
        digest = hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()
        text = WRAPPER.read_text(encoding="utf-8")
        self.assertIn(f'ARCHIVE_SHA256 = "{digest}"', text)

    def test_wrapper_names_the_manifest_it_checks_against(self):
        digest = hashlib.sha256(archive_member("MANIFEST.sha256")).hexdigest()
        self.assertIn(f'MANIFEST_SHA256 = "{digest}"', WRAPPER.read_text(encoding="utf-8"))

    def test_scripts_are_the_archive_versions(self):
        pairs = {"hololive_names.py": "hololive_names.py", "hololive_wiki_reader.py": "tools/hololive_wiki_reader_v31.py",
                 "hololive_adblock.py": "tools/hololive_adblock.py"}
        for script, member in pairs.items():
            with self.subTest(script=script):
                self.assertEqual((SCRIPTS / script).read_bytes(), archive_member(member))

    def test_cache_files_are_the_archive_versions(self):
        pairs = {"names_82.json": "names.json", "quick_profiles_82.json": "hololive_wiki_quick_profiles_82.json",
                 "roster_82.json": "hololive_wiki_roster_82.json"}
        for name, member in pairs.items():
            with self.subTest(name=name):
                self.assertEqual((CACHE / name).read_bytes(), archive_member(member))

    def test_the_reader_writes_no_bytecode_beside_it(self):
        # 2026-10-02: run as `python3 scripts/hololive_wiki_reader.py`, the reader compiled hololive_adblock.py into
        # scripts/__pycache__, so the skill folder did not stay as shipped (the wrapper and the lookup write none).
        with tempfile.TemporaryDirectory() as td:
            folder = Path(td)
            for name in ("hololive_wiki_reader.py", "hololive_adblock.py"):
                shutil.copyfile(SCRIPTS / name, folder / name)
            page = folder / "page.html"
            page.write_text('<html><body><div id="page-body-inner"><div class="user-area"><p>text</p></div></div></body></html>',
                            encoding="utf-8")
            env = {key: value for key, value in os.environ.items() if key not in {"PYTHONDONTWRITEBYTECODE", "PYTHONPYCACHEPREFIX"}}
            process = subprocess.run([sys.executable, str(folder / "hololive_wiki_reader.py"), "--url", "https://seesaawiki.jp/hololivetv/d/x",
                                      "--html-file", str(page), "--content-type", "text/html; charset=utf-8", "--format", "json"],
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
            self.assertEqual(process.returncode, 0, process.stderr)
            self.assertEqual(json.loads(process.stdout.decode("utf-8"))["lines"][0]["text"], "text")
            self.assertEqual(sorted(path.name for path in folder.rglob("*")), ["hololive_adblock.py", "hololive_wiki_reader.py", "page.html"])

    def test_companion_files_carry_no_bare_fiction_flag(self):
        for name in ("quick_profiles_82.json", "roster_82.json"):
            data = json.loads((CACHE / name).read_text(encoding="utf-8"))
            self.assertNotIn("fictional_world_no_graduates", data)
            self.assertIn("会話", data["fictional_world_note"]["applies_only_when"])
            self.assertEqual(len(data["people"]), 82)

    def test_skill_md_frontmatter(self):
        text = (SKILL / "SKILL.md").read_text(encoding="utf-8")
        match = re.match(r"^---\nname: ([a-z0-9-]+)\ndescription: >-\n((?:  .*\n)+)---\n", text)
        self.assertIsNotNone(match)
        self.assertEqual(match.group(1), "hololive-wiki")
        description = " ".join(line.strip() for line in match.group(2).splitlines())
        self.assertLessEqual(len(description), 1024)
        self.assertNotRegex(description, r"[<>]")
        for link in re.findall(r"\]\(((?:references|scripts|cache)/[^)#]+)", text):
            self.assertTrue((SKILL / link).is_file(), link)


class WrapperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="hololive skill ")      # a space in the path, on purpose
        cls.cache_dir = Path(cls.tmp.name) / "cache dir"
        code, out, err = run([WRAPPER, "--cache-root"], cls.cache_dir)
        assert code == 0, err
        cls.root = Path(out.strip())

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_unpacked_where_asked_and_private(self):
        # The wrapper prints the resolved folder: /private/var on macOS, long names instead of RUNNER~1 on Windows.
        asked = os.path.normcase(os.path.realpath(self.cache_dir))
        self.assertTrue(os.path.normcase(str(self.root)).startswith(asked + os.sep), (self.root, asked))
        self.assertTrue((self.root / "MANIFEST.sha256").is_file())
        if os.name == "posix":
            self.assertEqual(stat.S_IMODE(os.stat(self.root.parent).st_mode) & 0o077, 0)

    def test_reuse_imports_nothing_needed_only_to_unpack(self):
        env = dict(os.environ, HOLOLIVE_WIKI_CACHE_DIR=str(self.cache_dir))

        def imported(*argv):
            process = subprocess.run([sys.executable, "-X", "importtime", *argv],
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
            self.assertEqual(process.returncode, 0, process.stderr.decode("utf-8", "replace")[-500:])
            return {line.rpartition("|")[2].strip() for line in process.stderr.decode("utf-8", "replace").splitlines()
                    if line.startswith("import time:")}
        # A Python whose startup (sitecustomize, .pth files) already imports some of these is not the wrapper's doing.
        by_wrapper = imported(str(WRAPPER), "--cache-root") - imported("-c", "pass")
        self.assertFalse(by_wrapper & {"tarfile", "lzma", "tempfile", "subprocess", "shutil", "pathlib"}, sorted(by_wrapper))

    def test_a_python_without_lzma_is_told_what_to_do(self):
        # A Python built without the lzma module cannot read the .tar.xz archive: say so, not "damaged".
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "lzma.py").write_text("raise ImportError('this build has no lzma')\n", encoding="utf-8")
            code, out, err = run([WRAPPER, "--cache-root"], Path(td) / "cache", {"PYTHONPATH": td})
        self.assertEqual((code, out), (1, ""))
        self.assertTrue(err.startswith("Cache initialization failed: "), err)
        self.assertIn("this Python has no lzma module", err)
        self.assertIn("hololive_cache_lookup.py", err)
        self.assertNotIn("damaged", err)

    def test_arguments_with_spaces_exit_codes_and_utf8(self):
        code, out, err = run([WRAPPER, "read", "Gawr Gura", "--section", "公式情報", "--lines", "3"], self.cache_dir)
        self.assertEqual(code, 0, err)
        self.assertIn("# Gawr Gura", out)
        code, out, err = run([WRAPPER, "scene", "Gawr Gura", "Mori Calliope", "--brief"], self.cache_dir)
        self.assertEqual(code, 0, err)
        self.assertIn("- Gawr Gura→Mori Calliope:", out)
        code, out, err = run([WRAPPER, "show", "存在しない人"], self.cache_dir)
        self.assertEqual(code, 1)
        self.assertIn("該当する人物がいません", err)
        code, out, err = run([WRAPPER, "show", "フブちゃん"], self.cache_dir, {"PYTHONIOENCODING": "cp1252"})
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("白上フブキ | JP"))

    def test_help_for_the_wrapper_and_each_command(self):
        code, out, err = run([WRAPPER, "--help"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        self.assertTrue(out.startswith("usage: hololive_cache.py COMMAND"), out)
        # A command's help is argparse's: printed through the held output, then exit code 0.
        for argv, expected in ((["show", "--help"], "usage: hololive_cache.py show"), (["story", "-h"], "--topic")):
            with self.subTest(argv=argv):
                code, out, err = run([WRAPPER, *argv], self.cache_dir)
                self.assertEqual((code, err), (0, ""))
                self.assertIn(expected, out)
        code, out, err = run([WRAPPER, "nosuch"], self.cache_dir)
        self.assertEqual((code, out), (2, ""))
        self.assertIn("usage: hololive_cache.py", err)

    def test_story_and_status(self):
        code, out, err = run([WRAPPER, "story", "宝鐘マリン", "兎田ぺこら", "--topic", "料理"], self.cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("# 物語用資料パック: 宝鐘マリン × 兎田ぺこら"))
        self.assertIn("コンビ・ユニット名: ぺこマリ", out)
        self.assertIn("### 話題「料理」", out)
        code, out, err = run([WRAPPER, "status", "天音かなた", "--format", "json"], self.cache_dir)
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["people"][0]["category"], "graduated")
        code, out, err = run([WRAPPER, "--status"], self.cache_dir)
        report = json.loads(out)
        self.assertTrue(report["archive_sha256_ok"])
        self.assertEqual(report["candidates"][0]["complete"], True)

    def test_story_takes_fifteen_people_as_before(self):
        # These 15 give the longest pack of any 15 (a greedy search over all pairs on 2026-10-04); 15 was the most
        # one story took until 2026-10-08. Since 2026-10-06 the automatic limit is 80,000 characters for one person
        # and 10,000 for each other one, at most 200,000, and the detail level is chosen automatically: each
        # person's section stays above the pairs' mention candidates.
        names = ["不知火フレア", "桃鈴ねね", "雪花ラミィ", "宝鐘マリン", "博衣こより", "さくらみこ", "大空スバル", "星街すいせい",
                 "兎田ぺこら", "戌神ころね", "アキ・ローゼンタール", "白銀ノエル", "夏色まつり", "大神ミオ", "白上フブキ"]
        code, out, err = run([WRAPPER, "story", *names, "--format", "json"], self.cache_dir)
        self.assertEqual(code, 0, err)
        pack = json.loads(out)
        self.assertEqual([person["name"] for person in pack["people"]], names)
        self.assertEqual(len(pack["pairs"]), 15 * 14 // 2)
        self.assertEqual(pack["budget"], {"limit": 200000, "measured_as": "md", "automatic": True})
        self.assertLessEqual(pack["characters"], pack["budget"]["limit"])
        self.assertEqual((pack["detail"], pack["pair_detail"]), ("normal", "brief"))
        guide = (SKILL / "references" / "story.md").read_text(encoding="utf-8")
        self.assertIn("人数に上限はなく、場面の顔ぶれ全員を1回の `story` に入れる（組を分けて実行しない）。", guide)
        self.assertNotIn("15人までとする", guide)
        self.assertIn("最大200,000字で、13人以上は200,000字", guide)
        self.assertNotIn("5人を超える場合", guide)
        self.assertNotIn("--detail brief", guide)

    def test_a_scene_with_many_members(self):
        # 2026-10-09: a scene that needs many members gets them all: the central characters named first, the rest
        # added with --group, within the automatic limit (the pairs fall to names, people to cameo if need be).
        code, out, err = run([WRAPPER, "story", "宝鐘マリン", "兎田ぺこら", "--group", "JP", "--topic", "運動会",
                              "--format", "json"], self.cache_dir)
        self.assertEqual(code, 0, err)
        pack = json.loads(out)
        self.assertEqual(len(pack["people"]), 44)
        self.assertEqual([person["name"] for person in pack["people"]][:3], ["宝鐘マリン", "兎田ぺこら", "ときのそら"])
        self.assertEqual((pack["pair_detail"], pack["pairs"], len(pack["names"])), ("names", [], 44))
        self.assertLessEqual(pack["characters"], 200000)
        self.assertEqual(pack["cast"]["groups"], [{"name": "JP", "added": 42}])
        code, view, err = run([WRAPPER, "story", "--group", "all", "--include-former", "--level"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        lines = view.replace("\r\n", "\n").splitlines()
        self.assertIn("組み合わせ（3240組）: names", lines)
        self.assertEqual(len([line for line in lines if line.startswith("- ")]), 81)
        self.assertTrue(any(line.endswith(": cameo") for line in lines))
        code, out, err = run([WRAPPER, "story", "--group", "存在しない"], self.cache_dir)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("使える名前: JP・EN・ID・all", err)
        guide = (SKILL / "references" / "story.md").read_text(encoding="utf-8")
        self.assertIn("## 2. 顔ぶれを決める", guide)
        self.assertIn("利用者に人数や顔ぶれを尋ねない", guide)
        self.assertIn("1人あたりの資料が短くなることを理由に人数を減らさない", guide)
        self.assertIn("story '宝鐘マリン' '兎田ぺこら' --group JP --topic '運動会'", guide)
        self.assertIn("--group JP", (SKILL / "SKILL.md").read_text(encoding="utf-8"))

    def test_story_detail_is_automatic_unless_capped_and_topics_are_words(self):
        # From the 220,000 variant tried in another chat (2026-10-06): its three people and topics. The topics were
        # given there as one spaced string first, which found nothing; they are now searched word by word. Three
        # people leave room for ace (2026-10-06b), the level above full: each person's own sections whole.
        people = ["天音かなた", "風真いろは", "湊あくあ"]
        code, out, err = run([WRAPPER, "story", *people, "--topic", "マネージャー 専属 推し 仲良し オカン",
                              "--format", "json"], self.cache_dir)
        self.assertEqual(code, 0, err)
        automatic = json.loads(out)
        self.assertEqual((automatic["detail"], automatic["pair_detail"]), ("ace", "ace"))
        own = [{key: count for key, count in person["omitted"].items() if key != "topic"}     # topic lines: 30 each
               for person in automatic["people"]]
        self.assertEqual(own, [{}, {}, {}])
        self.assertEqual(automatic["budget"], {"limit": 100000, "measured_as": "md", "automatic": True})
        self.assertEqual(automatic["topics"], ["マネージャー", "専属", "推し", "仲良し", "オカン"])
        self.assertEqual(len(automatic["topic_notes"]), 1)
        self.assertIn("推し: あくたん、ねねち、るしあ先輩", json.dumps(automatic["people"][0]["sections"]["topic"],
                                                         ensure_ascii=False))
        for cap in ("ace", "full", "normal", "brief"):      # an explicit --detail is a ceiling
            code, out, err = run([WRAPPER, "story", *people, "--detail", cap, "--format", "json"], self.cache_dir)
            self.assertEqual(code, 0, err)
            pack = json.loads(out)
            self.assertEqual((pack["detail"], pack["pair_detail"]), (cap, cap))
        code, out, err = run([WRAPPER, "story", people[0], "--topic", " "], self.cache_dir)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("空の話題", err)
        guide = (SKILL / "references" / "story.md").read_text(encoding="utf-8")
        self.assertIn("詳細度は詳しい順に ace・full・normal・brief", guide)

    def test_digest_sections_through_the_wrapper(self):
        argv = [WRAPPER, "show", "兎田ぺこら", "湊あくあ", "--digest"]
        code, out, err = run(argv + ["--section", "性格", "--section", "特徴", "--section", "あいさつ",
                                     "--section", "立ち位置"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        self.assertIn("## 性格・癖", out)
        self.assertIn("## プロフィール・特徴（詳細）", out)          # 湊あくあ has no 性格・癖
        self.assertNotIn("## 語録", out)
        self.assertLess(len(out), 30000)
        code, out, err = run(argv, self.cache_dir)          # the whole digests: about 350,000 characters
        self.assertEqual(code, 0, err)
        self.assertIn("（兎田ぺこらのダイジェストは", err)
        self.assertIn("--section 見出しの語 で節ごとに読める", err)
        self.assertIn("--section", (SKILL / "references" / "story.md").read_text(encoding="utf-8"))

    def test_a_long_story_pack_is_read_in_parts(self):
        names = ["宝鐘マリン", "兎田ぺこら", "白銀ノエル"]
        code, whole, note = run([WRAPPER, "story", *names], self.cache_dir)
        self.assertEqual(code, 0, note)
        whole = whole.replace("\r\n", "\n")                     # Windows writes \r\n to the pipe
        count = int(re.search(r"--part 1 から --part (\d+) まで付けて", note).group(1))
        self.assertGreater(count, 1)
        bodies = []
        for number in range(1, count + 1):
            code, out, err = run([WRAPPER, "story", *names, "--part", str(number)], self.cache_dir)
            self.assertEqual((code, err), (0, ""))
            header, body = out.replace("\r\n", "\n").split("\n\n", 1)
            body, footer = body.rstrip("\n").rsplit("\n\n", 1)
            self.assertIn(f"全{count}部の第{number}部: ", header)
            self.assertTrue(footer.startswith(f"（第{number}部ここまで: "), footer)
            self.assertLessEqual(len(body), 15000)
            bodies.append(body)
        self.assertEqual("\n".join(bodies), whole.rstrip("\n"))
        self.assertIn("--part 1", (SKILL / "references" / "story.md").read_text(encoding="utf-8"))

    def test_story_level_shows_the_level_only(self):
        # 2026-10-07: --level, the last line of story.md's bash boxes, shows the detail level a story command gets
        # (each person's and the pairs': ace, full, normal or brief) to check it, never the pack itself.
        guide = (SKILL / "references" / "story.md").read_text(encoding="utf-8")
        boxes = re.findall(r"```bash\n(.*?)```", guide, flags=re.S)
        part_box = next(box for box in boxes if "--part 2" in box)
        self.assertIn("--level", part_box.rstrip().splitlines()[-1])
        last = boxes[-1].rstrip().splitlines()
        self.assertTrue(last[-1].endswith(" --level"), last[-1])
        cast = re.findall(r"'([^']+)'", "\n".join(last[-3:]))
        self.assertEqual(len(cast), 15)
        code, out, err = run([WRAPPER, "story", *cast, "--level"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        lines = out.replace("\r\n", "\n").splitlines()
        self.assertEqual(len(lines), 2 + 15 + 3)                  # the label, 各人:, 15 people, pairs, size, note
        shown = [line[4:] for line in last if line.startswith("#   ") and "…" not in line]
        self.assertGreater(len(shown), 5)
        for line in shown:                                          # the guide's example is what the command shows
            self.assertIn(line, lines)
        people = ["天音かなた", "風真いろは", "湊あくあ"]
        code, view, err = run([WRAPPER, "story", *people, "--level"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(view.replace("\r\n", "\n").splitlines()[:6],
                         ["詳細度: ace", "各人:", "- 天音かなた: ace", "- 風真いろは: ace", "- 湊あくあ: ace",
                          "組み合わせ（3組）: ace"])
        self.assertNotIn("物語用資料パック", view)
        code, same, err = run([WRAPPER, "story", *people, "--part", "1", "--level"], self.cache_dir)
        self.assertEqual((code, same, err), (0, view, ""))
        code, view, err = run([WRAPPER, "story", *people, "--detail", "normal", "--level"], self.cache_dir)
        self.assertEqual((code, err), (0, ""))
        self.assertIn("組み合わせ（3組）: normal", view)

    def test_no_bytecode_is_written_into_the_cache(self):
        for argv in (["show", "宝鐘マリン"], ["story", "兎田ぺこら"], ["verify"]):
            code, out, err = run([WRAPPER, *argv], self.cache_dir)
            self.assertEqual(code, 0, err)
        self.assertEqual(sorted(self.root.rglob("__pycache__")), [])

    def test_no_arguments_prints_usage_without_unpacking(self):
        with tempfile.TemporaryDirectory() as td:
            code, out, err = run([WRAPPER], Path(td) / "never")
            self.assertEqual(code, 2)
            self.assertIn("usage: hololive_cache.py", err)
            self.assertFalse((Path(td) / "never").exists())

    def test_lookup_without_unpacking_and_with_the_card(self):
        with tempfile.TemporaryDirectory() as td:
            empty = Path(td) / "unused"
            code, out, err = run([LOOKUP, "--list"], empty, {"PYTHONIOENCODING": "cp1252"})
            self.assertEqual(code, 0, err)
            self.assertEqual(len(out.splitlines()), 82)
            self.assertIn("湊あくあ\tminato_aqua\twikiトップ", out)
            code, out, err = run([LOOKUP, "ししろん", "--summary"], empty, {"PYTHONIOENCODING": "cp1252"})
            self.assertEqual(code, 0, err)
            record = json.loads(out)
            self.assertEqual(record["name"], "獅白ぼたん")
            self.assertEqual(record["matched"]["via"], "nickname")
            self.assertIn("@shishirobotan", record["handles"])
            code, out, err = run([LOOKUP, "@FUWAMOCO_EN", "--summary"], empty)
            self.assertEqual(code, 1)
            self.assertIn("Fuwawa Abyssgard", err)
            self.assertFalse(empty.exists())
        code, out, err = run([LOOKUP, "さくらみこ"], self.cache_dir, {"PYTHONIOENCODING": "cp932"})
        self.assertEqual(code, 0, err)
        self.assertIn("🌸", out)
        self.assertFalse(out.replace("\r\n", "\n").endswith("\n\n"))      # the card as stored, no blank line added

    def test_lookup_names_a_damaged_file_of_the_skill(self):
        # 2026-10-02: the lookup read cache/quick_profiles_82.json and names_82.json as they were; one that is not
        # JSON, nests 10,000 deep or has another shape ended it in a traceback instead of naming the file.
        deep = b"[" * 10000 + b"]" * 10000
        cases = [("quick_profiles_82.json", data, ["--list"])
                 for data in (deep, b"{not json", b"\xff\xfe", b"[]", b'{"people": [1]}', b'{"people": [{"region": 1}]}')]
        cases += [("names_82.json", data, ["ししろん", "--summary"])
                  for data in (deep, b"{not json", b"[]", b'{"schema": "x"}', b'{"schema": "hololive-wiki-names/1"}')]
        for name, data, argv in cases:
            with self.subTest(name=name, data=data[:12]), tempfile.TemporaryDirectory() as td:
                copy = Path(td) / "skill"
                (copy / "scripts").mkdir(parents=True)
                (copy / "cache").mkdir()
                for script in ("hololive_cache_lookup.py", "hololive_names.py"):
                    shutil.copyfile(SCRIPTS / script, copy / "scripts" / script)
                for shipped in ("quick_profiles_82.json", "names_82.json"):
                    shutil.copyfile(CACHE / shipped, copy / "cache" / shipped)
                (copy / "cache" / name).write_bytes(data)
                code, out, err = run([copy / "scripts" / "hololive_cache_lookup.py", *argv], Path(td) / "unused")
                self.assertEqual(code, 1, out + err)
                self.assertIn("cache/" + name, err)
                self.assertIn("reinstall the skill", err)
                self.assertNotIn("Traceback", err)
                self.assertEqual(sorted(copy.rglob("__pycache__")), [])

    def test_lookup_list_ends_quietly_when_its_reader_stops(self):
        # `--list | head -1`: the pipe is closed before the list is written. As for the cache CLI and the
        # reader, that is not an error: exit code 0 and no traceback.
        with tempfile.TemporaryDirectory() as td:
            env = dict(os.environ, HOLOLIVE_WIKI_CACHE_DIR=str(Path(td) / "unused"))
            process = subprocess.Popen([sys.executable, str(LOOKUP), "--list"], stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, env=env, cwd=str(SKILL))
            process.stdout.close()
            err = process.stderr.read().decode("utf-8", "replace")
            process.stderr.close()
            self.assertEqual((process.wait(), err), (0, ""))


class RepairTests(unittest.TestCase):
    def fresh(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        cache_dir = Path(tmp.name)
        code, out, err = run([WRAPPER, "--cache-root"], cache_dir)
        self.assertEqual(code, 0, err)
        return cache_dir, Path(out.strip())

    def test_missing_manifest_or_page_is_unpacked_again(self):
        cache_dir, root = self.fresh()
        (root / "MANIFEST.sha256").unlink()
        page = next((root / "people" / "houshou_marine" / "pages").glob("*.txt"))
        code, out, err = run([WRAPPER, "read", "宝鐘マリン", page.stem, "--lines", "1"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue((root / "MANIFEST.sha256").is_file())
        page.unlink()
        code, out, err = run([WRAPPER, "read", "宝鐘マリン", page.stem, "--lines", "1"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue(page.is_file())
        leftovers = [p.name for p in cache_dir.iterdir() if not p.name.endswith(".lock")]
        self.assertEqual(len(leftovers), 1, leftovers)

    def test_every_file_removed_but_folders_kept(self):
        cache_dir, root = self.fresh()
        for path in root.rglob("*"):
            if path.is_file():
                path.unlink()
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        code, out, err = run([WRAPPER, "verify"], cache_dir)
        self.assertEqual(code, 0, out + err)

    def test_truncated_manifest_page_and_changed_python_are_repaired(self):
        cache_dir, root = self.fresh()
        manifest = root / "MANIFEST.sha256"
        manifest.write_text(manifest.read_text(encoding="utf-8").splitlines()[0] + "\n", encoding="utf-8")
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        page = next((root / "people" / "houshou_marine" / "pages").glob("*.txt"))
        page.write_bytes(b"")
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        core = root / "hololive_cache_core.py"
        source = core.read_bytes()
        core.write_bytes(b"#" * len(source))  # Same size: Python source must still be hashed.
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue(out.startswith("宝鐘マリン | JP"))

    def same_size_change(self, path, old, new):
        data = path.read_bytes()
        changed = data.replace(old.encode(), new.encode(), 1)
        self.assertEqual((len(changed), changed != data), (len(data), True))
        private_file(path, changed)
        return data

    def test_same_size_change_is_caught_when_the_file_is_read(self):
        cache_dir, root = self.fresh()
        digest = root / "people" / "shirogane_noel" / "digest.md"
        original = self.same_size_change(digest, "白銀ノエル", "黒金ノエル")
        self.assertTrue(wrapper._complete(root))        # the scan compares sizes: it cannot tell
        code, out, err = run([WRAPPER, "show", "白銀ノエル", "--digest"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertNotIn("黒金ノエル", out)
        self.assertEqual(out.count("白銀ノエル | JP"), 1)   # the header printed before the read, once
        self.assertIn("unpacking it again", err)
        self.assertEqual(digest.read_bytes(), original)
        card = root / "people" / "sakura_miko" / "card.md"
        self.same_size_change(card, "さくらみこ", "さくらみそ")
        code, out, err = run([LOOKUP, "さくらみこ"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertNotIn("さくらみそ", out)

    def test_another_cache_is_checked_against_its_own_manifest(self):
        cache_dir, root = self.fresh()
        other = cache_dir / "other cache"
        names = ["catalog.json", "names.json"] + sorted(
            path.relative_to(root).as_posix() for path in (root / "people" / "shirogane_noel").rglob("*") if path.is_file())
        lines = []
        for name in names:
            target = other.joinpath(*name.split("/"))
            target.parent.mkdir(parents=True, exist_ok=True)
            data = (root / name).read_bytes()
            private_file(target, data)
            lines.append(hashlib.sha256(data).hexdigest() + "  " + name)
        private_file(other / "MANIFEST.sha256", "\n".join(lines) + "\n")
        argv = [WRAPPER, "--cache", other, "show", "白銀ノエル", "--digest"]
        code, out, err = run(argv, cache_dir)
        self.assertEqual(code, 0, err)
        self.assertIn("白銀ノエル | JP", out)
        self.assertIn("MANIFEST.sha256 と照合します", err)
        self.same_size_change(other / "people" / "shirogane_noel" / "digest.md", "白銀ノエル", "黒金ノエル")
        code, out, err = run(argv, cache_dir)
        self.assertEqual(code, 1)
        self.assertNotIn("黒金ノエル", out)
        self.assertIn("--cache のキャッシュのファイルが", err)
        self.assertNotIn("unpacking it again", err)          # not the skill's copy: nothing to unpack
        (other / "MANIFEST.sha256").unlink()
        code, out, err = run(argv, cache_dir)
        self.assertEqual((code, out), (1, ""))
        self.assertIn("MANIFEST.sha256 がありません", err)

    def test_manifest_changed_with_the_receipt_is_not_trusted(self):
        cache_dir, root = self.fresh()
        page = root / "people" / "houshou_marine" / "pages" / "main.txt"
        data = page.read_bytes()
        changed = data.replace("宝鐘マリン".encode(), "改変マリン".encode(), 1)
        private_file(page, changed)
        manifest = root / "MANIFEST.sha256"
        lines = manifest.read_text(encoding="utf-8").splitlines()
        new_digest = hashlib.sha256(changed).hexdigest()
        lines = [new_digest + "  " + line.split("  ", 1)[1] if line.endswith("  people/houshou_marine/pages/main.txt")
                 else line for line in lines]
        private_file(manifest, "\n".join(lines) + "\n")
        receipt = root.parent / ".wrapper-receipt.json"
        record = json.loads(receipt.read_text(encoding="utf-8"))
        record["manifest_sha256"] = hashlib.sha256(manifest.read_bytes()).hexdigest()
        private_file(receipt, json.dumps(record))
        self.assertFalse(wrapper._complete(root))        # MANIFEST_SHA256 comes with the skill
        code, out, err = run([WRAPPER, "read", "宝鐘マリン", "main", "--find", "改変マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertIn("matches: 0", out)                 # read from the copy unpacked again
        self.assertEqual(page.read_bytes(), data)

    def test_a_receipt_nested_too_deep_or_too_large_is_damage(self):
        # 2026-10-02: a receipt replaced by [[[[...]]]] 10,000 deep ended show, --status and the lookup card in
        # a RecursionError traceback instead of unpacking the copy again.
        cache_dir, root = self.fresh()
        receipt = root.parent / ".wrapper-receipt.json"
        for data in (b"[" * 10000 + b"]" * 10000, b'{"a":' * 10000 + b"1" + b"}" * 10000):
            private_file(receipt, data)
            self.assertFalse(wrapper._complete(root))
        for data in (b"[" * 10000 + b"]" * 10000, b" " * (wrapper.RECORD_LIMIT + 1)):
            with self.subTest(size=len(data)):
                private_file(receipt, data)
                code, out, err = run([WRAPPER, "--status"], cache_dir)
                self.assertEqual((code, "Traceback" in err), (0, False), err)
                self.assertFalse(json.loads(out)["candidates"][0]["complete"])
                code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
                self.assertEqual((code, "Traceback" in err), (0, False), err)
                self.assertTrue(out.startswith("宝鐘マリン | JP"))
                self.assertTrue(wrapper._complete(root))         # unpacked again, with a new receipt
                private_file(receipt, data)
                code, out, err = run([LOOKUP, "宝鐘マリン"], cache_dir)
                self.assertEqual((code, "Traceback" in err), (0, False), err)
                self.assertTrue(wrapper._complete(root))
        manifest = root / "MANIFEST.sha256"
        private_file(manifest, b"0" * (wrapper.RECORD_LIMIT + 1))
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue(wrapper._complete(root))

    def test_bytecode_in_the_cache_is_never_run(self):
        cache_dir, root = self.fresh()
        import importlib._bootstrap_external as external
        source = root / "hololive_cache_core.py"
        info = os.stat(source)
        code = compile(source.read_text(encoding="utf-8") + "\nprint('TAMPERED BYTECODE RAN')\n", str(source), "exec")
        # Plant bytecode inside this cache, regardless of the test runner's
        # optional external bytecode prefix. The plain-import probe must use
        # that same location; wrapper runs keep the inherited environment.
        with mock.patch.object(sys, "pycache_prefix", None):
            pyc = Path(importlib.util.cache_from_source(str(source)))
        probe_env = dict(os.environ)
        probe_env.pop("PYTHONPYCACHEPREFIX", None)
        pyc.parent.mkdir(mode=0o700, exist_ok=True)
        private_file(pyc, external._code_to_timestamp_pyc(code, info.st_mtime, info.st_size))
        probe = subprocess.run([sys.executable, "-c",
                                "import sys; sys.path.insert(0, sys.argv[1]); import hololive_cache_core", str(root)], cwd=str(root),
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=probe_env)
        self.assertIn(b"TAMPERED", probe.stdout)            # a plain import would run it
        self.assertTrue(wrapper._complete(root))            # bytecode is allowed in the folder ...
        for argv in ([WRAPPER, "show", "宝鐘マリン"], [WRAPPER, "story", "宝鐘マリン"]):
            code, out, err = run(argv, cache_dir)
            self.assertEqual(code, 0, err)
            self.assertNotIn("TAMPERED", out + err)          # ... but the wrapper never runs it
        direct = subprocess.run([sys.executable, str(root / "hololive_cache.py"), "verify"], cwd=str(root),
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=probe_env)
        self.assertNotIn(b"TAMPERED", direct.stdout)       # verify runs from the source it checks
        report = json.loads(direct.stdout.decode("utf-8"))
        self.assertEqual((direct.returncode, report["ok"], report["bytecode_files"]), (0, True, 1))
        self.assertIn("bytecode_note", report)

    def test_whole_folder_removed_or_strays_added_are_repaired(self):
        cache_dir, root = self.fresh()
        shutil.rmtree(root / "people" / "houshou_marine")
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertTrue(wrapper._complete(root))
        for stray in (root / "people" / "stray.txt", root / "stray folder" / "note.txt", root / "stray folder 2"):
            with self.subTest(stray=stray.name):
                if stray.suffix:
                    stray.parent.mkdir(exist_ok=True)
                    private_file(stray, "not in the manifest")
                else:
                    stray.mkdir()
                self.assertFalse(wrapper._complete(root))
                code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
                self.assertEqual(code, 0, err)
                self.assertFalse(stray.exists())
        pycache = root / "__pycache__"                        # bytecode written by the runs is allowed
        pycache.mkdir(mode=0o700, exist_ok=True)
        private_file(pycache / "extra.cpython-39.pyc.12345", b"")   # Python's temporary name while writing
        self.assertTrue(wrapper._complete(root))

    def test_concurrent_initializers_share_one_complete_copy(self):
        with tempfile.TemporaryDirectory() as td:
            cache_dir = Path(td) / "new cache directory"
            env = dict(os.environ, HOLOLIVE_WIKI_CACHE_DIR=str(cache_dir))
            commands = [subprocess.Popen([sys.executable, str(WRAPPER), "--cache-root"],
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
                        for _ in range(6)]
            outputs = []
            for command in commands:
                out, err = command.communicate(timeout=60)
                self.assertEqual(command.returncode, 0, err.decode("utf-8", "replace"))
                outputs.append(out.decode("utf-8").strip())
            self.assertEqual(len(set(outputs)), 1)
            self.assertTrue(wrapper._complete(Path(outputs[0])))
            self.assertEqual(sorted(p.name for p in cache_dir.iterdir()),
                             sorted([wrapper.FOLDER, wrapper.FOLDER + ".lock"]))

    @unittest.skipUnless(os.name == "posix", "symlink and permission checks are POSIX")
    def test_nested_symlink_and_writable_source_are_repaired(self):
        cache_dir, root = self.fresh()
        core = root / "hololive_cache_core.py"
        os.chmod(core, 0o666)
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        page = next((root / "people" / "houshou_marine" / "pages").glob("*.txt"))
        external = cache_dir / "external-page"
        external.write_bytes(page.read_bytes())
        page.unlink()
        page.symlink_to(external)
        self.assertFalse(wrapper._complete(root))
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 0, err)
        self.assertFalse(page.is_symlink())

    @unittest.skipUnless(os.name == "posix", "folder permissions are POSIX")
    def test_untrusted_directory_planted_during_extraction_is_refused(self):
        with tempfile.TemporaryDirectory() as td:
            dest = Path(td) / wrapper.FOLDER
            code = b"def run_cli(): return 0\n"
            manifest = hashlib.sha256(code).hexdigest() + "  hololive_cache_core.py\n"
            def plant(staging):
                root = staging / wrapper.ROOT_NAME
                private_folder(root)
                private_file(root / "hololive_cache_core.py", code)
                private_file(root / "MANIFEST.sha256", manifest)
                dest.mkdir(mode=0o777)
                os.chmod(dest, 0o777)
            with mock.patch.object(wrapper, "_archive_ok", return_value=True), \
                    mock.patch.object(wrapper, "_extract", side_effect=plant), \
                    mock.patch.object(wrapper, "_verify"), \
                    mock.patch.object(wrapper, "MANIFEST_SHA256", hashlib.sha256(manifest.encode()).hexdigest()):
                with self.assertRaisesRegex(ValueError, "writable by others; not used"):
                    wrapper._unpack(dest)
            self.assertTrue(dest.exists())
            self.assertFalse(any("staging-" in p.name for p in Path(td).iterdir()))

    @unittest.skipUnless(os.name == "posix", "folder permissions are POSIX")
    def test_non_sticky_writable_cache_ancestor_is_refused(self):
        with tempfile.TemporaryDirectory() as td:
            unsafe = Path(td) / "unsafe"
            unsafe.mkdir(mode=0o777)
            os.chmod(unsafe, 0o777)
            code, out, err = run([WRAPPER, "--cache-root"], unsafe / "child")
            self.assertEqual(code, 1)
            self.assertIn("unsafe cache ancestor", err)

    def test_other_versions_are_removed_once_this_one_is_unpacked(self):
        # Until 2026-10-07 every update left the unpacked copy of the version before it (about 300 MB) behind.
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            own = wrapper.PREFIX + wrapper._user_key() + "-"
            self.assertEqual(wrapper.FOLDER, own + wrapper.ARCHIVE_SHA256[:16])
            removed = [base / (own + "0" * 16), base / (own + "0123456789abcdef"), base / (own + "0" * 16 + ".lock"),
                       base / (own + "1" * 16 + ".lock"),            # a lock folder whose version is already gone
                       base / (wrapper.PREFIX + "staging-abandoned")]
            kept = {base / (wrapper.PREFIX + "00000000-" + "0" * 16): "another user's copy",
                    base / (own + "0" * 15): "not a version name", base / (own + "0" * 16 + ".old"): "not a version name",
                    base / (own + "g" * 16): "not a version name",
                    base / (wrapper.PREFIX + "staging-recent"): "a staging folder that may be in use",
                    base / "unrelated": "not a folder of the skill"}
            for folder in removed + list(kept):
                private_folder(folder)
            for folder in removed[:2]:
                private_folder(folder / wrapper.ROOT_NAME)
                page = folder / wrapper.ROOT_NAME / "page.txt"
                private_file(page, "old text")
                os.chmod(page, stat.S_IREAD)                       # read-only: on Windows a file attribute
            private_file(removed[2] / "install.lock", b"")
            os.utime(removed[4], (1, 1))
            if os.name == "posix":
                shared = base / (own + "2" * 16)
                shared.mkdir()
                os.chmod(shared, 0o777)
                kept[shared] = "a folder others can write to"
                target = base / "target"
                private_folder(target)
                private_file(target / "keep.txt", "keep")
                link = base / (own + "3" * 16)
                link.symlink_to(target, target_is_directory=True)
                kept[link] = "a link"
            report = json.loads(run([WRAPPER, "--status"], base)[1])
            self.assertEqual(report["candidates"][0]["other_versions"], [removed[0].name, removed[1].name])
            code, out, err = run([WRAPPER, "--cache-root"], base)
            self.assertEqual(code, 0, err)
            self.assertTrue(wrapper._complete(Path(out.strip())))
            for folder in removed:
                self.assertFalse(os.path.lexists(folder), folder.name)
            for folder, why in kept.items():
                self.assertTrue(os.path.lexists(folder), why)
            if os.name == "posix":
                self.assertEqual((target / "keep.txt").read_text(encoding="utf-8"), "keep")
            names = {path.name for path in base.iterdir()}
            self.assertTrue({wrapper.FOLDER, wrapper.FOLDER + ".lock"} <= names)
            self.assertFalse([name for name in names if name.startswith(wrapper.PREFIX + "stale-")])
            # Reusing the complete copy removes nothing; unpacking again (--repair) does.
            private_folder(removed[0])
            self.assertEqual(run([WRAPPER, "--cache-root"], base)[0], 0)
            self.assertTrue(removed[0].exists())
            report = json.loads(run([WRAPPER, "--status"], base)[1])
            self.assertEqual(report["candidates"][0]["other_versions"], [removed[0].name])
            self.assertEqual(run([WRAPPER, "--repair"], base)[0], 0)
            self.assertFalse(removed[0].exists())
            self.assertEqual(json.loads(run([WRAPPER, "--status"], base)[1])["candidates"][0]["other_versions"], [])

    def test_a_version_folder_that_cannot_be_moved_is_left_for_later(self):
        # Windows refuses to rename a folder while a file in it is open: that version stays, nothing fails.
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            old = base / (wrapper.OWN + "0" * 16)
            private_folder(old)
            private_file(old / "page.txt", "old text")
            private_folder(base / (old.name + ".lock"))
            real_rename = os.rename

            def held_open(source, target):
                if Path(source) == old:
                    raise PermissionError("simulated: a file in the folder is open on Windows")
                return real_rename(source, target)
            with mock.patch.object(wrapper.os, "rename", side_effect=held_open):
                wrapper._tidy(str(base), wrapper.FOLDER)
            self.assertEqual((old / "page.txt").read_text(encoding="utf-8"), "old text")
            self.assertTrue((base / (old.name + ".lock")).is_dir())    # kept while its version is
            self.assertEqual(sorted(path.name for path in base.iterdir()), [old.name, old.name + ".lock"])
            wrapper._tidy(str(base), wrapper.FOLDER)                    # the next unpacking
            self.assertEqual(list(base.iterdir()), [])

    def test_folders_without_permissions_do_not_stop_the_removal(self):
        # A retry used to call os.open again without its flags (rmtree reports a folder it cannot open that way):
        # the TypeError ended the command after the new version was in place. A user gets the refusal on POSIX;
        # for root, who is never refused, it is simulated.
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            old = base / (wrapper.OWN + "0" * 16)
            for folder in (old, old / "closed", old / "closed" / "inner", old / "read-only"):
                private_folder(folder)
            private_file(old / "closed" / "inner" / "page.txt", "old text")
            private_file(old / "read-only" / "page.txt", "old text")
            os.chmod(old / "closed", 0)
            os.chmod(old / "read-only", stat.S_IREAD | stat.S_IEXEC)     # on Windows a folder attribute
            real_open = os.open

            def as_a_user(path, flags, mode=0o777, *, dir_fd=None):
                info = os.stat(path, dir_fd=dir_fd, follow_symlinks=False)
                if stat.S_ISDIR(info.st_mode) and not info.st_mode & stat.S_IRUSR:
                    raise PermissionError(13, "Permission denied", path)
                return real_open(path, flags, mode, dir_fd=dir_fd)
            with mock.patch.object(wrapper.os, "open", side_effect=as_a_user):
                wrapper._tidy(str(base), wrapper.FOLDER)
            self.assertEqual(list(base.iterdir()), [])

    def test_a_lock_folder_held_by_an_installer_is_left(self):
        # An installer of that version holds the lock (its version folder is not there yet): removing the
        # folder would let a second installer lock a new file and unpack alongside it.
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            lock_folder = base / (wrapper.OWN + "0" * 16 + ".lock")
            private_folder(lock_folder)
            private_file(lock_folder / "install.lock", b"")
            descriptor = os.open(lock_folder / "install.lock", os.O_RDWR)
            try:
                release = wrapper._lock(descriptor)
                wrapper._tidy(str(base), wrapper.FOLDER)
                self.assertTrue((lock_folder / "install.lock").is_file())
                release()
            finally:
                os.close(descriptor)
            wrapper._tidy(str(base), wrapper.FOLDER)                    # the next unpacking, once released
            self.assertEqual(list(base.iterdir()), [])

    @unittest.skipUnless(os.name == "posix", "Windows does not remove a file another process has open")
    def test_an_installer_takes_the_lock_again_when_its_file_was_removed(self):
        # Another version's unpacking removed the lock folder after this installer opened the file: the lock
        # it then gets is on a removed file, so it takes the one at the path.
        with tempfile.TemporaryDirectory() as td:
            dest = Path(td) / (wrapper.OWN + "0" * 16)
            lock_file = dest.with_name(dest.name + ".lock") / "install.lock"
            real_lock, calls = wrapper._lock, []

            def removed_meanwhile(descriptor):
                if not calls:
                    shutil.rmtree(lock_file.parent)
                calls.append(descriptor)
                return real_lock(descriptor)
            with mock.patch.object(wrapper, "_lock", side_effect=removed_meanwhile):
                with wrapper._InstallationLock(dest) as held:
                    self.assertTrue(wrapper._same_file(held.descriptor, lock_file))
            self.assertEqual(len(calls), 2)

    @unittest.skipUnless(os.name == "posix", "umask is POSIX")
    def test_permissive_umask_does_not_make_reused_code_writable(self):
        with tempfile.TemporaryDirectory() as td:
            env = dict(os.environ, HOLOLIVE_WIKI_CACHE_DIR=td)
            command = subprocess.run([sys.executable, str(WRAPPER), "story", "宝鐘マリン", "兎田ぺこら"],
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, umask=0o002)
            self.assertEqual(command.returncode, 0, command.stderr.decode("utf-8", "replace"))
            self.assertTrue(wrapper._complete(Path(td) / wrapper.FOLDER / wrapper.ROOT_NAME))

    def test_failed_publication_restores_or_preserves_previous_copy(self):
        for fail_restore in (False, True):
            with self.subTest(fail_restore=fail_restore), tempfile.TemporaryDirectory() as td:
                dest = Path(td) / wrapper.FOLDER
                old = dest / wrapper.ROOT_NAME
                private_folder(dest)
                private_folder(old)
                private_file(old / "previous-copy", "preserve me")
                code = b"def run_cli(): return 0\n"
                manifest = hashlib.sha256(code).hexdigest() + "  hololive_cache_core.py\n"
                def extract(staging):
                    root = staging / wrapper.ROOT_NAME
                    private_folder(root)
                    private_file(root / "hololive_cache_core.py", code)
                    private_file(root / "MANIFEST.sha256", manifest)
                real_rename = os.rename
                def fail_publication(source, target):
                    if Path(target) == dest and (Path(source).name != "old" or fail_restore):
                        raise PermissionError("simulated Windows file handle blocks publication")
                    return real_rename(source, target)
                with mock.patch.object(wrapper, "_archive_ok", return_value=True), \
                        mock.patch.object(wrapper, "_extract", side_effect=extract), \
                        mock.patch.object(wrapper, "_verify"), \
                        mock.patch.object(wrapper, "MANIFEST_SHA256", hashlib.sha256(manifest.encode()).hexdigest()), \
                        mock.patch.object(wrapper.os, "rename", side_effect=fail_publication):
                    with self.assertRaises(PermissionError):
                        wrapper._unpack(dest, repair=True)
                copies = list(Path(td).rglob("previous-copy"))
                self.assertEqual(len(copies), 1)
                self.assertEqual(copies[0].read_text(encoding="utf-8"), "preserve me")
                if not fail_restore:
                    self.assertEqual(copies[0], old / "previous-copy")

    @unittest.skipUnless(os.name == "posix", "folder ownership and mode bits are POSIX")
    def test_a_folder_others_can_write_is_refused(self):
        cache_dir, root = self.fresh()
        os.chmod(root.parent, 0o777)
        (root / "hololive_cache_core.py").write_text("raise SystemExit('planted code ran')\n", encoding="utf-8")
        code, out, err = run([WRAPPER, "show", "宝鐘マリン"], cache_dir)
        self.assertEqual(code, 1)
        self.assertIn("writable by others; not used", err)
        self.assertNotIn("planted code ran", out + err)


def fake_folder(uid, mode, gid=0):
    return os.stat_result((stat.S_IFDIR | mode, 1, 1, 2, uid, gid, 4096, 0, 0, 0))


@unittest.skipUnless(os.name == "posix", "ownership, umask and user namespaces are POSIX")
class LocationTests(unittest.TestCase):
    def test_overflow_owner_is_trusted_only_inside_a_user_namespace(self):
        # bubblewrap/unshare show root's / and /tmp as owned by the overflow uid (65534).
        root_like, tmp_like = fake_folder(65534, 0o755), fake_folder(65534, 0o1777)
        with mock.patch.object(wrapper, "_overflow_uid", return_value=65534):
            self.assertIsNone(wrapper._unsafe_ancestor(root_like))
            self.assertIsNone(wrapper._unsafe_ancestor(tmp_like))
            self.assertIn("without the sticky bit", wrapper._unsafe_ancestor(fake_folder(65534, 0o777)))
        with mock.patch.object(wrapper, "_overflow_uid", return_value=None):
            self.assertIn("another user", wrapper._unsafe_ancestor(root_like))
        other = os.getuid() + 1 if os.getuid() + 1 != 65534 else os.getuid() + 2
        with mock.patch.object(wrapper, "_overflow_uid", return_value=65534):
            self.assertIn("another user", wrapper._unsafe_ancestor(fake_folder(other, 0o755)))

    def test_group_writable_folder_needs_a_group_of_this_user_alone(self):
        with tempfile.TemporaryDirectory() as td:
            shared = Path(td) / "group writable"
            shared.mkdir()
            os.chmod(shared, 0o775)
            with mock.patch.object(wrapper, "_group_of_this_user_alone", return_value=True):
                self.assertEqual(wrapper._safe_base(shared / "cache"), os.path.realpath(shared / "cache"))
            with mock.patch.object(wrapper, "_group_of_this_user_alone", return_value=False):
                with self.assertRaisesRegex(ValueError, "which has other members"):
                    wrapper._safe_base(shared / "cache")
            os.chmod(shared, 0o1777)                        # sticky: like /tmp
            with mock.patch.object(wrapper, "_group_of_this_user_alone", return_value=False):
                wrapper._safe_base(shared / "cache")

    def test_umask_002_creates_private_folders_and_keeps_working(self):
        with tempfile.TemporaryDirectory() as td:
            temp = Path(td) / "tmp"
            private_folder(temp)
            (temp / wrapper.FOLDER).symlink_to(td)          # the temp copy is unusable: fall back to XDG
            xdg = Path(td) / "xdg" / "nested"
            env = {key: value for key, value in os.environ.items() if key != "HOLOLIVE_WIKI_CACHE_DIR"}
            env.update(TMPDIR=str(temp), XDG_CACHE_HOME=str(xdg))
            roots = []
            for _ in range(3):
                command = subprocess.run([sys.executable, str(WRAPPER), "show", "宝鐘マリン"], stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, env=env, umask=0o002)
                self.assertEqual(command.returncode, 0, command.stderr.decode("utf-8", "replace"))
                self.assertTrue(command.stdout.decode("utf-8").startswith("宝鐘マリン | JP"))
                roots.append(subprocess.run([sys.executable, str(WRAPPER), "--cache-root"], stdout=subprocess.PIPE,
                                            env=env, umask=0o002).stdout.decode("utf-8").strip())
            self.assertEqual(len(set(roots)), 1)
            self.assertTrue(roots[0].startswith(os.path.realpath(xdg / "hololive-wiki") + os.sep), roots[0])
            for folder in (xdg.parent, xdg, xdg / "hololive-wiki"):
                self.assertEqual(stat.S_IMODE(os.stat(folder).st_mode), 0o700, folder)

    def test_umask_002_override_folder_of_this_user(self):
        with tempfile.TemporaryDirectory() as td:
            asked = Path(td) / "made with umask 002"
            asked.mkdir()
            os.chmod(asked, 0o775)
            code, out, err = run([WRAPPER, "--cache-root"], asked)
            if wrapper._group_of_this_user_alone(os.stat(asked).st_gid):
                self.assertEqual(code, 0, err)
            else:                                            # a shared group: refused, with the way out
                self.assertEqual(code, 1)
                self.assertIn("which has other members", err)
                self.assertIn("HOLOLIVE_WIKI_CACHE_DIR", err)

    def test_user_namespace_sandbox(self):
        """/ and /tmp owned by the overflow uid (bubblewrap, unshare): the wrapper still works."""
        probe = None
        for prefix in (["unshare", "--user", "--map-current-user"], ["unshare", "--user", "--map-root-user"],
                       ["bwrap", "--unshare-user", "--dev-bind", "/", "/"]):
            if shutil.which(prefix[0]) and subprocess.run(prefix + ["true"], stdout=subprocess.DEVNULL,
                                                          stderr=subprocess.DEVNULL).returncode == 0:
                probe = prefix
                break
        if probe is None:
            self.skipTest("no unprivileged user namespaces here (unshare/bwrap)")
        with tempfile.TemporaryDirectory() as td:
            env = {key: value for key, value in os.environ.items() if key != "HOLOLIVE_WIKI_CACHE_DIR"}
            for extra in ({"HOLOLIVE_WIKI_CACHE_DIR": str(Path(td) / "asked")}, {"TMPDIR": td}):
                with self.subTest(extra=sorted(extra)):
                    command = subprocess.run(probe + [sys.executable, str(WRAPPER), "show", "宝鐘マリン"],
                                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=dict(env, **extra))
                    self.assertEqual(command.returncode, 0, command.stderr.decode("utf-8", "replace"))
                    self.assertTrue(command.stdout.decode("utf-8").startswith("宝鐘マリン | JP"))


if __name__ == "__main__":
    unittest.main()
