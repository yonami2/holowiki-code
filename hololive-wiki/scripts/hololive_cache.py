#!/usr/bin/env python3
"""Skill entry for the v3 person cache: verify the archive once, unpack it privately, run a command.

    python3 scripts/hololive_cache.py <command> [...]   (Windows: python or py -3)
    python3 scripts/hololive_cache.py --cache-root      print the unpacked folder
    python3 scripts/hololive_cache.py --status          JSON: location and state of the unpacked copy
    python3 scripts/hololive_cache.py --repair          unpack again, then exit

First use: the archive's SHA-256 is checked; each member is validated as it is
unpacked (xz, with the standard lzma module) into a private staging folder;
the unpacked MANIFEST.sha256 is verified in a separate process; a receipt of
the verified folders and sizes is written; the folder is then moved into place
in one rename. Later uses check that MANIFEST.sha256 is the one this skill
ships (MANIFEST_SHA256), compare one directory scan with the receipt (every
listed file present, a regular file of this user with its verified size,
nothing unlisted except bytecode) and hash the code files (.py, .cmd) against
the manifest. Missing or damaged copies are unpacked again. Run explicit
--repair while other cache commands are idle; installation is serialized, but
running readers are not.

Each version of the archive has its own folder (hololive-wiki-v3-<user>-<first
16 hex digits of the archive's SHA-256>). Once a version is unpacked (first use
after an update, or --repair), the folders of this user's other versions in the
same location are removed with their lock folders: each is renamed aside first,
so a command of that version still running finds no copy, rather than a
half-deleted one, and unpacks its own again. A lock folder stays while an
installer of its version holds the lock in it. A folder Windows will not release
(a file held open) is removed at the next unpacking. Staging folders abandoned
for a day are removed as well. --status lists the other versions present.

The cache command runs in this process, from source bytes that match the
manifest: the modules are compiled here and bytecode in __pycache__ is never
run. Every file the command then reads is hashed and compared with the
manifest; a difference (a file changed after unpacking, even to the same size)
unpacks the cache again and reruns the command when it has printed nothing yet.
`verify` hashes every file at once. Another cache named with --cache DIR is
checked against DIR/MANIFEST.sha256 (required): that manifest does not come with
the skill, so a change made together with it goes unnoticed, and a difference is
an error rather than a reason to unpack. os.execv is not used: on Windows it does
not quote arguments with spaces, and it returns (with exit code 0) before the
command has finished. The modules needed only to unpack (tarfile, tempfile,
subprocess...) are imported only then.

Location: $HOLOLIVE_WIKI_CACHE_DIR when set, else the system temp folder, else
(POSIX) the per-user cache folder ~/.cache/hololive-wiki. On POSIX a location
is used only when no other user can replace entries on its path: every folder
from / down belongs to root or this user (in a user-namespace sandbox such as
bubblewrap, also to the overflow owner that stands for unmapped host accounts),
and one that others may write to has the sticky bit or a group of this user
alone (a user private group under umask 002). Missing folders are created
private (0700) whatever the umask.

Python 3.9+, standard library only.
"""

import hashlib
import json
import os
import stat
import sys


ARCHIVE = os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(__file__))),
                       "cache", "hololive_wiki_person_cache.tar.xz")
ARCHIVE_SHA256 = "654f3d296b5c1c9e8acb4ebd7dab041b0f107a4393ffd8da530d1ce254aeec95"
# The unpacked MANIFEST.sha256 of this archive: files are checked against it, not against anything
# stored beside them.
MANIFEST_SHA256 = "6f0ec47d2539518ad63b41009df794b7c63a6ebdc15b29f17cd64778140b2440"
ROOT_NAME = "hololive_wiki_person_cache"
PREFIX = "hololive-wiki-v3-"
OVERRIDE = "HOLOLIVE_WIKI_CACHE_DIR"
RECEIPT = ".wrapper-receipt.json"
RECEIPT_SCHEMA = 3
# Bytes. The receipt (about 110 KB) and the unpacked MANIFEST.sha256 (about 500 KB) are read whole; a larger file
# there is damage, not something to load into memory.
RECORD_LIMIT = 16 * 1024 * 1024
CODE_SUFFIXES = (".py", ".cmd")             # imported or executed: hashed on every use
REPARSE_POINT = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
POSIX = os.name == "posix"
USAGE = """usage: hololive_cache.py COMMAND [...] | --cache-root | --status | --repair

Commands (run `hololive_cache.py COMMAND --help` for each):
  list  show  scene  story  status  profile  pages  read  find  search
  nicknames  sources  tables  footnotes  check-updates  verify

  story NAME [NAME ...] [--topic WORD]  material pack for fiction about a cast
  show NAME / scene NAME NAME           summary cards / how each calls the others
  read NAME PAGE [--find WORD] [--section HEADING] [--all]
"""


def _user_key():
    if hasattr(os, "getuid"):
        return hashlib.sha256(("uid-%d" % os.getuid()).encode()).hexdigest()[:8]
    import getpass
    try:
        name = getpass.getuser()
    except (OSError, KeyError, ImportError):
        name = "user"
    return hashlib.sha256(name.encode("utf-8", "replace")).hexdigest()[:8]


OWN = PREFIX + _user_key() + "-"             # this user's copies: OWN + 16 hex digits of the archive's SHA-256
FOLDER = OWN + ARCHIVE_SHA256[:16]


def _likely_temp():
    """tempfile.gettempdir()'s usual answer (its first candidate), without importing tempfile."""
    for name in ("TMPDIR", "TEMP", "TMP"):
        if os.environ.get(name):
            return os.path.abspath(os.environ[name])
    return "/tmp" if POSIX else None


def _bases():
    """Folders that may hold the unpacked copy, in order of preference."""
    override = os.environ.get(OVERRIDE)
    if override:
        return [override]
    import tempfile
    bases = [tempfile.gettempdir()]
    if POSIX:
        cache_home = os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
        bases.append(os.path.join(cache_home, "hololive-wiki"))
    return bases


# --- ownership and permissions ------------------------------------------------------

def _owned(info):
    """This user's entry that no one else can write to (off POSIX: anything but a link or junction)."""
    if POSIX:
        return info.st_uid == os.getuid() and not info.st_mode & 0o022
    return not getattr(info, "st_file_attributes", 0) & REPARSE_POINT


def _private(path):
    """A real folder of this user that others cannot write to."""
    try:
        info = os.lstat(path)
    except OSError:
        return False
    return stat.S_ISDIR(info.st_mode) and _owned(info)


def _file_info(path):
    info = os.lstat(path)
    if not stat.S_ISREG(info.st_mode) or not _owned(info):
        raise ValueError(f"not a regular cache file of this user, or writable by others: {path}")
    return info


_OVERFLOW = []


def _overflow_uid():
    """In a user namespace (bubblewrap, unshare, rootless containers), the owner shown for unmapped host users."""
    if not _OVERFLOW:
        uid = None
        try:
            with open("/proc/self/uid_map", encoding="ascii") as stream:
                identity = stream.read().split() == ["0", "0", "4294967295"]
            if not identity:
                uid = 65534
                with open("/proc/sys/kernel/overflowuid", encoding="ascii") as stream:
                    uid = int(stream.read())
        except (OSError, ValueError):
            pass
        _OVERFLOW.append(uid)
    return _OVERFLOW[0]


def _group_of_this_user_alone(gid):
    """No account but root and this user belongs to the group (e.g. a user private group under umask 002)."""
    import grp
    import pwd
    trusted = (0, os.getuid())
    try:
        group = grp.getgrgid(gid)
        if any(pwd.getpwnam(name).pw_uid not in trusted for name in group.gr_mem):
            return False
        return all(user.pw_uid in trusted for user in pwd.getpwall() if user.pw_gid == gid)
    except (KeyError, OSError):
        return False


def _unsafe_ancestor(info):
    """Why another user could replace entries in this folder, or None."""
    if not stat.S_ISDIR(info.st_mode):
        return "not a folder"
    if info.st_uid not in (0, os.getuid()) and info.st_uid != _overflow_uid():
        return f"owned by another user (uid {info.st_uid})"
    if info.st_mode & stat.S_ISVTX:
        return None                        # sticky: others cannot rename or remove what they do not own
    if info.st_mode & stat.S_IWOTH:
        return "writable by all users without the sticky bit"
    if info.st_mode & stat.S_IWGRP and not _group_of_this_user_alone(info.st_gid):
        return f"writable by group {info.st_gid}, which has other members"
    return None


def _check_ancestors(base):
    path = base
    while True:
        try:
            reason = _unsafe_ancestor(os.stat(path))
        except FileNotFoundError:
            reason = None
        if reason:
            raise ValueError(f"{path}: unsafe cache ancestor ({reason}); "
                             f"set {OVERRIDE} to a folder of your own, e.g. ~/.cache/hololive-wiki")
        parent = os.path.dirname(path)
        if parent == path:
            return
        path = parent


def _safe_base(base, create=True):
    """Resolve once; create missing folders as private; reject POSIX paths another user could redirect."""
    base = os.path.realpath(base)
    if POSIX:
        _check_ancestors(base)
    if not create:
        return base
    missing = []
    path = base
    while not os.path.lexists(path) and os.path.dirname(path) != path:
        missing.append(path)
        path = os.path.dirname(path)
    for path in reversed(missing):
        try:
            os.mkdir(path, 0o700)
        except FileExistsError:
            continue
        if POSIX:
            os.chmod(path, 0o700)            # mkdir's mode is reduced by the umask
    if missing and POSIX:
        _check_ancestors(base)             # a folder someone else created meanwhile is caught here
    return base


# --- the unpacked copy ----------------------------------------------------------------

def _bytecode(name):
    """A compiled module's name (or Python's temporary name while it writes one)."""
    base, _, tail = name.rpartition(".pyc")
    return bool(base) and (tail == "" or tail[:1] == "." and tail[1:].isdigit())


_DIGESTS = {}           # root folder -> {relative path: SHA-256} of a manifest that matched MANIFEST_SHA256


def _manifest_digests(root):
    """{relative path: SHA-256} from the unpacked MANIFEST.sha256, which must be this archive's."""
    digests = _DIGESTS.get(root)
    if digests is None:
        path = os.path.join(root, "MANIFEST.sha256")
        if _file_info(path).st_size > RECORD_LIMIT:
            raise ValueError("the unpacked MANIFEST.sha256 is not this archive's")
        with open(path, "rb") as stream:
            raw = stream.read()
        if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA256:
            raise ValueError("the unpacked MANIFEST.sha256 is not this archive's")
        digests = {}
        for line in raw.decode("utf-8").splitlines():
            digest, _, name = line.partition("  ")
            digests[name] = digest
        _DIGESTS[root] = digests
    return digests


def _complete(root):
    """One scan against the receipt: every folder and listed file present, sizes as verified, all entries
    this user's and not writable by others, no strays but bytecode in __pycache__; code hashes as listed
    in the manifest this skill ships."""
    try:
        root = os.fspath(root)
        folder = os.path.dirname(root)
        if not (_private(folder) and _private(root)):
            return False
        receipt_path = os.path.join(folder, RECEIPT)
        if _file_info(receipt_path).st_size > RECORD_LIMIT:
            return False
        with open(receipt_path, "rb") as stream:
            receipt = json.loads(stream.read().decode("utf-8"))
        _DIGESTS.pop(root, None)
        digests = _manifest_digests(root)
        if (receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("archive_sha256") != ARCHIVE_SHA256
                or receipt.get("manifest_sha256") != MANIFEST_SHA256):
            return False
        folders = receipt["folders"]           # {folder: {file name: size}}, "" for the root
        uid = os.getuid() if POSIX else None
        is_dir, is_file = stat.S_ISDIR, stat.S_ISREG
        visited = 0
        pending = [(root, "")]
        while pending:
            path, relative = pending.pop()
            expected = folders.get(relative)
            if expected is None:
                if relative.rpartition("/")[2] != "__pycache__":
                    return False                                    # a folder the archive does not have
            else:
                visited += 1
            found = 0
            with os.scandir(path) as listing:
                for entry in listing:
                    info = entry.stat(follow_symlinks=False)        # from the listing itself on Windows
                    if (info.st_uid != uid or info.st_mode & 0o022) if POSIX else not _owned(info):
                        return False                                # others' entries, writable, junctions
                    if is_dir(info.st_mode):
                        pending.append((entry.path, relative + "/" + entry.name if relative else entry.name))
                    elif not is_file(info.st_mode):
                        return False                                # links, devices, sockets
                    elif expected is None:
                        if not _bytecode(entry.name):
                            return False
                    else:
                        size = expected.get(entry.name)
                        if size is None:
                            if relative or entry.name != "MANIFEST.sha256":
                                return False                        # a file the manifest does not list
                        elif size != info.st_size:
                            return False                            # truncated or replaced
                        else:
                            found += 1
            if expected is not None and found != len(expected):
                return False                                        # a listed file is missing
        if visited != len(folders):
            return False                                            # a whole folder is missing
        for name, digest in digests.items():
            if name.endswith(CODE_SUFFIXES):
                with open(os.path.join(root, *name.split("/")), "rb") as stream:
                    if hashlib.sha256(stream.read()).hexdigest() != digest:
                        return False
        return True
    except (OSError, ValueError, TypeError, AttributeError, KeyError, RecursionError):
        # RecursionError: a receipt nested deeper than the JSON decoder follows ([[[[...]]]]) is damaged like any
        # other, and the copy is unpacked again; it was a traceback.
        return False


def _reuse(base):
    """The complete copy under base, or None (nothing is created or repaired here)."""
    dest = os.path.join(_safe_base(base, create=False), FOLDER)
    if _private(dest) and _complete(os.path.join(dest, ROOT_NAME)):
        return os.path.join(dest, ROOT_NAME)
    return None


def _root(repair=False):
    """Path (str) of the unpacked, complete cache folder; unpacked (again) when needed."""
    if not repair and not os.environ.get(OVERRIDE):
        likely = _likely_temp()        # the usual temp folder, checked before importing tempfile
        if likely is not None:
            try:
                found = _reuse(likely)
                if found is not None:
                    return found
            except (OSError, ValueError):
                pass
    problems = []
    for base in _bases():
        dest = os.path.join(base, FOLDER)
        try:
            base = _safe_base(base)
            dest = os.path.join(base, FOLDER)
            if os.path.lexists(dest):
                if not _private(dest):
                    problems.append(f"{dest}: owned by another user or writable by others; not used")
                    continue
                if not repair and _complete(os.path.join(dest, ROOT_NAME)):
                    return os.path.join(dest, ROOT_NAME)
            from pathlib import Path
            return str(_unpack(Path(dest), repair=repair))
        except (OSError, ValueError) as exc:
            problems.append(f"{dest}: {exc}")
            if isinstance(exc, ValueError) and "checksum" in str(exc):
                break
    raise OSError("; ".join(problems) or "no usable cache folder")


def ensure_cache(repair=False):
    """The unpacked, complete cache folder (a Path); unpacked (again) when needed."""
    from pathlib import Path
    return Path(_root(repair))


# --- unpacking (first use and repair only) ---------------------------------------------

def _manifest(root):
    from pathlib import PurePosixPath
    raw = (root / "MANIFEST.sha256").read_bytes()
    entries = {}
    for line in raw.decode("utf-8").splitlines():
        digest, separator, name = line.partition("  ")
        path = PurePosixPath(name)
        if (separator != "  " or len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest)
                or not name or path.is_absolute() or ".." in path.parts or "\\" in name
                or str(path) != name or ":" in name or name in entries):
            raise ValueError("invalid cache manifest entry")
        entries[name] = digest
    if "hololive_cache_core.py" not in entries:
        raise ValueError("cache manifest does not list its implementation")
    return raw, entries


def _write_receipt(root):
    """Record the verified manifest's digest, the folders with each listed file's size, and the code hashes."""
    raw, entries = _manifest(root)
    folders = {}
    for folder, directories, _ in os.walk(root):
        directories[:] = [name for name in directories if name != "__pycache__"]
        relative = os.path.relpath(folder, root).replace(os.sep, "/")
        folders["" if relative == "." else relative] = {}
    for name in entries:
        directory, _, file_name = name.rpartition("/")
        folders[directory][file_name] = _file_info(root / name).st_size
    if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA256:
        raise ValueError("the archive's MANIFEST.sha256 is not the one this skill expects")
    receipt = {"schema": RECEIPT_SCHEMA, "archive_sha256": ARCHIVE_SHA256,
               "manifest_sha256": MANIFEST_SHA256, "folders": folders}
    path = root.parent / RECEIPT
    path.write_text(json.dumps(receipt, separators=(",", ":")), encoding="utf-8")
    if POSIX:
        path.chmod(0o600)


def _archive_ok():
    digest = hashlib.sha256()
    with open(ARCHIVE, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest() == ARCHIVE_SHA256


def _extract(staging):
    """Validate and unpack every member in one pass over the compressed stream."""
    try:
        import lzma
    except ImportError:
        raise ValueError("this Python has no lzma module, which unpacks the cache archive (.tar.xz). "
                         "Use a Python that has it: the python.org, Microsoft Store, Homebrew and Linux "
                         "distribution builds do. Without it, scripts/hololive_cache_lookup.py still reads "
                         "the names and summaries in cache/.") from None
    import tarfile
    from pathlib import Path, PurePosixPath
    safe = hasattr(tarfile, "data_filter")
    seen = set()
    try:
        with tarfile.open(ARCHIVE, "r|xz") as archive:
            for member in archive:
                parts = PurePosixPath(member.name).parts
                if (not parts or parts[0] != ROOT_NAME or ".." in parts or Path(member.name).is_absolute()
                        or "\\" in member.name or ":" in member.name
                        or str(PurePosixPath(member.name)) != member.name.rstrip("/")
                        or member.name.startswith(("/", "\\")) or not (member.isfile() or member.isdir())
                        or member.name in seen):
                    raise ValueError("invalid cache archive member: " + member.name)
                seen.add(member.name)
                if safe:
                    archive.extract(member, staging, filter="data")
                else:
                    archive.extract(member, staging)
    except (tarfile.TarError, EOFError, lzma.LZMAError) as exc:
        raise ValueError(f"damaged cache archive: {exc}") from exc
    if not seen:
        raise ValueError("the cache archive is empty")
    if POSIX:
        # The data filter leaves directory modes to the umask; a shared-group
        # umask must not make generated cache directories writable by others.
        for folder, _, _ in os.walk(staging):
            os.chmod(folder, 0o700)


def _verify(root):
    import subprocess
    result = subprocess.run([sys.executable, "-B", str(root / "hololive_cache.py"), "verify"],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL,
                            **({"umask": 0o077} if POSIX else {}))
    try:
        report = json.loads(result.stdout.decode("utf-8"))
    except (ValueError, RecursionError):
        report = {}
    if not isinstance(report, dict):
        report = {}
    if result.returncode or not report.get("ok") or report.get("unlisted_files"):
        detail = (report.get("problems") or [])[:3] or result.stderr.decode("utf-8", "replace")[-300:]
        raise ValueError(f"v3 cache manifest verification failed: {detail}")


def _other_version(name):
    """A folder name of another version of this user's unpacked cache, or of its lock folder."""
    version = name[len(OWN):]
    if version.endswith(".lock"):
        version = version[:-len(".lock")]
    return (name.startswith(OWN) and len(version) == 16 and version != FOLDER[len(OWN):]
            and all(c in "0123456789abcdef" for c in version))


def _remove_tree(path):
    """Delete a folder of the cache. What fails is given back the owner's permissions (Windows keeps a read-only
    attribute that blocks deleting a file; a folder without them cannot be emptied), a deletion is tried again,
    and a second pass empties what the first made readable. A link or junction is never followed. What still
    cannot be removed (a file another process holds open on Windows) is left for a later attempt."""
    import shutil

    def again(function, failed, _):
        try:
            info = os.lstat(failed)
            if (getattr(info, "st_file_attributes", 0) & stat.FILE_ATTRIBUTE_REPARSE_POINT
                    or not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode))):
                return
            os.chmod(failed, stat.S_IREAD | stat.S_IWRITE | stat.S_IEXEC)
            if function in (os.unlink, os.rmdir):       # never os.open, os.close...: they take other arguments
                function(failed)
        except OSError:
            pass
    for _ in range(2):
        if sys.version_info >= (3, 12):
            shutil.rmtree(path, onexc=again)
        else:
            shutil.rmtree(path, onerror=again)
        if not os.path.lexists(path):
            return


def _tidy(base, keep):
    """Remove this user's other versions with their lock folders (see the module notes), and staging folders
    abandoned for a day. Only real folders of this user that others cannot write to are touched."""
    import tempfile
    import time
    now = time.time()
    try:
        with os.scandir(base) as listing:
            entries = sorted(listing, key=lambda entry: entry.name.endswith(".lock"))   # versions before locks
    except OSError:
        return
    for entry in entries:
        name = entry.name
        if not name.startswith(PREFIX) or name in (keep, keep + ".lock") or not _private(entry.path):
            continue
        if _other_version(name):
            if not name.endswith(".lock"):
                try:
                    aside = tempfile.mkdtemp(prefix=PREFIX + "stale-", dir=base)
                except OSError:
                    continue
                try:
                    os.rename(entry.path, os.path.join(aside, "old"))
                except OSError:
                    pass                              # held open on Windows: tried again at the next unpacking
                _remove_tree(aside)
            elif not os.path.lexists(entry.path[:-len(".lock")]):
                _remove_lock_folder(entry.path)       # only once its version is gone, and not while held
            continue
        try:
            old = now - entry.stat(follow_symlinks=False).st_mtime > 24 * 3600
        except OSError:
            continue
        if old and name.startswith((PREFIX + "staging-", PREFIX + "stale-")):
            _remove_tree(entry.path)


def _remove_lock_folder(folder):
    """Remove another version's lock folder unless an installer of that version holds its lock (the folder then
    stays for a later unpacking). On POSIX the file is removed while this process holds the lock: an installer
    that opened it before then gets the lock on a removed file, notices, and takes the one at the path
    (_InstallationLock). Windows does not remove a file that another process has open."""
    path = os.path.join(folder, "install.lock")
    try:
        descriptor = os.open(path, os.O_RDWR | getattr(os, "O_NOFOLLOW", 0))
    except FileNotFoundError:
        _remove_tree(folder)
        return
    except OSError:
        return
    try:
        release = _try_lock(descriptor)
        if release is None:
            return                                    # an installer of that version is at work
        try:
            if POSIX:
                _remove_tree(folder)
        finally:
            release()
    finally:
        os.close(descriptor)
    if not POSIX:
        _remove_tree(folder)


def _try_lock(descriptor):
    """The exclusive lock on the file if no process holds it, else None; never waits. Returns the release
    function."""
    try:
        if os.name != "nt":
            import fcntl
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return lambda: fcntl.flock(descriptor, fcntl.LOCK_UN)
        import msvcrt
        msvcrt.locking(descriptor, msvcrt.LK_NBLCK, 1)    # the byte the installers lock (see _lock)
    except OSError:
        return None

    def release():
        os.lseek(descriptor, 0, os.SEEK_SET)
        msvcrt.locking(descriptor, msvcrt.LK_UNLCK, 1)
    return release


def _same_file(descriptor, path):
    try:
        held, current = os.fstat(descriptor), os.stat(path, follow_symlinks=False)
    except OSError:
        return False
    return (held.st_dev, held.st_ino) == (current.st_dev, current.st_ino)


def _lock(descriptor):
    """Wait for an exclusive lock on the file; returns the release function. The OS drops it if the process ends."""
    if os.name != "nt":
        import fcntl
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        return lambda: fcntl.flock(descriptor, fcntl.LOCK_UN)
    import msvcrt
    try:
        import ctypes
        from ctypes import wintypes
    except ImportError:            # a Python without ctypes: poll the C runtime's byte-range lock
        return _poll_lock(descriptor, msvcrt)

    class Overlapped(ctypes.Structure):
        _fields_ = [("Internal", ctypes.c_size_t), ("InternalHigh", ctypes.c_size_t),
                    ("Offset", wintypes.DWORD), ("OffsetHigh", wintypes.DWORD), ("hEvent", wintypes.HANDLE)]

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.LockFileEx.restype = kernel32.UnlockFileEx.restype = wintypes.BOOL
    kernel32.LockFileEx.argtypes = (wintypes.HANDLE, wintypes.DWORD, wintypes.DWORD, wintypes.DWORD,
                                    wintypes.DWORD, ctypes.POINTER(Overlapped))
    kernel32.UnlockFileEx.argtypes = (wintypes.HANDLE, wintypes.DWORD, wintypes.DWORD, wintypes.DWORD,
                                      ctypes.POINTER(Overlapped))
    handle = wintypes.HANDLE(msvcrt.get_osfhandle(descriptor))
    # LOCKFILE_EXCLUSIVE_LOCK without LOCKFILE_FAIL_IMMEDIATELY waits until granted. The byte lies
    # past the end of the empty file; nothing reads the file, which a held lock would refuse.
    if not kernel32.LockFileEx(handle, 0x2, 0, 1, 0, ctypes.byref(Overlapped())):
        raise ctypes.WinError(ctypes.get_last_error())
    return lambda: kernel32.UnlockFileEx(handle, 0, 1, 0, ctypes.byref(Overlapped()))


def _poll_lock(descriptor, msvcrt):
    import errno
    import time
    while True:
        try:
            msvcrt.locking(descriptor, msvcrt.LK_NBLCK, 1)
            break
        except OSError as exc:
            if exc.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK, 0, None):
                raise
            time.sleep(0.05)

    def release():
        os.lseek(descriptor, 0, os.SEEK_SET)
        msvcrt.locking(descriptor, msvcrt.LK_UNLCK, 1)
    return release


class _InstallationLock:
    """An OS-released lock in a private folder; a crashed installer cannot leave it locked."""

    def __init__(self, dest):
        self.folder = dest.with_name(dest.name + ".lock")

    def __enter__(self):
        # Another version's unpacking may remove this folder meanwhile (_remove_lock_folder): a lock taken on a
        # removed file guards nothing, so the lock is taken again on the file at the path.
        for _ in range(10):
            try:
                os.mkdir(self.folder, 0o700)
                if POSIX:
                    os.chmod(self.folder, 0o700)
            except FileExistsError:
                pass
            if not _private(self.folder):
                raise ValueError(f"{self.folder}: unsafe cache lock folder")
            path = self.folder / "install.lock"
            try:
                self.descriptor = os.open(path, os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0), 0o600)
            except FileNotFoundError:
                continue                                  # the folder went between mkdir and open
            try:
                _file_info(path)
                self.release = _lock(self.descriptor)
            except FileNotFoundError:
                os.close(self.descriptor)
                continue
            except BaseException:
                os.close(self.descriptor)
                raise
            if not POSIX or _same_file(self.descriptor, path):
                return self
            self.release()
            os.close(self.descriptor)
        raise ValueError(f"{self.folder}: the cache lock folder kept being removed; run the command again")

    def __exit__(self, *exc_info):
        try:
            self.release()
        finally:
            os.close(self.descriptor)


def _unpack(dest, repair=False):
    with _InstallationLock(dest):
        if os.path.lexists(dest):
            if not _private(dest):
                raise ValueError(f"{dest}: owned by another user or writable by others; not used")
            if not repair and _complete(dest / ROOT_NAME):
                return dest / ROOT_NAME
        return _unpack_locked(dest)


def _unpack_locked(dest):
    import shutil
    import tempfile
    from pathlib import Path
    if not _archive_ok():
        raise ValueError("v3 cache archive checksum mismatch: " + ARCHIVE)
    staging = Path(tempfile.mkdtemp(prefix=PREFIX + "staging-", dir=dest.parent))
    stale = None
    keep_stale = False
    root = dest / ROOT_NAME
    try:
        _extract(staging)
        _verify(staging / ROOT_NAME)
        _write_receipt(staging / ROOT_NAME)
        if os.path.lexists(dest):
            if not _private(dest):
                raise ValueError(f"{dest}: owned by another user or writable by others; not used")
            # An incomplete copy (a cleaner removed files) is moved aside, then replaced.
            stale = Path(tempfile.mkdtemp(prefix=PREFIX + "stale-", dir=dest.parent))
            try:
                os.rename(dest, stale / "old")
                keep_stale = True
            except OSError:
                if not (_private(dest) and _complete(root)):
                    raise
                return root                      # another process repaired it meanwhile
        try:
            os.rename(staging, dest)
        except OSError:
            if not (_private(dest) and _complete(root)):
                # Preserve the previous copy if publication failed (e.g. an open Windows handle).
                if stale is not None and not os.path.lexists(dest):
                    os.rename(stale / "old", dest)
                    keep_stale = False
                raise
        if not _private(dest):
            raise ValueError(f"{dest} is not a private folder of this user")
        keep_stale = False
        _tidy(dest.parent, dest.name)
        return root
    finally:
        for path in (staging, stale):
            if path is not None and path.exists() and not (path == stale and keep_stale):
                shutil.rmtree(path, ignore_errors=True)


def status():
    report = {"python": sys.version.split()[0], "archive": ARCHIVE, "archive_sha256_ok": None,
              "override": os.environ.get(OVERRIDE), "candidates": []}
    try:
        report["archive_sha256_ok"] = _archive_ok()
    except OSError as exc:
        report["archive_error"] = str(exc)
    for base in _bases():
        dest = os.path.join(base, FOLDER)
        candidate = {"folder": dest, "exists": os.path.lexists(dest)}
        if POSIX:
            try:
                _check_ancestors(os.path.realpath(base))
            except (OSError, ValueError) as exc:
                candidate["unsafe"] = str(exc)
        candidate["private"] = _private(dest) if candidate["exists"] else None
        candidate["complete"] = bool(candidate["private"]) and _complete(os.path.join(dest, ROOT_NAME))
        try:
            with os.scandir(base) as listing:
                others = [entry.name for entry in listing
                          if _other_version(entry.name) and not entry.name.endswith(".lock") and _private(entry.path)]
        except OSError:
            others = []
        candidate["other_versions"] = sorted(others)      # removed when this version is next unpacked
        report["candidates"].append(candidate)
    return report


def read_verified(relative):
    """A cache file's bytes (relative: "people/<slug>/card.md"), checked against the manifest; the
    cache is unpacked again once when the file is missing or differs."""
    for attempt in range(2):
        root = _root(repair=attempt == 1)
        try:
            with open(os.path.join(root, *relative.split("/")), "rb") as stream:
                data = stream.read()
        except FileNotFoundError:
            continue
        expected = _manifest_digests(root).get(relative)
        if expected is not None and hashlib.sha256(data).hexdigest() == expected:
            return data
        if expected is None:
            break
    raise ValueError(f"cache file missing or not as listed in its manifest: {relative}")


def _load_core(root):
    """hololive_cache_core compiled from bytes that match the manifest (never cached bytecode); from
    then on it checks every file it reads (verify_reads)."""
    digests = _manifest_digests(root)
    path = os.path.join(root, "hololive_cache_core.py")
    with open(path, "rb") as stream:
        source = stream.read()
    if hashlib.sha256(source).hexdigest() != digests.get("hololive_cache_core.py"):
        raise ValueError("hololive_cache_core.py is not as listed in the manifest")
    core = type(sys)("hololive_cache_core")
    core.__file__ = path
    sys.modules["hololive_cache_core"] = core
    exec(compile(source, path, "exec", dont_inherit=True), core.__dict__)
    core.verify_reads(root, dict(digests, **{"MANIFEST.sha256": MANIFEST_SHA256}))
    return core


class _Output:
    """sys.stdout for the command: its text is held until the command ends or flushes (before the reader
    runs), so a command that meets a changed file is run again with nothing printed twice."""

    def __init__(self, stream):
        self.stream, self.held, self.used = stream, [], False

    def write(self, text):
        self.held.append(text)
        return len(text)

    def flush(self):
        if self.held:
            self.used = True
            self.stream.write("".join(self.held))
            self.held = []
        self.stream.flush()

    def __getattr__(self, name):
        return getattr(self.stream, name)


def _run_checked(root, output):
    """Run the command; when a file it reads differs from the manifest, unpack again and run it once more."""
    for attempt in range(2):
        try:
            core = _load_core(root)
        except (OSError, ValueError) as exc:
            problem = str(exc)
        else:
            try:
                return core.run_cli()
            except core.CacheIntegrityError as exc:
                problem = str(exc)
        output.held = []
        print(f"Cache changed after unpacking ({problem}); unpacking it again.", file=sys.stderr)
        try:
            root = _root(repair=True)
        except (OSError, ValueError) as exc:
            print("Cache initialization failed: " + str(exc), file=sys.stderr)
            return 1
        if output.used:
            print("Part of the output was already printed: run the command again.", file=sys.stderr)
            return 1
    print("The cache changed again while the command ran; not run a third time.", file=sys.stderr)
    return 1


def main():
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, OSError, ValueError):
            pass
    arguments = sys.argv[1:]
    if not arguments or arguments in (["-h"], ["--help"]):
        (sys.stdout if arguments else sys.stderr).write(USAGE)
        return 0 if arguments else 2
    if arguments == ["--status"]:
        print(json.dumps(status(), ensure_ascii=False, indent=1))
        return 0
    try:
        root = _root(repair=arguments == ["--repair"])
    except (OSError, ValueError) as exc:
        print("Cache initialization failed: " + str(exc), file=sys.stderr)
        return 1
    if arguments in (["--cache-root"], ["--repair"]):
        print(root)
        return 0
    # Run the cache CLI here, from the checked source in the unpacked folder.
    previous_umask = os.umask(0o077) if POSIX else None
    output = _Output(sys.stdout)
    sys.stdout = output
    try:
        code = _run_checked(root, output)
    finally:
        sys.stdout = output.stream
        if previous_umask is not None:
            os.umask(previous_umask)
    try:
        output.flush()
    except BrokenPipeError:                  # e.g. `| head`: the rest of the output is not wanted
        with open(os.devnull, "w") as sink:
            os.dup2(sink.fileno(), sys.stdout.fileno())
    return code


if __name__ == "__main__":
    raise SystemExit(main())
