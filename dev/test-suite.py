#!/usr/bin/env -S python3 -P
"""The original eight-group kernel suite, using the raw Bend suite probe."""

from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import errno
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile


REPO = Path(__file__).resolve().parent.parent
MIGRATED = ("mu-erase", "mu-rec-direct", "mu-rec-indexed", "mu-rec-mutual")
PROBE_SETTING = os.environ.get("ATTEST_SUITE_PROBE")
PROBE = shlex.split(PROBE_SETTING) if PROBE_SETTING is not None else [str(REPO / "_build/default/dev/suite_probe.exe")]


def io_message(path: str, error: OSError, reading: bool = False) -> str:
    reason = os.strerror(error.errno) if error.errno is not None else str(error)
    return reason if reading and error.errno == errno.EISDIR else f"{path}: {reason}"


def read_file(path: str) -> tuple[bytes | None, str | None]:
    try:
        return Path(path).read_bytes(), None
    except OSError as error:
        return None, io_message(path, error, reading=True)


def kan_names(path: str) -> tuple[list[str] | None, str | None]:
    try:
        names = [name[:-4] for name in os.listdir(path) if name.endswith(".kan")]
        return sorted(names, key=os.fsencode), None
    except OSError as error:
        return None, io_message(path, error)


def path_of(directory: str, name: str, extension: str) -> str:
    return os.path.join(directory, name + extension)


@dataclass(frozen=True)
class Probe:
    code: int
    stdout: bytes
    stderr: bytes

    def failure(self) -> str:
        message = self.stderr.decode("utf-8", errors="surrogateescape").rstrip("\n")
        return message or f"the suite probe exited with status {self.code}"


def probe(mode: str, path: str | None = None) -> Probe:
    args = PROBE + [mode] + ([] if path is None else [path])
    try:
        result = subprocess.run(args, capture_output=True, check=False)
        return Probe(result.returncode, result.stdout, result.stderr)
    except OSError as error:
        return Probe(1, b"", io_message(args[0], error).encode("utf-8", errors="surrogateescape"))


def round_trip(path: str) -> str | None:
    result = probe("parse", path)
    if result.code != 0:
        return result.failure()
    if result.stdout or result.stderr:
        return "the round-trip probe returned unexpected output"
    return None


def fixture(root: str, name: str, erase: bool) -> str | None:
    source = path_of(os.path.join(root, "fixtures"), name, ".kan")
    _, failure = read_file(source)
    if failure is not None:
        return failure
    golden, failure = read_file(path_of(os.path.join(root, "golden"), name, ".erased" if erase else ".checked"))
    if failure is not None:
        return failure
    result = probe("erased" if erase else "checked", source)
    if result.code != 0:
        return result.failure()
    if result.stderr:
        return result.failure()
    if result.stdout != golden:
        return "the erased form is not the golden text" if erase else "the checked form is not the golden text"
    return None


def negative(root: str, name: str, erase: bool) -> str | None:
    directory = os.path.join(root, "erase-neg" if erase else "neg")
    source = path_of(directory, name, ".kan")
    _, failure = read_file(source)
    if failure is not None:
        return failure
    wanted, failure = read_file(path_of(directory, name, ".err"))
    if failure is not None:
        return failure
    result = probe("erase-error" if erase else "check-error", source)
    if result.code != 0 or result.stderr:
        return result.failure()
    # OCaml String.trim recognizes these five ASCII whitespace characters.
    if result.stdout != wanted.strip(b" \t\n\r\x0c"):
        return 'the message is "' + result.stdout.decode("utf-8", errors="surrogateescape") + '"'
    return None


def direct(mode: str) -> str | None:
    result = probe(mode)
    if result.code != 0:
        return result.failure()
    if result.stdout or result.stderr:
        return "the assertion probe returned unexpected output"
    return None


def report(kind: str, name: str, failure: str | None) -> bool:
    print(f"{kind} {name} OK" if failure is None else f"{kind} {name} FAIL: {failure}", flush=True)
    return failure is None


def group(pool: ThreadPoolExecutor, kind: str, label: str, run, names: list[str]) -> tuple[int, int]:
    passed = 0
    for name, failure in zip(names, pool.map(run, names)):
        passed += report(kind, name, failure)
    print(f"{label} {passed}/{len(names)}", flush=True)
    return passed, len(names)


def parse_group(pool: ThreadPoolExecutor, directories: list[tuple[str, list[str]]]) -> tuple[int, int]:
    files = [(directory, name) for directory, names in directories for name in names]
    results = pool.map(lambda item: round_trip(path_of(item[0], item[1], ".kan")), files)
    passed = 0
    for (_, name), failure in zip(files, results):
        if failure is None:
            passed += 1
        else:
            report("PARSE", name, failure)
    print(f"PARSE-OK {passed}/{len(files)}", flush=True)
    return passed, len(files)


def fail_out(message: str) -> int:
    print(f"SUITE {message}\nSUITE-KERNEL FAIL", flush=True)
    return 1


def run(root: str, fixtures: list[str], negatives: list[str], erase_negatives: list[str]) -> int:
    try:
        jobs = max(1, int(os.environ.get("ATTEST_SUITE_JOBS", "2")))
    except ValueError:
        return fail_out("ATTEST_SUITE_JOBS must be an integer")
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        parsed = parse_group(pool, [(os.path.join(root, "fixtures"), fixtures), (os.path.join(root, "neg"), negatives), (os.path.join(root, "erase-neg"), erase_negatives)])
        checked = group(pool, "CHECK", "CHECK-OK", lambda name: fixture(root, name, False), fixtures)
        erased = group(pool, "ERASE", "ERASE-OK", lambda name: fixture(root, name, True), fixtures)
        refused = group(pool, "NEG", "NEG-OK", lambda name: negative(root, name, False), negatives)
        unerased = group(pool, "ERASE-NEG", "ERASE-NEG-OK", lambda name: negative(root, name, True), erase_negatives)
        closed = group(pool, "KNEG", "KNEG-OK", lambda name: direct("kneg-" + name), ["smu", "self"])
        recursive = group(pool, "REC", "REC-OK", lambda name: direct("recursive-values"), ["values"])
        migration = group(pool, "MIGRATED", "MIGRATED-OK", lambda name: None if name in fixtures else "the migrated erasure fixture is missing", list(MIGRATED))
    full = all(passed == total and total > 0 for passed, total in [parsed, checked, erased, refused, closed, recursive, migration])
    sound = unerased[0] == unerased[1]
    print("SUITE-KERNEL OK" if full and sound else "SUITE-KERNEL FAIL", flush=True)
    return 0 if full and sound else 1


def large_io() -> int:
    """Opt-in reader regression, separate from the original eight group totals."""
    failures = 0
    expected = b"def x : Nat := 123456789012345678901234567890\n"
    with tempfile.TemporaryDirectory(prefix="attest-byte-reader-") as directory:
        for size in [65535, 65536, 131073]:
            path = Path(directory) / f"chunk-{size}.kan"
            path.write_bytes(b"--" + b"\xff" * size + b"\ndef x : Nat := 123456789012345678901234567890\n")
            result = probe("checked", str(path))
            failure = None if result.code == 0 and result.stdout == expected and not result.stderr else result.failure() if result.code != 0 or result.stderr else "the byte reader changed the checked form"
            failures += not report("LARGE-IO", str(size), failure)
    print(f"LARGE-IO-OK {3 - failures}/3", flush=True)
    return int(failures != 0)


def main() -> int:
    if os.environ.get("ATTEST_TEST_LARGE_IO") == "1":
        return large_io()
    root = sys.argv[1] if len(sys.argv) > 1 else "test"
    listed = []
    for directory in ["fixtures", "neg", "erase-neg"]:
        names, failure = kan_names(os.path.join(root, directory))
        if failure is not None:
            return fail_out(failure)
        listed.append(names)
    return run(root, *listed)


if __name__ == "__main__":
    raise SystemExit(main())
