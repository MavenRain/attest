#!/usr/bin/env python3
"""Run the five LEAN-TWIN release checks and record their outcomes.

Usage: python3 -P dev/lean-twin-checks.py [--record] [--timeout SECONDS]
       python3 -P dev/lean-twin-checks.py --roots

The five checks run from the repository root in order: the full gate
battery, the complete Bend test suite, the
corpus record command, the mutation record command, and the TRACE-ERASURE
comparison, which must pass with the Acc rows deferred to Stage C. Each check
must exit with its expected code. The two record commands rewrite
dev/validation/lean-twin.json and dev/validation/lean-twin-mutations.json,
so a run of this script is the one regeneration of all three records.

The test leg builds through make test and runs every registered program.
Its log must contain the complete 16-program summary. The trace leg
must print the verified Acc frontier line, one TRACE-COMPARE summary and one
passing verdict. The counts of the summary must agree with the TRACE row
lines. Each frontier row must be deferred to Stage C.

Every log is written under .gatework/lean-twin-checks. With --record the
logs are copied to dev/validation/lean-twin-checks (the directory is wiped
first) and dev/validation/lean-twin-checks.json is written with the exit
code, timing and log hash of every check, the hash of both records, and
record_hashes_verified, which is derived by rehashing every log named in
the two records against the log files on disk.
Every record must name this repository as its root: a record written in
another tree fails the check. Without --record the existing
dev/validation/lean-twin-checks.json root is checked before any command runs.
With --roots no command runs: the root of lean-twin.json,
lean-twin-mutations.json and lean-twin-checks.json is checked against this
repository and the script exits. dev/lean-twin.sh runs this mode before every
check run, so the LEAN-TWIN gate leg fails on a record from another tree.
While --record runs, its commands get ATTEST_LEAN_TWIN_CHECKS_RECORDING set
to this repository root, and only then --roots skips lean-twin-checks.json,
which this record run writes again at its end.
The per-command timeout defaults to 900 seconds and is recorded explicitly.
"""
import argparse
from collections import Counter
import datetime
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORK = ROOT / ".gatework/lean-twin-checks"
LOGS = ROOT / "dev/validation/lean-twin-checks"
RECORD = ROOT / "dev/validation/lean-twin-checks.json"
RECORDS = {
    "dev/validation/lean-twin.json": "dev/validation/lean-twin",
    "dev/validation/lean-twin-mutations.json": "dev/validation/lean-twin-mutations",
}
TIMEOUT = 900
RECORDING = "ATTEST_LEAN_TWIN_CHECKS_RECORDING"
TEST_SUMMARY = "TESTS programs=16 OK"
TRACE_VERDICT = "TRACE-ERASURE rows={rows} pairs={pairs} identical={pairs} deferred={deferred} OK"
TRACE_SUMMARY = re.compile(r"TRACE-COMPARE rows=(\d+) pairs=(\d+) identical=(\d+) carried_differs=(\d+) "
                           r"shape=(\d+) refusal=(\d+) check-only=(\d+) frontier=(\d+) single=(\d+) deferred=(\d+)")
TRACE_FIELDS = {
    "pair-raw": {"cmp", "carried"}, "pair-runtime": {"cmp", "carried"},
    "shape": {"cmp", "against"}, "refusal": {"exit"}, "check-only": {"check"},
    "frontier": {"check", "deferred"}, "single": {"erase"},
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_test_log(text):
    if text.splitlines().count(TEST_SUMMARY) != 1:
        raise ValueError("bend-tests missing complete 16-program result")


def check_trace_log(text):
    lines = text.splitlines()
    if "ACC-FRONTIER lean=accepted attest=refused reason=proof-quantity OPEN" not in lines:
        raise ValueError("trace-frontier missing verified Acc frontier")
    summaries = [match for match in map(TRACE_SUMMARY.fullmatch, lines) if match]
    if len(summaries) != 1 or sum(line.startswith("TRACE-COMPARE ") for line in lines) != 1:
        raise ValueError("trace-frontier missing the one TRACE-COMPARE summary")
    (summary,) = summaries
    rows, pairs, identical, carried, shape, refusal, check_only, frontier, single, deferred = map(int, summary.groups())
    printed = {}
    for line in (line for line in lines if line.startswith("TRACE ")):
        fields = line.split()[1:]
        if any(field.count("=") != 1 for field in fields):
            raise ValueError("trace-frontier malformed TRACE row")
        row = dict(field.split("=") for field in fields)
        name, kind = row.get("row"), row.get("class")
        if (len(row) != len(fields) or not name or name in printed or kind not in TRACE_FIELDS
                or set(row) != {"row", "class"} | TRACE_FIELDS[kind]):
            raise ValueError("trace-frontier malformed or duplicate TRACE row")
        if (("cmp" in row and row["cmp"] != "identical")
                or ("carried" in row and row["carried"] not in ("identical", "differs"))
                or ("check" in row and row["check"] != ("refused" if kind == "frontier" else "accepted"))
                or (kind == "frontier" and row["deferred"] != "stage-c")
                or (kind == "refusal" and row["exit"] != "2")
                or (kind == "single" and row["erase"] != "accepted")):
            raise ValueError(f"trace-frontier failed TRACE row: {name}")
        printed[name] = row
    expected = {path.stem for path in (ROOT / "fixtures/erasure").glob("*.att")
                if not path.stem.endswith("-opaque")}
    if set(printed) != expected:
        raise ValueError("trace-frontier TRACE rows disagree with the fixture census")
    for row in printed.values():
        if row["class"] == "shape" and printed.get(row["against"], {}).get("class") != "pair-raw":
            raise ValueError("trace-frontier shape row has no raw pair target")
    kinds = Counter(row["class"] for row in printed.values())
    pair_rows = [row for row in printed.values() if row["class"] in ("pair-raw", "pair-runtime")]
    actual = (len(printed), len(pair_rows), len(pair_rows),
              sum(row["carried"] == "differs" for row in pair_rows),
              *(kinds[kind] for kind in ("shape", "refusal", "check-only", "frontier", "single")),
              kinds["frontier"])
    if tuple(map(int, summary.groups())) != actual or frontier < 1:
        raise ValueError("trace-frontier TRACE-COMPARE summary disagrees with its TRACE rows")
    verdicts = [line for line in lines if line.startswith("TRACE-ERASURE ")]
    if verdicts != [TRACE_VERDICT.format(rows=rows, pairs=pairs, deferred=deferred)]:
        raise ValueError("trace-frontier did not pass with the Acc rows deferred to Stage C")


CHECKS = [
    {"name": "gates", "command": ["zsh", "-f", "dev/gates.sh", "all"], "expected": 0},
    {"name": "bend-tests", "command": ["make", "test"],
     "expected": 0, "inspect": check_test_log},
    {"name": "corpus-record", "command": ["zsh", "-f", "dev/lean-twin.sh", "--record"],
     "expected": 0},
    {"name": "mutation-record",
     "command": ["python3", "-P", "dev/lean-twin-mutations.py", "--record"], "expected": 0},
    {"name": "trace-frontier", "command": ["zsh", "-f", "dev/gates.sh", "TRACE-ERASURE"],
     "expected": 0, "inspect": check_trace_log},
]


def run_check(check, timeout=TIMEOUT, environment=None):
    name, command, expected = check["name"], check["command"], check["expected"]
    environment = dict(os.environ) if environment is None else environment
    started = time.monotonic()
    try:
        completed = subprocess.run(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        (WORK / f"{name}.log").write_bytes(error.output or b"")
        raise ValueError(f"{name} timed out after {timeout} seconds; log={WORK / (name + '.log')}") from error
    seconds = round(time.monotonic() - started, 3)
    (WORK / f"{name}.log").write_bytes(completed.stdout)
    if completed.returncode != expected:
        raise ValueError(f"{name} exit={completed.returncode} expected={expected}")
    check.get("inspect", lambda text: None)(completed.stdout.decode(errors="replace"))
    print(f"LEAN-TWIN-CHECK name={name} exit={completed.returncode} "
          f"expected={expected} seconds={seconds} OK", flush=True)
    row = {"name": name, "command": command, "exit_code": completed.returncode,
           "expected": expected, "seconds": seconds, "timeout_seconds": timeout,
           "log_sha256": digest(completed.stdout)}
    return row


def check_root(record, data):
    recorded = data.get("root")
    if recorded != str(ROOT):
        raise ValueError(f"{record} root={recorded!r} differs from repository root {str(ROOT)!r}; "
                         "record it again from this repository")


def verify_record(record, directory):
    data = json.loads((ROOT / record).read_text())
    check_root(record, data)
    hashes = data["log_sha256"]
    if not hashes:
        raise ValueError(f"{record} names no logs")
    stale = [name for name, value in hashes.items()
             if not (ROOT / directory / name).is_file()
             or digest((ROOT / directory / name).read_bytes()) != value]
    if stale:
        raise ValueError(f"{record} log hashes are stale: {' '.join(stale)}")
    return digest((ROOT / record).read_bytes())


def check_roots():
    own = str(RECORD.relative_to(ROOT))
    recording = os.environ.get(RECORDING) == str(ROOT)
    names = [*RECORDS, *([] if recording else [own])]
    list(map(lambda name: check_root(name, json.loads((ROOT / name).read_text())), names))
    print(f"LEAN-TWIN-ROOTS records={len(names)}/{len(RECORDS) + 1} root={ROOT} OK", flush=True)


def run(record=False, timeout=TIMEOUT):
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    if not record:
        check_root(str(RECORD.relative_to(ROOT)), json.loads(RECORD.read_text()))
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    inherited = {key: value for key, value in os.environ.items() if key != RECORDING}
    environment = {**inherited, **({RECORDING: str(ROOT)} if record else {})}
    results = [run_check(check, timeout, environment) for check in CHECKS]
    record_hashes = {path: verify_record(path, directory) for path, directory in RECORDS.items()}
    verified = len(record_hashes) == len(RECORDS)
    summary = (f"LEAN-TWIN-CHECKS passed={len(results)}/{len(CHECKS)} "
               f"records={len(record_hashes)}/{len(RECORDS)} OK")
    print(summary, flush=True)
    if record:
        if LOGS.exists():
            shutil.rmtree(LOGS)
        LOGS.mkdir(parents=True)
        hashes = {}
        for path in sorted(WORK.glob("*.log")):
            shutil.copyfile(path, LOGS / path.name)
            hashes[path.name] = digest((LOGS / path.name).read_bytes())
        payload = {"version": 1,
                   "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "root": str(ROOT), "summary": summary, "timeout_seconds": timeout, "checks": results,
                   "log_sha256": hashes, "record_sha256": record_hashes,
                   "record_hashes_verified": verified}
        RECORD.write_text(json.dumps(payload, indent=2) + "\n")
    return results


def positive_timeout(value):
    seconds = int(value)
    if seconds <= 0:
        raise argparse.ArgumentTypeError("timeout must be a positive number of seconds")
    return seconds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--roots", action="store_true",
                        help="only check that every LEAN-TWIN record names this repository")
    parser.add_argument("--timeout", type=positive_timeout, default=TIMEOUT,
                        help="per-command limit in seconds (default: 900)")
    args = parser.parse_args()
    if args.roots and args.record:
        parser.error("--roots and --record exclude each other")
    try:
        check_roots() if args.roots else run(args.record, args.timeout)
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"LEAN-TWIN-CHECKS FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
