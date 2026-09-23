#!/usr/bin/env python3
"""Run the five LEAN-TWIN release checks and record their outcomes.

Usage: python3 -P dev/lean-twin-checks.py [--record]

The five checks run from the repository root in order: the full gate
battery, the dune test suite with --force so that every test runs, the
corpus record command, the mutation record command, and the TRACE-ERASURE
frontier, which must still fail while Stage B is open. Each check must exit
with its expected code. The two record commands rewrite
dev/validation/lean-twin.json and dev/validation/lean-twin-mutations.json,
so a run of this script is the one regeneration of all three records.

The dune leg goes through dev/dunecho.sh like every dune verb. The dunecho
distiller accepts no dune option, so the leg runs with every PATH entry
that provides dunecho removed; the runner then execs dune itself with
--force, and the test log must show at least one result line and no
"0 run" summary. The record marks that leg with dunecho_bypassed and never
stores the machine PATH, so the record depends on the outputs alone.

Every log is written under .gatework/lean-twin-checks. With --record the
logs are copied to dev/validation/lean-twin-checks (the directory is wiped
first) and dev/validation/lean-twin-checks.json is written with the exit
code, timing and log hash of every check, the hash of both records, and
record_hashes_verified, which is derived by rehashing every log named in
the two records against the log files on disk.
"""
import argparse
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
ZERO_RUN = re.compile(r"(?<![0-9])0 run\b")
RESULT_LINE = re.compile(r"^\S.* OK$", re.MULTILINE)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def path_without_dunecho():
    entries = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry]
    return [entry for entry in entries if shutil.which("dunecho", path=entry) is None]


def check_dune_log(text):
    if ZERO_RUN.search(text):
        raise ValueError("dune-tests ran zero tests")
    if RESULT_LINE.search(text) is None:
        raise ValueError("dune-tests printed no result line")


CHECKS = [
    {"name": "gates", "command": ["zsh", "-f", "dev/gates.sh", "all"], "expected": 0},
    {"name": "dune-tests", "command": ["zsh", "-f", "dev/dunecho.sh", "test", "--force"],
     "expected": 0, "path": path_without_dunecho, "inspect": check_dune_log},
    {"name": "corpus-record", "command": ["zsh", "-f", "dev/lean-twin.sh", "--record"],
     "expected": 0},
    {"name": "mutation-record",
     "command": ["python3", "-P", "dev/lean-twin-mutations.py", "--record"], "expected": 0},
    {"name": "trace-frontier", "command": ["zsh", "-f", "dev/gates.sh", "TRACE-ERASURE"],
     "expected": 1},
]


def run_check(check):
    name, command, expected = check["name"], check["command"], check["expected"]
    environment = dict(os.environ)
    path_entries = check.get("path", lambda: None)()
    if path_entries is not None:
        environment["PATH"] = os.pathsep.join(path_entries)
    started = time.monotonic()
    completed = subprocess.run(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=TIMEOUT)
    seconds = round(time.monotonic() - started, 3)
    (WORK / f"{name}.log").write_bytes(completed.stdout)
    if completed.returncode != expected:
        raise ValueError(f"{name} exit={completed.returncode} expected={expected}")
    check.get("inspect", lambda text: None)(completed.stdout.decode(errors="replace"))
    print(f"LEAN-TWIN-CHECK name={name} exit={completed.returncode} "
          f"expected={expected} seconds={seconds} OK", flush=True)
    row = {"name": name, "command": command, "exit_code": completed.returncode,
           "expected": expected, "seconds": seconds, "log_sha256": digest(completed.stdout)}
    if path_entries is not None:
        row["dunecho_bypassed"] = True
    return row


def verify_record(record, directory):
    data = json.loads((ROOT / record).read_text())
    hashes = data["log_sha256"]
    if not hashes:
        raise ValueError(f"{record} names no logs")
    stale = [name for name, value in hashes.items()
             if not (ROOT / directory / name).is_file()
             or digest((ROOT / directory / name).read_bytes()) != value]
    if stale:
        raise ValueError(f"{record} log hashes are stale: {' '.join(stale)}")
    return digest((ROOT / record).read_bytes())


def run(record=False):
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    results = [run_check(check) for check in CHECKS]
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
                   "root": str(ROOT), "summary": summary, "checks": results,
                   "log_sha256": hashes, "record_sha256": record_hashes,
                   "record_hashes_verified": verified}
        RECORD.write_text(json.dumps(payload, indent=2) + "\n")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    try:
        run(args.record)
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"LEAN-TWIN-CHECKS FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
