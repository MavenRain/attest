#!/usr/bin/env python3
"""Collect the Stage B trace comparison evidence: nine mutations and two controls.

Usage: python3 -P dev/validation/stage-b-trace-comparison-run.py [--record] [--only NAME ...]

Each case copies the repository without .git, _build, _tools, .lake and
.gatework into a scratch tree under .gatework/stage-b-trace-comparison, copies
the cached _build/js output into it, applies one edit, and runs
`zsh -f dev/gates.sh TRACE-ERASURE` there. A mutation must exit 1 and print
its diagnostic. A control must exit 0, print the pinned TRACE-COMPARE summary
and end with the pinned verdict. The log of a control and of mutation M7 is
given to check_trace_log of the scratch tree's dev/lean-twin-checks.py: the
control log must pass and the M7 log must be rejected.
The trace-log and case-selection regressions run before the case logs are
replaced. Empty or unknown --only selections are usage errors.

The two Acc frontier rows are deferred to Stage C (USER ruling 2026-10-05).
M7 removes one row from the DEFERRED table: the leg must fail on that row.

Without --record the logs go to .gatework/stage-b-trace-comparison/logs and
no record is written. With --record every case runs, the logs go to
dev/validation/stage-b-trace-comparison (wiped first) and
dev/validation/stage-b-trace-comparison.json is written.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GATE = "dev/erasure-gates.py"
TWIN = "dev/lean-twin-checks.py"
RUNNER = "dev/validation/stage-b-trace-comparison-run.py"
TESTS = "dev/validation/stage-b-trace-comparison-test.py"
WORK = ROOT / ".gatework/stage-b-trace-comparison"
LOGS = ROOT / "dev/validation/stage-b-trace-comparison"
RECORD = ROOT / "dev/validation/stage-b-trace-comparison.json"
COMMAND = ["zsh", "-f", "dev/gates.sh", "TRACE-ERASURE"]
TIMEOUT = 900
IGNORE = shutil.ignore_patterns(".git", "_build", "_tools", ".lake", ".gatework", ".kanon-*", "__pycache__")
SUMMARY = ("TRACE-COMPARE rows=159 pairs=151 identical=151 carried_differs=119 "
           "shape=1 refusal=1 check-only=1 frontier=2 single=3 deferred=2")
VERDICT = "TRACE-ERASURE rows=159 pairs=151 identical=151 deferred=2 OK"
FAIL = "TRACE-ERASURE FAIL row=acc-runtime-proof phase=check; Stage B remains OPEN"
DEFERRED = 'DEFERRED = {"acc": "stage-c", "acc-runtime-proof": "stage-c"}'
SCOPE = ("The TRACE-ERASURE leg accounts for every base fixture row, comparing erased traces for "
         "paired rows and checking the other row classes separately. It prints one TRACE row line "
         "per row, one TRACE-COMPARE summary and one verdict. "
         "The two Acc frontier rows are deferred to Stage C by USER ruling of 2026-10-05. Nine "
         "mutations of the gate or of the fixture set must fail the leg with the named diagnostic. "
         "Two controls must pass with the pinned summary and verdict. Trace-log and case-selection "
         "regression tests must pass before collecting the cases.")

# name, kind, path, before, after, expected exit, required substrings, required last line, twin check
CASES = [
    ("M1", "replace", GATE, '["cmp", "-s", str(left), str(right)]', '["cmp", "-s", str(left), str(left)]',
     1, ("carried traces are identical, expected differs",), None, None),
    ("M2", "replace", GATE, 'return "identical" if code == 0 else "differs"', 'return "differs"',
     1, ("erased traces differ",), None, None),
    ("M3", "create", "fixtures/erasure/zz-unclassified.att", None, "-- a fixture without a trace row\n",
     1, ("fixture without a row: zz-unclassified.att",), None, None),
    ("M4", "replace", GATE, '"motive-index", "motive-self", ', '"motive-index", ',
     1, ("fixture without a row: motive-self.att",), None, None),
    ("M5", "replace", GATE, 'trace_file(work, name, ".opaque", opaque)',
     'trace_file(work, name, ".opaque", opaque + b"\\n")', 1, ("erased traces differ",), None, None),
    ("M6", "replace", GATE, DEFERRED, "FRONTIER = {}\n" + DEFERRED,
     1, ("fixture without a row: acc.att", "deferred row without a frontier row: acc"), None, None),
    ("M7", "replace", GATE, DEFERRED, 'DEFERRED = {"acc": "stage-c"}', 1, (FAIL,), FAIL, "reject"),
    ("M8", "replace", GATE, 'is read in a runtime position"', 'is read in a runtime positiom"',
     1, ("Acc frontier changed; update the Stage B gate and corpus",), None, None),
    ("M9", "replace", GATE, DEFERRED, DEFERRED[:-1] + ', "acc-family": "stage-c"}',
     1, ("deferred row without a frontier row: acc-family",), None, None),
    ("C1", "none", GATE, None, None, 0, (SUMMARY, VERDICT), VERDICT, "accept"),
    ("C2", "append", GATE, None, "# control: a comment-only edit of the gate\n",
     0, (SUMMARY, VERDICT), VERDICT, "accept"),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def edit_none(path, before, after):
    return None


def edit_replace(path, before, after):
    text = path.read_text()
    if text.count(before) != 1:
        raise ValueError(f"edit site occurs {text.count(before)} times in {path.name}: {before!r}")
    path.write_text(text.replace(before, after, 1))


def edit_append(path, before, after):
    path.write_text(path.read_text() + after)


def edit_create(path, before, after):
    if path.exists():
        raise ValueError(f"{path.name} exists already")
    path.write_text(after)


EDITS = {"none": edit_none, "replace": edit_replace, "append": edit_append, "create": edit_create}


def twin_check(scratch, text):
    spec = importlib.util.spec_from_file_location("scratch_twin_checks", scratch / TWIN)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        module.check_trace_log(text)
    except ValueError as error:
        return "reject", str(error)
    return "accept", ""


def run_case(case, logs):
    name, kind, relative, before, after, expected, required, last, twin = case
    started = time.monotonic()
    with tempfile.TemporaryDirectory(dir=WORK / "copies", prefix=name + "-") as directory:
        scratch = pathlib.Path(directory) / "tree"
        shutil.copytree(ROOT, scratch, ignore=IGNORE)
        shutil.copytree(ROOT / "_build/js", scratch / "_build/js")
        path = scratch / relative
        original = digest(path.read_bytes()) if path.exists() else None
        EDITS[kind](path, before, after)
        mutated = digest(path.read_bytes())
        environment = {**os.environ,
                       "ATTEST_BEND_ROOT": os.environ.get("ATTEST_BEND_ROOT", str(ROOT / "_tools/bend"))}
        completed = subprocess.run(COMMAND, cwd=scratch, env=environment, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, timeout=TIMEOUT)
        text = completed.stdout.decode(errors="replace")
        verdict, reason = twin_check(scratch, text) if twin else (None, "")
    seconds = round(time.monotonic() - started, 1)
    log = logs / f"{name}.log"
    log.write_bytes(completed.stdout)
    lines = text.splitlines()
    missing = [item for item in required if item not in text]
    checks = [(completed.returncode == expected, f"exit={completed.returncode} expected={expected}"),
              (not missing, "missing: " + " | ".join(missing)),
              (last is None or (lines and lines[-1] == last), f"last line is not {last!r}"),
              (twin is None or verdict == twin, f"twin check {verdict} expected {twin}: {reason}")]
    problems = [message for ok, message in checks if not ok]
    if problems:
        raise ValueError(f"case {name}: " + "; ".join(problems) + f"; log={log}")
    print(f"TRACE-MUTATION name={name} kind={kind} exit={completed.returncode} "
          f"twin={twin or 'none'} seconds={seconds} OK", flush=True)
    return {"name": name, "kind": kind, "path": relative, "before_sha256": original,
            "mutated_sha256": mutated, "gate_exit": completed.returncode, "expected_exit": expected,
            "required": list(required), "last_line": last, "twin_check": twin, "seconds": seconds,
            "gate_command": COMMAND, "log": {"path": str(log.relative_to(ROOT)), "sha256": digest(completed.stdout)}}


def write_record(results, summary, regressions):
    sources = [RUNNER, TESTS, GATE, TWIN, "dev/gates.sh", "dev/validation/stage-b-trace-control.log"]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    payload = {"version": 1, "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "root": str(ROOT), "base_revision": revision, "scope": SCOPE, "gate_command": COMMAND,
               "summary_line": SUMMARY, "verdict_line": VERDICT,
               "implementation_sha256": {source: digest((ROOT / source).read_bytes()) for source in sources},
               "regressions": regressions, "cases": results, "result": summary}
    RECORD.write_text(json.dumps(payload, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--only", nargs="+", choices=[case[0] for case in CASES], default=None,
                        help="case names to run (default: every case)")
    args = parser.parse_args()
    if args.record and args.only is not None:
        parser.error("--record runs every case")
    cases = [case for case in CASES if args.only is None or case[0] in args.only]
    test_command = [sys.executable, "-P", TESTS]
    tested = subprocess.run(test_command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=60)
    if tested.returncode:
        print(tested.stdout.decode(errors="replace"), end="")
        print("STAGE-B-TRACE-COMPARISON FAIL regression tests", flush=True)
        return 1
    logs = LOGS if args.record else WORK / "logs"
    if logs.exists():
        shutil.rmtree(logs)
    logs.mkdir(parents=True)
    test_log = logs / "regressions.log"
    test_log.write_bytes(tested.stdout)
    regressions = {"command": test_command, "exit_code": tested.returncode,
                   "log": {"path": str(test_log.relative_to(ROOT)), "sha256": digest(tested.stdout)}}
    (WORK / "copies").mkdir(parents=True, exist_ok=True)
    try:
        results = [run_case(case, logs) for case in cases]
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"STAGE-B-TRACE-COMPARISON FAIL {error}", flush=True)
        return 1
    mutations = sum(row["name"].startswith("M") for row in results)
    summary = (f"STAGE-B-TRACE-COMPARISON cases={len(results)} mutations={mutations} "
               f"controls={len(results) - mutations} OK")
    print(summary, flush=True)
    if args.record:
        write_record(results, summary, regressions)
    return 0


if __name__ == "__main__":
    sys.exit(main())
