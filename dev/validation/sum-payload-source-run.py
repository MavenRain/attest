#!/usr/bin/env python3
"""Record bounded numeric sum payload recovery and scoped mutations."""
import contextlib
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
LOGS = ROOT / "dev/validation/sum-payload-source"
WORK = ROOT / ".gatework/sum-payload-mutations"
REQUIRED = {
    "sum-payload-disabled", "sum-payload-range",
    "sum-payload-arity", "sum-payload-scope",
    "sum-payload-address", "sum-payload-size",
    "sum-payload-fuel", "sum-payload-shape",
    "sum-payload-steps",
}
CONTROLS = {
    "neutral-projection-disabled", "sum-index-result-fuel",
    "index-reduction-left", "index-reduction-right",
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def evidence(path):
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}

def check(name, command):
    log = LOGS / (name + ".log")
    started = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, timeout=3600)
    row = {"name": name, "command": command, "exit_code": result.returncode,
           "log": evidence(log), "elapsed_seconds": round(time.monotonic() - started, 3)}
    if result.returncode:
        raise ValueError(f"{name}: exit={result.returncode}; see {log}")
    print(f"SUM-PAYLOAD-SOURCE {name} OK", flush=True)
    return row

def run_case_with_retry(run_case, case, logs, scratch_root, snapshot):
    try:
        return run_case(case, logs, scratch_root, snapshot)
    except ValueError as error:
        name = case[0]
        if str(error) != f"{name}: build failed, not a caught behavior mutation":
            raise
        failure = (logs / (name + "-build.log")).read_bytes()
        markers = (b"Bun v", b"panic(main thread): Segmentation fault", b" js exit=-5;")
        if not all(marker in failure for marker in markers):
            raise
        crash = LOGS / (name + "-bun-crash.log")
        crash.write_bytes(failure)
        print(f"SUM-PAYLOAD-SOURCE {name}: retrying Bun compiler segmentation fault once", flush=True)
    result = run_case(case, logs, scratch_root, snapshot)
    result["compiler_retry"] = {"reason": "Bun compiler segmentation fault", "log": evidence(crash)}
    return result

def main():
    LOGS.mkdir(parents=True, exist_ok=True)
    (LOGS / ".gitattributes").write_text(
        "# Preserve process output exactly for hash verification.\n*.log whitespace=-blank-at-eof\n")
    harness = runpy.run_path(str(ROOT / "dev/erasure-mutations.py"))
    selected = [case[0] for case in harness["CASES"] if case[0] in REQUIRED | CONTROLS]
    if set(selected) != REQUIRED | CONTROLS:
        raise ValueError("scoped mutation catalog changed")
    inputs = harness["implementation_hashes"](ROOT)
    for name in ("dev/bend-policy.json", "dev/bend-migration.json",
                 "dev/validation/sum-payload-source-run.py"):
        inputs[name] = digest(ROOT / name)
    checks = [
        check("anchors", ["python3", "-P", "dev/erasure-mutations.py", "--check-anchors"]),
        check("tests", ["make", "test"]),
        check("gates", ["zsh", "-f", "dev/gates.sh"]),
        check("erasure-record", ["python3", "-P", "dev/erasure-gates.py", "--record"]),
    ]
    records = []
    original = harness["run_cases"]
    original_case = harness["run_case"]
    def collect(*arguments):
        result = original(*arguments)
        records.extend(result)
        return result
    harness["main"].__globals__["run_case"] = lambda *arguments: run_case_with_retry(original_case, *arguments)
    harness["main"].__globals__["run_cases"] = collect
    command = ["dev/erasure-mutations.py", "--jobs", "2", "--logs", str(WORK)]
    for name in selected:
        command += ["--case", name]
    old_arguments = sys.argv
    started = time.monotonic()
    log = LOGS / "mutations.log"
    try:
        sys.argv = command
        with log.open("w") as output, contextlib.redirect_stdout(output):
            code = harness["main"]()
    finally:
        sys.argv = old_arguments
    if code != 0 or {row["name"] for row in records} != set(selected) or len(records) != len(selected):
        raise ValueError(f"scoped mutations failed: exit={code}; see {log}")
    for row in records:
        for suffix, key in ((".log", "log"), ("-build.log", "build_log")):
            target = LOGS / (row["name"] + suffix)
            shutil.copyfile(WORK / target.name, target)
            row[key] = evidence(target)
        if row["log_sha256"] != row["log"]["sha256"] or row["build_exit"] != 0:
            raise ValueError(f"mutation evidence mismatch: {row['name']}")
    shutil.copyfile(WORK / "baseline.log", LOGS / "mutation-baseline.log")
    checks.append({"name": "mutations", "harness_argv": command, "exit_code": code,
                   "log": evidence(log), "elapsed_seconds": round(time.monotonic() - started, 3),
                   "baseline": evidence(LOGS / "mutation-baseline.log")})
    for name, expected in inputs.items():
        if digest(ROOT / name) != expected:
            raise ValueError(f"input changed during validation: {name}")
    record = {
        "version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "root": str(ROOT), "base_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "scope": "Numeric sum injection payloads in constructor source indices; shared reduction and transition budgets, address, shape, arity, scope and reconstruction size guards. Concrete case scrutinees keep their existing path.",
        "implementation_sha256": inputs, "checks": checks,
        "supporting_records_sha256": {"dev/validation/erasure.json": digest(ROOT / "dev/validation/erasure.json")},
        "catalog_total": len(harness["CASES"]), "selected": selected, "mutations": records,
    }
    (ROOT / "dev/validation/sum-payload-source.json").write_text(
        json.dumps(record, indent=2) + "\n")
    print(f"SUM-PAYLOAD-SOURCE recorded checks={len(checks)} caught={len(records)} total={len(harness['CASES'])}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
