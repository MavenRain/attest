#!/usr/bin/env python3
"""Record constructor payload source fixtures, semantic variants, and mutations."""
import argparse
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
LOGS = ROOT / "dev/validation/constructor-payload-fixtures"
WORK = ROOT / ".gatework/constructor-payload-mutations"
REQUIRED = {
    "constructor-payload-let-fixture-call",
    "constructor-payload-beta-fixture-call",
    "constructor-payload-annotation-fixture-call",
    "constructor-payload-projection-fixture-call",
    "constructor-payload-let-passthrough",
    "constructor-payload-beta-passthrough",
    "constructor-payload-annotation-passthrough",
    "constructor-payload-projection-passthrough",
}
CONTROLS = {
    "constructor-payload-disabled",
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
    print(f"CONSTRUCTOR-PAYLOAD-FIXTURES {name} OK", flush=True)
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
        print(f"CONSTRUCTOR-PAYLOAD-FIXTURES {name}: retrying Bun compiler segmentation fault once", flush=True)
    result = run_case(case, logs, scratch_root, snapshot)
    result["compiler_retry"] = {"reason": "Bun compiler segmentation fault", "log": evidence(crash)}
    return result

def reuse_checks(inputs):
    checkpoint = json.loads((LOGS / "checks.json").read_text())
    if checkpoint["validated_inputs"] != inputs:
        raise ValueError("checked implementation changed; rerun the full collector")
    checks = checkpoint["checks"]
    expected = {
        "anchors": ["python3", "-P", "dev/erasure-mutations.py", "--check-anchors"],
        "tests": ["make", "test"],
        "gates": ["zsh", "-f", "dev/gates.sh"],
        "erasure-record": ["python3", "-P", "dev/erasure-gates.py", "--record"],
    }
    if len(checks) != len(expected) or {row["name"] for row in checks} != set(expected):
        raise ValueError("incomplete passed-check checkpoint")
    for row in checks:
        if row["exit_code"] != 0 or row["command"] != expected[row["name"]]:
            raise ValueError("invalid passed-check checkpoint")
        if evidence(ROOT / row["log"]["path"]) != row["log"]:
            raise ValueError("passed-check log changed")
    return [dict(row, reused=True) for row in checks]

def checkpoint_case(case, logs, inputs, original_case, arguments, reuse):
    path = LOGS / "completed-mutations.json"
    saved = json.loads(path.read_text()) if path.exists() else {
        "version": 1, "implementation_sha256": inputs, "cases": {},
    }
    if saved["version"] != 1 or saved["implementation_sha256"] != inputs:
        if reuse:
            raise ValueError("completed mutation inputs changed; rerun without cached results")
        saved = {"version": 1, "implementation_sha256": inputs, "cases": {}}
    cached = saved["cases"].get(case[0])
    if reuse and cached is not None:
        row = cached["record"]
        if cached["recipe"] != list(case) or row["build_exit"] != 0 or row["gate_exit"] != 1:
            raise ValueError("invalid completed mutation checkpoint")
        source = (ROOT / case[1]).read_bytes()
        changed = original_case.__globals__["mutate_source"](
            case[0], source.decode(), case[2], case[3]).encode()
        if row["before_sha256"] != hashlib.sha256(source).hexdigest() or row["mutated_sha256"] != hashlib.sha256(changed).hexdigest():
            raise ValueError("completed mutation source recipe changed")
        if row["diagnostic"] != case[4] or row["log_sha256"] != row["log"]["sha256"]:
            raise ValueError("completed mutation identity changed")
        for key, suffix in (("log", ".log"), ("build_log", "-build.log")):
            source = ROOT / row[key]["path"]
            if evidence(source) != row[key]:
                raise ValueError("completed mutation log changed")
            shutil.copyfile(source, logs / (case[0] + suffix))
        if case[4] not in (logs / (case[0] + ".log")).read_text():
            raise ValueError("completed mutation diagnostic changed")
        return dict(row, reused=True)
    row = run_case_with_retry(original_case, *arguments)
    for key, suffix in (("log", ".log"), ("build_log", "-build.log")):
        target = LOGS / (case[0] + suffix)
        shutil.copyfile(logs / target.name, target)
        row[key] = evidence(target)
    saved["cases"][case[0]] = {"recipe": list(case), "record": row}
    path.write_text(json.dumps(saved, indent=2) + "\n")
    return row

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, choices=(1,), default=1)
    parser.add_argument("--reuse-checks", action="store_true",
                        help="reuse unchanged, hash-checked checks.json after a mutation failure")
    parser.add_argument("--reuse-mutations", action="store_true",
                        help="reuse completed, hash-checked isolated mutation results")
    args = parser.parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    (LOGS / ".gitattributes").write_text(
        "# Preserve process output exactly for hash verification.\n*.log whitespace=-blank-at-eof\n")
    harness = runpy.run_path(str(ROOT / "dev/erasure-mutations.py"))
    selected = [case[0] for case in harness["CASES"] if case[0] in REQUIRED | CONTROLS]
    if set(selected) != REQUIRED | CONTROLS:
        raise ValueError("scoped mutation catalog changed")
    inputs = harness["implementation_hashes"](ROOT)
    for name in ("dev/bend-policy.json", "dev/bend-migration.json"):
        inputs[name] = digest(ROOT / name)
    if args.reuse_checks:
        checks = reuse_checks(inputs)
    else:
        checks = [
            check("anchors", ["python3", "-P", "dev/erasure-mutations.py", "--check-anchors"]),
            check("tests", ["make", "test"]),
            check("gates", ["zsh", "-f", "dev/gates.sh"]),
            check("erasure-record", ["python3", "-P", "dev/erasure-gates.py", "--record"]),
        ]
        (LOGS / "checks.json").write_text(json.dumps({
            "version": 1, "validated_inputs": inputs, "checks": checks,
            "producer_sha256": digest(Path(__file__)),
        }, indent=2) + "\n")
    inputs["dev/validation/constructor-payload-fixtures-run.py"] = digest(Path(__file__))
    records = []
    original = harness["run_cases"]
    original_case = harness["run_case"]
    def collect(*arguments):
        result = original(*arguments)
        records.extend(result)
        return result
    harness["main"].__globals__["run_case"] = lambda *arguments: checkpoint_case(
        arguments[0], arguments[1], inputs, original_case, arguments, args.reuse_mutations)
    harness["main"].__globals__["run_cases"] = collect
    command = ["dev/erasure-mutations.py", "--jobs", str(args.jobs), "--logs", str(WORK)]
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
        "scope": "Four parsed constructor payload fixture pairs cover let, beta, annotation, and numeric projection fields. Each semantic row changes the Pick index spelling on a consistent elaborated copy, rechecks Pick and keep in the kernel, checks inline proof sealing and prepared typing, and compares runtime output with its opaque twin. The gate binds each row to its exact sources and variant mode. Four isolated mutations drop the semantic variant and require named fixture binding failures; a constructor payload recovery mutation remains a control.",
        "implementation_sha256": inputs, "checks": checks,
        "check_checkpoint": evidence(LOGS / "checks.json"),
        "mutation_checkpoint": evidence(LOGS / "completed-mutations.json"),
        "supporting_records_sha256": {"dev/validation/erasure.json": digest(ROOT / "dev/validation/erasure.json")},
        "catalog_total": len(harness["CASES"]), "selected": selected, "mutations": records,
    }
    (ROOT / "dev/validation/constructor-payload-fixtures.json").write_text(
        json.dumps(record, indent=2) + "\n")
    print(f"CONSTRUCTOR-PAYLOAD-FIXTURES recorded checks={len(checks)} caught={len(records)} total={len(harness['CASES'])}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
