#!/usr/bin/env python3
"""Probe Stage A's failure paths in independent temporary source copies.

Scratch outputs go to .gatework/mutations/ (baseline.log, one log per probe,
results.json). With --record (the dev/mutations.sh wrapper forwards its
arguments) or MUTATIONS_RECORD=1, a fully caught run also writes the committed
record:
dev/validation/stage-a.json (envelope plus the probe records),
dev/validation/stage-a-gates.txt (the baseline gate transcript that
baseline_sha256 hashes) and dev/validation/mutations/<name>.log (the probe
logs that log_sha256 hashes). Regenerate with
`MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

unknown_arguments = [arg for arg in sys.argv[1:] if arg != "--record"]
if unknown_arguments:
    print(f"MUTATIONS FAIL: unknown argument {unknown_arguments[0]!r}; only --record is accepted")
    sys.exit(2)

root = Path(__file__).resolve().parent.parent
logs = root / ".gatework/mutations"
logs.mkdir(parents=True, exist_ok=True)
validation = root / "dev/validation"
build = ["zsh", "-f", "dev/dunecho.sh", "build"]
# dev/mutations.sh sets MUTATIONS_VIA_WRAPPER=1 so mutation_command names the
# invocation that really ran: wrapper or direct, env flag or --record.
via_wrapper = os.environ.get("MUTATIONS_VIA_WRAPPER") == "1"
record_env = os.environ.get("MUTATIONS_RECORD") == "1"
record_flag = "--record" in sys.argv[1:]
record = record_env or record_flag
baseline_command = "zsh -f dev/gates.sh"
mutation_command = "".join((
    "MUTATIONS_RECORD=1 " if record_env else "",
    "zsh -f dev/mutations.sh" if via_wrapper else "python3 -P dev/mutations.py",
    " --record" if record_flag else ""))

# Stage A implementation surface pinned by dev/validation/stage-a.json: the
# kernel driver, the gate scripts and their probes, the build files and the
# fixtures the gates read. Hashed from the live tree at record time.
implementation = (
    "bin/attest.ml", "corpus/id.att",
    "dev/axioms-empty.py", "dev/axioms-empty.sh", "dev/bench.sh",
    "dev/carry-check.py", "dev/carry-check.sh", "dev/carry-manifest.json",
    "dev/driver-exit.py", "dev/driver-exit.sh", "dev/dunecho.sh", "dev/gates.sh",
    "dev/house-catchalls.py", "dev/house.sh", "dev/mutations.py", "dev/mutations.sh",
    "dev/pass_bench.ml", "dev/r0-audit.py", "dev/r0-audit.sh", "dev/r0-count.py",
    "dev/r0-count.sh", "dev/r0-diff.py", "dev/r0-diff.sh", "dev/r0-diff/shape.ml",
    "dev/r0-diff/spec_count.ml", "dev/r0-diff/term.ml", "dev/ratio.py", "dev/ratio.sh",
    "dev/stage-a-gates.py", "dev/trusted-lines.py", "dev/trusted-lines.sh",
    "dune", "dune-project", "fixtures/axiom.att", "fixtures/ill-typed.att", "test/dune",
)

def script(name):
    return ["zsh", "-f", "dev/" + name + ".sh"]

def sha256(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

def run(command, cwd):
    """Run a gate with UTF-8 decoding so the hashed logs do not depend on the locale."""
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")

def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError(f"mutation anchor is not unique: {before!r}")
    return text.replace(before, after, 1)

def first_match(pattern, output):
    return next((line for line in output.splitlines() if re.search(pattern, line)), "")

def write_record(baseline_output, records):
    """Write the committed Stage A record so every pinned hash resolves in the tree."""
    kept = validation / "mutations"
    kept.mkdir(parents=True, exist_ok=True)
    (validation / "stage-a-gates.txt").write_text(baseline_output, encoding="utf-8")
    for entry in records:
        shutil.copyfile(root / entry["log"], kept / (entry["name"] + ".log"))
    envelope = {
        "version": 1,
        "stage": "A",
        "recorded_at": datetime.now(timezone.utc).isoformat(),
        "baseline_command": baseline_command,
        "baseline_exit": 0,
        "baseline_sha256": sha256(baseline_output),
        "implementation_sha256": {
            path: hashlib.sha256((root / path).read_bytes()).hexdigest()
            for path in implementation},
        "mutation_command": mutation_command,
        "mutation_exit": 0,
        "mutations": [
            {**entry, "log": str((kept / (entry["name"] + ".log")).relative_to(root))}
            for entry in records],
    }
    target = validation / "stage-a.json"
    target.write_text(json.dumps(envelope, indent=2) + "\n", encoding="utf-8")
    print(f"MUTATIONS RECORD {target.relative_to(root)} logs={len(records)}")

# name, source path, mutation, gate command, required diagnostic, build first
cases = [
    ("PIN", "dev/PIN", lambda s: s[:-2] + ("0" if s[-2] != "0" else "1") + "\n",
     script("carry-check"), r"PIN .* FAIL expected=", False),
    ("CARRY", "lib/quantity.ml", lambda s: s + "(* unlisted source edit *)\n",
     script("carry-check"), r"CARRY FAIL path=lib/quantity.ml", False),
    ("CARRY-unlisted", "lib/unlisted.ml", lambda s: "let marker = ()\n",
     script("carry-check"), r"unlisted=1", False),
    ("CARRY-origin", "dev/carry-manifest.json",
     lambda s: s.replace('"origin": "assay"', '"origin": "unknown"', 1),
     script("carry-check"), r"unknown carry origin", False),
    ("BUILD", "lib/quantity.ml",
     lambda s: s + "\nlet mutant () = let unused = () in ()\n",
     build, r"unused-var|unused variable unused", False),
    ("SUITE-KERNEL", "test/golden/a01-fun-app.checked",
     lambda s: s + "invalid expected checked form\n",
     ["_build/default/test/main.exe", "test"], r"SUITE-KERNEL FAIL", True),
    ("R0-former-count", "lib/term.ml",
     lambda s: replace_once(s, '[ "Lan"; "Ran" ]', '[ "Lan"; "Ran"; "KHost" ]'),
     script("r0-count"), r"R0-COUNT FAIL", True),
    ("R0-third-constructor", "lib/term.ml",
     lambda s: replace_once(s, "  | Lan of t Shape.t * t",
                           "  | KHost of t Shape.t * t\n  | Lan of t Shape.t * t"),
     build, r"KHost", False),
    ("R0-shape", "lib/shape.ml",
     lambda s: replace_once(s, "  | SNu of string * 'a list",
                           "  | SNu of string * 'a list\n  | KHost of 'a"),
     script("r0-audit"), r"KHost.*no refusal row", False),
    ("R0-walk-order", "lib/shape.ml",
     lambda s: replace_once(s, "| SPar (a, b) -> [ a; b ]",
                           "| SPar (a, b) -> [ b; a ]"),
     script("r0-diff"), r"R0-DIFF FAIL row=shape.ml", False),
    ("R0-reference", "dev/r0-diff/term.ml", lambda s: s + "(* corrupt snapshot *)\n",
     script("r0-diff"), r"reference checksum", False),
    ("AXIOMS", "corpus/id.att", lambda s: s + "\naxiom smuggled : Type 0\n",
     script("axioms-empty"), r"AXIOM smuggled", True),
    ("kernel-growth", "lib/check.ml", lambda s: s + "(* budget mutant *)\n" * 200,
     script("trusted-lines"), r"kernel=4197/4100.*FAIL", False),
]

records = []
try:
    baseline = run(script("gates"), root)
    baseline_output = baseline.stdout + baseline.stderr
    (logs / "baseline.log").write_text(baseline_output, encoding="utf-8")
    if baseline.returncode:
        raise ValueError("unmutated Stage A gates failed; see baseline.log")
    for name, relative, mutate, command, diagnostic, needs_build in cases:
        with tempfile.TemporaryDirectory(prefix="mutation-", dir=logs) as temporary:
            scratch = Path(temporary) / "tree"
            shutil.copytree(root, scratch, ignore=shutil.ignore_patterns(
                ".git", "_build", ".gatework", ".kanon-*", "__pycache__"))
            source = scratch / relative
            original = source.read_text(encoding="utf-8") if source.exists() else ""
            changed = mutate(original)
            if changed == original:
                raise ValueError(f"{name}: mutation made no change")
            source.write_text(changed, encoding="utf-8")
            if needs_build:
                built = run(build, scratch)
                (logs / (name + "-build.log")).write_text(built.stdout + built.stderr,
                                                          encoding="utf-8")
                if built.returncode:
                    raise ValueError(f"{name}: prerequisite build failed; see build log")
            result = run(command, scratch)
            output = result.stdout + result.stderr
            log = logs / (name + ".log")
            log.write_text(output, encoding="utf-8")
            caught = result.returncode != 0 and re.search(diagnostic, output) is not None
            records.append({"name": name, "path": relative, "gate": command,
                            "before_sha256": sha256(original),
                            "after_sha256": sha256(changed),
                            "exit": result.returncode, "caught": caught,
                            "diagnostic": diagnostic, "log": str(log.relative_to(root)),
                            "observed": first_match(diagnostic, output),
                            "log_sha256": sha256(output)})
            print(f"MUTATION {name} " + ("CAUGHT" if caught else "MISSED"), flush=True)
            if not caught:
                raise ValueError(f"{name}: expected a nonzero exit and {diagnostic!r}; see {log}")
    print(f"MUTATIONS caught={len(records)} total={len(cases)} OK")
    if record:
        write_record(baseline_output, records)
except (OSError, ValueError, subprocess.SubprocessError) as error:
    print(f"MUTATIONS FAIL: {error}")
    sys.exit(1)
finally:
    (logs / "results.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
