#!/usr/bin/env python3
"""Check the paired corpus, including the declaration where each refusal occurs."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
DRIVER = "_build/default/bin/attest.exe"
COUNTS = {"accept": 24, "refuse": 12}
FORBIDDEN = re.compile(r"\b(by|sorry|admit|axiom|opaque|unsafe|partial|set_option|"
                       r"macro|elab|syntax|namespace|section|mutual|example|instance|"
                       r"abbrev|constant|initialize|native_decide|structure|class|"
                       r"deriving|attribute|open|variable|universe|noncomputable)\b")
LEAN_HEADS = r"def|theorem|inductive|structure|class|abbrev|instance|example|opaque|axiom"
ATT_HEADS = r"def|mu"
DECL = re.compile(rf"^(?:{LEAN_HEADS}) ([A-Za-z][A-Za-z0-9_]*)\b", re.M)
ATT_DECL = re.compile(rf"^(?:{ATT_HEADS}) ([A-Za-z][A-Za-z0-9_]*)\b", re.M)
LEAN_HEAD_COUNT = re.compile(rf"\b(?:{LEAN_HEADS})\b")
ATT_HEAD_COUNT = re.compile(rf"\b(?:{ATT_HEADS})\b")
AXIOM_LINE = re.compile(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])$")
ERROR_LINE = re.compile(r"^.*?:(\d+):(\d+): error: (.*)$", re.M)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def code_only(source):
    """Remove nested Lean/attest comments, preserving physical line numbers."""
    out = []
    depth = 0
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        else:
            out.append("\n" if source[i] == "\n" else " " if depth else source[i])
            i += 1
    if depth:
        raise ValueError("unclosed source comment")
    return "".join(out)


def inventory(root):
    data = json.loads((root / "lean/corpus.json").read_text())
    if set(data) != {"version", "rows"} or data["version"] != 1:
        raise ValueError("unsupported corpus manifest")
    rows = data["rows"]
    if not isinstance(rows, list) or len(rows) != sum(COUNTS.values()):
        raise ValueError("corpus must contain 24 ACCEPT and 12 REFUSE rows")
    ids = set()
    counts = dict.fromkeys(COUNTS, 0)
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("corpus row must be an object")
        expected = row.get("expected")
        keys = {"id", "topic", "expected"}
        if expected == "refuse":
            keys |= {"site", "attest_error", "lean_error"}
        if set(row) != keys or expected not in COUNTS:
            raise ValueError("invalid corpus row fields")
        if any(not isinstance(v, str) or not v.strip() for v in row.values()):
            raise ValueError("corpus row fields must be nonempty strings")
        if not re.fullmatch(r"[a-z][a-z0-9-]*", row["id"]) or row["id"] in ids:
            raise ValueError("invalid or duplicate corpus id")
        if expected == "refuse" and not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", row["site"]):
            raise ValueError("invalid refusal declaration")
        ids.add(row["id"])
        counts[expected] += 1
    if counts != COUNTS:
        raise ValueError(f"corpus counts={counts} expected={COUNTS}")
    for directory, extension in (("fixtures/lean-twin", ".att"), ("lean/Corpus", ".lean")):
        present = {p.relative_to(root / directory).as_posix()
                   for p in (root / directory).rglob("*" + extension)}
        wanted = {name + extension for name in ids}
        if present != wanted:
            raise ValueError(f"{directory} missing={sorted(wanted - present)} extra={sorted(present - wanted)}")
    return rows


def execute(root, logs, name, command, expected=0):
    result = subprocess.run(command, cwd=root, capture_output=True, timeout=60)
    (logs / (name + ".log")).write_bytes(result.stdout + result.stderr)
    if result.returncode != expected:
        raise ValueError(f"{name} exit={result.returncode} expected={expected}; log={logs / (name + '.log')}")
    return result


def lean_source(source):
    code = code_only(source)
    forbidden = FORBIDDEN.search(code)
    if forbidden or '"' in code or '#' in code:
        raise ValueError("Lean corpus requires term proofs, no axioms or commands")
    imports = re.findall(r"^import (.*)$", code, re.M)
    if imports != ["AttestTwin"]:
        raise ValueError("Lean corpus must import only AttestTwin")
    names = DECL.findall(code)
    heads = LEAN_HEAD_COUNT.findall(code)
    if not names or len(names) != len(heads) or len(names) != len(set(names)):
        raise ValueError("Lean declaration enumeration incomplete")
    return names


def attest_declarations(source):
    """Enumerate the attest head names; every def or mu keyword must start a line."""
    code = code_only(source)
    names = ATT_DECL.findall(code)
    heads = ATT_HEAD_COUNT.findall(code)
    if not names or len(names) != len(heads) or len(names) != len(set(names)):
        raise ValueError("attest declaration enumeration incomplete")
    return names


def accepted_lean(root, logs, name, source):
    names = lean_source(source)
    path = logs / (name + ".lean")
    path.write_text(source + "\n" + "".join(f"#print axioms {n}\n" for n in names))
    result = execute(root, logs, name, ["lake", "env", "lean", "-DwarningAsError=true", str(path)])
    reported = []
    for line in result.stdout.decode().splitlines():
        match = AXIOM_LINE.fullmatch(line)
        if match is None or match.group(2):
            raise ValueError(f"{name} unexpected Lean diagnostic or axiom: {line}")
        reported.append(match.group(1))
    if result.stderr or reported != names:
        raise ValueError(f"{name} axiom report incomplete: {reported} expected={names}")
    return names


def accepted_attest(root, logs, name, path):
    result = execute(root, logs, name, [DRIVER, "check", "--axioms", str(path)])
    if result.stderr or not re.search(rb"^AXIOMS .*count=0(?:\s|$)", result.stdout, re.M):
        raise ValueError(f"{name} missing empty axiom disclosure")


def refusal_prefix(source, site, lean):
    marker = f"-- REFUSE: {site}\n"
    if source.count(marker) != 1:
        raise ValueError("refusal requires exactly one declaration marker")
    prefix, suffix = source.split(marker)
    code = code_only(suffix)
    heads = (LEAN_HEAD_COUNT if lean else ATT_HEAD_COUNT).findall(code)
    keyword = "def|inductive" if lean else "def|mu"
    if len(heads) != 1 or not re.match(rf"(?:{keyword}) {re.escape(site)}\b", code):
        raise ValueError("refusal marker must precede exactly one final declaration")
    return prefix, prefix.count("\n") + 2


def check_row(root, logs, row):
    name = row["id"]
    att = root / "fixtures/lean-twin" / (name + ".att")
    lean = root / "lean/Corpus" / (name + ".lean")
    att_source, source = att.read_text(), lean.read_text()
    lean_source(source)
    if re.search(r"\baxiom\b", code_only(att_source)):
        raise ValueError(f"{name} attest row contains an axiom")
    record = {"row": name, "topic": row["topic"], "expected": row["expected"],
              "attest_sha256": digest(att.read_bytes()), "lean_sha256": digest(lean.read_bytes())}
    if row["expected"] == "accept":
        if "-- REFUSE:" in source or "-- REFUSE:" in att_source:
            raise ValueError(f"{name} ACCEPT row has a refusal marker")
        accepted_attest(root, logs, name + "-attest", att)
        record["declarations"] = accepted_lean(root, logs, name + "-lean", source)
        record["attest_declarations"] = attest_declarations(att_source)
        if record["attest_declarations"] != record["declarations"]:
            raise ValueError(f"{name} twin declarations differ: attest={record['attest_declarations']}"
                             f" lean={record['declarations']}")
    else:
        prefix_att, _ = refusal_prefix(att_source, row["site"], False)
        prefix_lean, start = refusal_prefix(source, row["site"], True)
        path = logs / (name + "-prefix.att")
        path.write_text(prefix_att)
        accepted_attest(root, logs, name + "-prefix-attest", path)
        accepted_lean(root, logs, name + "-prefix-lean", prefix_lean)
        a = execute(root, logs, name + "-attest", [DRIVER, "check", str(att)], 1)
        att_error = a.stderr.decode()
        if not att_error.startswith("attest: check: ") or row["attest_error"].lower() not in att_error.lower():
            raise ValueError(f"{name} wrong attest refusal: {att_error.strip()}")
        b = execute(root, logs, name + "-lean", ["lake", "env", "lean", "-DwarningAsError=true", str(lean)], 1)
        diagnostics = b.stdout.decode()
        errors = ERROR_LINE.findall(diagnostics)
        if (b.stderr or not errors or row["lean_error"].lower() not in diagnostics.lower()
                or any(not start <= int(line) <= len(source.splitlines()) for line, _, _ in errors)
                or "warning:" in diagnostics):
            raise ValueError(f"{name} wrong Lean refusal site or diagnostic")
        record.update(site=row["site"], prefix_accepted=True,
                      lean_error_lines=[int(line) for line, _, _ in errors])
    return record


def run(root, record=False):
    rows = inventory(root)
    logs = root / ".gatework/lean-twin"
    if logs.exists():
        shutil.rmtree(logs)
    logs.mkdir(parents=True)
    execute(root, logs, "BUILD", ["zsh", "-f", "dev/dunecho.sh", "build"])
    builder = ["leancho", "AttestTwin"] if shutil.which("leancho") else ["lake", "build", "AttestTwin"]
    execute(root, logs, "LEAN-BUILD", builder)
    version = execute(root, logs, "LEAN-TOOLCHAIN", ["lake", "env", "lean", "--version"]).stdout.decode()
    pinned = (root / "lean-toolchain").read_text().strip()
    found = re.search(r"Lean \(version ([0-9A-Za-z.\-]+)", version)
    if found is None or pinned.rsplit(":v", 1)[-1] != found.group(1):
        raise ValueError("Lean toolchain does not match lean-toolchain")
    results = []
    for row in rows:
        results.append(check_row(root, logs, row))
        print(f"LEAN-TWIN row={row['id']} {row['expected'].upper()} OK", flush=True)
    summary = f"LEAN-TWIN accept={COUNTS['accept']}/24 refuse={COUNTS['refuse']}/12 axioms=0 OK"
    print(summary, flush=True)
    if record:
        destination = root / "dev/validation/lean-twin"
        destination.mkdir(parents=True, exist_ok=True)
        hashes = {}
        for path in sorted(logs.glob("*.log")):
            shutil.copyfile(path, destination / path.name)
            hashes[path.name] = digest(path.read_bytes())
        sources = ["dev/lean_twin.py", "dev/lean-twin.sh", "lean/corpus.json",
                   "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                   "AttestTwin.lean", "AttestTwin/Core.lean", "bin/attest.ml"]
        payload = {"version": 1, "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "root": str(root), "summary": summary, "toolchain": pinned,
                   "implementation_sha256": {p: digest((root / p).read_bytes()) for p in sources},
                   "driver_sha256": digest((root / DRIVER).read_bytes()),
                   "rows": results, "log_sha256": hashes}
        (root / "dev/validation/lean-twin.json").write_text(json.dumps(payload, indent=2) + "\n")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    try:
        run(ROOT, args.record)
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"LEAN-TWIN FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
