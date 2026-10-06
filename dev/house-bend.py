#!/usr/bin/env python3
"""Enforce the Bend equivalents of the seven HOUSE rules."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys

def check(root):
    source = runpy.run_path(str(root / "dev/bend-source.py"))
    paths = source["paths"](root)
    cleaned = {str(path.relative_to(root)): source["code"](path.read_text()) for path in paths}
    failures = []

    def report(name, errors):
        print(f"HOUSE {name} " + ("FAIL" if errors else "OK"))
        for error in errors:
            print(error)
        failures.extend(errors)

    def scan(pattern, selected=None):
        return [f"{path}:{number}:{line.strip()}" for path, text in cleaned.items()
                if selected is None or selected(path)
                for number, line in enumerate(text.splitlines(), 1) if re.search(pattern, line)]

    policy = json.loads((root / "dev/bend-policy.json").read_text())
    sites = source["policy_sites"](root)
    site_errors = []
    for kind in ("catchalls", "unsafe"):
        actual = Counter(json.dumps(row, sort_keys=True) for row in sites[kind])
        allowed = Counter(json.dumps(row, sort_keys=True) for row in policy[kind])
        site_errors.extend(f"{kind}: unregistered {row}" for row in sorted((actual - allowed).elements()))
        site_errors.extend(f"{kind}: stale policy entry {row}" for row in sorted((allowed - actual).elements()))
    report("no-exception", scan(r"(?<![\w.])(?:raise|throw|panic|assert|try|catch)\b|\b(?:Result|Maybe)\.unwrap\b") + site_errors)
    pure = lambda path: path.startswith(("lib/", "erase/", "elf/")) and "/test/" not in path
    report("no-mutable-state", scan(r"\b(?:IO|File|Ref)\.|\b(?:mutable|foreign)\b|@(?:ffi|extern)\b", pure))
    print("HOUSE no-mutable-state roots=lib erase elf")

    io_errors = scan(r"\bFile\.(?:open|read_bytes|close)\b", lambda path: path != "surface/io.bend")
    io = cleaned.get("surface/io.bend", "")
    if "IO(Result<" not in io or not all(token in io for token in ("case Fail{", "case Done{", "File.close")):
        io_errors.append("surface/io.bend: missing explicit file Result boundary")
    report("result-io-boundary", io_errors)

    if failures:
        report("exhaustive-types", ["source policy failed before Bend checking"])
    else:
        result = subprocess.run([sys.executable, "-P", str(root / "dev/build.py"), "--check", "attest"],
                                cwd=root, capture_output=True, text=True)
        logs = root / ".gatework"
        logs.mkdir(exist_ok=True)
        (logs / "house-check.log").write_text(result.stdout + result.stderr)
        report("exhaustive-types", [] if result.returncode == 0 else [f"Bend check exit={result.returncode}; .gatework/house-check.log"])

    prose = subprocess.run(["rg", "-n", "--glob", "!vendor", "--glob", "!**/vendor/**",
        "--glob", "!_build", "--glob", "!**/_build/**", "--glob", "!_tools",
        "--glob", "!design", "--glob", "!**/design/**", chr(0x2014), str(root)],
        capture_output=True, text=True)
    report("no-em-dash", [] if prose.returncode == 1 else
           [prose.stdout.replace(str(root) + "/", "") or prose.stderr or f"rg exit={prose.returncode}"])
    report("no-loop-keyword", scan(r"\b(?:for|while)\b"))
    division = []
    for path, text in cleaned.items():
        for number, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("import "):
                continue
            for match in re.finditer(r"(?:/|%)\s*([^\s,)]+)", line):
                value = match.group(1).removesuffix("n")
                if not value.isdecimal() or int(value) == 0:
                    division.append(f"{path}:{number}: divisor requires an explicit nonzero proof: {match.group(1)}")
    report("nonzero-division", division)
    print("HOUSE " + ("FAIL" if failures else "OK"))
    return int(bool(failures))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    return check(args.root.resolve())

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print(f"HOUSE FAIL: {error}")
        sys.exit(1)
