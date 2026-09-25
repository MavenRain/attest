#!/usr/bin/env python3
"""Record the reference CLI contract, or compare a migrated executable with it."""
import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys

def digest(data):
    return hashlib.sha256(data).hexdigest()

def execute(executable, root, args, timeout=180):
    try:
        result = subprocess.run([str(executable), *args], cwd=root, capture_output=True, timeout=timeout)
        return {
            "args": args,
            "exit": result.returncode,
            "stdout": base64.b64encode(result.stdout).decode("ascii"),
            "stderr": base64.b64encode(result.stderr).decode("ascii"),
        }
    except subprocess.TimeoutExpired:
        return {"args": args, "timeout": timeout}

def canonical_digest(row):
    return digest(json.dumps(row, sort_keys=True, separators=(",", ":")).encode())

def divergence_errors(entry, matches, cases, manifest_sha):
    """Return the reasons why one divergence entry does not pin exactly one frozen reference row."""
    return ([f"matches {len(matches)} reference cases"] if len(matches) != 1 else
            ["reference manifest digest changed"] if entry["reference_manifest_sha256"] != manifest_sha else
            ["reference row digest changed"] if canonical_digest(cases[matches[0]]) != entry["reference_sha256"] else
            ["replacement args differ"] if entry["expected"]["args"] != entry["args"] else
            ["replacement equals the reference row"] if entry["expected"] == cases[matches[0]] else [])

def apply_divergences(cases, path, manifest_sha):
    """Replace each named frozen reference row with its pinned replacement row.

    Each entry must match exactly one reference case, and the digest of that case must be the
    pinned digest. The frozen reference file is not changed."""
    if not path.is_file():
        return cases, [], [], None
    data = json.loads(path.read_text())
    entries = [{**entry, "reference_manifest_sha256": data["reference_manifest_sha256"]}
               for entry in data["divergences"]]
    matches = [[index for index, row in enumerate(cases) if row["args"] == entry["args"]] for entry in entries]
    duplicates = len({json.dumps(entry["args"]) for entry in entries}) != len(entries)
    errors = [f"DIFFERENTIAL divergence {json.dumps(entry['args'])}: {problem}"
              for entry, found in zip(entries, matches)
              for problem in divergence_errors(entry, found, cases, manifest_sha)]
    errors = errors + (["DIFFERENTIAL divergence file repeats a case"] if duplicates else [])
    replaced = {found[0]: entry["expected"] for entry, found in zip(entries, matches) if len(found) == 1}
    originals = [(index, cases[index]) for index in sorted(replaced)]
    return [replaced.get(index, row) for index, row in enumerate(cases)], errors, originals, digest(path.read_bytes())

def source_files(root):
    tracked = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=True).stdout
    return sorted(path for path in tracked.decode().split("\0")
                  if path.endswith((".att", ".kan")) and path.split("/")[0] in {"test", "corpus", "fixtures", "twin"})

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("record", "retry", "compare"))
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--divergences", type=Path,
                        help="named divergences from the reference (default: dev/validation/differential-divergences.json)")
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout < 1:
        parser.error("jobs and timeout must be positive")
    root, driver = args.root.resolve(), args.driver.resolve()
    if args.mode == "record":
        if args.manifest.exists():
            parser.error("refusing to overwrite the reference manifest")
        sources = source_files(root)
        commands = [["spec-count"], [], ["unknown"], ["spec-count", "extra"], ["check", "README.md"]]
        for source in sources:
            commands.extend([["check", source], ["check", "--print", source],
                             ["check", "--axioms", source], ["build", "--erase", source]])
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            rows = list(pool.map(lambda cmd: execute(driver, root, cmd, args.timeout), commands))
        revision = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, check=True).stdout.decode().strip()
        data = {"version": 1, "reference_revision": revision,
                "reference_executable_sha256": digest(driver.read_bytes()),
                "sources": {source: digest((root / source).read_bytes()) for source in sources}, "cases": rows}
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(data, indent=2) + "\n")
        timed_out = sum("timeout" in row for row in rows)
        print(f"REFERENCE files={len(sources)} cases={len(rows)} timeouts={timed_out} manifest={args.manifest}")
        return 1 if timed_out else 0
    reference = json.loads(args.manifest.read_text())
    drift = [source for source, sha in reference["sources"].items()
             if not (root/source).is_file() or digest((root/source).read_bytes()) != sha]
    if drift:
        print(f"DIFFERENTIAL source drift: {drift}")
        return 1
    if args.mode == "retry":
        if digest(driver.read_bytes()) != reference["reference_executable_sha256"]:
            parser.error("retry requires the original reference executable")
        for index, row in enumerate(reference["cases"]):
            if "timeout" in row:
                reference["cases"][index] = execute(driver, root, row["args"], args.timeout)
        pending = sum("timeout" in row for row in reference["cases"])
        args.manifest.write_text(json.dumps(reference, indent=2) + "\n")
        print(f"REFERENCE cases={len(reference['cases'])} timeouts={pending}")
        return 1 if pending else 0
    if any("timeout" in row for row in reference["cases"]):
        print("DIFFERENTIAL reference includes unresolved timeouts")
        return 1
    manifest_sha = digest(args.manifest.read_bytes())
    divergence_path = args.divergences or root / "dev/validation/differential-divergences.json"
    cases, divergence_problems, originals, divergence_sha = apply_divergences(
        reference["cases"], divergence_path, manifest_sha)
    if divergence_problems:
        print("\n".join(divergence_problems))
        return 1
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        actual = list(pool.map(lambda row: execute(driver, root, row["args"], args.timeout), cases))
    failures = [{"expected": want, "actual": got}
                for want, got in zip(cases, actual) if want != got]
    # A divergence that the driver no longer needs is stale and fails the run.
    stale = [row["args"] for index, row in originals if actual[index] == row]
    report = {"passed": len(actual)-len(failures), "total": len(actual), "failures": failures,
              "driver_sha256": digest(driver.read_bytes()),
              "jobs": args.jobs, "timeout_seconds": args.timeout,
              "reference_manifest_sha256": manifest_sha,
              "divergences": len(originals), "divergences_sha256": divergence_sha,
              "stale_divergences": stale}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"DIFFERENTIAL pass={report['passed']} total={report['total']} fail={len(failures)} "
          f"divergences={len(originals)} stale={len(stale)}")
    for row in failures[:8]:
        print("FAIL", json.dumps(row["expected"]["args"]))
    for row in stale:
        print("STALE-DIVERGENCE", json.dumps(row))
    return 1 if failures or stale else 0

if __name__ == "__main__":
    sys.exit(main())
