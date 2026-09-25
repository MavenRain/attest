#!/usr/bin/env python3
"""Run Stage A gates, stopping immediately on a failed command or contract."""
from pathlib import Path
import os
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
logs = root / ".gatework/stage-a"
logs.mkdir(parents=True, exist_ok=True)

def run(name, command, *, quiet=False, env=None):
    result = subprocess.run(command, cwd=root, capture_output=True, text=True, env=env)
    (logs / (name + ".log")).write_text(result.stdout + result.stderr)
    if not quiet or result.returncode:
        print(result.stdout, end="")
        print(result.stderr, end="")
    if result.returncode:
        raise ValueError(f"{name} exit={result.returncode}; log={logs / (name + '.log')}")
    return result.stdout

def script(name, path):
    return run(name, ["zsh", "-f", "dev/" + path + ".sh"])

def quote_depth(depth=24, bound=10):
    """Check a chain of stuck lets: quoting a stuck elimination must not copy its whole environment."""
    lets = "".join(f"let y{i} : Type 0 := case b as s in B return Type 0 with | tt => {'B' if i == 1 else f'y{i - 1}'} | ff => B in "
                   for i in range(1, depth + 1))
    path = logs / "quote-depth.att"
    path.write_text("mu B : Type 0 with\n| tt : B\n| ff : B\n\n"
                    f"def Y : (b : B) -> Type 0 := fun (b : B) => {lets}y{depth}\n"
                    "def keep : (b : B) -> (x : Y b) -> Y b := fun (b : B) => fun (x : Y b) => x\n")
    try:
        result = subprocess.run(["_build/default/bin/attest.exe", "check", str(path)], cwd=root,
                                capture_output=True, text=True, timeout=bound)
    except subprocess.TimeoutExpired:
        raise ValueError(f"QUOTE-DEPTH depth={depth} took more than {bound} s")
    if result.returncode or result.stderr:
        raise ValueError(f"QUOTE-DEPTH exit={result.returncode}: {result.stdout}{result.stderr}")
    print(f"QUOTE-DEPTH depth={depth} bound_s={bound} OK")

try:
    run("BUILD", ["python3", "-P", "dev/build.py"])
    print("BUILD OK")
    for name, path in (("CARRY", "carry-check"), ("R0-COUNT", "r0-count"),
                       ("R0-AUDIT", "r0-audit"), ("R0-DIFF", "r0-diff"),
                       ("HOUSE", "house"), ("DRIVER-EXIT", "driver-exit")):
        script(name, path)
    suite = run("SUITE-KERNEL", ["_build/default/test/main.exe", "test"], quiet=True)
    counts = re.findall(r"^[A-Z-]+-OK (\d+)/(\d+)$", suite, re.M)
    if "SUITE-KERNEL OK\n" not in suite or len(counts) != 8:
        raise ValueError("SUITE-KERNEL incomplete group output")
    passed = sum(int(have) for have, _want in counts)
    total = sum(int(want) for _have, want in counts)
    if passed != total:
        raise ValueError(f"SUITE-KERNEL pass={passed} fail={total - passed}")
    bench = run("BENCH", ["zsh", "-f", "dev/bench.sh", "SUITE-KERNEL",
                         "_build/default/test/main.exe test"],
                env={**os.environ, "RUNS": "7"})
    median = re.search(r"median_ms=([0-9.]+)", bench)
    if median is None:
        raise ValueError("SUITE-KERNEL missing benchmark median")
    print(f"SUITE-KERNEL pass={passed} fail=0 median_ms={median.group(1)} OK")
    run("SURFACE", ["_build/default/test/sl_surface.exe"])
    quote_depth()
    script("AXIOMS-empty", "axioms-empty")
    script("TRUSTED-LINES", "trusted-lines")
    script("M0-RATIO", "ratio")
    print("STAGE-A OK")
except (OSError, ValueError) as error:
    print(f"STAGE-A FAIL: {error}")
    sys.exit(1)
