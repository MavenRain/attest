#!/usr/bin/env python3
"""Report measured Stage A frontend passes; later denominators remain open."""
from pathlib import Path
import hashlib
import statistics
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
try:
    source = (root / "corpus/id.att").read_bytes()
    samples = {"parse": [], "elaborate-check": []}
    for iteration in range(8):
        result = subprocess.run([str(root / "_build/default/dev/pass_bench.exe")],
                                input=source, capture_output=True, check=True)
        rows = [line.split() for line in result.stdout.decode().splitlines()]
        if [row[0] for row in rows] != list(samples) or any(len(row) != 2 for row in rows):
            raise ValueError("invalid pass timing output")
        if iteration:
            for name, elapsed in rows:
                samples[name].append(float(elapsed))
    for name, values in samples.items():
        print(f"M0-RATIO rung=1 pass={name} ms={statistics.median(values):.6f} runs=7"
              " batch=100 clock_resolution_ms=1"
              f" corpus=corpus/id.att sha={hashlib.sha256(source).hexdigest()}")
    print("M0-RATIO rung=2 OPEN reason=denominators-not-frozen")
    print("M0-RATIO rung=3 OPEN reason=denominators-not-frozen")
except (OSError, ValueError, subprocess.SubprocessError) as error:
    print(f"M0-RATIO FAIL: {error}")
    sys.exit(1)
