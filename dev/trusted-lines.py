#!/usr/bin/env python3
"""Measure the four OQ4 buckets, including all source in new backend folders."""
from pathlib import Path
import sys

BUCKETS = (("lower", 1100, "lower", {".bend"}),
           ("encoder", 800, "elf", {".bend"}),
           ("harness", 100, "harness", {".rs"}))

def lines(path):
    return len(path.read_bytes().splitlines())

def check(root):
    kernel = [root / "lib/foundation.bend", *sorted((root / "lib").glob("kernel*.bend"))]
    kernel = [path for path in kernel if path.name not in {"kernel_pp.bend", "kernel_metadata.bend"}]
    # Includes shared types, explicit continuations and arbitrary-precision arithmetic.
    # The migration records the old 4100-line OCaml bound separately.
    counts = [("kernel", sum(lines(path) for path in kernel), 6000)]
    for name, bound, folder, suffixes in BUCKETS:
        total = sum(lines(path) for path in (root / folder).rglob("*")
                    if path.is_file() and path.suffix in suffixes)
        counts.append((name, total, bound))
    good = all(count <= bound for _name, count, bound in counts)
    print("TRUSTED-LINES " + " ".join(f"{name}={count}/{bound}"
          for name, count, bound in counts) + (" OK" if good else " FAIL"))
    whole = sum(lines(path) for path in (root / "lib").glob("*.bend"))
    print(f"TRUSTED-LINES whole_lib={whole} language=Bend INFO")
    return int(not good)

if __name__ == "__main__":
    try:
        sys.exit(check(Path(sys.argv[1]).resolve()))
    except OSError as error:
        print(f"TRUSTED-LINES FAIL: {error}")
        sys.exit(1)
