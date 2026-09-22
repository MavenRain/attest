#!/usr/bin/env python3
"""Measure the four OQ4 buckets, including all source in new backend folders."""
from pathlib import Path
import sys

KERNEL = "shape term rules check value eval conv totality positivity global order bignum".split()
BUCKETS = (("lower", 1100, "lower", {".ml", ".mli"}),
           ("encoder", 800, "elf", {".ml", ".mli"}),
           ("harness", 100, "harness", {".rs"}))

def lines(path):
    return len(path.read_bytes().splitlines())

def check(root):
    counts = [("kernel", sum(lines(root / "lib" / (name + ".ml"))
                             for name in KERNEL), 4100)]
    for name, bound, folder, suffixes in BUCKETS:
        total = sum(lines(path) for path in (root / folder).rglob("*")
                    if path.is_file() and path.suffix in suffixes)
        counts.append((name, total, bound))
    good = all(count <= bound for _name, count, bound in counts)
    print("TRUSTED-LINES " + " ".join(f"{name}={count}/{bound}"
          for name, count, bound in counts) + (" OK" if good else " FAIL"))
    whole = sum(lines(path) for path in (root / "lib").glob("*.ml"))
    print(f"TRUSTED-LINES whole_lib={whole}/6193 INFO")
    return int(not good)

if __name__ == "__main__":
    try:
        sys.exit(check(Path(sys.argv[1]).resolve()))
    except OSError as error:
        print(f"TRUSTED-LINES FAIL: {error}")
        sys.exit(1)
