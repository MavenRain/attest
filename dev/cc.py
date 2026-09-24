#!/usr/bin/env -S python3 -P
"""Select C optimization without modifying the pinned Bend compiler."""
import os
from pathlib import Path
import shutil
import sys

compiler = os.environ.get("ATTEST_CC") or shutil.which("clang")
optimization = os.environ.get("ATTEST_C_OPT", "3")
if optimization not in {"0", "1", "2", "3", "s"}:
    sys.exit("ATTEST_C_OPT must be 0, 1, 2, 3, or s")
if not compiler or Path(compiler).resolve() == Path(__file__).resolve():
    sys.exit("ATTEST_CC must name a real Clang executable")
arguments = [f"-O{optimization}" if item == "-O3" else item for item in sys.argv[1:]]
os.execvp(compiler, [compiler, *arguments])
