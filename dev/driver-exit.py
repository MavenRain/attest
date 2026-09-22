#!/usr/bin/env python3
"""Exercise Stage A's public output and filesystem failure boundaries."""
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
driver = root / "_build/default/bin/attest.exe"
passed = 0

def case(name, args, code, stdout=None, stderr=None):
    global passed
    result = subprocess.run([str(driver), *args], cwd=root, capture_output=True, text=True)
    good = result.returncode == code
    if stdout is not None:
        good = good and result.stdout == stdout
    if stderr is not None:
        good = good and stderr in result.stderr
    if not good:
        print(f"DRIVER-EXIT FAIL case={name} exit={result.returncode} expected={code}")
        print(result.stdout, end="")
        print(result.stderr, end="")
        raise ValueError(name)
    passed += 1

try:
    case("check", ["check", "corpus/id.att"], 0, "CHECK corpus/id.att defs=1 ok\n")
    case("empty axioms", ["check", "--axioms", "corpus/id.att"], 0,
         "AXIOMS corpus/id.att count=0\n")
    case("postulate", ["check", "--axioms", "fixtures/axiom.att"], 0,
         "AXIOM Witness\nAXIOMS fixtures/axiom.att count=1\n")
    case("type error", ["check", "fixtures/ill-typed.att"], 1, stderr="attest: check:")
    case("missing", ["check", ".gatework/does-not-exist.att"], 64, stderr="attest: check:")
    case("suffix", ["check", "README.md"], 64, stderr="expected a .att")
    case("no args", [], 64, stderr="usage: attest")
    case("unknown verb", ["unknown"], 64, stderr="usage: attest")
    case("extra args", ["spec-count", "extra"], 64, stderr="usage: attest")
    case("duplicate flag", ["check", "--axioms", "--axioms", "corpus/id.att"], 64,
         stderr="usage: attest")
    work = root / ".gatework"
    work.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=work, prefix="driver-") as directory:
        folder = Path(directory) / "directory.att"
        folder.mkdir()
        case("directory", ["check", str(folder)], 64, stderr="attest: check:")
        source = Path(directory) / "bad syntax.att"
        source.write_text("def\n")
        case("parse error", ["check", str(source)], 1, stderr="attest: check:")
        source.write_text((root / "corpus/id.att").read_text())
        case("space in path", ["check", str(source)], 0,
             f"CHECK {source} defs=1 ok\n")
    print(f"DRIVER-EXIT pass={passed} fail=0 stage=A OK")
except (OSError, ValueError) as error:
    print(f"DRIVER-EXIT FAIL: {error}")
    sys.exit(1)
