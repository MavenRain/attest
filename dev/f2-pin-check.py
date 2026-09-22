#!/usr/bin/env python3
"""Reproduce both F2 differences on a built, unchanged assay pin checkout."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_EXECUTABLE_SHA256 = "35d102b909bfba3a27046402ec517507ebf47ed51a9622e3fc4feaffbc0ac4f3"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked(command, cwd):
    result = subprocess.run(command, cwd=cwd, capture_output=True, timeout=30)
    if result.returncode:
        raise ValueError(f"exit={result.returncode}: {result.stderr.decode().strip()}")
    return result.stdout


def main():
    if len(sys.argv) != 2:
        print("usage: python3 -P dev/f2-pin-check.py ASSAY_PIN", file=sys.stderr)
        return 64
    try:
        pin = Path(sys.argv[1]).resolve()
        expected = (ROOT / "dev/PIN").read_text().strip()
        revision = checked(["git", "rev-parse", "HEAD"], pin).decode().strip()
        if revision != expected:
            raise ValueError("assay revision does not match dev/PIN")
        status = checked(["git", "status", "--porcelain"], pin)
        if status.strip():
            raise ValueError("assay pin worktree is not clean: " + status.decode().strip())
        executable = pin / "_build/default/bin/assay.exe"
        executable_sha256 = digest(executable.read_bytes())
        if executable_sha256 != EXPECTED_EXECUTABLE_SHA256:
            raise ValueError("pin executable digest differs from the pinned value")
        work = ROOT / ".gatework/f2-pin"
        work.mkdir(parents=True, exist_ok=True)
        logs = ROOT / "dev/validation/f2-pin"
        logs.mkdir(parents=True, exist_ok=True)
        rows = []
        for name in ("f2-a", "f2-b"):
            outputs = []
            for suffix in ("", "-opaque"):
                source = ROOT / "fixtures/erasure" / (name + suffix + ".att")
                path = work / (name + suffix + ".kan")
                path.write_bytes(source.read_bytes())
                output = checked([str(executable), "check", "--erased", str(path)], pin)
                carried = checked(["_build/default/dev/erase_probe.exe", str(source)], ROOT)
                if not output or output != carried:
                    raise ValueError(f"{name}{suffix}: pin and compiled carried eraser disagree")
                (logs / (name + suffix + ".log")).write_bytes(output)
                outputs.append(output)
                rows.append({"row": name + suffix, "source_sha256": digest(source.read_bytes()),
                             "output_sha256": digest(output)})
            if outputs[0] == outputs[1]:
                raise ValueError(f"{name}: did not reproduce F2")
        record = {"version": 1, "pin": revision, "pin_worktree": str(pin),
                  "executable_sha256": executable_sha256,
                  "script_sha256": digest(Path(__file__).read_bytes()), "rows": rows}
        (ROOT / "dev/validation/f2-pin.json").write_text(json.dumps(record, indent=2) + "\n")
        print("F2-PIN rows=2 different=2 carried_agreement=4 OK")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"F2-PIN FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
