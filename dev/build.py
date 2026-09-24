#!/usr/bin/env python3
"""Build attest with the pinned Bend compiler and cache by transitive source hashes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
TARGETS = {
    "attest": ("bin/attest.bend", "bin/attest.exe"),
    "foundation": ("test/foundation.bend", "test/foundation.exe"),
    "global-map": ("test/global_map.bend", "test/global_map.exe"),
    "order": ("test/order.bend", "test/order.exe"),
    "kernel": ("test/kernel.bend", "test/kernel.exe"),
    "surface": ("test/surface.bend", "test/sl_surface.exe"),
    "ir": ("erase/test/ir_test.bend", "erase/test/ir_test.exe"),
    "repr": ("erase/test/repr_test.bend", "erase/test/repr_test.exe"),
    "inline-scan": ("erase/test/inline_scan.bend", "erase/test/inline_scan.exe"),
    "inline-sealing": ("erase/test/inline_sealing.bend", "erase/test/inline_sealing.exe"),
    "opaque-core": ("erase/test/opaque_core.bend", "erase/test/opaque_core.exe"),
    "erasure-budget": ("erase/test/budget_test.bend", "erase/test/budget_test.exe"),
    "erasure-refusal": ("erase/test/refusal_test.bend", "erase/test/refusal_test.exe"),
    "inline": ("erase/test/inline_test.bend", "erase/test/inline_test.exe"),
    "opaque": ("erase/test/opaque_test.bend", "erase/test/opaque_test.exe"),
    "prop-index": ("erase/test/prop_index.bend", "erase/test/prop_index.exe"),
    "parse-probe": ("dev/parse_probe.bend", "dev/parse_probe.exe"),
    "erase-probe": ("dev/erase_probe.bend", "dev/erase_probe.exe"),
    "pass-bench": ("dev/pass_bench.bend", "dev/pass_bench.exe"),
    "suite-probe": ("dev/suite_probe.bend", "dev/suite_probe.exe"),
}
IMPORT = re.compile(r"^import[^\S\n]+(\S+\.bend)(?:[^\S\n]+as[^\S\n]+\w+)?[^\S\n]*(?:(?://|#)[^\n]*)?$", re.M)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def dependencies(source, seen=None):
    seen = set() if seen is None else seen
    source = source.resolve()
    if source in seen:
        return seen
    if ROOT not in source.parents:
        raise ValueError(f"source import escapes the repository: {source}")
    seen.add(source)
    for imported in IMPORT.findall(source.read_text()):
        dependencies(source.parent / imported, seen)
    return seen

def compiler():
    pin = json.loads((ROOT / "dev/bend-toolchain.json").read_text())
    checkout = Path(os.environ.get("ATTEST_BEND_ROOT", ROOT / "_tools/bend")).resolve()
    if not (checkout / "bend2/main.ts").is_file():
        raise ValueError("pinned Bend checkout missing; run sh dev/setup-bend.sh or set ATTEST_BEND_ROOT")
    revision = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True).stdout.strip()
    if revision != pin["revision"]:
        raise ValueError(f"Bend revision {revision} differs from pin {pin['revision']}")
    for command in (["git", "-C", str(checkout), "diff", "--quiet"],
                    ["git", "-C", str(checkout), "diff", "--cached", "--quiet"]):
        if subprocess.run(command).returncode:
            raise ValueError("pinned Bend checkout has modified tracked sources")
    binary = checkout / "bin/bend"
    if binary.is_file() and os.access(binary, os.X_OK):
        command = [str(binary)]
        compiler_hash = digest(binary.read_bytes())
    else:
        bun = shutil.which("bun")
        if not bun:
            raise ValueError("Bun is required to run the pinned Bend compiler")
        command = [bun, str(checkout / "bend2/main.ts")]
        compiler_hash = digest(subprocess.run([bun, "--version"], capture_output=True, check=True).stdout)
    return command, pin["revision"], compiler_hash

def activate(name, backend, output):
    launcher = ROOT / "_build/default" / TARGETS[name][1]
    launcher.parent.mkdir(parents=True, exist_ok=True)
    relative = os.path.relpath(output, launcher.parent)
    runtime = '"${ATTEST_JS_RUNTIME:-bun}" ' if backend == "js" else ""
    script = (f"#!/bin/sh\n# Bend {backend} sha256:{digest(output.read_bytes())}\n"
              + 'exec ' + runtime + '"$(dirname -- "$0")/' + relative + '" "$@"\n')
    if not launcher.is_file() or launcher.read_bytes() != script.encode():
        launcher.write_bytes(script.encode())
    launcher.chmod(0o755)

def build(name, backend, check_only, command, revision, compiler_hash):
    source_name, output_name = TARGETS[name]
    source = ROOT / source_name
    output = ROOT / "_build" / backend / output_name
    if backend == "js":
        output = output.with_suffix(".js")
    source_hashes = {str(path.relative_to(ROOT)): digest(path.read_bytes())
                     for path in sorted(dependencies(source))}
    fingerprint = digest(json.dumps({"sources": source_hashes, "revision": revision,
        "compiler": compiler_hash, "backend": backend, "builder": digest(Path(__file__).read_bytes()),
        "cc_wrapper": digest((ROOT / "dev/cc.py").read_bytes()),
        "c_optimization": os.environ.get("ATTEST_C_OPT", "3") if backend == "native" else None,
        "c_compiler": os.environ.get("ATTEST_CC", os.environ.get("CC", "clang"))},
        sort_keys=True).encode())
    stamp = output.with_suffix(output.suffix + ".json")
    if not check_only and output.is_file() and stamp.is_file():
        previous = json.loads(stamp.read_text())
        if previous.get("fingerprint") == fingerprint and previous.get("output_sha256") == digest(output.read_bytes()):
            activate(name, backend, output)
            print(f"BUILD {name} {backend} cached", flush=True)
            return
    output.parent.mkdir(parents=True, exist_ok=True)
    logs = ROOT / ".gatework/build"
    logs.mkdir(parents=True, exist_ok=True)
    log = logs / f"{name}-{backend}{'-check' if check_only else ''}.log"
    temporary = output.with_name(output.stem + ".building" + output.suffix)
    arguments = [*command, str(source), "--check-only"] if check_only else [*command, str(source), "-o", str(temporary)]
    env = {**os.environ, "BEND_NO_TELEMETRY": "1", "BEND_LIB": str(ROOT / "_build/bend-cache"),
           "ATTEST_CC": os.environ.get("ATTEST_CC", os.environ.get("CC", shutil.which("clang") or "clang")),
           "CC": str(ROOT / "dev/cc.py")}
    print(f"BUILD {name} {backend} {'check' if check_only else 'compile'}", flush=True)
    result = subprocess.run(arguments, cwd=ROOT, capture_output=True, env=env)
    log.write_bytes(result.stdout + result.stderr)
    if result.returncode:
        sys.stderr.buffer.write(result.stdout + result.stderr)
        raise ValueError(f"{name} {backend} exit={result.returncode}; log={log.relative_to(ROOT)}")
    current_hashes = {str(path.relative_to(ROOT)): digest(path.read_bytes())
                      for path in sorted(dependencies(source))}
    if current_hashes != source_hashes:
        temporary.unlink(missing_ok=True)
        raise ValueError(f"{name}: sources changed during compilation; rerun the build")
    if not check_only:
        temporary.replace(output)
        stamp.write_text(json.dumps({"fingerprint": fingerprint, "output_sha256": digest(output.read_bytes()),
            "revision": revision, "sources": source_hashes}, indent=2) + "\n")
        activate(name, backend, output)
    print(f"BUILD {name} {backend} OK", flush=True)

def activate_suite():
    launcher = ROOT / "_build/default/test/main.exe"
    launcher.parent.mkdir(parents=True, exist_ok=True)
    launcher.write_text('#!/bin/sh\nexec python3 -P "$(dirname "$0")/../../.."/dev/test-suite.py "$@"\n')
    launcher.chmod(0o755)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", choices=tuple(TARGETS))
    parser.add_argument("--backend", choices=("native", "js", "both"), default="js")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.backend in {"js", "both"} and not shutil.which(os.environ.get("ATTEST_JS_RUNTIME", "bun")):
        parser.error("Bun is required by Bend's JavaScript file I/O runtime")
    command, revision, compiler_hash = compiler()
    backends = ("native", "js") if args.backend == "both" else (args.backend,)
    for name in args.targets or TARGETS:
        for backend in backends:
            build(name, backend, args.check, command, revision, compiler_hash)
    if not args.check:
        activate_suite()
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"BUILD FAIL: {error}", file=sys.stderr)
        sys.exit(1)
