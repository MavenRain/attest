#!/usr/bin/env python3
"""Record and verify the reviewed source boundary of the OCaml-to-Bend migration.

The original carry manifest remains historical evidence. This record links its
removed files to their replacements and pins the new sources; it does not claim
that source hashes prove semantic equivalence. The differential suite does that
for the captured cases.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

REFERENCE = "ba7a65416e7786031b64dc997e9300d2741ce889"
ROOTS = ("lib", "surface", "bin", "erase", "elf", "test", "dev")
RECORD = "dev/bend-migration.json"
RETIRED_TOOLS = {"dev/house-catchalls.py", "dev/house-allow.txt", "pilot/bend2/run.py"}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def source_paths(root):
    return sorted(str(path.relative_to(root)) for folder in ROOTS
                  for path in (root / folder).rglob("*.bend"))

def replacements(path):
    name = Path(path).stem
    if path in {"dev/house-catchalls.py", "dev/house-allow.txt"}:
        return ["dev/house-bend.py", "dev/bend-source.py", "dev/bend-policy.json"], "Bend policy registry and compiler checks replace the OCaml lexical policy."
    if path.startswith("dev/r0-diff/"):
        return ["lib/foundation.bend", "lib/kernel_metadata.bend"], "Historical R0 source hashes retained; live schema checked in Bend."
    if name in {"dune", "dune-project", "dunecho"}:
        return ["dev/build.py", "Makefile"], "Build and test targets now use the pinned Bend compiler."
    if path.startswith("pilot/bend2/"):
        return ["dev/migration-differential.py", "dev/validation/ocaml-reference.json"], "The pilot oracle is superseded by the full captured compiler reference."
    if path in {"test/asm_cases.ml", "test/contract_route.ml", "test/emit_cases.ml", "test/keccak_vec.ml"}:
        return [], "Retired unbuilt module, excluded from the original test/dune module list. Existing checked and erased goldens remain in the suite."
    if path == "test/main.ml":
        return ["dev/suite_probe.bend", "dev/test-suite.py"], "All eight original groups, raw goldens and refusals retained."
    if path == "test/sys_io.ml":
        return ["surface/io.bend"], "Byte-preserving file input and explicit Result errors."
    if path == "test/sl_surface.ml":
        return ["test/surface.bend"], "Lexer, parser, elaboration and recursive-value assertions retained."
    if path.startswith("bin/"):
        return ["bin/attest.bend"], "CLI commands, streams and exit codes retained."
    if path.startswith("surface/"):
        return ["surface/" + name + ".bend"], "Surface syntax and elaboration, with explicit continuation helpers."
    if path.startswith("erase/") or path.startswith("dev/"):
        return [str(Path(path).with_suffix(".bend"))], "Erasure or development probe port."
    kernel = {
        "check": ["lib/kernel.bend", "lib/kernel_check.bend", "lib/kernel_declarations.bend"],
        "conv": ["lib/kernel_conv.bend"], "eval": ["lib/kernel_eval.bend"],
        "pp": ["lib/kernel_pp.bend"], "rules": ["lib/kernel_rules.bend"],
        "prim": ["lib/kernel_primitives.bend"], "spec_count": ["lib/kernel_metadata.bend"],
        "order": ["lib/kernel_order.bend"], "totality": ["lib/kernel_order.bend"],
        "positivity": ["lib/kernel_order.bend"],
        "erase": ["lib/erasure.bend"], "eterm": ["lib/erasure.bend"],
        "budget": ["lib/kernel_context.bend"],
    }
    if path.startswith("lib/"):
        return kernel.get(name, ["lib/foundation.bend"]), "Typed kernel and shared-data port."
    raise ValueError(f"no migration disposition for {path}")

def record(root):
    listing = subprocess.run(["git", "ls-tree", "-r", "-z", "--name-only", REFERENCE],
                             cwd=root, capture_output=True, check=True).stdout
    paths = [raw.decode() for raw in listing.split(b"\0") if raw]
    removed = []
    for path in paths:
        if path not in RETIRED_TOOLS and Path(path).suffix not in {".ml", ".mli"} and Path(path).name not in {"dune", "dune-project", "dunecho.sh"}:
            continue
        original = subprocess.run(["git", "show", f"{REFERENCE}:{path}"], cwd=root,
                                  capture_output=True, check=True).stdout
        targets, rationale = replacements(path)
        removed.append({"path": path, "sha256": digest(original),
                        "replacements": targets, "rationale": rationale})
    removed_paths = {entry["path"] for entry in removed}
    carry = json.loads((root / "dev/carry-manifest.json").read_text())
    adapted = {}
    for entry in carry["files"]:
        path = entry["path"]
        previous = entry.get("adapted_sha256", entry["source_sha256"])
        if path not in removed_paths and (root / path).is_file():
            current = digest((root / path).read_bytes())
            if current != previous:
                adapted[path] = {"original_sha256": previous, "sha256": current}
    result = {"version": 1, "reference_revision": REFERENCE,
              "carry_manifest_sha256": digest((root / "dev/carry-manifest.json").read_bytes()),
              "removed": removed,
              "adapted": adapted,
              "bend_sources": {path: digest((root / path).read_bytes()) for path in source_paths(root)}}
    (root / RECORD).write_text(json.dumps(result, indent=2) + "\n")
    print(f"MIGRATION recorded removed={len(removed)} bend={len(result['bend_sources'])}")

def validate(root):
    manifest = json.loads((root / RECORD).read_text())
    if manifest.get("version") != 1 or manifest.get("reference_revision") != REFERENCE:
        raise ValueError("unexpected Bend migration record")
    if manifest["carry_manifest_sha256"] != digest((root / "dev/carry-manifest.json").read_bytes()):
        raise ValueError("historical carry manifest changed")
    removed = {entry["path"]: entry for entry in manifest["removed"]}
    if len(removed) != len(manifest["removed"]):
        raise ValueError("duplicate migration disposition")
    for path, entry in removed.items():
        candidate = PurePosixPath(path)
        if candidate.is_absolute() or ".." in candidate.parts or str(candidate) != path:
            raise ValueError(f"invalid migration path: {path}")
        if re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is None:
            raise ValueError(f"invalid original hash: {path}")
        if (root / path).exists():
            raise ValueError(f"old implementation still present: {path}")
        for target in entry["replacements"]:
            candidate = PurePosixPath(target)
            if candidate.is_absolute() or ".." in candidate.parts or str(candidate) != target:
                raise ValueError(f"invalid replacement path: {target}")
            if not (root / target).is_file():
                raise ValueError(f"missing replacement for {path}: {target}")
    current = set(source_paths(root))
    for path, entry in manifest["adapted"].items():
        candidate = PurePosixPath(path)
        if candidate.is_absolute() or ".." in candidate.parts or str(candidate) != path:
            raise ValueError(f"invalid adapted path: {path}")
        if (root / path).is_symlink() or not (root / path).is_file() or digest((root / path).read_bytes()) != entry["sha256"]:
            raise ValueError(f"unreviewed build or gate change: {path}")
    if current != set(manifest["bend_sources"]):
        changed = sorted(current.symmetric_difference(manifest["bend_sources"]))
        raise ValueError(f"unlisted or missing Bend sources: {changed}")
    for path, expected in manifest["bend_sources"].items():
        if (root / path).is_symlink() or digest((root / path).read_bytes()) != expected:
            raise ValueError(f"unreviewed Bend source change: {path}")
    legacy = subprocess.run(["rg", "--files", "--hidden", "-g", "*.ml", "-g", "*.mli"],
                            cwd=root, capture_output=True, text=True)
    if legacy.returncode not in (0, 1):
        raise ValueError(f"OCaml source scan failed: {legacy.stderr.strip()}")
    if legacy.stdout:
        raise ValueError("OCaml sources remain: " + ", ".join(legacy.stdout.splitlines()))
    return manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("record", "check"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    if args.mode == "record":
        record(args.root.resolve())
    else:
        manifest = validate(args.root.resolve())
        print(f"MIGRATION bend={len(manifest['bend_sources'])} old-sources=0 OK")
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"MIGRATION FAIL: {error}", file=sys.stderr)
        sys.exit(1)
