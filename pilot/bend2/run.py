#!/usr/bin/env python3
"""Check the Bend evaluator pilot and measure both proposed migration benefits."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "pilot/bend2"
PIN = "ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b"
VERSION = "bend 2.0.25"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Experiment:
    def __init__(self, toolchain, record):
        self.toolchain = toolchain.resolve()
        self.compiler = self.toolchain / "bin/bend"
        self.work = ROOT / ".gatework/bend-pilot"
        self.logs = ROOT / ("dev/validation/bend-pilot" if record else ".gatework/bend-pilot/logs")
        self.work.mkdir(parents=True, exist_ok=True)
        self.logs.mkdir(parents=True, exist_ok=True)
        self.env = {**os.environ, "BEND_NO_TELEMETRY": "1",
                    "BEND_LIB": str(self.work / "packages"), "CC": shutil.which("clang") or "clang"}
        self.commands = []

    def call(self, name, command, cwd=None, expected=0, env=None):
        start = time.perf_counter_ns()
        result = subprocess.run([str(x) for x in command], cwd=cwd or ROOT,
                                env=env or self.env, capture_output=True, timeout=120)
        elapsed = (time.perf_counter_ns() - start) / 1_000_000
        log = self.logs / (name + ".log")
        raw_output = result.stdout + result.stderr
        log.write_bytes(b"\n".join(line.rstrip(b" \t\r") for line in raw_output.split(b"\n")))
        self.commands.append({"name": name, "command": [str(x) for x in command],
                              "cwd": str(cwd or ROOT), "exit": result.returncode,
                              "ms": elapsed, "log_sha256": sha(log),
                              "raw_output_sha256": hashlib.sha256(raw_output).hexdigest()})
        if result.returncode != expected:
            raise ValueError(f"{name}: exit={result.returncode}, expected={expected}; see {log}")
        return result.stdout.decode(), elapsed

    def bend(self, name, source, *args, expected=0):
        return self.call(name, [self.compiler, source, *args], expected=expected)

    def pin(self):
        revision, _ = self.call("pin", ["git", "rev-parse", "HEAD"], self.toolchain)
        if revision.strip() != PIN:
            raise ValueError("Bend checkout does not match the pilot pin")
        self.call("pin-clean", ["git", "diff", "--exit-code", "HEAD", "--", "bend2"], self.toolchain)
        if not self.compiler.is_file():
            raise ValueError("build the pinned CLI first; see pilot/bend2/README.md")
        version, _ = self.call("bend-version", [self.compiler, "version"])
        if version.strip() != VERSION:
            raise ValueError("compiled Bend CLI version mismatch")
        versions = {}
        for name, cmd in (("ocaml", ["ocamlopt", "-version"]), ("dune", ["dune", "--version"]),
                          ("bun", ["bun", "--version"]), ("clang", [self.env["CC"], "--version"]),
                          ("node", ["node", "--version"])):
            output, _ = self.call(name + "-version", cmd)
            versions[name] = output.splitlines()[0]
        return {"commit": PIN, "version": version.strip(), "binary_sha256": sha(self.compiler),
                "source_sha256": {p: sha(self.toolchain / "bend2" / p)
                    for p in ("main.ts", "bend.ts", "comp.ts", "base.bend")},
                "tools": versions, "platform": platform.platform(), "machine": platform.machine()}


def generate_term(rng, depth, scope):
    choices = ["lit", "ann", "let", "let"] + (["var"] if scope else [])
    tag = rng.choice(choices) if depth else rng.choice(["lit"] + (["var"] if scope else []))
    if tag == "lit":
        return [tag, rng.choice([0, 1, 7, 42, 65535, 2147483647, 4294967295])]
    if tag == "var":
        return [tag, rng.randrange(scope)]
    if tag == "ann":
        return [tag, generate_term(rng, depth - 1, scope)]
    return [tag, generate_term(rng, depth - 1, scope), generate_term(rng, depth - 1, scope + 1)]


def render(term, language, names=()):
    tag, *args = term
    if tag == "lit":
        return {"bend": f"Core.Lit{{{args[0]}}}", "ocaml": f"Model.Lit {args[0]}",
                "attest": str(args[0])}[language]
    if tag == "var":
        return {"bend": f"Core.Var{{{args[0]}n, Unit{{}}}}", "ocaml": f"Model.Var {args[0]}",
                "attest": names[args[0]]}[language]
    if tag == "ann":
        value = render(args[0], language, names)
        return {"bend": f"Core.Ann{{{value}}}", "ocaml": f"Model.Ann ({value})",
                "attest": f"({value} : Nat)"}[language]
    name = "v" + str(len(names))
    value = render(args[0], language, names)
    body = render(args[1], language, (name, *names))
    return {"bend": f"Core.Let{{{value}, {body}}}", "ocaml": f"Model.Let ({value}, {body})",
            "attest": f"(let {name} : Nat := {value} in {body})"}[language]


def corpus(exp):
    rng = random.Random(20260922)
    terms = [["lit", 0], ["lit", 4294967295], ["let", ["lit", 7], ["var", 0]],
             ["let", ["lit", 7], ["let", ["lit", 9], ["var", 1]]]]
    terms.extend(generate_term(rng, 5, 0) for _ in range(124))
    folder = exp.work / "corpus"
    folder.mkdir(exist_ok=True)
    shutil.copyfile(SOURCE / "core.bend", folder / "core.bend")
    shutil.copyfile(SOURCE / "model.ml", folder / "model.ml")
    (folder / "terms.json").write_text(json.dumps(terms, indent=2) + "\n")
    bend = """import Base
import ./core.bend as Core
def show(result: Core.Outcome) -> String:
  match result:
    case Core.Done{value}:
      U32.show(value)
    case Core.Exhausted{}:
      "EXHAUSTED"
def main() -> IO(Unit):
  do IO<Unit>:
"""
    bend += "".join("    IO.print(show(Core.run(1024n, Core.Eval{0n, " + render(t, "bend")
                    + ", Unit{}}, Core.Halt{})))\n" for t in terms)
    (folder / "main.bend").write_text(bend)
    ocaml = "let cases = [\n" + ";\n".join(render(t, "ocaml") for t in terms) + "]\n"
    ocaml += """let () = List.iter (fun term ->
  match Model.run 1024 (Model.Eval (term, [])) Model.Halt with
  | Model.Done n -> Printf.printf "%d\\n" n
  | Model.Exhausted -> print_endline "EXHAUSTED"
  | Model.Invalid_scope -> print_endline "INVALID_SCOPE") cases
"""
    (folder / "main.ml").write_text(ocaml)
    (folder / "corpus.att").write_text("".join(f"def row{i:03d} : Nat := {render(t, 'attest')}\n"
                                               for i, t in enumerate(terms)))
    exp.call("oracle-build", ["zsh", "-f", "dev/dunecho.sh", "build"])
    oracle = ROOT / "_build/default/pilot/bend2/oracle.exe"
    if not oracle.is_file():
        raise ValueError("Dune returned without building the oracle artifact")
    expected, _ = exp.call("oracle-corpus", [oracle, folder / "corpus.att"])
    expected = [line.split(" ", 1)[1] for line in expected.splitlines()]
    if len(expected) != len(terms) or not all(x.isdigit() for x in expected):
        raise ValueError("oracle did not return every literal result")
    exp.bend("corpus-check", folder / "main.bend", "--check-only")
    exp.bend("corpus-native-build", folder / "main.bend", "-o", folder / "bend-native")
    native, _ = exp.call("corpus-native-run", [folder / "bend-native", "--threads", "1", "--gpu", "off"])
    exp.bend("corpus-js-build", folder / "main.bend", "-o", folder / "main.js")
    javascript, _ = exp.call("corpus-js-run", ["node", folder / "main.js"])
    exp.call("corpus-ocaml-build", ["ocamlopt", "-O3", "-o", "ocaml-native", "model.ml", "main.ml"], folder)
    ocaml, _ = exp.call("corpus-ocaml-run", [folder / "ocaml-native"])
    for name, output in (("Bend native", native), ("Bend JS", javascript), ("OCaml model", ocaml)):
        if output.splitlines() != expected:
            raise ValueError(name + " differs from attest's checked evaluator")
    print(f"BEND-PILOT differential={len(terms)} lanes=3 OK", flush=True)
    return {"rows": len(terms), "lanes": ["Bend native", "Bend JavaScript", "OCaml model"],
            "oracle": "attest Elab.check_in + Eval.eval + Eval.quote", "seed": 20260922,
            "corpus_sha256": sha(folder / "terms.json"), "attest_source_sha256": sha(folder / "corpus.att"),
            "oracle_binary_sha256": sha(oracle),
            "oracle_source_sha256": {str(path.relative_to(ROOT)): sha(path)
                for directory in (ROOT / "lib", ROOT / "surface")
                for path in sorted(directory.rglob("*"))
                if path.is_file() and (path.suffix in (".ml", ".mli") or path.name == "dune")}}


def guarantees(exp):
    core = (SOURCE / "core.bend").read_text()
    if "@unsafe" in core or "{!!}" in core:
        raise ValueError("the proved core must not use unsafe definitions or proof holes")
    exp.bend("proofs", SOURCE / "smoke.bend", "--check-only")
    rejected = []
    for filename, expected_type in (("closed_var.bend", "Empty"), ("environment.bend", "Unit"),
                                    ("let_scope.bend", "Empty")):
        path = SOURCE / "reject" / filename
        name = "reject-" + path.stem
        exp.bend(name, path, "--check-only", expected=1)
        diagnostic = (exp.logs / (name + ".log")).read_text()
        if "- expected : " + expected_type not in diagnostic or "Location: main" not in diagnostic:
            raise ValueError("invalid program failed for an unexpected reason: " + name)
        rejected.append(path.name)
    mutations = [
        ("lookup-head", "        case 0n:\n          head", "        case 0n:\n          0", "lookup_head"),
        ("let-value", "Eval{1n+n, body, Cell{value, env}}", "Eval{1n+n, body, Cell{0, env}}", "let_bound_value"),
    ]
    caught = []
    for name, before, after, law in mutations:
        if core.count(before) != 1:
            raise ValueError("mutation target is not unique: " + name)
        folder = exp.work / ("mutation-" + name)
        folder.mkdir(exist_ok=True)
        shutil.copyfile(SOURCE / "smoke.bend", folder / "smoke.bend")
        (folder / "core.bend").write_text(core.replace(before, after))
        exp.bend("mutation-" + name, folder / "smoke.bend", "--check-only", expected=1)
        diagnostic = (exp.logs / ("mutation-" + name + ".log")).read_text()
        if law not in diagnostic:
            raise ValueError("mutation failed without identifying its law: " + name)
        caught.append({"mutation": name, "law": law})
    print(f"BEND-PILOT laws=4 rejected={len(rejected)} mutations={len(caught)} OK", flush=True)
    return {"laws": ["lookup_head", "lookup_tail", "closed_var_impossible", "let_bound_value"],
            "invalid_programs_rejected": rejected, "proof_mutations_caught": caught,
            "unsafe_definitions": 0, "proof_holes": 0}


def project(folder, language, count=2500):
    folder.mkdir(parents=True, exist_ok=True)
    if language == "bend":
        shutil.copyfile(SOURCE / "core.bend", folder / "core.bend")
        main = (SOURCE / "runtime.bend").read_text().replace("2500n", str(count) + "n")
        (folder / "main.bend").write_text(main)
    else:
        shutil.copyfile(SOURCE / "model.ml", folder / "model.ml")
        main = (SOURCE / "runtime.ml").read_text().replace("2500", str(count))
        (folder / "main.ml").write_text(main)
        (folder / "dune-project").write_text("(lang dune 3.11)\n(name bend_pilot_benchmark)\n")
        (folder / "dune").write_text("(executable (name main) (modules model main) (ocamlopt_flags (:standard -O3)))\n")


def build(exp, folder, language, name):
    if language == "bend":
        _, elapsed = exp.bend(name, folder / "main.bend", "-o", folder / "main")
        binary = folder / "main"
    else:
        _, elapsed = exp.call(name, ["dune", "build", "main.exe", "--display=quiet"], folder,
                              env={**exp.env, "DUNE_ROOT": str(folder)})
        binary = folder / "_build/default/main.exe"
    if not binary.is_file():
        raise ValueError("build returned without the expected artifact: " + name)
    return binary, elapsed


def runtime(exp, binary, language, name, count=2500, seed=7):
    args = [binary, "--threads", "1", "--gpu", "off", "--", str(seed)] if language == "bend" else [binary, str(seed)]
    output, elapsed = exp.call(name, args)
    checksum = (count * (seed + 23) + count * (count - 1) // 2) & 0xFFFFFFFF
    if output.strip() != f"{checksum} 0":
        raise ValueError("runtime checksum or failure count differs: " + name)
    return elapsed


def timing_summary(rows):
    result = {lang: {"median_ms": statistics.median(row[lang] for row in rows),
                     "min_ms": min(row[lang] for row in rows),
                     "max_ms": max(row[lang] for row in rows)} for lang in ("bend", "ocaml")}
    result["bend_over_ocaml"] = result["bend"]["median_ms"] / result["ocaml"]["median_ms"]
    result["paired_samples_ms"] = rows
    return result


def benchmark(exp, samples):
    cold, edited = [], []
    with tempfile.TemporaryDirectory(prefix="builds-", dir=exp.work) as temporary:
        root = Path(temporary)
        for i in range(samples):
            row = {}
            for language in (("bend", "ocaml") if i % 2 == 0 else ("ocaml", "bend")):
                folder = root / ("cold-" + str(i)) / language
                project(folder, language)
                binary, row[language] = build(exp, folder, language, f"cold-{i}-{language}")
                runtime(exp, binary, language, f"cold-{i}-{language}-verify")
            cold.append(row)
        print("BEND-PILOT cold native builds measured", flush=True)
        previous = {}
        for language in ("bend", "ocaml"):
            folder = root / "edited" / language
            project(folder, language)
            binary, _ = build(exp, folder, language, "edit-warm-" + language)
            previous[language] = sha(binary)
        for i in range(samples):
            row = {}
            count = 2501 + i
            for language in (("ocaml", "bend") if i % 2 == 0 else ("bend", "ocaml")):
                folder = root / "edited" / language
                project(folder, language, count)
                binary, row[language] = build(exp, folder, language, f"edit-{i}-{language}")
                digest = sha(binary)
                if previous[language] == digest:
                    raise ValueError("an edit produced an unchanged binary: " + language)
                previous[language] = digest
                runtime(exp, binary, language, f"edit-{i}-{language}-verify", count=count)
            edited.append(row)
        print("BEND-PILOT native rebuilds after a source edit measured", flush=True)
        binaries = {}
        for language in ("bend", "ocaml"):
            folder = root / "runtime" / language
            project(folder, language)
            binaries[language], _ = build(exp, folder, language, "runtime-build-" + language)
            runtime(exp, binaries[language], language, "runtime-warm-" + language)
        execution = []
        for i in range(samples):
            row = {}
            for language in (("bend", "ocaml") if i % 2 == 0 else ("ocaml", "bend")):
                row[language] = runtime(exp, binaries[language], language, f"runtime-{i}-{language}", seed=7 + i)
            execution.append(row)
        checking = []
        for i in range(samples):
            _, elapsed = exp.bend(f"check-only-{i}", root / "runtime/bend/main.bend", "--check-only")
            checking.append(elapsed)
    return {"cold_native_build": timing_summary(cold), "edited_native_build": timing_summary(edited),
            "native_runtime": timing_summary(execution),
            "bend_check_only": {"samples_ms": checking, "median_ms": statistics.median(checking)},
            "method": {"samples": samples, "order": "alternating paired languages", "threshold_ratio": 0.9,
                       "cold": "fresh artifacts; filesystem and OS caches are not flushed",
                       "edited": "one source constant changed; binary hash and new checksum required",
                       "included": "compiler process, proof checking, optimization, native compile and link",
                       "excluded": "toolchain bootstrap, source generation, correctness runs",
                       "runtime": "single process including startup; 2500 terms, 24 nested lets, dynamic seed",
                       "bend_threads": 1, "bend_gpu": "off", "ocaml_build": "Dune native, -O3"}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bend-root", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=7)
    parser.add_argument("--record", action="store_true", help="write evidence under dev/validation")
    args = parser.parse_args()
    if args.samples < 7:
        parser.error("at least seven paired samples are required")
    exp = Experiment(args.bend_root, args.record)
    try:
        toolchain = exp.pin()
        proofs = guarantees(exp)
        differential = corpus(exp)
        timings = benchmark(exp, args.samples)
        cold_pass = timings["cold_native_build"]["bend_over_ocaml"] <= 0.9
        edited_pass = timings["edited_native_build"]["bend_over_ocaml"] <= 0.9
        sources = {str(path.relative_to(ROOT)): sha(path) for path in sorted(SOURCE.rglob("*"))
                   if path.is_file() and (path.suffix in (".bend", ".ml", ".py", ".sh") or path.name == "dune")}
        result = {"schema": 1, "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "log_normalization": "trailing spaces, tabs, and CR removed per line; raw output hashes retained",
                  "toolchain": toolchain, "source_sha256": sources, "guarantees": proofs,
                  "differential": differential, "timings": timings,
                  "verdict": {"stronger_scope_guarantees": True, "faster_cold_build": cold_pass,
                              "faster_edited_build": edited_pass,
                              "both_benefits_demonstrated": cold_pass and edited_pass,
                              "recommendation": "expand pilot" if cold_pass and edited_pass else "retain OCaml"},
                  "commands": exp.commands}
        output = ROOT / "dev/validation/bend-pilot.json" if args.record else exp.work / "result.json"
        output.write_text(json.dumps(result, indent=2) + "\n")
        print("BEND-PILOT " + json.dumps(result["verdict"], sort_keys=True), flush=True)
        for metric in ("cold_native_build", "edited_native_build", "native_runtime"):
            summary = timings[metric]
            print(f"{metric}: Bend {summary['bend']['median_ms']:.2f} ms; "
                  f"OCaml {summary['ocaml']['median_ms']:.2f} ms; ratio {summary['bend_over_ocaml']:.2f}")
        print("evidence=" + str(output))
        return 0
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print("BEND-PILOT FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
