#!/usr/bin/env python3
"""Mutate isolated copies of the erasure increment and require named failures."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SOURCE = "erase/opaque.ml"
KERNEL = "lib/check.ml"
INLINE = "erase/inline.ml"
CASES = (
    ("proof-guard", SOURCE, "if List.mem name names then",
     "if List.mem name names && false then", "OPAQUE-ERASE exit=1"),
    ("row-reinsertion", SOURCE,
     "let rows = List.map (fun (name, entry) -> (name, seal names name entry)) rows in",
     "let rows = rows in", "OPAQUE-ERASE exit=1"),
    ("inherited-scope", SOURCE,
     "Global.StringMap.mapi (seal names) globals.Global.entries",
     "Global.StringMap.mapi (fun name entry -> let _ = seal names name entry in entry) globals.Global.entries",
     "OPAQUE-ERASE exit=1"),
    ("inline-walker", SOURCE,
     "Inline.prepare (Check.make globals budget) opaque rows", "Ok (opaque, rows)",
     "INLINE-ERASE row=let-body FAIL"),
    ("inline-name-collision", INLINE,
     "if Option.is_some (Global.find name state.globals)",
     "if false && Option.is_some (Global.find name state.globals)",
     "INLINE-ERASE row=name-collision FAIL"),
    ("inline-local-type", INLINE,
     "closed depth value && closed depth ty", "closed depth value && (closed depth ty || true)",
     "INLINE-ERASE row=local-type FAIL"),
    ("inline-row-reinsertion", INLINE,
     "Result.map (fun entry -> (name, entry))", "Result.map (fun _entry -> (name, _original))",
     "INLINE-ERASE row=rows FAIL"),
    ("inline-leg-binders", INLINE,
     "closed (depth + List.length leg.Term.l_binders) leg.Term.l_body",
     "closed depth leg.Term.l_body", "INLINE-ERASE row=binders FAIL"),
    ("inline-motive-binders", INLINE,
     "closed (depth + List.length m.Term.m_idx + 1) m.Term.m_body",
     "closed depth m.Term.m_body", "INLINE-ERASE row=motive FAIL"),
    ("inline-shape-payload", INLINE,
      "let shape s = List.for_all (closed depth) (Shape.payload s) in",
      "let shape _s = true in", "INLINE-ERASE row=shape-payload FAIL"),
    ("local-context", INLINE,
     "let* context = bind_domain context name q domain in",
     "let* context = bind_domain context name q domain |> Result.map root in",
     "INLINE-ERASE row=local-index FAIL"),
    ("local-domain-order", INLINE, "ty context.domains", "ty (List.rev context.domains)",
     "INLINE-ERASE row=local-dependent FAIL"),
    ("local-argument-depth", INLINE,
     "Term.APt (Quantity.Zero, Term.Var ix)", "Term.APt (Quantity.Zero, Term.Var 0)",
     "INLINE-ERASE row=local-dependent FAIL"),
    ("local-argument-quantity", INLINE,
     "Rules.arrow Quantity.Zero name domain body", "Rules.arrow Quantity.One name domain body",
     "INLINE-ERASE row=local-dependent FAIL"),
    ("local-codomain-universe", INLINE,
     "Ok (Some (context, codomain))",
     "let* value = Eval.eval context.checker.Check.globals context.checker.Check.env codomain in\n"
     "                 let* codomain = Eval.quote context.checker.Check.globals context.checker.Check.size value in\n"
     "                 Ok (Some (context, codomain))",
     "INLINE-ERASE row=local-universe FAIL"),
    ("local-domain-universe", INLINE,
     "Rules.arrow Quantity.Zero name domain body",
     "Rules.arrow Quantity.Zero name (let _ = domain in Rules.unit_ty Level.zero) body",
     "INLINE-ERASE row=local-universe FAIL"),
    ("local-branch-scope", INLINE,
     "let checker = if leg.Term.l_binders = [] then checker else root checker in",
     "let checker = checker in", "INLINE-ERASE row=branch-scope FAIL"),
    ("local-inferred-universe", INLINE,
     "if not (closed 0 term) then Ok None", "if not (closed checker.Check.size term) then Ok None",
     "INLINE-ERASE row=local-runtime-call FAIL"),
    ("local-proof-let", INLINE,
     "if not (closed checker.Check.size domain && typed 0 body) then Ok false",
     "if not (closed checker.Check.size domain && typed 0 body && false) then Ok false",
     "INLINE-ERASE row=local-proof-let FAIL"),
    ("local-proof-let-value", INLINE,
     "if proof then Ok (value, state) else term context state (Some domain) value in",
     "term context state (Some domain) value in",
     "INLINE-ERASE row=local-proof-let-value FAIL"),
    ("local-proof-let-type", INLINE,
     "occurs target ty || occurs target value",
     "occurs target ty || (occurs target value && false)",
     "INLINE-ERASE row=local-proof-let-type FAIL"),
    # A syntactic universe test on the let type seals a proof let that only
    # a later proof let alias reads.
    ("local-proof-let-alias", INLINE,
     "occurs target ty || occurs target value",
     "occurs target ty || ((match ty with Term.Univ _ -> true | Term.Var _ | Term.Global _ | Term.Lit _ | Term.Auto | Term.Lan _ | Term.Ran _ | Term.In _ | Term.Out _ | Term.Sec _ | Term.Elim _ | Term.Let _ | Term.Ann _ -> false) && occurs target value)",
     "INLINE-ERASE row=local-proof-let-alias FAIL"),
    # A twin edit outside the proof line keeps the runtime output, so only the
    # twin structure check can refuse it.
    ("inline-twin-extra-edit", "fixtures/erasure/local-let-opaque.att",
     "| refl : (0 n : Nat) -> Equal n", "| refl : (0 m : Nat) -> Equal m",
     "row=local-let opaque twin changes more than its proof"),
    # A twin edit on the proof line but outside the proof span keeps the
    # runtime output, so only the token comparison can refuse it.
    ("inline-twin-same-line-edit", "fixtures/erasure/local-let-opaque.att",
     "case proof n as p in Equal k", "case proof n as r in Equal k",
     "row=local-let opaque twin changes more than its proof"),
    # A source let next to the dropped proof let makes the twin drop both.
    # The runtime output is kept, so only the token comparison can refuse it.
    ("inline-twin-adjacent-let-drop", "fixtures/erasure/let-proof.att",
     ":= refl in case p", ":= refl in let u : Type 0 := Nat in case p",
     "row=let-proof opaque twin changes more than its proof"),
    # The gate tests the presence of every opaque twin before it reads it, so the
    # pin is the gate's named diagnostic and not a missing-file errno.
    ("missing-twin", "fixtures/erasure/f2-a-opaque.att", None, None,
     "row=f2-a opaque twin missing"),
    # The twin gate runs lean with -DwarningAsError=true, so a sorry ends the
    # LEAN-F2 leg on exit 1 before the empty-log and axiom checks run.
    ("lean-sorry", "twin/F2.lean", "def proof : AttestTwin.Equal := .refl trivial",
     "def proof : AttestTwin.Equal := sorry", "LEAN-F2 exit=1 expected=0"),
    ("prop-index-withdrawn", KERNEL,
     "if Level.equal level Level.zero || Level.le l level then Ok ()",
     "if Level.le l level then Ok ()", "PROP-INDEX row=nat-index FAIL"),
    ("type-index-unbounded", KERNEL,
     "if Level.equal level Level.zero || Level.le l level then Ok ()",
     "if Level.le l l then Ok ()", "PROP-INDEX row=type-index-bound FAIL"),
    ("prop-field-quantity", KERNEL,
     "&& Quantity.equal q Quantity.Zero",
     "&& (Quantity.equal q Quantity.Zero || true)",
     "PROP-INDEX row=runtime-proof-field FAIL"),
    ("prop-field-unindexed", KERNEL,
     "&& List.exists (parameter_at index) cd.ct_res_idx",
     "&& (List.exists (parameter_at index) cd.ct_res_idx || true)",
     "PROP-INDEX row=unindexed-proof-field FAIL"),
    ("prop-field-depth", KERNEL,
     "(depth - i - 1, field)", "(i, field)",
     "PROP-INDEX row=accessibility-family FAIL"),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(root, command):
    return subprocess.run(command, cwd=root, capture_output=True, timeout=90)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    logs = ROOT / ("dev/validation/erasure-mutations" if args.record else ".gatework/erasure-mutations")
    logs.mkdir(parents=True, exist_ok=True)
    scratch_root = ROOT / ".gatework/erasure-copies"
    scratch_root.mkdir(parents=True, exist_ok=True)
    try:
        baseline = run(ROOT, ["python3", "-P", "dev/erasure-gates.py"])
        (logs / "baseline.log").write_bytes(baseline.stdout + baseline.stderr)
        if baseline.returncode != 0:
            raise ValueError("unmutated erasure gate failed")
        records = []
        for name, relative, before, after, diagnostic in CASES:
            with tempfile.TemporaryDirectory(dir=scratch_root, prefix=name + "-") as directory:
                scratch = Path(directory) / "tree"
                shutil.copytree(ROOT, scratch, ignore=shutil.ignore_patterns(
                    ".git", "_build", ".lake", ".gatework", ".kanon-*", "__pycache__"))
                path = scratch / relative
                original = path.read_bytes()
                if before is None:
                    path.unlink()
                    changed = None
                else:
                    source = original.decode()
                    if source.count(before) != 1:
                        raise ValueError(f"{name}: mutation anchor is not unique")
                    changed = source.replace(before, after, 1).encode()
                    path.write_bytes(changed)
                build = run(scratch, ["zsh", "-f", "dev/dunecho.sh", "build"])
                (logs / (name + "-build.log")).write_bytes(build.stdout + build.stderr)
                if build.returncode:
                    raise ValueError(f"{name}: build failed, not a caught behavior mutation")
                result = run(scratch, ["python3", "-P", "dev/erasure-gates.py"])
                output = result.stdout + result.stderr
                (logs / (name + ".log")).write_bytes(
                    output.replace(str(scratch).encode(), b"<mutation-tree>"))
                if diagnostic.startswith("PROP-INDEX row="):
                    if b"PROP-INDEX exit=1 expected=0" not in output:
                        raise ValueError(f"{name}: did not reach the Prop index regression")
                    output += (scratch / ".gatework/erasure/PROP-INDEX.log").read_bytes()
                if diagnostic.startswith("INLINE-ERASE row="):
                    if b"INLINE-ERASE exit=1 expected=0" in output:
                        output += (scratch / ".gatework/erasure/INLINE-ERASE.log").read_bytes()
                    else:
                        # An earlier gate can fail on the same fault. Also require
                        # the named semantic regression in the compiled mutant.
                        unit = run(scratch, ["_build/default/erase/test/inline_test.exe"])
                        output += b"\nINLINE-ERASE direct regression:\n" + unit.stdout + unit.stderr
                        (logs / (name + ".log")).write_bytes(
                            output.replace(str(scratch).encode(), b"<mutation-tree>"))
                        if unit.returncode != 1:
                            raise ValueError(f"{name}: inline proof regression exit={unit.returncode}")
                # A temporary checkout path is not part of a diagnostic's identity.
                output = output.replace(str(scratch).encode(), b"<mutation-tree>")
                (logs / (name + ".log")).write_bytes(output)
                if result.returncode != 1 or diagnostic.encode() not in output:
                    raise ValueError(f"{name}: expected named gate failure {diagnostic!r}")
                records.append({"name": name, "path": relative, "before_sha256": digest(original),
                    "mutated_sha256": None if changed is None else digest(changed),
                    "log_sha256": digest(output),
                    "build_exit": build.returncode, "gate_exit": result.returncode,
                    "diagnostic": diagnostic, **({"deleted": True} if changed is None else {})})
                print(f"ERASURE-MUTATION {name} caught")
        if args.record:
            record = {"version": 1, "baseline_sha256": digest(baseline.stdout + baseline.stderr),
                      "implementation_sha256": {p: digest((ROOT / p).read_bytes()) for p in
                        (SOURCE, INLINE, "erase/inline.mli", KERNEL,
                         "erase/test/prop_index.ml", "erase/test/dune",
                         "erase/test/opaque_test.ml", "erase/test/inline_test.ml",
                         "dev/erasure-mutations.py", "dev/erasure-gates.py")},
                      "mutations": records}
            (ROOT / "dev/validation/erasure-mutations.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"ERASURE-MUTATIONS caught={len(records)} total={len(CASES)} OK")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"ERASURE-MUTATIONS FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
