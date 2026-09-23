# Mutation log

## 2026-09-22: Lean checking corpus mutations

`python3 -P dev/lean-twin-mutations.py --record` runs thirteen mutations in
isolated corpus copies. Each starts with a passing control. The checked
driver and Lean library are reused because these mutations change only
corpus data, never compiler or library sources.

| mutation | expected failure |
| --- | --- |
| missing-row | Manifest no longer contains the required 36 rows. |
| missing-source | A paired Lean source is absent. |
| sorry | An ACCEPT source introduces an admitted term. |
| axiom | An ACCEPT source introduces a postulate. |
| refuse-accepted | The attest REFUSE declaration becomes well typed. |
| attest-prefix | The attest prefix fails before the intended refusal. |
| lean-prefix | The Lean prefix fails before the intended refusal. |
| wrong-diagnostic | Lean refuses an unknown identifier instead of the intended universe mismatch. |
| wrong-attest-diagnostic | The driver refuses a tuple without a right former instead of the intended universe mismatch. |
| wrong-attest-universe | The driver refuses a universe against `Nat` instead of against `Type 1`. |
| lean-axiom-reached | An ACCEPT source passes the token scan, and Lean reports a declaration that depends on axioms. |
| lean-sorryax | An ACCEPT source passes the token scan, and Lean rejects the `sorryAx` term under `-DwarningAsError=true`. |
| attest-refuses | An ACCEPT attest source passes the token scan, and the driver refuses it. |

All thirteen are caught. Four mutants (missing-row, missing-source, sorry,
axiom) die in the inventory check or the token scan before any compiler
runs, so their evidence is the gate refusal log alone. The other nine
reach Lean or the driver. `validation/lean-twin-mutations.json` records
passing controls, mutation hashes, expected reasons, hashes of the refusal
logs, and hashes of the actual compiler logs for the controls and for the
nine compiler-reaching mutants. This battery validates the new corpus gate and does not
claim to close the outstanding Acc or inline proof erasure mutations.


## 2026-09-22: Stage A

A fresh positive gate run passed before all 13 scratch-copy probes. Each probe required both a nonzero exit and its expected diagnostic. The scratch trees were removed after the run. Scratch outputs are under `.gatework/mutations/` (not tracked). The kept probe logs are under [validation/mutations/](validation/mutations/); hashes and exact observed diagnostics are recorded in [validation/stage-a.json](validation/stage-a.json). Regenerate both with `MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root.

| probe | changed path | exit | observed failure |
| --- | --- | --- | --- |
| PIN | `dev/PIN` | 1 | `PIN eebe37e00ecb7fdce739c49f50a6dd49c45022b0 FAIL expected=eebe37e00ecb7fdce739c49f50a6dd49c45022b1` |
| CARRY | `lib/quantity.ml` | 1 | `CARRY FAIL path=lib/quantity.ml` |
| CARRY-unlisted | `lib/unlisted.ml` | 1 | `CARRY files=594 diff=0 unlisted=1 FAIL` |
| CARRY-origin | `dev/carry-manifest.json` | 1 | `CARRY FAIL: unknown carry origin: unknown` |
| BUILD | `lib/quantity.ml` | 1 | `E lib/quantity.ml:160:20  unused-var  unused variable unused.` |
| SUITE-KERNEL | `test/golden/a01-fun-app.checked` | 1 | `SUITE-KERNEL FAIL` |
| R0-former-count | `lib/term.ml` | 1 | `R0-COUNT FAIL: spec-count exit=1: attest: spec-count: expected two formers and five shapes` |
| R0-third-constructor | `lib/term.ml` | 1 | `E lib/term.ml:102:4  partial-match  this pattern-matching is not exhaustive. Here is an example of a case that is not matched: KHost (_, _)` |
| R0-shape | `lib/shape.ml` | 1 | `SPEC.md: KHost of lib/shape.ml has no refusal row` |
| R0-walk-order | `lib/shape.ml` | 1 | `R0-DIFF FAIL row=shape.ml` |
| R0-reference | `dev/r0-diff/term.ml` | 1 | `R0-DIFF FAIL row=term.ml: reference checksum` |
| AXIOMS | `corpus/id.att` | 1 | `AXIOM smuggled` |
| kernel-growth | `lib/check.ml` | 1 | `TRUSTED-LINES kernel=4197/4100 lower=0/1100 encoder=0/800 harness=0/100 FAIL` |

The former checks use two bounded probes: extending the former inventory after a successful rebuild exercises R0-COUNT; adding a term constructor exercises exhaustive-match rejection at BUILD. This does not claim a fully routed third former. The shape probe adds a declared constructor without its refusal citation. The axiom probe adds a well-typed postulate of Type 0 to the ACCEPT example. These are the concrete probes used for the corresponding plan rows.

## 2026-09-22: Stage B erasure increment

All five mutations build successfully and then fail with the required
named diagnostic. Three are behavioral kills of the sealing code. The
fourth is an input-presence check: the gate tests that each opaque twin
exists before it reads it and names the row that lacks one. The fifth
replaces the F2 twin proof term with `sorry` and shows that the Lean leg
rejects it. The harness
uses isolated copies and first requires the unmutated erasure gate to
pass. Records and logs are in `validation/erasure-mutations.json` and
`validation/erasure-mutations/`. A row whose change is a source edit
records the hash of the mutated file as `mutated_sha256`. A row whose
change is a file removal records `mutated_sha256: null` and
`deleted: true`; no hash of empty bytes stands in for a missing file.

| probe | change | observed gate failure |
| --- | --- | --- |
| proof-guard | Disable sealing of proof definitions. | F2 function erased outputs differ. |
| row-reinsertion | Leave the declaration stream unsealed. | The carried walker restores the proof body; F2 outputs differ. |
| inherited-scope | Leave the input environment unsealed. | The opaque environment tests reject retained proof bodies. |
| missing-twin | Remove one opaque companion (recorded with `mutated_sha256: null`, `deleted: true`). | `row=f2-a opaque twin missing`, the presence check before the read. |
| lean-sorry | Replace `.refl trivial` with `sorry` in `twin/F2.lean`. | `LEAN-F2 exit=1 expected=0`: lean runs with `-DwarningAsError=true`, so the sorry warning ends the leg before the empty-log, token and axiom checks. |

The changed-proof-shape control (`fixtures/erasure/f2-a-shape.att`) agrees
with the `f2-a` body log under the new eraser. This shows that the sealing
eraser does not read the proof body. It is not a positive control for
sealing: its proof normalizes to `refl` before erasure, so the carried
eraser also prints identical output for `f2-a` and `f2-a-shape`. Any closed
proof of `Equal` without axioms normalizes to `refl` under the carried
evaluator, so no control with a closed `Layout` can differ under the
carried eraser. A proof stuck on a bound variable needs `Layout` to be a
function, which changes the runtime rows and no longer compares with
`f2-a`. The gate row reports the control as `shape_insensitive=1`. Among
the mutants, proof-guard and row-reinsertion fail earlier at row `f2-a`
(`first_diff=27`), missing-twin fails on the absent opaque twin, and
inherited-scope and lean-sorry reach the control and pass it, which shows the control
cannot discriminate. The planned Acc mutations remain open because the
carried kernel currently rejects the Acc family at checking, before
erasure.

The `ERASURE-OPEN` rows (`let-proof`, `scrutinee-proof`) are expected-different
pins, not sealing mutants: they hold while the carried walker keeps inline
proof bodies and turn red when `lib/erase.ml` seals let-bound and scrutinee
proofs. No mutant targets them yet.
