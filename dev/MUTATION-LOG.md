# Mutation log
## 2026-09-27: Lambda type alias mutations

Four new cases bring the erasure battery to 104. They bypass alias recovery
for lambda scopes, replace the declared binder quantity, replace the source
codomain, and wire a lambda fixture row to the wrong source pair. Each
requires a named semantic or fixture-binding failure. The prior unknown-scope
fixtures now require let reduction, preserving their original refusal checks
while transparent alias scopes become supported.

## 2026-09-26: Function type alias mutations

Eleven new cases bring the erasure battery to 100. They bypass alias recovery,
remove global or local declaration-scope checks, shift a local alias to the
wrong depth, and admit opaque, recursive, or partial definitions. Three
cases replace the hop bound with a constant 3, drop its spare hop, or return
the type when the bound is exhausted. A four-hop chain that uses every global
entry catches the first two, and a direct call with no fuel catches the third.
One case removes the globals when a local alias hop
continues, and the local-to-global chain catches it. Each
requires a specific semantic failure. Existing application and local-type
mutation anchors now distinguish type lookup from alias-body lookup.


## 2026-09-25: Application source type mutations

Five new cases bring the erasure battery to 89. They disable application
recovery, shift outer variables during substitution, remove codomain closure,
remove argument closure, and admit a nonpoint former. Each requires a named
semantic failure. Without the codomain closure guard, the walker refuses the
free codomain with a hard Source error. The guard changes that error into a
conservative None{} refusal, so this case pins the walker diagnostic. The
existing unknown-term mutation anchor now follows the application case,
preserving its original fallback diagnostic.

## 2026-09-25: Unnamed motive context mutations

Nine new cases bring the erasure battery to 84. They disable unnamed motive
recovery, give self a runtime quantity, bypass source type closure, admit
unexpected indices, admit an inductive shape, redirect a plain motive
case to a different valid fixture pair, bind self to a hardcoded `Nat`
domain, give the checker entry a different type than the Inline
parameter, and give an unsupported scrutinee term a source type. The
record shows all 84 cases caught. All nine new cases build. All except
the fixture mutation fail their named semantic rows. The four guard cases
pin the full message of the guard check that catches them. The fixture
mutation fails the gate's exact
pair binding check. The closure case removes two checks: the
`Inline.source_expected` filter and the closure check that
`Inline.bind_domain_state` does on the self domain. The second check alone
gives the same scope, so a mutation of only the filter changes only the
optional result and not the scope. With both checks removed, the plain
path evaluates the open self domain. The evaluation error replaces the
conservative root scope fallback, and the free annotation guard of
`motive-plain-guards` fails on that error state. Records and full logs
remain under `dev/validation/erasure-mutations*`.

## 2026-09-25: Named motive context mutations

Seventeen new cases join the battery: fourteen behavior mutations of the
eraser and three fixture-binding gate mutations of the semantic suite.
The fourteen behavior mutations cover resetting the motive context, dropping
self indices, corrupting index order, omitting parameter shifts, shifting
parameters by a constant one, omitting substitution, admitting free index
domains or free parameter arguments, skipping an index depth step, giving an index or self a runtime
quantity, ignoring family identity or shape arity, and ignoring parameter
arity. A fixture-binding mutation redirects a reported motive case to another
valid pair; the gate must reject it even though that substituted semantic test
passes.

Two more binding mutations cover the exempt parameterized branch pairs and
dead copies. `parameter-fixture-binding` redirects the `branch-parameter-global`
case to the `branch-parameter` pair. `fixture-binding-dead-copy` keeps the
correct `motive-index` case line in an unused definition and redirects the
live case to the `motive-self` pair. The gate rejects both.

The battery now contains 75 cases, and the record shows caught=75. Every code
mutant builds and fails its named semantic row. The three fixture-binding
mutants fail the named gate check.
The two existing branch parameter arity and argument-scope mutation anchors
include the branch-field validation expression to keep them distinct from
the new motive path. Records and full logs remain under
`dev/validation/erasure-mutations*`.


## 2026-09-24: Parameterized constructor selection and field syntax mutations

Four more probes cover the parameterized branch path. The fixture pair
`branch-parameter-ctor` has a family with two constructors of the same field
shape, and its proof is in the first constructor. The semantic row
`branch-parameter-ctor` also seals a proof in the last constructor.
`parameter-ctor-name` selects the first constructor, and
`parameter-ctor-last` selects the last constructor, in the parameterized
constructor lookup. The row must fail for each probe.

The fixture pair `branch-parameter-universe` has a proof field whose domain
contains a universe and an annotation. The semantic row
`branch-parameter-universe` compares the sealed postulate type with the type
of the opaque twin axiom. `parameter-field-quote` sends the specialized fields
through evaluation and quotation, which removes the annotation.
`parameter-source-universe` changes the universe level in the shared source
traversal. The row must fail for each probe.

The erasure battery now registers fifty-eight cases. The unmutated erasure
gate passes all 46 inline semantic rows and all 29 inline runtime comparisons.
## 2026-09-24: Parameterized constructor branch proof mutations

The erasure battery then registered fifty-four cases. Eleven new probes cover
parameter order, argument shifting, dependent field depth, parameter arity,
free arguments, local source type shifting, context fallback, function binder
depth, diagram width, family shape, and captured elimination environments.
Each new probe requires its named semantic row to fail after a successful
build. A compiler error does not count as detecting one of these mutations.

The existing constructor-name and constructor-selection probes keep their
original parameter-free targets. Their anchors now include the surrounding
call so the additional parameterized constructor lookup stays distinct.

Two more probes cover the motive half of stuck elimination quotation.
`quote-elimination-motive` keeps the unquoted motive term, and
`quote-motive-binders` opens the motive without its own binder. The
fixture motives do not read an outer binder, so the erasure rows cannot
detect these changes. Kernel unit case 17 quotes a stuck elimination whose
motive reads an outer binder that the environment binds to a literal. Each
probe must build and then fail that case. The mutation driver builds and
runs `test/kernel.exe` for these probes.

Validation: `python3 -P dev/erasure-mutations.py --record --jobs 2` catches
58/58 probes. The unmutated erasure gate passes all 46 inline semantic rows
and all 29 inline runtime comparisons. The independent Stage A battery
catches all 13 of its probes. No gate limit, refusal, or existing runtime
difference control was relaxed.
## 2026-09-24: Constructor branch proof mutations

The complete erasure battery contains 41 cases. The `local-branch-scope`
mutation now discards the recovered constructor field context and must fail
the passing `branch-scope` semantic row. Two new mutations,
`branch-field-quantity` and `branch-field-depth`, remove the field
quantity check or increase the permitted metadata variable depth. Both must
fail `branch-metadata`, which also checks missing and extra binders.
`branch-field-depth-step` increases the depth step between fields and must
fail the two-field `branch-metadata` probe. `branch-ctor-name` takes the
first constructor of the family instead of the named one, and
`branch-ctor-last` takes the last one. Each branch of the multi-constructor
pair holds a local proof over its own fields, so both must fail
`branch-multi-ctor`, which requires two sealed postulates. `branch-param-fallback` sends parameterized families
through the field check, and `branch-missing-family` accepts a branch whose
family metadata is missing. Both must fail `branch-fallback`.
`leg-scope-root` keeps the outer scope for a lambda leg without a known
domain and must fail `alias-leg-scope`.
The former open branch fixture now participates in the same opaque-twin and
carried-erasure comparisons as every other passing inline pair.
`inline-twin-repeated-arg` applies the `branch-nested` postulate to one
name twice and must fail the twin structure check. The nested pair gives
its outer binder and its two branch fields distinct types, so a permuted
application does not type-check.

The complete `--record --jobs 2` run caught all 41 variants. The resulting
record was checked against the current sources, reconstructed mutations,
stored logs and expected diagnostics before staging.



## 2026-09-23: Local inline proof mutations

Twelve compiled mutations remove the typed local context, reverse the domain
telescope, use the wrong local argument index, retain a runtime parameter,
normalize away codomain universes, corrupt domain universes, confuse a
constructor branch binder with an outer local, classify a local runtime
call from inferred readback, seal a proof let whose variable occurs in a
type annotation in its body, seal the value of such a let in a postulate type, and seal a proof let
that only the value of a type let reads, and restore the syntactic universe
test on the let type, which seals a proof let that only a later alias reads. Each must fail its named `INLINE-ERASE` semantic row. Three more
mutations edit an inline twin: one outside its proof line, one on the
proof line outside the proof span, and one that adds a source let next to
a dropped proof let, so the twin drops both. Each must fail the twin structure check.
The complete battery contains thirty-two cases. When an earlier gate
fails first, the harness also runs the compiled inline suite directly and
retains both failures before checking the named row.

The closed-proof binder row also requires whole-proof sealing. Its original
mutation remains observable even when local sealing can preserve runtime
output. The type-only and shape-payload scope controls use indirectly typed
lambdas, which remain outside the local telescope pass.


## 2026-09-23: Closed inline proof mutations

Seven added compiled mutations disable the inline pass, allow a generated
proof name to reference an existing global, ignore locals in annotation
types, reinsert original declaration rows, and drop the binder depth of
legs, motives, and shape payloads. Each must fail its named
`INLINE-ERASE` semantic test. The harness retains that test output and any
unexpected gate failure before rejecting a mutation run.

The three earlier global-sealing mutations now fail the opacity unit suite,
which runs before output comparisons. This pins the global and row
invariants even where inline sealing also prevents a layout difference.
The complete battery contains seventeen mutations. Its generated record
also hashes the inline implementation, interface, and semantic tests.



## 2026-09-23: Erased Prop index mutations

The erasure mutation battery adds five cases, for ten total. Each new
mutant must compile and reach a named failing `PROP-INDEX` regression row;
its log includes the regression output from the isolated checkout.

| mutation | change | required failing row |
| --- | --- | --- |
| prop-index-withdrawn | Restore the predicative index bound for Prop. | nat-index |
| type-index-unbounded | Remove the retained Type-family index bound. | type-index-bound |
| prop-field-quantity | Allow nonzero indexed fields above Prop. | runtime-proof-field |
| prop-field-unindexed | Allow fields without a direct result index. | unindexed-proof-field |
| prop-field-depth | Use the forward field position as its de Bruijn index. | accessibility-family |

Producer: `python3 -P dev/erasure-mutations.py --record`. The record pins
the checker, regression source and Dune stanza alongside the existing
erasure implementation, and stores before/after hashes and diagnostics for
every mutant.

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
