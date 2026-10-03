# Mutation log

## 2026-10-03: Nested constructors in payload fixture mutations

Two fixture binding mutations replace the nested-first or nested-last semantic
variant with the ordinary source pair check. Two recovery mutations pass the
enclosing constructor through with its fields unreduced; they apply one edit
and name different fixture rows. The three constructor field pass-through
mutations of 2026-10-02 apply the same edit. Each requires its named new
fixture failure after a successful isolated build. The constructor recovery
control fails both new rows. The field order control is new to this record.
It fails only the constructor payload syntax row, because the fixture rows
compare two reduced indices. The six-case record is
`dev/validation/nested-constructor-payload-fixtures.json`; the catalog contains
353 unique anchors.

## 2026-10-02: Tuple and sum fields in constructor payload fixture mutations

Three fixture binding mutations replace the tuple, sum-left, or sum-right
semantic variant with the ordinary source pair check. Three further mutations
pass the enclosing constructor through with its fields unreduced; they apply
one edit and name different fixture rows. One mutation passes every source
tuple index through with its legs unreduced; it also fails the tuple and
constructor payload rows. Two mutations pass every source sum injection
through with its payload unreduced; they apply one edit, and each fails both
sum fixture rows and the sum, tuple, constructor, and neutral payload rows.
Each requires its named new fixture failure after a successful isolated
build. The constructor payload recovery mutation remains a control. The
ten-case record is `dev/validation/collection-payload-fixtures.json`; the
full catalog contains 349 unique anchors. No mutation changes the order of
recovered tuple fields or the address of a recovered sum payload.

## 2026-10-02: Case expressions in constructor payload fixture mutations

Two fixture binding mutations replace the finite-case or constructor-case
semantic variant with the ordinary source pair check. Two further mutations
pass the enclosing constructor through with its fields unreduced. Another
two pass every index source case elimination, the field's included, through
without recovering its scrutinee and result; they also fail the sum, nested,
and constructor index rows. Each pair applies one edit and names a different
fixture row. Each requires its named new fixture failure after a successful
isolated build. The constructor payload recovery mutation remains a control.
The seven-case record is
`dev/validation/constructor-case-payload-fixtures.json`; the full catalog
contains 340 unique anchors. The selected branch in each fixture returns zero
while the unused branch returns one, so the kernel recheck rejects a
semantic variant whose case selects the wrong branch. No mutation changes
the eraser's branch selection.

## 2026-10-02: Constructor payload source fixture mutations

Four mutations replace the let, beta, annotation, or projection fixture's
semantic variant check with the ordinary source pair check. Each must fail
the named fixture binding check, proving that a row cannot silently drop its
post-elaboration index spelling variant. Four further mutations restore the
earlier path that passes a constructor index to the pending frames with its
fields unreduced. Each must fail its named lambda-constructor-payload row,
proving that the row depends on field recovery and not only on constructor
acceptance. A constructor payload recovery mutation is retained as a control.
The catalog contains 334 unique anchors.

`python3 -P dev/validation/constructor-payload-fixtures-run.py` records these
nine isolated mutations, full tests, default gates, fresh erasure evidence,
input freshness, checkpoints, and exact logs in
`dev/validation/constructor-payload-fixtures.json`.

## 2026-10-02: Constructor payload source index mutations

Twelve new mutations disable constructor payload recovery or weaken field
order, field count, full arity, field scope, parameter scope, index scope,
result scope, result index count, family label, reconstruction size, or entry
fuel. Each requires a successful isolated build and its named inline failure.
The catalog contains 326 unique
anchors.

`python3 -P dev/validation/constructor-payload-source-run.py` records these
mutations and two controls for numeric sum and tuple payload recovery,
together with full tests, default gates, the erasure record, input freshness,
checkpoints, and exact logs in `dev/validation/constructor-payload-source.json`.

## 2026-10-02: Composed neutral source index mutations

The new `neutral-composition-disabled` mutation refuses recovered neutral
case heads and must fail `neutral-composition-syntax`. The catalog contains
314 unique anchors. The predecessor neutral head anchor retains its exact
fallback suffix.

`python3 -P dev/validation/neutral-composition-source-run.py` records this
mutation and four controls for sum payloads, neutral projections, and the
left and right index comparison paths. Each mutation requires a successful
isolated build and its named failure. Full tests, default gates, the erasure
record, input freshness, checkpoints, and exact logs are collected in
`dev/validation/neutral-composition-source.json` and its matching directory.

## 2026-09-30: Nested constructor shape payload mutations

Seven new mutations disable nested recovery, reset either payload side's
fuel, accept a mismatched payload count, bypass the shared transition bound,
or disconnect either checked-core fixture from its exact source pair.
The catalog contains 254 unique anchors. Existing constructor and sum case
anchors follow the new pending-frame path.

`python3 -P dev/validation/nested-index-source-run.py` records 39 scoped
mutations with successful isolated builds and named behavior failures. It
also runs full tests, default gates, and the erasure record collector, checks
input freshness, and requires disabled nested recovery to fail both proof
sealing variants. Evidence is in `dev/validation/nested-index-source.json`
and `dev/validation/nested-index-source/`. The historical complete mutation
record is retained as its original snapshot.


## 2026-09-30: Constructor index source mutations

Nine isolated mutations cover constructor cases inside source indices:
disabling recovery, ignoring the injection shape, accepting unequal shape
payloads, ignoring the family name, using the wrong shape index count,
refunding the scrutinee step, resetting result fuel, and replacing either
new fixture call. Each mutation must produce its named failure.
The disabled-recovery mutant must also fail both checked-core fixture variants.

The previous unsupported-case control now uses a non-injection scrutinee.
The old sum index control now admits a valid indexed constructor case.
The existing sum mutation anchors include the new globals argument.

`dev/validation/constructor-index-source-run.py` collects full tests,
default gates, erasure evidence, and 66 scoped mutations: nine new cases,
28 existing constructor and sum cases, and 29 index, binder, scope, alias,
and budget controls. It retains the existing mutation harness's baseline,
snapshot, isolated compilation, named failures, freshness checks, and
single retry for a recorded Bun compiler segmentation fault.

The catalog contains 247 anchors. Scoped evidence does not claim a new
complete mutation run; the historical full mutation record is preserved.

## 2026-09-30: Sum index source mutations

Eight isolated mutations cover sum cases inside constructor source indices:
disabling case recovery, refunding the scrutinee step, resetting the selected
result's budget, skipping the pending case, ignoring the injection width,
ignoring motive metadata, and replacing either new fixture call with an
existing let fixture. Each must produce its named failure.
The existing `index-reduction-cases` mutation now changes the index case
helper's fallback to admit a constructor scrutinee, retaining its previous
constructor-case refusal check.

The disabled sum recovery mutant must also fail both new fixture rows.
Their unmutated execution includes kernel-rechecked constructor index variants.
Fixture-call mutations are checked against the
gate's exact fixture pair and mode. The unmutated suite passes all 185 rows,
and all 238 mutation anchors match exactly once.

`dev/validation/sum-index-source-run.py` runs the full tests, default gates,
anchor check, and refreshed erasure record before the existing harness's
baseline and 65 scoped mutants. Its record pins implementation inputs,
fixture files, the source policy, collector, supporting erasure record, and
kept logs. The harness's freshness checks remain in effect. The historical
full mutation record remains unchanged; this scoped run does not claim a
full 238-mutant run.

New logs replace the kept evidence only after every check passes. A Bun
compiler segmentation fault may retry once, preserving its crash log.

## 2026-09-29: Compound index source mutations

The catalog adds seventeen isolated mutations for bounded constructor index
recovery. They disable compound reduction, skip either comparison direction,
drop the head alias comparison of a payload pair, admit a case payload, move
the 64-step boundary by one in either direction, make applications free,
reset the budget after an application, drop the refund of an unspent step
when reduction stops, lower the step bound alone by one, skip an index let,
skip a pending application, or replace one of the four fixture calls with an
unrelated existing pair.
Each mutation must compile and hit its named regression or fixture-binding
failure. The disabled-recovery mutation must fail all four kernel-checked
let, beta, annotation, and projection index variants.

`python3 -P dev/erasure-mutations.py --check-anchors` checks all 230 catalog
anchors. `python3 -P dev/validation/index-reduction-source-run.py` records the
full tests, default gates, erasure record, and 57 scoped mutations in
`dev/validation/index-reduction-source.json`, retaining the complete logs and
input hashes. The selection includes the preceding index and alias mutations
plus the existing case, scope, alias, and proof controls. The historical full
mutation record is retained; the scoped evidence does not claim a complete
230-mutation run.

The existing `index-alias-local-scope` mutation still disables the common
local unfolding scope check. Its named witness remains `index-alias-source-local`,
because the head alias comparison of a payload pair has no exit scope check.
The index reducer additionally refuses open results in their use scope.
The collector pins the scoped index names and fails when the selection changes.


## 2026-09-29: Transparent index alias mutations

The thirteen new mutants cover disabled alias comparison, lost neutral endpoints,
vacuous equality, omitted later-index checks, unequal widths, an alias bound
one declaration short, disabled local alias unfolding, an exhausted alias
chain that is not refused, parameter and global endpoints that lose their
syntax, open global and local index aliases, and a swapped fixture call. They
require named semantic failures or the existing exact fixture-call gate failure.
The collector also requires disabled alias recovery to fail both kernel-checked
constructor index variants, whose alias spellings are introduced after elaboration.

`dev/validation/index-alias-source-run.py` selects 40 mutants: these thirteen,
the indexed-constructor guards, global and local alias scope and unfolding
guards, and the existing proof, case-fuel, and unknown-scope controls. All 213
catalog anchors are checked. The collector retains the harness's unmutated
baseline, snapshots, compilation, named failure, and input freshness checks.
Complete build and failure logs accompany `dev/validation/index-alias-source.json`.
This scoped record does not claim a complete 213-mutant run.


## 2026-09-29: Recursive constructor source type mutations

The catalog contains 200 cases. `recursive-disabled` replaces the earlier
constructor-recursion guard mutation: it restores that refusal and must fail
the new global recursive-family twin. `recursive-fixture-call` verifies that
the gate binds the new suite case to its exact fixture pair.
`recursive-metadata-bypass` accepts every recursive constructor without its
metadata checks and must fail the recursive metadata case.

Non-recording runs accept `--logs` to isolate their evidence from concurrent
runs. Relative paths use the repository root. Release recording retains its
canonical log directory and refuses this override. The scoped collector uses
`.gatework/recursive-source-mutations` for its baseline and mutant logs.

The scoped collector `dev/validation/recursive-source-run.py` selects 31 cases:
the constructor controls, the three recursive controls, the proof guard, shared
case-fuel controls, and four scope controls. Those last controls check that the
three fixtures moved beyond the 64-step source-recovery budget still catch
local-type, shape-payload, and lambda-scope defects.

The collector keeps the harness's baseline, input snapshots, compiled mutants,
named failure requirements, and input freshness checks. It records test and
gate commands, mutant source hashes, and complete build and failure logs in
`dev/validation/recursive-source.json` and its companion directory. This scoped
record does not replace the historical full mutation record or claim a full
200-case run.


## 2026-09-29: Indexed constructor source type mutations

The catalog contains 198 cases. Thirteen new controls disable indexed recovery or
weaken index telescope scope, parameter depth, result index count and scope,
motive presence, shape count, equality, and payload length, and the
fixture-to-suite binding.
Existing constructor and parameter controls are adapted to the indexed metadata
signatures. The old indexed-family refusal control now checks inconsistent
metadata, since valid indexed families are supported.

The scoped run selects all thirteen new controls, all twenty-one constructor
controls, the eight parameter-source controls, and five shared proof, case fuel,
and fixture-binding controls. Each mutant must compile and produce its required
named failure through the existing harness. The collection helper retains the
baseline, snapshot, and input freshness checks and records their actual return
values and log hashes in `dev/validation/index-source.json`.

Only a Bun compiler segmentation fault receives one retry. Its crash log is
retained, and the retry must pass the same compilation and named-failure checks.
Other build failures and a second compiler crash still fail the run.

Final scoped validation caught 47/47 mutants after a successful unmutated
baseline, with all 198 source anchors valid. Each mutant compiled and produced
its required named failure. After collection, the runner rechecked every
recorded input hash, and `dev/validation/index-source.json` records the hash of
each saved log.

The prior full mutation record remains historical evidence. Scoped results do
not replace it or claim a complete 198-case mutation run.

## 2026-09-28: Parameterized constructor source type mutations

The catalog now contains 185 cases. Eight new controls disable parameterized
recovery, drop expected types from constructor applications or variables,
accept a wrong constructor expected family, omit
parameters from full arity, check fields in an empty parameter scope, skip
parameter-telescope closure, or detach a fixture row from its intended pair.

The existing constructor controls now use the parameter-aware helper signatures
and full-arity invariant. The former parameter refusal control checks malformed
metadata that omits parameters from full arity. No parameter binders are added
to branch bodies, and the shared 64-step and 4096-node limits remain in force.

Scoped validation selects all eight of these controls, the 21 existing constructor
controls, and `proof-guard`, `beta-work-bound`, `case-exhausted`, `case-disabled`,
and `case-fixture-binding`, for 34 cases. Each selected mutant must compile
and produce its required named failure. Evidence is recorded in
`dev/validation/parameter-source.json`. This scoped run does not replace the
historical full mutation record.

All 34 selected mutants compile and produce their required named failures.
The baseline erasure gate and all 185 mutation anchors also pass.

## 2026-09-28: Constructor case source type mutations

Twenty-one new cases bring the catalog to 177. They disable recovery or remove
shape agreement, family name agreement, branch coverage, constructor branch
addresses, uniqueness, constructor field validation,
nonrecursion, metadata arity, motive agreement, whole-case closure, argument
arity, family parameter/index restrictions, the elimination-shape and named-motive
index restrictions, positivity, completeness, or the
result-size cap. Two variants corrupt simultaneous substitution order or the
outer-variable mapping.

The 35-case scoped selection includes those cases and `case-disabled`,
`case-duplicate`, `case-fuel`, `case-head-fuel`, `case-pending`, `case-result-fuel`, `case-exhausted`,
`case-scope`, `case-fixture-binding`, `inline-local-type`, `inline-shape-payload`,
`leg-scope-root`, `beta-work-bound`, and `source-size-cap`. All 177 catalog anchors are valid.
The two existing pending-case mutations now pass the global environment to
source recovery. The duplicate-branch and size-cap anchors are qualified to their original helpers. Their required failures are unchanged.

The scope regression tests an open unused branch before open selected bodies,
so a later substitution error cannot conceal a missing closure check. A large
constructor result tests its own size cap. Recursive families keep the three
unknown-scope controls outside the supported recovery fragment.

All 35 selected variants compiled and produced their required named failures.
Captured evidence is in `dev/validation/constructor-source.json`; the previous
full 127-case mutation record is unchanged.
## 2026-09-28: Finite case source type mutations

Seventeen new cases bring the catalog to 156. They disable recovery, remove shape
agreement, branch coverage, duplicate, range, scope, motive, or binder checks,
remove the one-binder limit on unused branches, select the wrong branch, omit
payload substitution, bypass exhaustion, truncate or skip the shared fuel,
starve the case result, discard a pending frame, or misbind a fixture pair.

The scoped selection includes those 17 cases plus `beta-disabled`,
`beta-head-fuel`, `beta-result-fuel`, `beta-work-bound`, `beta-let-pending`,
`source-size-cap`, `inline-local-type`, `inline-shape-payload`, and
`leg-scope-root`. Existing beta anchors now identify the application frame so
the case frame does not make them ambiguous. All 156 catalog anchors remain
valid.

Shape probes isolate width agreement from branch count. The unused-branch
scope probe precedes the selected-branch probe so substitution failure cannot
hide a missing whole-case closure check. The three existing unknown-scope
controls now use inductive cases, which remain unsupported. Validation results
and captured logs are in `dev/validation/case-source.json`; the previous full
127-case mutation record is unchanged.

All 26 selected variants compiled successfully and produced their required
named failures. The initial serial mutation launch was interrupted after the
full gates passed, then the same selection ran successfully with the harness's
two-worker mode. The interrupted attempt is retained in the scoped record.

## 2026-09-28: Tuple projection source type mutations

The catalog now has 139 cases. Seven new cases disable projection recovery,
skip collection-shape agreement, skip tuple arity, admit open components,
admit unused leg binders, select the wrong component, or misbind a fixture
pair. Guard fixtures isolate shape agreement from tuple length and keep a
free variable inside a selected function type, so later alias lookup cannot
hide a removed scope check.

The scoped run includes these seven cases plus `beta-free-scope`,
`beta-head-fuel`, `beta-result-fuel`, `beta-work-bound`, and `beta-let-pending`.
It also includes three existing inline cases: `inline-local-type`,
`inline-shape-payload`, and `leg-scope-root`. The beta scope anchor now targets the beta call specifically because tuple
projections perform their own whole-application scope check. Every catalog
anchor remains unique. Results, commands, source hashes, and captured logs
are in `dev/validation/projection-source.json`; the older full mutation record
is unchanged. All 15 selected variants compiled and produced their required
named behavioral failures.

## 2026-09-28: Head annotation source type mutations

Five new cases bring the erasure battery to 132. They disable annotation
recovery, remove each of the body and annotation closure checks, unwrap a
wrapper after fuel exhaustion, and stop charging wrappers against the shared
reduction budget. Each must compile and fail its named semantic row. The let
annotation mutation now uses a larger unique anchor to keep targeting the let
guard. Direct tests cover the exact 64/65 boundary and mixed annotation, let,
and beta chains. Unknown-scope controls use nonpoint tuple projections.
This slice validates the five new cases plus `let-free-annotation`,
`beta-let-pending`, and `beta-work-bound` in scoped mode. The existing
127-case full-battery record remains historical. The first scoped run showed
that the body-closure probe also triggered alias rejection. Its replacement
uses a function type with a free domain, so removing the closure check must
fail the named body-closure row.

## 2026-09-27: Beta source type mutations

Twelve new cases bring the erasure battery to 127. They disable beta recovery,
remove closure checking, replace each point-shape check, and bypass quantity
matching. Other cases discard the remaining function-head or result budget,
shorten the structural step bound, and bind a lambda row to the wrong fixture
pair. Three cases drop the pending application under a head let, accept more
than one section binder, and remove the 4096-node size cap on let and beta
results. Every mutation must build and trigger
its named semantic or fixture-binding failure. Existing let mutations now
target the shared reducer. Direct tests also cover the exact 64/65 boundary,
mixed let/beta chains, and a budget split between a function head and its
result. They also cover cycles in each position and a doubling let chain that
exceeds the size cap. Unknown-scope controls use annotated wrappers.

## 2026-09-27: Head let source type mutations

Eleven new cases bring the erasure battery to 115. They disable let recovery,
replace the substituted value, shift the outer telescope incorrectly, remove
each of the annotation/value/body closure guards, shorten or extend the let
bound, drop the remaining reduction fuel, bypass exhaustion, and substitute
a different fixture pair. Each case must build and fail its named semantic
or fixture-binding check. The 64/65 boundary and a cycle passing through a
let protect termination. Three existing unknown-scope fixtures now require
beta reduction while preserving their refusal assertions.

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
