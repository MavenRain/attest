# M0 build log

## 2026-10-05: Stage B collection-selected case scrutinees in collection payload fields

Four constructor index fixture pairs put a Payload case with a
collection-selected scrutinee in the first tuple field or a sum branch of
a collection payload field. The scrutinee selects a Payload constructor
from the second field of a tuple or from a branch of a sum. The first
tuple field holds the tuple selector and the left-sum selector in turn.
The left sum branch holds the right-sum selector and the right sum branch
holds the tuple selector. The selected constructor has distinct zero and
one fields. The unselected tuple field holds a constructor with one in
both fields, and each unselected sum branch returns such a constructor.
The Payload case substitutes and swaps both fields before recovery resumes
the trailing IndexBox field.

Modes 48 through 51 recheck alternate source indices in Pick and keep,
preparation, proof sealing and runtime equality with opaque twins. Four
syntax rows compare the recovered parsed Index with explicit literal
fields through the existing collection parsed-source oracle. The gate
binds each semantic row to its exact pair and mode and each syntax row to
its mode and source. Existing recovery code, budgets and refusal guards
apply.

`python3 -P dev/validation/collection-case-scrutinee-collection-constructor-payload-fixtures-run.py`
records full tests, default gates, fresh erasure evidence, twenty-four
scoped mutations and two controls. The edits drop semantic variants,
substitute the opaque twin as the syntax fixture, bypass collection,
constructor or case recovery, or reverse field order. Each edit must
compile and fail its named row. The collection bypass of each kind acts at
the position of the case in the collection payload field. The tuple bypass
skips `Inline.index_tuple_enter` and the sum bypass skips
`Inline.index_sum_context`. Identical edits share hash-verified executions
and logs. Sixteen mutation reuse checks and thirteen check-cache checks
remain required. Passed-check reuse pins the full source and fixture tree,
gate scripts, Lean records, repository root and generated erasure records
and logs. Changed inputs or outputs invalidate the cache, and erasure
outputs are checked again after the mutations.

The inline suite passes 307 of 307 cases. The erasure corpus contains
four global pairs and 147 inline pairs, including 94 lambda
pairs. HOUSE retains 68 unsafe functions and registers 420
catch-all sites. The mutation catalog contains 491 anchors. Implementation
and final validation run in `/Users/oobi/Documents/attest`, where the saved
Lean evidence is bound to the repository path. The record pins the
implementation, runner, policy and migration inputs. Stage B remains open
at the Acc checker frontier and full trace comparison.

## 2026-10-05: Stage B mixed nested case scrutinees in collection payload fields

Four constructor index fixture pairs put a mixed three-stage case chain in
the first tuple field or a sum branch of a collection payload field. The
constructor-finite chain has a Switch case that returns a sum injection, a
finite case that returns a Payload constructor, and a Payload case. The
finite-constructor chain has a finite case that returns a Switch
constructor, a Switch case that returns a Payload constructor, and a
Payload case. The first tuple field holds each chain in turn. The left sum
branch holds the constructor-finite chain and the right sum branch holds
the finite-constructor chain. The selected branches give distinct zero and
one fields. Each unused branch selects a different constructor or sum
address, or returns one in both fields. The Payload case substitutes and
swaps both fields before recovery resumes the trailing IndexBox field.

Modes 44 through 47 recheck alternate source indices in Pick and keep,
preparation, proof sealing and runtime equality with opaque twins. Four
syntax rows compare the recovered parsed Index with explicit literal
fields through the existing collection parsed-source oracle. The gate
binds each semantic row to its exact pair and mode and each syntax row to
its mode and source. Existing recovery code, budgets and refusal guards
apply.

`python3 -P dev/validation/mixed-case-scrutinee-collection-constructor-payload-fixtures-run.py`
records full tests, default gates, fresh erasure evidence, twenty-four
scoped mutations and two controls. The edits drop semantic variants,
substitute the opaque twin as the syntax fixture, bypass collection,
constructor or case recovery, or reverse field order. Each edit must
compile and fail its named row. These fixtures have no second field
projection, so the tuple collection bypass skips `Inline.index_tuple_enter`
and the sum bypass skips `Inline.index_sum_context`. Identical edits share
hash-verified executions and logs. Sixteen mutation reuse checks and thirteen
check-cache checks remain required. Passed-check reuse pins the full
source and fixture tree, gate scripts, Lean records, repository root and
generated erasure records and logs. Changed inputs or outputs invalidate
the cache, and erasure outputs are checked again after the mutations.

The inline suite passes 299 of 299 cases. The erasure corpus contains
four global pairs and 143 inline pairs, including 90 lambda
pairs. HOUSE retains 68 unsafe functions and registers 420
catch-all sites. The mutation catalog contains 467 anchors. Implementation
and final validation run in `/Users/oobi/Documents/attest`, where the saved
Lean evidence is bound to the repository path. The record pins the
implementation, runner, policy and migration inputs. Stage B remains open
at the Acc checker frontier and full trace comparison.

## 2026-10-04: Stage B case scrutinees in collection payload fields

Three constructor index fixture pairs put a constructor case in the first
tuple field or either sum branch of a collection payload field. The
scrutinee of that case is a case on a sum injection that returns a Payload
constructor. The selected branch gives distinct zero and one fields. The
unused branch returns one in both fields. The outer constructor case
substitutes and swaps both fields before recovery resumes the trailing
IndexBox field.

Modes 41 through 43 recheck alternate source indices in Pick and keep,
preparation, proof sealing and runtime equality with opaque twins. Three
syntax rows compare the recovered parsed Index with explicit literal
fields through a new collection parsed-source oracle. The gate binds each
semantic row to its exact pair and mode and each syntax row to its mode and
source. Existing recovery code, budgets and refusal guards apply.

`python3 -P dev/validation/case-scrutinee-collection-constructor-payload-fixtures-run.py`
records full tests, default gates, fresh erasure evidence, eighteen scoped
mutations and two controls. The edits drop semantic variants, substitute
the opaque twin as the syntax fixture, bypass collection, constructor or
case recovery, or reverse field order. Each edit must compile and fail its
named row. These fixtures have no second field projection, so the tuple
collection bypass skips `Inline.index_tuple_enter` and the sum bypass skips
`Inline.index_sum_context`. Identical edits share hash-verified executions
and logs. Thirteen mutation reuse checks and nine check-cache checks
remain required. Passed-check reuse pins the full source and fixture tree,
gate scripts, Lean records, and repository root so changed test or gate
inputs invalidate the cache.

The inline suite passes 291 of 291 cases. The erasure corpus contains
four global pairs and 139 inline pairs, including 86 lambda
pairs. HOUSE retains 68 unsafe functions and registers 420
catch-all sites. The mutation catalog contains 443 anchors. Implementation
and final validation run in `/Users/oobi/Documents/attest`, where the saved
Lean evidence is bound to the repository path. The record pins the
implementation, runner, policy and migration inputs. Stage B remains open
at the Acc checker frontier and full trace comparison.

## 2026-10-04: Stage B collection-selected constructor case scrutinees

Three constructor index fixture pairs select a Payload constructor from the
second tuple field or either sum branch. Selected fields reduce to distinct
zero and one values. Unused alternatives return one in both fields. The
outer constructor case substitutes and swaps both selected fields before
recovery resumes the trailing IndexBox field.

Modes 38 through 40 recheck alternate source indices in Pick and keep,
preparation, proof sealing and runtime equality with opaque twins. Three
syntax rows compare the recovered parsed Index with explicit literal
fields. The existing parsed-source oracle now has a shared name and serves
both mixed and collection-selected case scrutinees. The gate binds each
semantic row to its exact pair and mode and each syntax row to its source.
Existing recovery code, budgets and refusal guards apply.

`python3 -P dev/validation/collection-case-scrutinee-constructor-payload-fixtures-run.py`
records full tests, default gates, fresh erasure evidence, eighteen scoped
mutations and two controls. The edits drop semantic variants, substitute
syntax fixtures, bypass collection, constructor or case recovery, or
reverse field order. Each edit must compile and fail its named row.
Identical edits share hash-verified executions and logs. Thirteen mutation
reuse checks and nine check-cache checks remain required. Passed-check
reuse pins the full source and fixture tree, gate scripts, Lean records,
and repository root so changed test or gate inputs invalidate the cache.

The inline suite passes 285 of 285 cases. The erasure corpus contains four
global pairs and 136 inline pairs, including 83 lambda pairs. HOUSE retains
68 unsafe functions and registers 420 catch-all sites. The mutation catalog
contains 425 anchors. Implementation was prepared in the isolated checkout
`/Users/oobi/Documents/gpt4/attest-continue-20261004`. Final validation runs
in `/Users/oobi/Documents/attest`, where the saved Lean evidence is bound
to the repository path. The record pins the implementation, runner, policy
and migration inputs. Stage B remains open at the Acc checker frontier and
full trace comparison.

## 2026-10-04: Stage B mixed nested case scrutinees in payload fields

Two constructor index fixture pairs compose three case stages in the first
IndexBox field. One finite case returns a Switch constructor, whose case
returns a Payload constructor. The other Switch case returns a finite
injection, whose case returns a Payload constructor. The final Payload case
substitutes both fields and reverses their order. Selected fields reduce to
distinct zero and one values. Unused branches select a different constructor
or address, or return one in both fields. Recovery resumes the trailing
outer field after completing the case chain.

Modes 36 and 37 recheck alternate source indices in Pick and keep, preparation,
proof sealing and runtime equality with opaque twins. The two syntax rows
recover the parsed Index and compare it with explicit literal fields, so
they independently detect field order and outer resumption. The gate binds
each semantic row to its exact pair and mode and each syntax row to its
source fixture. Existing inline recovery code and budgets apply.

`python3 -P dev/validation/mixed-case-scrutinee-constructor-payload-fixtures-run.py`
records full tests, default gates, fresh erasure evidence, ten scoped
mutations and two controls. Scoped edits drop the semantic variant, bypass
constructor or case recovery, drop an adjacent pending case, or reverse
field order. Each must compile and fail its named row. Identical edits share
verified isolated executions with unchanged inputs, exact recipes and
source hashes, matching logs and each required failure. The collector
records shared execution explicitly and checks thirteen reuse cases.

The inline suite passes 279 of 279 cases. The erasure corpus contains four
global pairs and 133 inline pairs, including 80 lambda pairs. HOUSE retains
68 unsafe functions and registers 419 catch-all sites. The mutation catalog
contains 407 anchors. Stage B remains open at the Acc checker frontier and
full trace comparison.

## 2026-10-03: Stage B constructor-valued case scrutinees in payload fields

Two source fixture pairs place a constructor-valued finite or constructor
case in an outer constructor case's scrutinee, inside an IndexBox payload.
The inner selected branch returns two distinct compound fields. The unused
branch returns one in both fields, so it matches neither the selected nor the
final payload. The outer case substitutes both fields and reverses their order
with let and beta expressions, then recovery resumes a trailing outer
constructor field. Each source has an opaque proof twin. Exact semantic
modes 34 and 35 recheck Pick and keep, preparation and proof sealing, and
compare runtime rows with the twin. The gate binds each row to its exact
fixture sources and mode. Inline recovery uses the existing pending case
frames. The reducer implementation is unchanged.

The direct constructor case scrutinee syntax row compares explicit reduced
terms for both combinations. It checks the two substitutions, field order
and outer resumption. The fixture rows compare two reduced indices and do
not independently detect constructor field order. Eight scoped mutations
replace semantic variants or bypass constructor recovery, case recovery or
only the adjacent outer case frame. The latter preserves the enclosing
constructor field frame and must fail because the outer case changes the
inner result. Constructor recovery and field order remain controls.

`dev/validation/case-scrutinee-constructor-payload-fixtures-run.py` records
full tests, default gates, fresh erasure evidence and ten named mutations.
Identical edits share verified isolated execution logs with explicit shared
execution metadata. Thirteen checks protect cache reuse. The inline suite
has 275 cases, the erasure corpus has 131 inline pairs including 78 lambda
pairs, and the mutation catalog contains 397 anchors. HOUSE retains 68 unsafe
functions and 418 registered catch-all sites.

## 2026-10-03: Stage B constructor-valued cases in collection payload fields

Six constructor index fixture pairs put a finite or constructor case inside
a tuple or either sum branch in the first IndexBox payload field. Each selected
branch returns a two-field Payload constructor with let and beta fields that
reduce to distinct zero and one values. The unused branch reverses them.
The tuple sibling and a trailing outer field also reduce. Each inline proof
has an opaque twin. Semantic variants recheck Pick and keep, preparation,
sealing and runtime equality. The gate binds exact pairs and modes 28 to 33.

The direct constructor case collection syntax row compares explicit reduced
terms for all six combinations. It checks branch substitution, nested and
outer field order, tuple resumption and both sum addresses. The fixture rows
compare two reduced indices and do not independently detect field order.

The inline suite passes 272 of 272 cases. The erasure corpus contains four
global pairs and 129 inline pairs, including 76 lambda pairs. HOUSE retains
68 unsafe functions and 418 catch-all sites. Existing source recovery guards
and limits apply.

`python3 -P dev/validation/case-collection-constructor-payload-fixtures-run.py`
collects full tests, default gates, fresh erasure evidence and 26 serial
isolated mutations. Six mutations drop semantic variants. Eighteen mutations
bypass constructor, case or collection recovery. Each recovery group shares
anchors but requires distinct named fixture failures. Constructor recovery
and field order are controls. Every mutation requires a successful isolated
build and its named failure. Input and log hashes bind the record to the
validated implementation. The catalog has 389 anchors.
Identical edits reuse verified isolated build and gate logs with unchanged
inputs, exact recipes and source hashes, matching log hashes and each named
failure. Shared executions are explicit in the record. A run without
`--reuse-mutations` starts from an empty mutation checkpoint, so it shares
only executions from the same run. Thirteen reuse checks reject altered
metadata and logs, different recipes and missing failures.

## 2026-10-03: Stage B constructor-valued cases in payload fields

Two constructor index fixture pairs place a finite or constructor case in
the first field of an IndexBox constructor. The selected branch returns a
two-field Payload constructor. Its let and beta expressions reduce to zero
and one, while the unused branch returns the reversed values. A scalar
outer field follows the case. Each inline proof has an opaque twin.
Semantic variants recheck Pick and keep, verify preparation and sealing,
and compare runtime rows with the twin. The gate binds exact pairs and modes.

The rows require branch substitution, nested constructor field reduction,
and outer resumption. They compare two reduced indices and do not
independently detect field order. The direct constructor case payload syntax
row compares explicit reduced terms for both case forms. It checks distinct
branch binders, nested field order and the trailing outer field.

The inline suite passes 265 of 265 cases. The erasure corpus contains four
global pairs and 123 inline pairs, including 70 lambda pairs. HOUSE retains
68 unsafe functions and registers 418 catch-all sites. Existing source
recovery guards and limits apply.

`python3 -P dev/validation/case-constructor-payload-fixtures-run.py` collects
full tests, default gates, fresh erasure evidence, and eight serial isolated
mutations. Two drop semantic variants, two bypass constructor fields, and
two bypass case elimination. Each pair of recovery mutations applies the
same edit and requires distinct named fixture failures. Constructor recovery
and field order are controls. Every mutation requires a successful isolated
build and its named failure. Input and log hashes bind the record to the
validated implementation. The catalog has 365 anchors.

## 2026-10-03: Stage B constructors inside collection payload fields

Three additional constructor index fixture pairs put a two-field Payload
constructor inside a tuple or either sum branch in an IndexBox field. A scalar
field follows the collection. The inner fields reduce to distinct zero and
one values. Each inline proof has an opaque twin. Semantic variants recheck
an alternate spelling of Pick and keep in the kernel, verify preparation and
sealing, and compare runtime rows with the twin. The gate binds each row to
its exact fixture pair and mode.

The rows require recovery to reduce the nested constructor, finish the
collection and resume the remaining outer field. They compare two reduced
indices and do not independently detect field order. Direct constructor
payload syntax checks compare with explicit reduced terms and check the
inner and outer field order and both sum addresses.

The inline suite passes 262 of 262 cases. The erasure corpus contains four
global pairs and 121 inline pairs, including 68 lambda pairs. HOUSE retains
68 unsafe functions and registers 417 catch-all sites. Existing source
recovery guards and limits apply.

`python3 -P dev/validation/nested-collection-constructor-payload-fixtures-run.py`
collects full tests, default gates, fresh erasure evidence, and eight serial
isolated mutations. Three mutations drop semantic variants and three pass
constructor fields through unreduced. The three pass-through cases apply
the same edit and require different named fixture failures. The constructor
recovery control fails all three new rows. The field order control fails
only the syntax row. Every mutation requires a successful isolated build
and its named failure. Input and log hashes bind the record to the validated
implementation. The catalog has 359 anchors.


## 2026-10-03: Stage B nested constructors in payload fixtures

Two additional constructor index fixture pairs put a nested two-field Payload
constructor in the first or last field of an IndexBox constructor. The nested
fields reduce to distinct zero and one values. Each inline proof has an opaque
twin. Semantic variants recheck an alternate spelling of the Pick index and
keep in the kernel. They check preparation and sealing and compare runtime
rows with the twin. The gate binds each row to its exact source pair and
variant mode.

The rows require recovery to reduce every nested and outer field. Recovery
compares the annotation index with the Pick index after it reduces both, so a
field order error changes both sides and the rows do not detect it.
Suite.constructor_payload_syntax now also checks field order and outer
resumption with a nested constructor in the last field. It already checked
them with a nested constructor in the first field.

The inline suite passes 259 of 259 cases. The erasure corpus contains four
global pairs and 118 inline pairs, including 65 lambda pairs. HOUSE retains 68
unsafe functions and registers 416 catch-all sites, including the new nested
field position dispatch. Existing source recovery guards and limits apply.

`python3 -P dev/validation/nested-constructor-payload-fixtures-run.py` collects
full tests, default gates, fresh erasure evidence, and six serial isolated
mutations. Two mutations drop the semantic variant, and two pass constructor
fields through unreduced. The two pass-through mutations apply one edit and
name different fixture rows. The three constructor field pass-through
mutations of 2026-10-02 apply the same edit. The constructor recovery control
fails both new rows. The field order control is new to this record and fails
only the constructor payload syntax row. Each mutation requires a successful
build and its named failure. Input and log hashes bind the record to the
validated implementation. The catalog has 353 anchors.

## 2026-10-02: Stage B collections in constructor payload fixtures

Three additional constructor index fixture pairs place a numeric tuple or
either sum address in a constructor field. Tuple fields reduce to distinct
values (zero and one) in source order. Each inline proof has an opaque twin.
Semantic variants recheck an alternate spelling of the Pick index and keep
in the kernel, check preparation and proof sealing, and compare runtime rows
with the twin. The gate binds each row to its exact source pair and mode.

The inline suite passes 257 of 257 cases. The erasure corpus contains four
global pairs and 116 inline pairs, including 63 lambda pairs. HOUSE retains
68 unsafe functions and registers 415 catch-all sites, including the new
collection field fixture dispatch.

`python3 -P dev/validation/collection-payload-fixtures-run.py` collects full
tests, default gates, fresh erasure evidence, and ten serial isolated mutations.
Three mutations drop the semantic variant, three pass constructor fields
through unreduced, one passes tuple legs through unreduced, and two pass sum
payloads through unreduced. The three constructor field mutations apply one
edit and name different fixture rows; the two sum mutations also apply one
edit. The constructor payload recovery mutation remains a control. Each requires a successful build
and its named failure. Input and log hashes bind the record to the validated
implementation. The catalog contains 349 anchors.

## 2026-10-02: Stage B case expressions in constructor payload fixtures

Two additional constructor payload fixture pairs contain a numeric finite case
or a constructor case in their Nat field. The selected branch returns its
zero-valued argument; the unused branch returns One. Each inline source has
an opaque proof twin. Semantic variants spell the Pick index as a constructor
with the case expression in its field, recheck Pick and keep in the kernel,
check preparation and proof sealing, and compare runtime rows with the twin.
The gate binds each suite row to its exact fixture pair and reduction mode.

The inline suite passes 254 of 254 cases. The erasure corpus contains four
global pairs and 113 inline pairs, including 60 lambda pairs. Existing
recovery semantics, metadata guards, scope checks, and work limits are
unchanged. HOUSE retains 414 catch-all sites and 68 unsafe functions.

`python3 -P dev/validation/constructor-case-payload-fixtures-run.py` collects
full tests, default gates, fresh erasure evidence, and seven serial isolated
mutations. Two mutations drop the semantic variant, two pass constructor
fields through unreduced, and two pass every index source case elimination,
the field's included, through unreduced. Each pair applies one edit and names
a different fixture row.
The constructor payload recovery mutation is retained as a control. Each
requires a successful build and its named failure. Input and log hashes bind
the record to the validated implementation. The catalog contains 340 anchors.

## 2026-10-02: Stage B constructor payload source fixture corpus

Four source fixture pairs exercise constructor fields containing a let, beta
application, annotation, or numeric tuple projection. Their indexed Choice
family carries an IndexBox value. Recovery compares the raw source indices
syntactically, so only the semantic variant, which spells the Pick index as a
constructor with a compound field, reaches field recovery. Each inline source
has an opaque proof twin. The semantic suite row also changes the Pick index spelling on a consistent elaborated copy,
rechecks Pick and keep in the kernel, checks preparation and proof sealing,
and compares runtime rows with the opaque twin. The gate binds each row to
its exact fixture pair and reduction mode.

The inline suite passes 252 of 252 cases. The erasure corpus now contains
four global pairs and 111 inline pairs, including 58 lambda pairs. The HOUSE
registry adds the field-expression helper's numeric dispatch fallback, for
414 catch-all sites and 68 unsafe functions. Recovery semantics and their
existing fuel, transition, scope, metadata, and node limits are unchanged.

`python3 -P dev/validation/constructor-payload-fixtures-run.py` records full
tests, default gates, fresh erasure evidence, four isolated fixture binding
mutations, four recovery pass-through mutations, and a constructor payload
recovery control in `dev/validation/constructor-payload-fixtures.json`. Each
pass-through mutation restores the earlier verbatim constructor path and must
fail its named fixture row. Every mutation requires a successful build and its
named failure. Input and log hashes bind the record to the implementation.
The catalog contains 334 unique anchors.

## 2026-10-02: Stage B constructor payload source indices

Constructor injections now recover their fields in source order under the
enclosing 64 reductions and 129 transitions. The entry checks complete,
positive family metadata, matching family name and index count, field counts,
full arity including parameters, and parameter, index, field, and result
scope. Reconstruction preserves shapes and constructor names and retains
the 4096-node cap. A refused field refuses the injection. Concrete case
scrutinees keep the existing substitution path and its fuel boundary.

Eight inline rows cover reduction, nested constructors, sums and tuples,
comparison in both directions, source syntax, local scope, metadata refusals,
parameterized and indexed families, recursive metadata, shared fuel,
the 127-field transition boundary, and reconstruction size. The collector
`python3 -P dev/validation/constructor-payload-source-run.py` records full
tests, default gates, the erasure record, twelve new isolated mutations, and
two sum and tuple controls in
`dev/validation/constructor-payload-source.json`. Every mutation requires
a successful build and its named failure. Input and log hashes bind the
record to the validated implementation. The inline suite passes 248 of 248
cases. HOUSE records 413 catch-all sites and 68 unsafe functions, and the
mutation catalog contains 326 unique anchors.

## 2026-10-02: Stage B composed neutral source indices

Recovered neutral numeric and constructor cases now serve as scrutinees of
other cases, heads of point applications, and heads of numeric collection
projections. Each inner case passes the existing branch, motive, family
metadata, scope, and size checks before the enclosing continuation rebuilds
its parent. Branch bodies, motives, quantities, order, and shape payloads
retain source syntax. All nested heads and arguments share the existing
64 reductions and 129 transitions. Reconstruction retains the 4096-node cap.

Five inline rows cover all four numeric/constructor case combinations,
applications, projections, constructor index comparison, sum payloads, local
scope, inner refusals, outer projection addresses, concrete reduced results,
size limits, and exact work budgets. A chain of 64 neutral cases fits exactly
129 transitions; 128 transitions and a 65-case chain are refused. The inline
suite contains 240 cases. The HOUSE registry in `dev/bend-policy.json` retains
408 catch-all sites and 68 unsafe functions. The catalog has 314 unique mutation
anchors.

`dev/validation/neutral-composition-source-run.py` collects full tests, default
gates, the erasure record, and five serial scoped mutations into
`dev/validation/neutral-composition-source.json`. The new mutation disables
composition and must fail its named syntax row after a successful build.
Four controls cover sum payloads, neutral projections, and both index
comparison directions. Checkpoints and logs pin the implementation and runner.
Full tests, default gates, and the erasure record pass. All five scoped
mutations are caught after successful isolated builds.

## 2026-10-02: Stage B neutral constructor cases in source indices

Source index recovery now retains constructor cases when the recovered
scrutinee is a neutral global, local variable, point application, or numeric
collection projection. Scrutinee recovery uses the enclosing 64 reductions
and 129 transitions. Reconstruction returns through the existing neutral
return frame and does not restart recovery.

The family must be complete and positive, with a matching family name and
index count, closed parameter and index telescopes, the required motive, complete
unique constructor branches, and matching field quantities and arities.
The complete case must be closed and fit the 4096-node cap. Branch bodies,
motives, quantities, branch order, and shape payloads retain source syntax.
Recursive and indexed families use the same metadata checks. No unsafe
function is added; HOUSE registers two new refusal/fallback catch-alls.

Five inline rows cover scrutinee reductions, neutral applications and
projections, constructor index comparison, nested sum payloads, local
scope, syntax preservation, reversed branches, malformed branches and
motives, family metadata, shared fuel, exact transition limits, and size.
The inline suite contains 235 cases. Twelve new targeted mutations bring the
catalog to 313 anchors. Four controls cover sum payloads, neutral projections,
and both index comparison directions.

`dev/validation/neutral-constructor-source-run.py` collects full tests, default
gates, the erasure record, and the 16 serial scoped mutations into
`dev/validation/neutral-constructor-source.json`. The record pins the checked
implementation, mutation recipes, checkpoints, and logs. Full tests and
default gates pass, and all 16 scoped mutations are caught after successful
isolated builds.

The first full test run passed every new row but failed a predecessor test
that still required refusal of a neutral constructor scrutinee (234/235).
That test now checks the exact recovered syntax. Its failed output is retained
as `tests-prior-neutral-refusal.log`; the final collector reruns all checks.

The first mutation battery exposed a masked parameter-scope fixture: its
constructor arities omitted the parameter count. Correct arities now isolate
the open parameter type, and a valid parameterized-family control checks that
the fixture can recover. The failed mutation output and prior checkpoints
are retained. `mutations-masked-parameter.log` records the uncaught
`neutral-constructor-parameters` mutation, and `parameter-mask.log` records
its masked gate run. `checks-before-parameter-fix.json` and
`mutations-before-parameter-fix.json` keep the prior checkpoints.
All checks and all 16 mutations are rerun on the corrected tests.

Stale ignored mutation snapshots from September 24 through 30 were removed
after the local disk guard held a status probe below its 30 GiB floor.

This entry records local implementation and executable validation.
No independent review agent or Stage B completion is claimed.


## 2026-10-01: Stage B neutral numeric cases in source indices

Source index recovery now retains a numeric case when its recovered scrutinee
is a neutral global, local variable, application, or collection projection.
The case preserves branch bodies, motives, quantities, and branch order.
Collection width, complete numeric branch coverage, one binder per branch,
unnamed and unindexed motives, full syntax scope, and the 4096-node cap remain
required. A refused scrutinee refuses the case. Branch bodies and motives keep
their source syntax; neutral constructor cases remain conservative.

Case entry consumes one of the shared 64 reductions. Scrutinee arguments use
the same budget, and reconstruction uses the existing return frame under the
129-transition limit. Returning reconstructed syntax avoids re-entering the
same neutral case. Concrete sum and constructor cases retain their selected
result path.

Five suite rows cover scrutinee reductions, nested sum payloads, syntax
preservation, malformed branches, motives, scope, local variables, empty
collections, reversed branches, exact reduction and transition boundaries,
and reconstruction size. The prior neutral sum refusal now checks exact
recovered syntax. The inline suite contains 230 cases. Eight targeted mutations
bring the catalog to 301 anchors; four controls exercise sum payloads, neutral
projections, and both index comparison directions. No unsafe function is added.

`dev/validation/neutral-case-source-run.py` collects full tests, default gates,
the erasure record, and the 12 serial scoped mutations into
`dev/validation/neutral-case-source.json`. Logs and validated inputs are hashed,
and interrupted checks or mutations can be reused only when their pins match.

The first mutation run completed four cases, but the compiler was killed with
exit -9 while building the sum-payload control. That failed build is retained
as `sum-payload-disabled-killed-build.log` and is not counted as a caught
behavior mutation. The retry reused four checks and four completed mutation
results only after rechecking their input, recipe, and log hashes. The runner
does not write the top-level `recovery` block in
`dev/validation/neutral-case-source.json`. That block was added by hand after
the retry. It records the killed attempt, the resume arguments, and the
counts of reused checks (4) and reused mutation results (4).

## 2026-10-01: Stage B numeric tuple fields in source indices

Numeric tuple indices now recover every field while preserving their collection
shape and source order. Recovery checks that the width equals the field count,
fields have no binders, and the complete tuple is closed. Empty tuples are
supported. Reconstruction keeps the 4096-node cap and propagates a refused
field to the whole tuple.

Tuple entry consumes one of the enclosing 64 reductions. Fields, nested
tuples, sum payloads, and outer applications share that budget and the existing
129 transitions. `IndexTupleField` retains the completed and remaining fields;
the existing return frame prevents another recovery pass over the rebuilt tuple.
Tuple dispatch precedes the exhausted-fuel arm. Concrete projections keep
their selected-field path, so an unselected field does not consume recovery
fuel. Point sections retain beta recovery and their source syntax.

Seven new suite rows cover aliases, lets, beta steps, annotations, projections,
cases, nested terms, shifted locals, field order, malformed tuples, scope,
refusal propagation, shared fuel, exact transition boundaries, size, and
concrete projections. The inline suite contains 225 cases. Eleven targeted
mutations bring the catalog to 293 anchors. Four new registry sites disclose
tuple refusal and dispatch; no unsafe function is added.

`dev/validation/tuple-payload-source-run.py` collects the full tests, default
gates, erasure record, and 15 scoped mutations into
`dev/validation/tuple-payload-source.json`. The four controls cover both
enclosing index comparison directions, neutral projections, and sum payloads.
The collector defaults to one mutation worker. Two concurrent compiler
processes were killed with exit -9 after the four preliminary checks passed.
The serial retry reuses those checks through a checkpoint that binds their
source inputs and log hashes. The original collector snapshot and failed
attempt logs preserve the recovery evidence. Original check timings were not
persisted and remain null. `--reuse-checks` refuses changed inputs or logs.
The order mutation initially expected the syntax row, while the nested tuple
assertion correctly failed in the fuel row. Its expected diagnostic now names
that row. The anchor check ran again. The original harness snapshot records
the single diagnostic change; compiler and gate inputs stayed unchanged.
Completed isolated mutation results are checkpointed with their source
recipes and log hashes. `--reuse-mutations` validates those bindings before
reuse, and unfinished cases still compile and run in isolated copies.
Eleven results came from the interrupted serial battery. The checkpoint marks
them `recovered` and binds them to the original harness snapshot.
A single-worker refusal mutation build was later killed with exit -9. Its log
is retained in the mutation checkpoint. That failed build is not a caught
mutation; a manual serial retry keeps the thirteen completed results.

Stage B stays open at Acc runtime elimination, neutral scrutinees, builtin and
provisional constructor families, source types needing further inference or
recovery, and index payloads unequal after bounded recovery.

## 2026-10-01: Stage B numeric sum payloads in source indices

Numeric sum injection indices now recover their single payload while retaining
their collection shape and address. Recovery requires an address within the
collection width, one argument, closed source syntax, and a reconstructed term
within 4096 nodes. A pending frame rebuilds the injection without reducing the
completed term again. Concrete case scrutinees retain their original case path
and recover the selected result after substitution.

Payload recovery consumes one enclosing reduction. Nested injections, outer
head reductions, neutral applications, and projections share the existing
64 reductions and 129 transitions. Six semantic cases cover both comparison
directions, aliases, lets, annotations, beta steps, projections, concrete cases,
nested payloads, shifted local aliases, scope, malformed shapes and addresses,
argument counts, distinct values, and exact versus excessive budgets. The size
case accepts a 4096-node reconstruction and refuses one with 4097 nodes. The
transition case separates 129 from 131 transitions beneath 42 point
applications. The inline suite contains 218 cases in 16 test programs.

Nine new mutations bring the catalog to 282 anchors. Three new policy sites
disclose the explicit payload refusal, case frame dispatch, and numeric
injection dispatch. No unsafe function is added.

The collector `dev/validation/sum-payload-source-run.py` records the full tests,
default gates, erasure record, and 13 scoped mutations in
`dev/validation/sum-payload-source.json`. The four controls cover both enclosing
payload comparison directions, neutral projections, and concrete case fuel.

Commit 8fcc478 kept a projection record from before its collector fixes, and
its gate log was later overwritten by a failed Lean build. The projection
collector ran again on this tree, so
`dev/validation/neutral-projection-source.json` and its logs match the current
sources.

Stage B stays open at Acc runtime elimination, neutral scrutinees, builtin and
provisional constructor families, constructor injection arguments requiring
recovery, and index payloads unequal after bounded recovery.


## 2026-10-01: Stage B neutral collection projections in source indices

Neutral numeric collection projections now retain their recovered heads and
addresses during constructor index comparison. Recovery requires a collection
shape, an address within its width, a neutral head, closed source syntax, and
a reconstructed term within 4096 nodes. Completed projections use the existing
neutral return frame so their source syntax is not reduced again.

Head reduction, nested projections, and point applications share the enclosing
64 reductions and 129 transitions. Six direct semantic cases cover both
comparison directions, annotations, lets, beta reduction, shifted local aliases,
outer variables, nested applications, malformed shapes and addresses, open
heads, size limits, and exact versus excessive shared budgets. The transition
test uses 42 neutral point applications around one or two projections to
separate 129 from 131 transitions while staying below the reduction limit.
The inline suite contains 212 cases in 16 test programs.

Nine new mutations bring the catalog to 273 anchors. The existing finite-case
range mutation now names its complete branch-check expression to retain a
unique anchor. Two registry entries disclose explicit projection refusal and
the address dispatch to the existing neutral point helper. No unsafe function
is added.

The collector `dev/validation/neutral-projection-source-run.py` records the full
tests, default gates, erasure record, and 13 scoped mutations in
`dev/validation/neutral-projection-source.json`. The historical complete
mutation record remains unchanged.

Stage B stays open at Acc runtime elimination, neutral scrutinees, builtin and
provisional constructor families, and index payloads unequal after recovery.


## 2026-09-30: Stage B nested constructor shape payloads in source indices

Constructor cases inside source indices can now recover equivalent nested
shape payloads. Equal payload lists retain the direct path. Otherwise, two
pending frames recover and compare each side in order. Both sides, later
payloads, the scrutinee, and the selected result share the enclosing 64
reductions and 129 transitions. Metadata, branch, motive, closedness, and
4096-node substitution checks remain in force. No unsafe function is added.

Two indexed `IndexBox` fixture pairs exercise payload changes on opposite
sides of a constructor case. Their checked-core variants recheck the index
and its use with the kernel, seal one proof, and preserve their opaque twins'
runtime. Four direct suite cases cover mixed reductions, multiple payloads,
outer variables, mismatches, and exact versus excessive shared budgets.
The nested transition test accepts depth 21 and refuses depth 22 while both
are below the reduction bound. The inline suite contains 198 cases in 16
test programs.

The collector `dev/validation/nested-index-source-run.py` records full tests,
default gates, the erasure record, and 39 scoped mutations in
`dev/validation/nested-index-source.json`. Seven new mutations bring the
catalog to 254 anchors. Existing constructor and sum mutation anchors follow
their live paths. The historical complete mutation record remains unchanged.
Three new catchall entries record explicit refusal or sum-case dispatch.

Stage B remains open at Acc runtime elimination, neutral scrutinees, builtin
and provisional families, and payloads that remain unequal after recovery.


## 2026-09-30: Stage B constructor cases in source indices

Index source recovery now selects a branch of a concrete constructor case.
It reuses the existing complete, positive family checks, branch coverage,
field arity and quantities, motive metadata, closedness, and simultaneous
substitution. Parameterized, indexed, and recursive constructor metadata
remain supported. Nested elimination and injection shape payloads must
match syntactically; recovery does not restart index comparison inside an
index payload. This keeps nested case recovery within the existing budget.

Each constructor case spends one of its payload's 64 steps before its
scrutinee. The scrutinee and selected result share the remainder with sum
cases, lets, annotations, applications, and projections. Substitution retains
the 4096-node cap, and pending frames retain the 129-transition limit.

Two opaque-twin pairs cover zero-field and field-bearing constructors.
Each suite variant changes an elaborated constructor index to an equivalent
case, rechecks the definition and its use with the kernel, seals one proof,
and compares runtime output with the opaque twin. Five direct cases cover
comparison direction, retained source syntax, mixed pending frames, aliases,
outer variables, malformed and open cases, indexed and recursive metadata,
unequal nested shape payloads, substitution size, and reduction boundaries.

The inline suite contains 192 cases in 16 test programs. Nine new mutations
bring the catalog to 247 anchors. The collector
`dev/validation/constructor-index-source-run.py` records the full tests,
default gates, erasure record, and 66 scoped mutations in
`dev/validation/constructor-index-source.json`. The historical complete
mutation record remains unchanged. The only new catchall policy entry is
the index constructor helper's explicit refusal. No unsafe function is added.

Stage B stays open at the Acc runtime-elimination frontier. Further recovery
of nested constructor shape payloads, builtin and provisional families,
unequal payloads after bounded recovery, and neutral scrutinees remain open.

## 2026-09-30: Stage B sum cases in constructor source indices

Index source recovery now reduces a case over a concrete sum injection.
Recovery checks matching collection widths, complete and unique numeric
branches, one binder per branch, and an optional unnamed, unindexed motive.
The whole payload must be closed, including unused branches, scrutinee
annotations, and the motive. Substitution retains the 4096-node cap and
preserves outer variables. Transparent global and local aliases keep their
existing scope and unfolding guards. Constructor cases inside an index
still do not reduce, so index recovery does not reenter constructor comparison.

A case consumes one of the payload's 64 steps before its scrutinee.
Its scrutinee and selected result share the remaining budget with lets,
annotations, applications, and projections. Pending case and application
frames share the existing 129-transition limit.

Two opaque-twin pairs cover both sum injections. Each also changes an
elaborated constructor index to an equivalent case expression, rechecks the
definition and its use with the kernel, seals one proof, and compares its
runtime output with the opaque twin. Four direct suite rows cover both
comparison directions, preserved result syntax, reordered branches, mixed
reductions, global and local aliases, shifting, capture, unequal later
indices, malformed and open cases, refused constructor cases, substitution
size, and exact versus excessive head, result, shared, and mixed reduction
budgets. Let prefixes keep the excessive head, result, and shared budget rows
inside the 129-transition limit, so only the 64-step budget refuses them.

The inline suite has 185 cases in 16 test programs. Eight new mutations
bring the catalog to 238 checked anchors. The collector
`dev/validation/sum-index-source-run.py` records the full tests, default
gates, erasure record, and 65 scoped mutations in
`dev/validation/sum-index-source.json`. The historical full mutation
record remains unchanged. The two new catchall policy entries are the
index case helper's explicit refusal and the fixture's scalar branch dispatch.

Stage B stays open at the Acc runtime-elimination frontier. Constructor cases
inside indices, builtin and provisional constructor families, unequal
payloads after bounded recovery, and neutral scrutinees remain open.

## 2026-09-29: Stage B compound constructor source indices

Constructor source recovery compares unequal index spellings after bounded
head let, beta, annotation, and tuple projection reductions. Each payload pair
also keeps the earlier comparison after transparent head aliases, so a payload
whose reduction reaches a neutral application, projection, or case still
matches its own spelling. Neutral globals
and parameters retain their syntax; transparent global and local aliases keep
their scope, opacity, recursion, partiality, shifting, and declaration-count
guards. Each index payload has a separate 64-reduction budget. Applications
spend a step before their head and share the remainder with their result.
Substitution keeps the existing 4096-node cap. Case expressions in index
payloads do not reduce, which prevents index recovery from reentering
constructor comparison. The surrounding source recovery keeps its shared
64-step case budget and whole-term scope and metadata checks.

Four opaque-twin pairs declare let, beta, annotation, and projection indices
in a constructor's declared type. Recovery compares their raw sources
syntactically, so only a suite variant reaches the reducer. Each variant
changes an elaborated constructor index to an equivalent compound
spelling and rechecks the definition and its use with the kernel before
sealing. Each variant seals one proof and preserves its opaque twin's runtime.
Four direct regression cases cover both comparison directions, preserved
result syntax, mixed aliases and reductions, local shifting and capture,
unequal later indices, open payloads, neutral applications kept by the head
alias comparison, refused cases, alias cycles, the 64/65-step boundary, and
the budget that lets and applications share.

The inline suite contains 179 cases, and the mutation catalog has 230 checked
anchors. `dev/validation/index-reduction-source-run.py` collects the full
tests, default gates, erasure record, and 57 scoped mutations into
`dev/validation/index-reduction-source.json`. The disabled-recovery mutant
must fail all four checked-core variants. The historical full mutation record
is retained. Case reductions in index payloads, builtin and provisional
families, and neutral scrutinees remain unsupported. Stage B stays open at
the Acc runtime-elimination frontier.


## 2026-09-29: Stage B source indices through transparent aliases

Constructor source recovery compares index payloads after transparent head
aliases unfold, when their original syntax differs. Global and local alias
bodies reuse the existing scope, opacity, recursion, and partiality guards.
Neutral globals and parameters retain their source syntax. Local alias values
shift into the use scope, and each alias chain has a declaration-count bound.
The original case remains subject to its whole-term scope and metadata checks.
The shared 64-step case limit and 4096-node substitution cap still apply.

Two opaque-twin pairs cover a global index alias and a local let alias. Each
also rewrites an elaborated constructor index to an equivalent alias spelling,
then checks the modified definition and its use with the kernel before sealing.
The variants must seal one proof and preserve their opaque twins' runtime.
The disabled-recovery mutant must fail both checked-core variants. Four
direct regression cases cover syntax preservation, comparison direction,
neutral endpoints, width and later-index mismatches, local shifting, capture,
scope, refused unfoldings, cycles, and the 64/65-step boundary. The inline suite
contains 171 cases, and the mutation catalog has 213 checked anchors.

`dev/validation/index-alias-source-run.py` collects the full tests and default
gates, the erasure record, and 40 scoped mutations into
`dev/validation/index-alias-source.json`. The historical full mutation record
is retained. Compound index reductions, builtin and provisional families,
and neutral scrutinees remain unsupported. Stage B stays open at the Acc
runtime-elimination frontier.


## 2026-09-29: Stage B recursive constructor source types

Source recovery now reduces cases over complete, positive recursive families.
The kernel passes only constructor fields to a case branch, so the existing
simultaneous source substitution also handles recursive fields. Recovery does
not introduce induction hypotheses or recursively traverse field values.
Nested cases retain the shared 64-step limit and the 4096-node result cap.
Family completeness, positivity, field quantities, arity, source indices, and
whole-case scope checks remain in force.

Four opaque-twin pairs cover global aliases, dependent parameters, nested local
cases, and a parameterized indexed family. Four direct cases cover source
syntax and capture, metadata, scope, and the 64/65-step boundary. The inline
suite now contains 165 cases. The three unknown-scope controls use 65 source
annotations to keep their types beyond recovery; their leak assertions remain
unchanged, and their mutations are included in this slice's validation.

`dev/validation/recursive-source-run.py` collects the test suite, default gates,
all 200 mutation anchors, the erasure record, and 31 scoped mutants. Evidence
is recorded in `dev/validation/recursive-source.json`. The historical full
mutation record is retained. Builtin and provisional families, unequal source
index payloads, and neutral scrutinees remain unsupported. Stage B stays open
at the Acc runtime-elimination frontier.


## 2026-09-29: Stage B indexed constructor source types

Source recovery now reduces cases over complete, positive, nonrecursive indexed
families. Elimination and injection shapes carry the declared index count and
syntactically equal payloads. Parameter values remain in the scrutinee's type.
Index telescope types are closed over parameters and earlier indices. Constructor
result indices have the declared count and are closed over parameters and fields.
Full constructor arity still counts parameters and fields. Only fields become
branch binders, so simultaneous substitution preserves the outer scope.

Indexed motives name the matching family and bind exactly its index count.
Unindexed motives remain optional. The kernel continues to check index types and
conversion; source recovery does not evaluate indices or equate distinct syntax.
Recursive, provisional, and builtin families, unequal source index payloads, and
neutral scrutinees remain unsupported. Stage B remains open at the Acc
runtime-elimination frontier.

Four opaque-twin pairs cover global, dependent, local, and curried function types.
They include an unparameterized family, parameter-dependent index types, and an
index telescope whose later type depends on an earlier index. Six direct cases
cover source syntax, motives, metadata, shape payloads, scope, size, and shared
fuel. The inline suite contains 157 cases.

Validation passed: `make test` (16 test programs and 157/157 inline cases),
`zsh -f dev/gates.sh`, and all 198 mutation anchors. Inline equality passed for
89/89 pairs with 57 carried differences. The Lean twin passed 24 acceptances and
12 refusals with zero axioms. All 47 scoped mutants compiled and produced their
required named failures.

Validation evidence and exact commands are recorded in
`dev/validation/index-source.json`, collected by the pinned in-tree helper
`dev/validation/index-source-run.py`. The mutations row records the helper
command and the harness argument list. The historical full mutation record is
preserved. HOUSE adds one explicit refusal site for mismatched index payload
lists and no unsafe functions. The source migration manifest is refreshed.

## 2026-09-28: Stage B parameterized constructor source types

Source recovery now reduces cases over complete, positive, unindexed families
with parameters. Both core shapes remain bare family markers. Parameters live
in the scrutinee's type; the reducer uses checked family metadata to validate
the parameter telescope, field scope, and full constructor arity. Parameter
types must be closed over earlier parameters. Field types may refer to those
parameters and earlier fields. Full arity includes parameters and fields, while
branches bind only fields. Simultaneous substitution preserves the outer scope.

The frontend now passes expected types through constructor variables and
applications. This supplies the context required for parameterized constructor
introductions, including zero-field constructors, typed lets, dependent scopes,
and function arguments. Family names must match; the kernel continues to check
fields, quantities, and result indices. An introduction without an expected
type still refuses, and fields needing an expected type require an annotation.

Four opaque-twin pairs exercise global, dependent, local, and curried function
types with dependent family parameters and a field whose type uses a parameter.
Five direct cases cover syntax, malformed shapes, metadata closure, scope,
substitution size, and shared fuel. A frontend case covers accepted introductions
and refusals for wrong families, field types, arity, result indices, and missing
expected types. The inline suite contains 147 cases.

Validation passes `make build`, all 16 programs in `make test`, the full Stage A
gate battery, and the erasure gate. The erasure record covers 85 identical inline
proof pairs and 53 carried differences. All 185 mutation anchors check. All 34
selected mutants compile and reach their required named failures.

The mutation catalog contains 185 cases. Scoped validation selects all
eight new controls, all 21 constructor controls, and five existing proof, case, budget,
and fixture controls. Commands, hashes, logs, and outcomes are recorded in
`dev/validation/parameter-source.json`. The prior full mutation record remains
historical evidence. HOUSE adds one explicit nonfamily refusal site and no
unsafe functions. Indexed, recursive, provisional, and builtin case recovery
remain unsupported. Stage B remains open at the Acc runtime-elimination frontier.

## 2026-09-28: Stage B source types through constructor cases

Source recovery now reduces cases over complete, positive constructor families
without parameters, indices, or recursive constructors. Elimination and injection
shapes must name the same family. Branches cover every constructor exactly once,
in any order, with its declared field quantities and arity. The entire case must
be closed, including unused branches, arguments, and the optional unindexed
motive. A named motive must name the matching family.

Simultaneous source substitution preserves field order, outer variables,
annotations, and universes. Zero-field constructors are supported. Constructor
cases reuse the pending case frames and share the 64-step reduction limit and
4096-node substitution-result cap. Parameterized, indexed, recursive, provisional,
and builtin families and neutral scrutinees remain unsupported.

Four opaque-twin pairs cover global, dependent, local, and curried function types.
Six direct cases exercise source syntax, malformed shapes and metadata, scope,
size, mixed pending frames, and the shared reduction limit. The three existing
unknown-scope controls now use recursive families. All 137 inline cases and all
16 test programs pass. All 81 inline pairs match their opaque twins, while 49
retain different carried runtime outputs.

The mutation catalog has 177 cases. Scoped validation exercises all 21 new
mutations plus 14 existing reducer, fixture-binding, and scope controls. All 35
compile and produce their required named failures. Full gates pass, including
all 36 Lean twins. Commands, hashes, logs, and outcomes are recorded in
`dev/validation/constructor-source.json`. The prior full mutation record remains
historical evidence. HOUSE adds six explicit fallback sites and no unsafe
functions. The source manifest is refreshed. Stage B remains open at the Acc
runtime-elimination frontier.

## 2026-09-28: Stage B source types through finite cases

Source recovery now reduces finite collection cases with matching injection and
elimination widths, one payload, and one binder in every branch. Branch addresses
must cover the collection exactly once; their order does not matter. An optional
motive must be unnamed and unindexed. The entire recovered case must be closed,
including unused branches and the motive. Source substitution preserves outer
variables, annotations, and universes in the selected branch.

Application and case frames share the existing pending stack. Cases consume the
same 64-step budget as annotations, lets, beta steps, and projections, including
work in scrutinees and selected results. Case substitution also uses the existing
4096-node result cap. Inductive cases and neutral scrutinees stay unsupported.

Four new opaque-twin pairs cover global, dependent, local, and curried function
types. Five direct rows cover syntax, malformed shapes and branches, scope,
64/65-step boundaries, and mixed pending frames. The inline suite passes all 127
cases, and all 16 test programs pass. Three existing unknown-scope controls now use inductive cases, preserving
their refusal purpose after finite cases became recoverable.

The mutation catalog has 156 cases. The scoped selection exercises all 17 new
cases and nine existing reducer, size-cap, and scope mutations. Commands, source
hashes, logs, and results are recorded in `dev/validation/case-source.json`.
All 26 selected variants compiled successfully and produced their required
failures. The full gates pass, including all 36 Lean twin cases.
The previous full 127-case mutation record remains historical evidence.
The source manifest is refreshed, and HOUSE registers five explicit fallback
sites without adding unsafe functions. The kernel is unchanged. Stage B remains
open at the Acc runtime-elimination frontier.

## 2026-09-28: Stage B source types through tuple projections

Source recovery now selects a tuple component when the projection and section
have matching collection widths, the section has exactly that many legs, and
every leg has no binders. The entire recovered projection must be closed in
the current scope, including unused components. Selection preserves source
syntax and uses the existing pending-application stack, so tuple heads and
selected components can pass through aliases, annotations, lets, beta steps,
and nested projections. All four reduction forms share the 64-step budget.

Four new opaque-twin pairs cover global, dependent, local, and curried function
types. Direct cases cover component indices, annotations and outer variables,
malformed shapes and tuples, free components, and the exact 64/65 boundary in
heads, results, and mixed reduction chains. Three unknown-scope controls now
use case expressions, which remain outside source recovery.

The inline suite has 118 cases. The erasure gate compares 73 inline pairs,
including 41 with different carried outputs, and all 16 Bend test programs
pass. Seven new mutations check projection recovery, shape agreement, tuple
arity, scope, binder arity, component selection, and fixture binding. Scoped
validation also exercises five existing beta scope, fuel, work-bound, and
pending-frame mutations, and three existing inline mutations for local types,
shape payloads, and leg scope. The full 127-case mutation record remains
evidence for its earlier slice. All 15 selected mutations were caught after their
variants compiled successfully. Current results and source hashes are recorded in
`dev/validation/projection-source.json`.

The first full gate attempt stopped at the expected source-integrity check
because the migration manifest still pinned the previous four Bend sources.
The reviewed manifest now pins the implementation and tests in this slice.
The HOUSE registry adds three explicit projection fallback sites and no
unsafe functions. Stage B remains open at the Acc runtime-elimination frontier.

## 2026-09-28: Stage B source types through head annotations

Source recovery now opens head annotation wrappers whose body and annotation
are closed in the current scope. Each wrapper consumes one step from the
existing shared 64-step let and beta budget. Pending applications survive the
step, and annotations inside function domains and codomains retain their source
syntax. The kernel and its trusted-line budget are unchanged.

Four lambda pairs cover global, dependent, local, and curried types. Two motive
pairs cover dependent and curried application results. Each semantic row
requires a closed postulate, rechecks the transformed program, and compares
with its opaque twin. Direct tests cover outer variables, source syntax, open
bodies and annotations, the exact 64/65 boundary, and mixed annotation, let,
and beta chains. Unknown-scope controls now use nonpoint tuple projections.

The semantic suite has 111 cases and the integration gate compares 69 inline
pairs. Five new mutations bring the erasure battery to 132. Validation of this
slice uses the five new mutations, the changed let annotation anchor, and the
shared beta pending-frame and transition-bound mutations. The full 127-case
mutation record remains historical. The attempted full rerun was stopped
because of its runtime; no partial result replaces that full record.
Mutation testing exposed an inadequate body-closure regression: a bare free
variable was rejected later as an unresolved alias. The strengthened test
puts the free variable inside a function domain, isolating the closure guard.
All eight scoped mutations were caught after that correction, and the current
baseline passed all 111 semantic cases and 73 fixture pairs. The 16-program
Bend test suite passed before the body-closure test was strengthened. The
scoped baseline then reran only the inline suite. Detailed outcomes, source
hashes, and logs are in `dev/validation/annotation-source.json`. A later
review fix changed one guard row in `Suite.lambda_alias_guards`: it now calls
the lambda context directly, so the open annotation reaches the annotation
step instead of the alias closure check. The source hashes in that record
predate this fix. The full Lean release runner timed out
after 900 seconds during Stage A, so this entry does not claim a release pass.
Stage B remains
open for Acc runtime elimination, full trace comparison, and source reductions
beyond the documented subset.

## 2026-09-27: Stage B source types through beta reduction

Source recovery now reduces point applications whose head resolves to a
single-binder section. Head aliases, local function aliases, intervening lets,
and curried applications preserve source syntax. Applications and sections must
have point shapes with matching address and binder quantities respectively.
The recovered application must be closed in the current scope. Let and beta
steps share a 64-step budget, consumed before descending into an application
head and threaded into its result. Cycles and exhausted recovery yield no type.
The kernel and its trusted-line budget are unchanged.

Four lambda pairs and two motive pairs require a generated closed postulate,
recheck the transformed program, and compare it with its opaque twin. Direct
cases protect source syntax, outer variables, shape and quantity guards,
single-binder arity, cyclic heads and results, and the exact shared budget.
A direct case also reduces a head let while its application is pending.
Unknown-scope controls now use annotated type wrappers and retain their
conservative assertions. The suite has 102 cases and compares 63 inline pairs;
12 new mutations bring the erasure battery to 127. A structural step bound
allows each beta step to push and pop its pending application before the final
result. Thus the Bend implementation also checks termination directly. The step
bound does not limit substitution work, because duplicating let or beta
arguments can double the term at each step. A cap of 4096 syntax nodes on each
let or beta result bounds that work, and a doubling let chain tests the cap.

Validation passed with 102/102 inline cases, 63 matching inline pairs,
127/127 erasure mutations caught, and 5/5 Lean release checks. The release
checks reran Stage A and all 16 Bend test programs. The Lean corpus accepted
24/24 cases and refused 12/12, with zero axioms. The trace-frontier check
retained its expected refusal. Refreshed records are in
`dev/validation/erasure.json`, `dev/validation/erasure-mutations.json`, and
`dev/validation/lean-twin-checks.json`.
We removed the final blank line from eight new mutation logs before staging.
We updated their recorded hashes. Their diagnostics did not change otherwise.

Stage B remains open for Acc runtime elimination, full trace comparison, and
source reductions beyond the documented subset.

## 2026-09-27: Stage B source types through head lets

The shared lambda and application source resolver now reduces head lets,
including lets reached through global and local aliases. Source substitution
preserves annotations, universe syntax, binder quantities, and outer variables.
The annotation and value must be closed in the current scope, and the body
must be closed under its let binder. Each recovery permits 64 let reductions;
each intervening alias chain retains its declaration-count bound. Cycles and
exhausted recovery return no source type. Beta reduction and annotated type
wrappers remain unsupported. The kernel and its trusted-line budget are unchanged.

Four lambda pairs cover global, dependent, nested local, and curried types.
Two motive pairs cover dependent and curried applications. Every semantic row
requires a closed postulate, rechecks the transformed program, and compares
with its opaque twin. The gate binds each row to its exact fixture pair and
checks the embedded fixture bytes. Direct cases cover source syntax, free
variables in all three let positions, cycles, binder scope, and the exact
64/65 reduction boundary. Existing unknown-scope fixtures now require beta
reduction and retain their refusal checks.

The suite has 91 cases, the integration gate compares 57 inline pairs, and
11 new mutations bring the erasure battery to 115. Stage B remains open for
Acc runtime elimination, full trace comparison, and the documented source limits.

## 2026-09-27: Stage B lambda scopes through function type aliases

Lambda scope recovery now follows the same transparent global and local let
alias chains as application source recovery. It retains source domain and
codomain syntax, uses the declared binder quantity, and shifts local alias
bodies into the use scope. Opaque, recursive, partial, cyclic, and open alias
bodies remain unsupported. Let reduction and other normalization stay open.

Four new fixture pairs cover global chains, dependent types, local chains
beneath outer binders, and curried codomain aliases. Each pair failed to seal
before the change. Their semantic rows require one closed postulate, recheck
the transformed program, and compare with an opaque twin. The gate checks
the embedded fixture bytes and binds each row to its exact pair. Two direct
cases cover refusal guards, the alias hop bound, binder quantity and names,
and preservation of source annotations. Existing unknown-scope regressions
now use types requiring let reduction and retain their refusal assertions.

The suite has 81 cases and the integration gate compares 51 inline pairs.
Four new mutations bring the erasure battery to 104. The kernel is unchanged.
Stage B remains open for Acc runtime elimination, full trace comparison,
and the other documented source-recovery limits.

## 2026-09-26: Stage B function source types through aliases

Application source recovery now follows transparent nonrecursive global
aliases and local let aliases until it reaches a syntactic function type.
It checks alias bodies in their declaration scope before shifting local
bodies into the use scope. A bound derived from the visible declarations
terminates cyclic inputs. Opaque, recursive, and partial definitions remain
conservative, and arbitrary type normalization remains open.

Four new fixture pairs cover global chains, dependent function types, local
chains under outer binders, and curried calls. Their semantic cases require
one closed proof postulate, recheck the transformed program, and compare it
with the opaque twin. Five direct cases cover scope, shifting, a local alias
that names a global alias, the hop bound, and refusal guards. The suite has
75 cases and the gate compares 47 inline pairs. Eleven new mutations bring
the erasure battery to 100 cases.

The kernel and its trust budget are unchanged. Stage B remains open for
Acc runtime elimination, full trace comparison, and the other documented
source-recovery limits.


## 2026-09-25: Stage B source types for function applications

Scrutinee source recovery now follows function applications with syntactic
point-function types. It substitutes each argument into the codomain using
the existing source walker, removes the function binder, and preserves outer
variables and source annotations under nested binders. This supports global,
local, dependent, and curried function calls without changing the kernel.
Unsupported heads and addresses remain conservative; free codomains and
arguments are refused before substitution.

Four new motive fixture pairs require one sealed proof, recheck the
generated postulate and program, and compare with an opaque twin. The gate
ties their embedded source strings and semantic rows to the fixture files.
Two direct rows check binder capture and six unsupported or malformed input
forms. The suite now has 66 cases and 43 inline fixture pairs.
Five new mutations target disabled recovery, shifted outer variables,
free codomains, free arguments, and nonpoint function types.

Stage B remains open for the seven items in dev/validation/erasure.json.
These include unnamed motive scopes whose source scrutinee type needs alias
unfolding, lambda scopes without a syntactic expected function type, Acc
runtime elimination, and full trace comparison.

## 2026-09-25: Stage B proofs in unnamed motives

Unnamed motives now retain the source type of their erased self binder.
The eraser recovers it from an annotated scrutinee, a global declaration,
or a typed local binder, including a let. It requires a source type closed
in the current scope and refuses context recovery for index binders or an
inductive elimination shape. The trusted kernel is unchanged.

Five `motive-plain-*` fixture pairs cover annotations, globals, typed locals,
lets, and a sum type dependent on an outer type binder. Their semantic rows
require one closed proof postulate, recheck its type and the rewritten
program, and compare the erased output with the opaque twin. The gate binds
each case to its fixture files. Separate checks cover malformed scopes,
missing source types, and self's erased quantity and original source domain.
The quantity check uses a source type other than `Nat` and compares both
the Inline parameter and the quoted checker entry with it. Each guard
check reports its own message.
The semantic suite has 60 cases and the erasure gate compares 39 inline
pairs. The ten motive pairs and eight parameterized branch pairs rely on
the semantic sealing checks because their carried runtime outputs agree.

Nine new mutation cases bring the battery to 84: disabled recovery, runtime
self, a free source type that passes both closure checks (the
`Inline.source_expected` filter and the self binder closure check),
unexpected indices, an inductive shape, a redirected fixture pair, a
hardcoded `Nat` self domain, a different checker entry type, and a source
type for an unsupported scrutinee term.
Validation is recorded through the erasure gates, mutation battery, and
Lean twin checks. The source manifest and HOUSE test fallback registry are
refreshed. Stage B remains open for additional source type inference,
indirectly typed lambda scopes, Acc runtime elimination, and the full trace
comparison.

## 2026-09-25: Stage B proofs in named inductive motives

Inline erasure now recovers the index and self binders of a named inductive
motive from checked family metadata. It specializes original index domains
with source parameter arguments and shifts those arguments beneath the new
indices when constructing the self type. Indices retain declaration order.
All motive binders have quantity zero, including indices declared with
quantity one in the family telescope. The kernel and its 6000-line bound are
unchanged.

The five `motive-index`, `motive-self`, `motive-dependent`,
`motive-parameter`, and `motive-parameter-indices` fixture pairs cover the new
contexts. The dependent family lives at Type 1 and the parameterized families
take an outer type variable. The `motive-parameter-indices` family has two
indices, so a parameter shift by a constant one gives an ill-typed self.
Each semantic row requires exactly one new closed proof postulate, checks its
type and declaration rows, rechecks `keep`, and compares runtime output with
the opaque twin. Separate guard rows cover missing family metadata, absent
names and parameter syntax, mismatched families and index counts, wrong
parameter arity, free arguments and index domains, and erased binder quantities.

The semantic suite has 53 cases. The erasure gate compares 34 inline pairs:
21 reproduce a carried runtime difference, while eight parameterized branch
pairs and five motive pairs already agree in the carried eraser. The latter
13 rely on semantic sealing checks. Motive suite strings must equal the
fixture files, and the gate ties every motive and parameterized branch
case in `Suite.cases` to its exact pair and one-postulate assertion. Fourteen
new behavior mutations and three fixture-binding gate mutations (seventeen
new cases) bring the battery to 75 cases. Two older parameter mutation anchors now include their branch
validation context so they still select exactly one expression.

Validation is recorded by `dev/erasure-gates.py --record`,
`dev/erasure-mutations.py --jobs 2 --record`, and
`dev/lean-twin-checks.py --record`. The Bend migration source manifest is
refreshed for the added fixture module.

Stage B stays open. Motives without an explicit family name, scrutinee types
needing additional inference or normalization, indirectly typed lambda
scopes, Acc runtime elimination, and full trace comparison remain outside
this increment.


## 2026-09-24: Stage B parameterized constructor branch proofs

Branch-local proofs now seal when the constructor belongs to a parameterized
family and the scrutinee has a source type available from an annotation,
global declaration, or typed local binder (including a let). The eraser checks
the family shape, parameter count, argument scope, constructor quantities,
and field dependencies before specializing the original field syntax.

The shared source traversal substitutes parameters without normalizing
universes. It shifts free variables under field, function, let, motive, and
branch binders. The explicit task dispatcher is the only new `@unsafe` site:
it walks finite syntax, and substituted arguments are traversed only in shift
mode, so substitution cannot recursively expand an argument.

The new dependent witnesses exposed an existing quotation bug. Quoting a
stuck elimination copied its branch and motive syntax without applying the
captured environment. Moving the result under newer binders could capture an
outer variable. Quotation now opens the motive, branch and point closures on
fresh variables in the captured environment and quotes their bodies under
the new binders. It reads only the environment entries that these bodies
use. A first version quoted every environment entry before it substituted
them, so checking time doubled with each nested stuck let. The new Stage A
QUOTE-DEPTH row checks a chain of 24 nested stuck lets within 10 seconds;
the first version did not finish in 45 seconds. A hand-written opaque proof
reproduced the capture failure on the prior compiler, and the new quotation
mutation checks this correction.

Eight source/opaque pairs cover concrete and dependent parameters, function
fields, annotated scrutinees, lets, globals, two constructors of the same
field shape, and a proof field at a universe. Their semantic rows require
exactly one generated postulate and recheck its closed type. Nine malformed
metadata probes exercise the conservative fallback. The carried eraser gives
the same runtime output for both sides of these eight pairs, so their runtime
rows are identical but do not discriminate: they pass also when no proof is
sealed. The gate requires this carried equality, records it as
`runtime-identical-coarse`, and keeps the runtime-difference requirement for
all twenty-one earlier pairs. The two groups must be disjoint, and each
parameter pair must have a semantic suite row. The semantic suite reads its
own copies of these sources in `erase/test/parameter_fixtures.bend`, so the
gate requires each copy to equal its `.att` file byte for byte.

The kernel stays within its existing 6,000-line bound at 6,000 lines, with no
lines of headroom. Removing
76 lines of unused tuple/list helpers, an obsolete primitive reduction path,
and unused wrapper reconstruction functions made room for the shared source
traversal. The generated driver JavaScript is byte-for-byte unchanged by this
cleanup. The helper removal changed no gate threshold. The erasure gate now
exempts the eight parameter pairs from the carried runtime-difference check
(see above).

The full build, all sixteen test programs, Stage A gates, and erasure gates
pass. All thirteen Stage A mutations are caught. The kernel unit suite passes
34/34 cases and the inline semantic suite passes 46/46 cases, including the
new parameter witnesses. All twenty-nine inline runtime pairs agree.
All fifty-eight erasure mutations are caught, including the fifteen new parameter
and quotation probes and two motive quotation probes that kernel unit case 17
catches. The Lean twin check (`python3 -P dev/lean-twin-checks.py`) refuses
a record whose log hashes do not match its logs. The frozen OCaml reference and its single existing divergence
allowance are unchanged.

The frozen comparison matches 936/941 approved expected results after bounded
retries. The initial two-worker run at 180 seconds matched 930 cases and had
eleven timeouts. Four checking cases matched with 600-second limits, and the
remaining two multiplication checking modes matched in sequential runs with
900-second limits. Five arithmetic agreement cases still time out under
load, and the set of cases that time out changes with the load. No output
mismatch occurs, and no new divergence allowance was introduced. The
sequential multiplication print and axiom checks took 453.981 and 414.136
seconds; the previous committed addition checker also needed 301.489 seconds
under load.

Stage B remains open. Motive binder contexts, source types requiring further
inference or normalization, Acc runtime elimination, and trace comparison
remain outside this increment.

## 2026-09-24: Stage B constructor branch proofs

The Bend inline eraser now recovers constructor field contexts from the
checked family metadata. Families without parameters supply their original
field types, quantities and dependent field order. The traversal retains the
outer local telescope across nested branches. It rejects mismatched binder
counts or quantities and field types that refer beyond earlier fields.
Missing metadata and parameterized families keep the conservative fallback.
No kernel rules or semantic recursion exemptions changed.

The existing `branch-local-proof.att` frontier pair now joins the passing
inline regression set. New dependent-field and nested-branch pairs cover
proof hypotheses and references to both outer and branch-local variables.
A multi-constructor pair requires the fields of the named constructor.
The semantic suite passes 37 cases, including closed generated postulate types,
rechecking rewritten definitions, metadata guards, fallback behavior and the
root scope of an alias-typed lambda leg.
`dev/validation/erasure.json` records 4 global proof pairs and 21 inline
pairs. Each inline pair is identical to its opaque twin and different with
the carried eraser, and the semantic suite log records 37 of 37 cases.
`dev/validation/erasure-mutations.json` records 41 of 41 mutants caught.
`dev/validation/stage-a.json` pins the sources of this slice. In that
record, Stage A passes its 337 kernel cases and benchmark, and the 13
Stage A mutations are caught. `dev/validation/lean-twin.json` pins the
sources of this slice. In that record, the Lean twins pass 24 accepted and
12 refused cases. `make test` passes all 16 programs.

The migration differential now allows exactly one named divergence from the
frozen OCaml reference: `build --erase fixtures/erasure/branch-local-proof.att`.
The Bend eraser keeps `keep` as the runtime identity, which is identical to
its opaque twin. The OCaml reference erases `keep`.
`dev/validation/differential-divergences.json` pins the digest of the frozen
reference row and the replacement output. The differential fails if the
reference row changes or if the Bend output equals the reference row again.
`dev/validation/ocaml-reference.json` does not change.

Stage B remains open. Motive binders, parameterized constructor branches,
indirectly typed lambda scopes, source-free local proof types and family
metadata rewriting remain outside this slice. The Acc restrictions and the
nonzero TRACE-ERASURE result are unchanged.



## 2026-09-23: Stage B local inline proofs

Extended `erase/inline.ml` with a local checker context and a telescope of
original domain types. Typed function, let, and type-former binders can now
contribute erased parameters to a closed proof postulate. Applications use
the original local order, including dependencies between parameter types.
Keeping source domain and codomain syntax avoids confusing empty runtime
products with propositions during readback. Known proof bodies remain opaque.

The local Nat index frontier now closes. Ten new fixture pairs cover
dependent local types, let indices, let-bound type aliases, type-former
diagrams, runtime calls returning proof-computed types, and proof lets whose
value a local proof type reduces, directly or through the value of any later
let, including a proof let alias chain, a type family and a let typed by a
universe alias. All seventeen inline
pairs reproduce a difference with the carried eraser and agree after sealing.
A let keeps its value in the telescope, so a local proof type can use a
let-bound type alias. A local proof whose value reads a local hypothesis
abstracts over that hypothesis. A proof let keeps its value, in the program
and in the telescope of each local proof sealed in its body, when its variable
occurs in its body in an annotation, a let type, the value of a later let, a
motive, a shape payload or a type former. A proof let that a dependent large
elimination reads only as its scrutinee is still sealed, and erasure refuses
the program (`build --erase` exits 2), also at `c26c41a`. A postulate type keeps the value of a kept proof let
verbatim. The semantic suite has thirty-one rows, including closed postulate types,
rechecking dependent applications, poisoned local bodies, inherited entries,
universe preservation, payloads, and unknown branch scope isolation.

Stage B stays open. `branch-local-proof.att` pins the remaining constructor
branch frontier. Motive binders (no pinned row), lambda scopes without a syntactic expected
function type, local proofs without source type syntax, unannotated
introductions without an inferable type, and
family metadata remain conservative. Both Acc refusals remain pinned.
No carried kernel source or carry-manifest hash changes in this slice.

The erasure mutation battery contains thirty-two compiled mutations.
Records are generated by `dev/erasure-gates.py --record` and
`dev/erasure-mutations.py --record` from the attest checkout.


## 2026-09-23: Stage B closed inline proofs

Added `erase/inline.ml` between global proof sealing and the carried eraser.
It classifies closed proof terms in the original checked environment and
replaces them with fresh typed postulates. The erasure environment and its
declaration rows share the rewritten entries. Closedness accounts for type
syntax, shape payloads, motive binders, and term binders. No carried kernel
source or carry-manifest hash changes in this slice.

The let-bound and direct-scrutinee frontiers now close, along with both pair
projection positions. Six inline fixture pairs compare runtime output
after dropping erased declaration notices. Every pair also reproduces the
old runtime difference through `dev/erase_probe.exe`. Thirteen semantic tests
cover poisoned proof bodies, inherited entries, both namespaces, runtime
lets, type-only locals, declaration-row consistency, binder depth, motive
and shape-payload closedness, redeclared globals, and payload postulates.

Stage B stays open. `local-proof.att` pins the remaining local-index proof
frontier; unannotated introductions without an inferable type and family
metadata remain outside the pass. The two Acc refusals are unchanged.
The erasure mutation battery now contains seventeen compiled mutations.
Records are generated through `dev/erasure-gates.py --record` and
`dev/erasure-mutations.py --record` from the attest checkout.



## 2026-09-23: Stage B erased Prop indices

Adapted `lib/check.ml` to admit erased indices of Prop families independently
of their universe. A constructor field above the family universe is allowed
only in Prop, at quantity zero, and when it occurs as a direct result index.
The result indices are still type checked. Type family bounds, positivity,
and the recursive singleton criterion are retained.

`fixtures/erasure/acc-family.att` now checks its family and constructor
application. `acc.att` reaches the erased-proof runtime-read refusal;
`acc-runtime-proof.att` reaches the recursive-singleton refusal. Both
diagnostics are pinned by the erasure gate. This is a Stage B increment;
inline proof erasure and full Acc runtime elimination remain open.

The new `erase/test/prop_index.ml` suite runs twenty-eight cases through the
surface checker, with eleven accepts and seventeen named refusals. Five new compiled
mutations target the index exception, retained Type bound, field quantity,
field-to-index requirement, and field telescope depth. The mutation harness
retains the failing regression output and checks its named row.

The carry manifest pins the exact checker adaptation. This is the first
adaptation of a carried kernel source; the plan's Stage A row pins lib/
verbatim and the manifest row records the departure (plan ruling R2-7).
No carried term, shape, or count definition changes. Erasure records are generated by
`python3 -P dev/erasure-gates.py --record` and
`python3 -P dev/erasure-mutations.py --record`.

## 2026-09-22: Stage B Lean checking corpus

Implemented the full LEAN-TWIN checking corpus: 24 ACCEPT and 12 REFUSE
pairs, with individual attest and Lean sources and a strict manifest. The
gate checks the pinned Lean version, complete source membership, term
proofs, and empty axiom reports. Refusal prefixes must check successfully;
the final declaration must fail for the expected reason in both languages,
with Lean diagnostic locations inside that declaration.

The default gate battery now includes LEAN-TWIN. Its standalone command is
`zsh -f dev/gates.sh LEAN-TWIN`. The carried gate wrapper's exact adapted
hash and CARRIED.md entry have been updated; no carried kernel or surface
source changed.

The corpus passes 24/24 ACCEPT and 12/12 REFUSE pairs. Thirteen mutation
controls pass and all thirteen mutations are caught. The executable records
are `validation/lean-twin.json` and `validation/lean-twin-mutations.json`,
with per-command logs and source hashes. The release check record
`dev/validation/lean-twin-checks.json` is written by
`python3 -P dev/lean-twin-checks.py --record`: it runs the full gate battery,
the forced dune tests, both record commands and the TRACE-ERASURE frontier,
pins each exit code, timing and log hash, hashes both records above, and
derives `record_hashes_verified` by rehashing the logs those records name.
See `lean/README.md` for coverage, refusal-site checks, and reproduction
commands.

Stage B remains OPEN on Acc checking and inline proof erasure. This corpus
covers the shared checking fragment and does not erase or conceal the
known Acc divergence. The initial F2, F2Neg, and Acc probes still run in
the separate ERASURE group. The earlier build-log entries and records
remain historical evidence of their own implementation trees.


## 2026-09-22: Stage A implementation

Carried 594 files from assay `eebe37e00ecb7fdce739c49f50a6dd49c45022b1`
and the pinned mechanism build wrapper. The kernel and surface OCaml sources
are unchanged. Twelve build and gate adaptations are listed in CARRIED.md
and frozen by exact hashes in dev/carry-manifest.json.

Implemented `attest check`, checked-form output, axiom disclosure, and
`spec-count`. The driver shares the carried result-returning file boundary.
The public package is attest; internal library names preserve upstream
module references. Dune runtest includes the fixture dependencies and
explicitly selects the kernel and surface runners.

Validation on the implementation tree. The gate battery ran on the checkout
/Users/oobi/Documents/gpt4/attest-stage-a, the working copy that produced
this slice; the attest repository carries the same files:

| check | result |
| --- | --- |
| BUILD | Passed with warnings as errors. |
| CARRY | 594 files, zero differences, zero unlisted paths; both origins checked against Git blobs. |
| R0-COUNT | Two formers, four schema constructors, five declared shapes, three admitted shapes. |
| R0-AUDIT and R0-DIFF | Passed; three canonical files agree with kanon 2c2e6e6. |
| HOUSE | Passed, with one inherited catch site and the exact CLI argument-dispatch allowance. |
| DRIVER-EXIT | 13 success, refusal, disclosure, and filesystem cases passed. |
| SUITE-KERNEL | 337 checks passed; seven-run median 207.645 ms in the recorded run. |
| SL-SURFACE | 20 checks passed. |
| AXIOMS-empty | The Stage A ACCEPT example reports zero axioms; a separate postulate fixture reports one. |
| TRUSTED-LINES | kernel 3997/4100, lower 0/1100, encoder 0/800, harness 0/100; whole-lib 6193 informational. |
| Rung 1 | Measured parse and combined elaboration/check on the named, hashed example. |
| Dune runtest | Exit 0; the wrapper's custom-runner summary does not supply test counts. |
| Mutation probes | 13/13 caught after a fresh successful baseline gate run. |

validation/stage-a-gates.txt is the positive gate transcript captured on
that checkout. Its one path row (the HOUSE catch site) is rewritten to the
tree-relative form that dev/house.sh prints since the review round of
2026-09-22, and baseline_sha256 is repinned over the rewritten text; the
record is captured again from this tree at the close of the review.
validation/stage-a.json pins the implementation files and records the
mutation diagnostics. The probes are rerunnable with `zsh -f dev/mutations.sh`;
`MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root also
rewrites validation/stage-a.json, validation/stage-a-gates.txt and
validation/mutations/<name>.log.

Integration fixes found during validation: include Sys_io in the kernel
test stanza; reuse that boundary in the driver; explicitly select Dune's
root through DUNE_ROOT so nested mutation copies build themselves. The
wrapper's dunecho frontend does not accept Dune's --root flag directly.
Final local review tightened unknown-origin and symlink handling in the
carry gate and tied R0 snapshot checksums to the pinned carry hashes.

This entry records local implementation review and executable validation.
No independent review agent, commit, or milestone ratification is claimed.
The changes are prepared for the user's review and commit.

Next: Stage B's opaque-proof erasure work. USER step 8 remains required for
a green TRACE-ERASURE row. Stage 0 toolchain, SP1, and denominator tasks are
not closed by Stage A. Rungs 2 and 3 remain OPEN until denominator freezing.

## 2026-09-22: Stage B erasure increment

Starting from Stage A commit `9a03183`, implemented `attest build --erase`
and a proof-opaque erasure environment in `erase/opaque.ml`. Classification
uses checked types; every Prop-valued definition becomes a typed postulate
before erasure. Both the full environment and the declaration stream are
sealed, so the carried program walker cannot restore proof bodies. Runtime
definitions, types, and the family table are preserved. No kernel or surface
source changed; all 594 carried files still pass the provenance gate.

USER step 8 now has executable evidence. The F2 function and pair examples
both change erased output on the actual assay `eebe37e` checkout. Those four
pin outputs agree with the newly compiled carried eraser. The pin commit,
binary hash, fixture hashes, and output hashes are in
`validation/f2-pin.json`; `python3 -P dev/f2-pin-check.py ASSAY_PIN`
regenerates the evidence on a clean pin checkout whose assay.exe digest
matches the value pinned in the script.

Validation on the implementation working copy:

| check | result |
| --- | --- |
| Stage A gates | Passed, including 337 kernel tests, 20 surface checks, carry, R0, house rules, and line budgets. |
| Erasure regressions | Four pairs identical; all four differ with the carried evaluator; proof-shape control identical. |
| Opaque environment tests | Six tests cover direct proofs, aliases, proof functions, inherited scope, runtime reduction, classifier errors, and a poisoned proof body. |
| Erasure CLI | Six checks passed, including usage/input errors, check errors, and a checked but unsupported layout returning exit 2. |
| Initial Lean twins | F2 and Acc sources elaborate with Lean 4.33.1 under `-DwarningAsError=true` with empty logs; LEAN-TOOLCHAIN compares the lean that ran with `lean-toolchain`; a token guard rejects `by`, `sorry`, `admit` and `native_decide` outside comments; LEAN-AXIOMS prints the axioms of every enumerated declaration and allows only `F2Fixture.opaqueProof` and `AccFixture.R`. The Acc eliminator is noncomputable. |
| Erasure mutations | All five caught after successful builds in isolated copies, including the Lean `sorry` row. |
| Dune runtest | Passed, including the new erasure test executable. |
| Stage A mutations | Not rerun against the updated tree; the Stage A record is a historical snapshot. |

`python3 -P dev/erasure-gates.py --record` regenerates
`validation/erasure.json` and its logs with implementation hashes.
`python3 -P dev/erasure-mutations.py --record` regenerates mutation evidence.
The Stage A record remains a historical snapshot of its original tree.

Stage B remains OPEN. The concrete Acc seed is refused at its Nat index:
`index above universe: the index x of Acc lives at 1 and Acc is declared at 0`.
The Lean twin accepts the corresponding Prop family. The carried singleton
large-elimination criterion also excludes recursive families, so relaxing
the index check alone will not implement the planned Acc row. The full
24 ACCEPT / 12 REFUSE twin corpus and Acc erasure/mutation gates are not
claimed. `dev/gates.sh TRACE-ERASURE` fails explicitly on this frontier.
The existing carry pin and kernel budgets remain binding for the next step.

This entry records local implementation review and executable validation.
No independent review agent or Stage B completion is claimed.

## 2026-09-22: Bend 2 evaluator pilot

Added an optional evaluator subset under `pilot/bend2/` to test both proposed
migration benefits. The production kernel remains OCaml. Bend is pinned to
2.0.25, commit `ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b`.

The dependent scope and environment representation checks four laws, rejects
three invalid programs, and catches two mutations through failed proofs.
All 128 generated programs agree with attest's checked evaluator across
Bend native, Bend JavaScript, and the matched OCaml implementation.

The final seven paired measurements gave median fresh native builds of
508.83 ms for Bend versus 298.39 ms for OCaml (1.71 times longer), and
edited builds of 569.23 ms versus 237.64 ms (2.40 times longer). The
predeclared adoption gate required at least a 10% improvement in both.
The stronger scope guarantees passed; the build-speed gate failed.
Keep OCaml for the production evaluator under this toolchain.

`python3 -P pilot/bend2/run.py --bend-root PATH --record` regenerates
`dev/validation/bend-pilot.json` and its logs. The record pins compiler,
pilot, and oracle sources and retains all paired samples. See the pilot
README for the subset boundary, trusted components, and reproduction steps.
This experiment does not close the existing Stage B Acc frontier.

### 2026-09-22 (review fix F3: inline proof positions pinned as open)

The carried `lib/erase.ml` stays verbatim. Its let arm evaluates a
Prop-typed binding to its value and a case on an inline proof reduces, so a
proof written inside a runtime-typed definition keeps its body and selects
the erased layout. SPEC.md 1.1 names both positions as open. Four fixtures
(`let-proof`, `scrutinee-proof` and their `-opaque` twins) and the
`ERASURE-OPEN` rows of `dev/erasure-gates.py` pin the difference; the rows
fail when the frontier closes, which is the signal to move them into
`ROWS`. `dev/validation/erasure.json` is re-recorded with the new rows.
