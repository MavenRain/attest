# attest

attest is a programming language with Kan extensions as its only type formers.  The compiler targets the RISC-V bytecode that Succinct SP1 proves.

M0 includes the carried Kan kernel, parser, checker, axiom disclosure, and
the Stage B erasure increment and 24 ACCEPT / 12 REFUSE Lean twins.
`attest build --erase` prints the
erased term with proof globals opaque. RISC-V emission and SP1 execution
follow in later stages of [the M0 plan](design/attest-m0/M0-PLAN.md).

The compiler, kernel, frontend and erasure passes are implemented in Bend 2.
With Bun (tested with 1.3.11), Git, Python 3, ripgrep and zsh available:

```sh
sh dev/setup-bend.sh
make build
_build/default/bin/attest.exe check corpus/id.att
_build/default/bin/attest.exe check --axioms corpus/id.att
_build/default/bin/attest.exe spec-count
_build/default/bin/attest.exe build --erase fixtures/erasure/f2-a.att
zsh -f dev/gates.sh
make test
zsh -f dev/mutations.sh
zsh -f dev/gates.sh LEAN-TWIN
python3 -P dev/lean-twin-mutations.py
```

The setup command checks out the pinned Bend 2.0.25 compiler under `_tools/bend`.
Set `ATTEST_BEND_ROOT` to use an existing checkout at the same revision.
JavaScript is the default backend; the executable launchers under
`_build/default` run Bun. The `.exe` paths preserve the existing CLI and gate
interfaces. Native compilation is optional and experimental. See the
[migration and build notes](dev/BEND-MIGRATION.md) for its current limitations.

The default gates also require the pinned Lean toolchain in `lean-toolchain`.
`zsh -f dev/gates.sh STAGE-A` runs the original stage alone. The erasure
increment compares four global proof pairs and one hundred and seven inline proof
pairs against their opaque twins. It reproduces the carried eraser's layout
differences for the four global pairs and seventy-five inline pairs, including
fifty-four lambda alias, let, beta, annotation, projection, finite case, constructor case, sum index, constructor index, nested index, and neutral index pairs. The eight parameterized branch pairs and twenty-four motive pairs give identical outputs
with the carried eraser too, so their runtime rows do not discriminate; the
semantic suite checks their sealing on copies that the gate requires to
equal the fixture files, and the gate binds each of their suite cases to its exact pair. The gate also checks the initial F2 and Acc
witnesses plus the F2 negative probe. `python3 -P dev/erasure-mutations.py`
contains 301 isolated mutations. The full mutation record covers the preceding
127-case slice; annotation recovery has separate
[scoped validation evidence](dev/validation/annotation-source.json), as does
[tuple projection recovery](dev/validation/projection-source.json) and
[finite case recovery](dev/validation/case-source.json) and
[constructor case recovery](dev/validation/constructor-source.json) and
[parameterized constructor case recovery](dev/validation/parameter-source.json) and
[indexed constructor case recovery](dev/validation/index-source.json) and
[recursive constructor case recovery](dev/validation/recursive-source.json) and
[index alias recovery](dev/validation/index-alias-source.json) and
[compound index recovery](dev/validation/index-reduction-source.json) and
[sum index recovery](dev/validation/sum-index-source.json) and
[constructor index recovery](dev/validation/constructor-index-source.json) and
[nested index recovery](dev/validation/nested-index-source.json) and
[neutral point index recovery](dev/validation/neutral-index-source.json).
`python3 -P dev/validation/neutral-index-source-run.py` collects the full tests,
default gates, erasure record, and 24 scoped mutations for the neutral index slice.
`python3 -P dev/validation/neutral-projection-source-run.py` records the full
tests, default gates, erasure record, and 13 scoped mutations for
[neutral collection projection recovery](dev/validation/neutral-projection-source.json).
`python3 -P dev/validation/sum-payload-source-run.py` records the full tests,
default gates, erasure evidence, and scoped mutations for
[numeric sum payload recovery](dev/validation/sum-payload-source.json).
`python3 -P dev/validation/tuple-payload-source-run.py` records the full tests,
default gates, erasure evidence, and 15 scoped mutations for
[numeric tuple field recovery](dev/validation/tuple-payload-source.json).
`python3 -P dev/validation/neutral-case-source-run.py` records the full tests,
default gates, erasure evidence, and 12 scoped mutations for
[neutral numeric case recovery](dev/validation/neutral-case-source.json).
`python3 -P dev/validation/neutral-constructor-source-run.py` records full tests,
default gates, the erasure record, and 16 scoped mutations for
[neutral constructor case recovery](dev/validation/neutral-constructor-source.json).
`python3 -P dev/validation/neutral-composition-source-run.py` records full tests,
default gates, the erasure record, and five scoped mutations for
[composed neutral source indices](dev/validation/neutral-composition-source.json).
The default gates also run all 36 pairs in
`lean/corpus.json`; `dev/lean-twin.sh --record` records their evidence.

The checker now admits erased indices of `Prop` families, including the
`Acc` declaration and constructor in `fixtures/erasure/acc-family.att`.
Twenty-eight regression cases cover their universe and quantity boundaries.
Stage B remains open: `Acc` runtime elimination still hits the erased-binder
and recursive-singleton restrictions. Closed inline proofs and proofs under
typed function, let, type-former, constructor branch, and motive binders now erase like
their opaque twins. Branch contexts use the original constructor field types
of families with and without parameters, including dependent fields and nested scopes.
Parameterized branches recover arguments from an annotated scrutinee, a global
declaration, or a typed local binder (including lets). Source substitution keeps
dependent fields and universe syntax intact. Named motives recover dependent
indices and self from the family telescope, specialize parameter arguments,
and shift those arguments beneath the fresh index binders. Both indices and
self remain erased. Unnamed motives recover an erased self binder from the
scrutinee's annotation, global declaration, or typed local binder, including
lets. Function applications recover their result type from a syntactic
function type, substituting arguments without capturing outer variables.
This includes dependent and curried calls. Transparent global and local let
aliases can expose the function type while preserving its source syntax.
Lambda scopes use the same recovery for their expected types, including
dependent and curried functions and local alias chains beneath outer binders.
Source types can also expose a function through head let and beta reduction.
Point applications recover a single-binder section through aliases, lets, and
nested applications. Substitution preserves outer variables, universes, and
annotations. Head annotation wrappers expose their body only when both the
body and annotation are closed in the current scope. Tuple projections select
a component from a section with matching collection widths, exactly that many
legs, and no leg binders. The entire recovered projection must be closed in
the current scope, including unused components. Finite cases select a branch
from an injection with the same collection width and exactly one payload.
Branches must cover every numeric address once, in any order, and each must
bind one variable. Recovery substitutes the payload into the selected branch
without capturing outer variables. The whole recovered case must be closed,
including unused branches and its optional unnamed, unindexed motive.
Constructor cases recover types from complete, positive families, including
recursive constructors. Both shapes must name the same family and carry the
declared number of index values. Payloads must match directly or after
transparent head aliases, lets, beta steps, annotations, tuple projections,
and concrete sum or constructor cases expose matching syntax. Each index payload has a separate
64-step budget. Sum cases share that budget with their scrutinee and selected
result and retain the collection width, complete branch coverage, binder,
motive, scope, and substitution checks. Constructor cases inside index
payloads use the existing complete-family and field checks. Their elimination
and injection shape payloads may expose equal syntax through the same bounded
recovery. Both sides, later payloads, and the selected result share the enclosing
64 reductions and 129 pending-frame transitions. Equal shape payload lists take
the direct path. Nested comparison never restarts either budget.
Neutral point applications retain their recovered head and point shape while
their arguments use the enclosing reduction and transition budgets. Curried
applications share those budgets across the function head and every argument.
Point quantities must match their shapes, and reconstructed applications have
the same 4096-node cap as substitution results. Neutral numeric collection
projections recover their heads, preserve their addresses, and require a
matching collection shape and an address within its width. Rebuilt projections
share the existing budgets and node cap. Numeric sum injection indices recover
their single payload under the same budgets, preserving their collection shape
and address. The address must be within the collection width, and the entire
injection must be closed and fit the node cap. Concrete case scrutinees keep
their existing case recovery path. Numeric tuple indices recover their fields
in source order under the same budgets. Their collection width must equal the
field count, fields must have no binders, and the complete tuple must be closed.
Tuple entry consumes one reduction, and reconstruction retains the node cap.
Concrete projections recover only the selected field, while point sections
retain their existing application path. Neutral numeric cases recover their
scrutinees ending at globals, local variables, point applications, or numeric
collection projections under the same budgets and retain branch bodies, motives, quantities,
and branch order. Their collection branches must cover every address once and
bind one variable each; motives remain unnamed and unindexed. The complete
case must be closed and fit the node cap. Neutral constructor cases recover
the same scrutinee forms for complete, positive families. Family names, index
counts, telescope scope, motives, branch coverage, and field binders must match
the family metadata. Their branches, motives, quantities, order, and shape
payloads keep their source syntax under the same budgets and node cap.
Recovered neutral numeric and constructor cases can themselves supply a case
scrutinee, point application head, or numeric collection projection head.
Each inner case passes recovery before the outer syntax is rebuilt. Nested
heads and application arguments share the same reduction and transition budgets.
Neutral globals and parameters retain their
source syntax, and local aliases shift into the current scope. Parameter values live in
the scrutinee's type. Parameter types must be closed over earlier parameters;
index types may depend on parameters and earlier indices, while field types
may depend on parameters and earlier fields. Constructor result indices must
have the declared count and be closed over parameters and fields.
Parameterized constructor introductions use their expected family type, including
annotations, typed lets, and function arguments. Constructor calls supply only
fields. The kernel checks their field types and result indices. An introduction
without an expected type remains unsupported.
Every constructor must have exactly one branch with matching field
quantities and arity. Recovery substitutes all fields together while preserving
outer variables. Recursive constructors supply only their fields, so a case
does not add induction hypotheses or recursively traverse its fields. Nested
cases use the same shared reduction limit. The whole case must be closed, including unused branches and
its motive. Indexed families require a motive naming the matching family with
the declared number of index binders. Unindexed motives remain optional.
Annotation, let, beta, projection, and case steps share a limit of 64 reductions
per recovery outside index payloads, which have their own 64-reduction budget
each, including reductions in heads, scrutinees, and selected results. A let,
beta, or case result with more than 4096 syntax nodes gives no type. Each alias chain
retains its declaration-count bound. Source recovery through
provisional or builtin constructor families, index payloads that remain unequal
after bounded head recovery, or neutral heads beyond the supported forms remains open.
Alias bodies must be closed in their declaration scope; opaque, recursive,
partial, and cyclic aliases remain unsupported. The source type must be closed
in the current scope; unnamed motives
with index binders or an inductive elimination shape stay conservative.
Quotation opens the motives and
branches of stuck eliminations on fresh variables in their captured environment.
A proof let keeps its value when its variable occurs in its body in an
annotation, a let type, the value of a later let, a motive, a shape payload
or a type former. It then also keeps its value in the telescope of each local
proof sealed in its body. So a proof let alias chain, a type family and a let
typed by a universe alias stay transparent. The test examines no other
position. A proof let that a dependent large elimination reads only as its
scrutinee is still sealed, and erasure then refuses the program
(`build --erase` exits 2). The same limit is at commit `c26c41a`.
The inline suite contains 240 semantic cases, including this boundary. Scrutinee types that need
normalization or inference beyond those source forms,
lambda scopes requiring further normalization, local proofs without source type syntax,
unannotated introductions without an inferable type, and family metadata remain open.
`zsh -f dev/gates.sh TRACE-ERASURE` runs the erasure regression, prints the
remaining Acc frontier rows, and always exits 1 until the Stage B
trace comparison exists.
See [the build log](dev/M0-BUILD-LOG.md).

The Lean package is reusable with `require attestTwin from "../attest"` in
a dependent project's `lakefile.lean`, followed by `import AttestTwin`.
Its sources use term proofs; the `Acc` witness checks elimination in the
kernel and is explicitly noncomputable. The separate LEAN-TWIN corpus covers
the shared checking fragment, with accepted declaration prefixes pinning
every refusal site. See [the corpus guide](lean/README.md).

See [SPEC.md](SPEC.md) for the current command contract and
[CARRIED.md](CARRIED.md) for provenance and the documented carry adjustments.
The package is licensed under MIT OR Apache-2.0.

The earlier [evaluator pilot](pilot/bend2/README.md) is historical. The production
port includes the complete checking, elaboration and erasure paths, with a
captured OCaml reference corpus for exact behavioral comparisons.

The design corpus is under design/:

- kan-sp1-lang-design-brief.md: the design brief and the ratified rulings (section 10).
- kan-sp1-lang-dossier-kernels.md, kan-sp1-lang-dossier-toolchain.md, kan-sp1-lang-dossier-priorart.md: the three scout dossiers.
- kan-sp1-lang-proposal-1.md to -3.md and kan-sp1-lang-attack-1.md to -3.md: the three proposals and the three attacks of the design panel.
- kan-sp1-lang-design-verdict.md: the panel verdict, the milestones and the Stage 0 steps.
- kan-sp1-lang-design-panel.js and kan-sp1-lang-design-panel.json: the panel script and its run record.
- attest-m0/M0-PLAN.md: the M0 plan, with its section parts under attest-m0/parts.
- kan-sp1-lang-m0-plan.js, kan-sp1-lang-m0-plan.json, kan-sp1-lang-m0-attack-1.md to -3.md, kan-sp1-lang-m0-adjudication.md, kan-sp1-lang-m0-reverify.md: the M0 plan script, its run record and its review records.
- kan-sp1-lang-m0-handoff/: the handoff notes the plan units wrote.
- kan-sp1-lang-bend-cli.txt, kan-sp1-lang-design-panel-tail.js, kan-sp1-lang-design-panel-p1-tail.js: scout notes and script chunks from the panel authoring rounds, kept as a record.
