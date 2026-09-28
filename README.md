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
increment compares four global proof pairs and sixty-nine inline proof
pairs against their opaque twins. It reproduces the carried eraser's layout
differences for the four global pairs and thirty-seven inline pairs, including
sixteen lambda alias, let, beta, and annotation pairs. The eight parameterized branch pairs and twenty-four motive pairs give identical outputs
with the carried eraser too, so their runtime rows do not discriminate; the
semantic suite checks their sealing on copies that the gate requires to
equal the fixture files, and the gate binds each of their suite cases to its exact pair. The gate also checks the initial F2 and Acc
witnesses plus the F2 negative probe. `python3 -P dev/erasure-mutations.py`
contains 132 isolated mutations. The full mutation record covers the preceding
127-case slice; annotation recovery has separate
[scoped validation evidence](dev/validation/annotation-source.json).
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
body and annotation are closed in the current scope. Annotation, let, and beta
steps share a limit of 64 reductions per recovery,
including reductions in the function head and its result. A let or beta
result with more than 4096 syntax nodes gives no type. Each alias chain
retains its declaration-count bound. Nonpoint tuple projections remain open.
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
One hundred and eleven semantic tests protect this boundary. Scrutinee types that need
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
