# attest

attest is a programming language with Kan extensions as its only type formers.  The compiler targets the RISC-V bytecode that Succinct SP1 proves.

M0 includes the carried Kan kernel, parser, checker, axiom disclosure, and
the Stage B erasure increment and 24 ACCEPT / 12 REFUSE Lean twins.
`attest build --erase` prints the
erased term with proof globals opaque. RISC-V emission and SP1 execution
follow in later stages of [the M0 plan](design/attest-m0/M0-PLAN.md).

With OCaml 5.2 or newer, Dune 3.24, Zarith 1.14, Python 3, ripgrep, and zsh
already available:

```sh
zsh -f dev/dunecho.sh build
_build/default/bin/attest.exe check corpus/id.att
_build/default/bin/attest.exe check --axioms corpus/id.att
_build/default/bin/attest.exe spec-count
_build/default/bin/attest.exe build --erase fixtures/erasure/f2-a.att
zsh -f dev/gates.sh
zsh -f dev/dunecho.sh test
zsh -f dev/mutations.sh
zsh -f dev/gates.sh LEAN-TWIN
python3 -P dev/lean-twin-mutations.py
```

The build wrapper uses `dunecho` when available and otherwise Dune. Set
`ATTEST_OPAM_SWITCH` to select an installed switch. The tools install nothing.

The default gates also require the pinned Lean toolchain in `lean-toolchain`.
`zsh -f dev/gates.sh STAGE-A` runs the original stage alone. The erasure
increment compares four proof-bodied/opaque pairs, reproduces the carried
eraser's layout differences, and checks the initial F2 and Acc witnesses
plus the F2 negative probe. `python3 -P dev/erasure-mutations.py` checks ten
isolated mutations. The default gates also run all 36 pairs in
`lean/corpus.json`; `dev/lean-twin.sh --record` records their evidence.

The checker now admits erased indices of `Prop` families, including the
`Acc` declaration and constructor in `fixtures/erasure/acc-family.att`.
Twenty-eight regression cases cover their universe and quantity boundaries.
Stage B remains open: `Acc` runtime elimination still hits the erased-binder
and recursive-singleton restrictions, and inline proof erasure is unfinished.
`zsh -f dev/gates.sh TRACE-ERASURE` reports these frontiers and exits 1.
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

The optional [Bend 2 evaluator pilot](pilot/bend2/README.md) tests stronger
scope guarantees and native build speed against OCaml. The guarantees pass;
native builds and rebuilds are slower on the pinned toolchain, so the pilot
does not recommend migrating the production evaluator.

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
