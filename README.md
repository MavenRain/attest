# attest

attest is a programming language with Kan extensions as its only type formers.  The compiler targets the RISC-V bytecode that Succinct SP1 proves.

M0 Stage A implements the carried Kan kernel, parser, checker, and axiom
disclosure. RISC-V emission and SP1 execution follow in later stages of
[the M0 plan](design/attest-m0/M0-PLAN.md).

With OCaml 5.2 or newer, Dune 3.24, Zarith 1.14, Python 3, ripgrep, and zsh
already available:

```sh
zsh -f dev/dunecho.sh build
_build/default/bin/attest.exe check corpus/id.att
_build/default/bin/attest.exe check --axioms corpus/id.att
_build/default/bin/attest.exe spec-count
zsh -f dev/gates.sh
zsh -f dev/dunecho.sh test
zsh -f dev/mutations.sh
```

The build wrapper uses `dunecho` when available and otherwise Dune. Set
`ATTEST_OPAM_SWITCH` to select an installed switch. The tools install nothing.

See [SPEC.md](SPEC.md) for the current command contract and
[CARRIED.md](CARRIED.md) for provenance and the documented carry adjustments.
The package is licensed under MIT OR Apache-2.0.

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
