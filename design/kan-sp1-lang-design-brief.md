# kan-sp1-lang design brief

Working slug: kan-sp1-lang (the panel names the language, see Q7).
Written 2026-09-21 by the main loop after two builder agents (Fable, then
Opus) died on the API classifier before their first tool call.
Status: DRAFT for the user's pre-panel rulings (section 9).  The panel
launches only on an explicit "use a workflow" opt-in.

## 1.  The question

The user asked on 2026-09-21:

> I want to write a new programming language.  This programming language
> will have Kan extensions as the only "type formers", aspire to
> type-strength at least that of Lean 4, and compilation speed at least
> that of Bend 2, and will compile to the bytecode that Succinct SP1
> consumes in order to generate proofs.  Feel free to choose between assay
> and mechanism-lang as a kernel, if needed.

The question for the panel: design a kanon-family language whose kernel
has Lan and Ran as its only type formers, whose expressiveness matches
Lean 4 on twin corpora, whose compiler is at least as fast as Bend 2 per
line, and whose output is a RISC-V ELF that the SP1 executor runs and the
SP1 prover proves.  The kernel starts from assay or from mechanism-lang.
The panel must say which one and why, with measurements.

The deliverable of this brief is the ruled set of pins, the grounding
ledger, a strawman calculus and target contract, the judge's axes, the
panel mechanics and eight open questions with defaults.

## 2.  The pins

Five pins.  R0 to R3 come from the user's sentence.  R4 comes from the
user's offer of a kernel.

### R0.  Kan extensions are the only type formers (kanon verbatim)

The kernel type formers are exactly `Lan_s` and `Ran_s` along a CLOSED
shape grammar:

| Shape `s` | `Lan_s` gives | `Ran_s` gives | Lean 4 feature recovered |
|---|---|---|---|
| `pi_A` (weakening by `A`) | Sigma | Pi | dependent pairs, dependent functions |
| finite discrete collapse | variants (sums) | records (products) | inductive enumerations, structures |
| parallel pair collapse | `Quot` (coequalizer) | equalizer subtypes | `Quot`, subtypes |
| `mu_P` (polynomial `P`) | initial algebras (W types) | none | inductive types and families |
| `nu_P` (polynomial `P`) | none | terminal coalgebras | coinductives (a row Lean 4 lacks) |

Rules that follow from the pin:

- Pi = `Ran_pi`, Sigma = `Lan_pi`, variants = Lan over a discrete collapse,
  `Quot` = Lan over the parallel pair, inductive families = the fibered
  initial algebra rule of `mu_P` with strict positivity meaning "P is a
  polynomial", coinductives = `Ran_nu`.
- Universes, contexts, substitution and literal accelerators are the
  ambient framework, not primitives.
- A surface macro over a Pi/Sigma/inductive kernel FAILS R0.
- Definitional eta only where Lean 4 has it (functions, structures).
- The R0-COUNT gate prints the former count (two) from SPEC.md and the
  R0-AUDIT gate walks the term sum and refuses any third former.
- ZK is NOT a former and NOT a shape.  The whole program is the zkVM guest.
  The proof is a proof of the program's execution.  Nothing ZK-shaped
  enters the kernel or the surface.  This is the opposite of veil's `SZk`
  host shape and of taciturn's first-class proof values (section 8).

### R1.  Type strength at least Lean 4

Proof-theoretic strength is met by a Lean-class kernel: prenex universe
polymorphism as Lean 4 has it, `Prop` with proof irrelevance, subsingleton
large elimination, `Quot.sound` as a tracked axiom disclosed by
`--axioms`.  So R1 bites on EXPRESSIVENESS parity, measured two ways:

1. Twin corpora.  An ACCEPT corpus (programs Lean 4 accepts and this
   language must accept) and a REFUSE corpus (programs Lean 4 rejects and
   this language must reject), with `lean` as the oracle.  A row that
   diverges is a gate failure, not a note.
2. The import oracle.  mechanism-lang's lean4export importer and its
   PRELUDE-CHECKED gate (external=2,477 names, counts NAME_AND_TYPE,
   NAME_ONLY, UNMAPPED, NEVER, failing when NAME_ONLY or UNMAPPED is above
   zero) are borrowed as the measurable oracle.  The covered percentage is
   always printed beside the NEVER count.

### R2.  Compilation speed at least Bend 2

Two forms, both binding:

1. Measurement (trice form).  The twin-program ratio: the same program
   written for Bend 2 and for this language.  The denominator is the
   wall-clock of the Bend 2 check-plus-compile stage.  Single core.
   Medians over at least 5 runs.  Ratio at most 1.0 per 1,000 lines,
   informational at M0 and binding at M1.  Denominators are frozen as
   hashed artifacts at Stage 0 (`dev/denominators.json` and
   `DENOMINATORS.sha256`), the kanon recipe.
2. Architecture (trawl form).  The compiler prints the number of walks per
   definition.  There is no optimizer pass.  Encoding is direct: no LLVM, no
   rustc, no external assembler and no linker in the path.  Memoised
   conversion over hashconsed terms and per-definition fuel (trice form)
   are candidate levers.  The panel scopes each lever to M0 or M1 (Q6).

Known risk: assay's own M1 closure bound is open at a frozen ratio of
1.956099 against a limit of 1.0.  The kernel lineage is not fast today.
R2 is the pin most likely to fail.  The panel treats it as the main event
beside the R0 smuggling attack.

### R3.  Target: the RISC-V ELF that Succinct SP1 consumes

- The compiler emits the ELF directly with its own ELF32 encoder.  assay's
  Cancun assembler and bytecode listing are the precedent.
- The ELF carries `_start`, the SP1 syscalls for input read, public-value
  commit and halt, and the precompile syscalls (keccak, sha256, bn254,
  secp256k1, uint256 mul) as host externs.  All of them are constructors of
  one `Host` sum type at the boundary, never shapes.
- Proof erasure over emitted bytes (assay Stage F precedent): erased proof
  terms never change the instruction trace.  The TRACE-ERASURE gate
  compiles each corpus program with and without its proof terms and
  requires byte-identical ELFs.
- Cost model = cycles.  The CYCLE-BUDGET gate prints and pins the executor
  cycle count per corpus program, the analogue of assay's gas discipline.
  Proof-supplied arithmetic without a second runtime check (assay's
  `addLt` and `subLe`) is the lever that lowers cycles.
- Execution oracle = SP1's own executor, run without proving through a
  pinned Rust harness on `sp1-sdk` (the analogue of assay's geth
  `evm run`), differential against our own OCaml RV32IM emulator twin.
- Proving runs ONCE per milestone exit on the smallest corpus program
  (`prove`, then `verify`), never per commit.

### R4.  Kernel base: assay or mechanism-lang

The user offers the choice.  The default and the flip trigger are Q0.
Both candidates are kanon descendants, so R0 holds under either.

## 3.  Grounding facts

Every row is VERIFIED (by the main loop on 2026-09-21) or BELIEVED (a
scout pins it before any proposal cites it).  A proposal that cites a
believed row as fact loses a point on the axis it supports.

### 3.1 The family (verified)

| Sibling | Kernel | Target | Note |
|---|---|---|---|
| tot, tally | own | native | the first two |
| kanon | Kan sole primitive | WasmGC | the kernel root, HEAD 69f3be5 |
| taciturn | kanon | WASM + circom/snarkjs | first-class ZK proof values |
| tick | kanon | Verilog-2005 | erased twice |
| mechanism-lang | veil submodule | WASM | level overlay, lean4export importer |
| trice | kanon | WASM | Agda strength, TinyCC speed, trap census |
| trawl | kanon | JavaScript text | media scraping |
| assay | kanon fork at 2c2e6e6 | EVM bytecode | the architecture this brief copies |
| veil | kanon | WASM | SZk, SFhc, SMpc host shapes |
| lanyard, tether | kanon | various | staged and under review |

Kickoff recipe, the same every time: brief, then a 10-agent panel (3
scouts, 3 opposed proposals, 3 attacks, 1 judge), then a verdict with at
most 7 open questions, then user ratification, then an M0 plan, then
staged workflows.

### 3.2 The candidate kernels (verified)

assay at `/Users/oobi/Documents/assay`:

- HEAD eebe37e "M1: enforce the closure performance bound".  Porcelain 76
  lines (a staged review slice).  Pin the COMMIT, never the tree.
- `PIN` = 8cf0b8b (tot).  `vendor/tot` present.
- README: "Assay is a Kanon language fork for EVM contracts.  It inherits
  the kernel and surface at 2c2e6e6."
- `lib/` = 25 files, 6,193 lines: bignum, budget, check, conv, erase,
  error, eterm, eval, global, level, literal, order, positivity, pp, prim,
  quantity, rules, shape, spec_count, term, totality, value.
- Other dirs: abi, asm, emit, evm, keccak, proofs, reference,
  verification, corpus, surface, test.
- Stages: A checker, erasure, axiom disclosure and carry gates.  B Keccak
  and selectors.  C Cancun assembler and bytecode listing.  D hand-assembled
  reference and Cancun execution gates.  E closed first-order EVM effect
  programs.  F frozen corpus, compile time and proof erasure checks over
  emitted bytes.  M1 slices add geth `evm run` and `t8n` differential
  execution, a source model `run` command with checked arithmetic,
  proof-producing guards, erased bound proofs, proof-supplied arithmetic
  without a second runtime check, storage invariants, named predicates and
  a Lean transaction model.
- `zsh -f dev/gates.sh` runs 75 checks.  M1 is OPEN on performance: frozen
  ratio 1.956099 against a limit of 1.0.

mechanism-lang at `/Users/oobi/Documents/mechanism-lang`:

- HEAD 1e4f371 "M0 Stage C / U1: horizontal associativity".  Porcelain 72
  lines (a staged slice).
- README: "a sibling of kanon, with Veil as its kernel dependency.
  vendor/veil is a git submodule pinned at
  a7534cedeac82d396de8e23058ee6bc990560f65 (PIN).  The submodule is never
  forked and never rebased.  mechanism-lang adds a level overlay in lib/,
  an importer for the lean4export format in import/, and a prelude in
  prelude/ that states its mapping targets in map/prelude.map.tsv."
- `lib/` = 11 files, 3,744 lines: check, conv, eval, level, level_eq,
  level_scope, level_var, rules, rules_lvl.
- Driver `mech`, extension `.mech`.  PRELUDE-CHECKED gate over
  external=2,477 names.  The README notes the active kernel exceeds the
  3,000-line TRUSTED-LINES bound.

veil at `/Users/oobi/Documents/veil`: HEAD ebd2a97.  "kanon plus three
host shapes for private computation: SZk, SFhc, SMpc." Trusted kernel
bound 5,250 lines.  `lib/*.ml` = 7,578 lines.

### 3.3 Pin worktrees (verified, created 2026-09-21)

| Pin | Path | HEAD |
|---|---|---|
| assay | `/Users/oobi/Documents/kan-sp1-lang-assay-pin` | eebe37e |
| mechanism-lang | `/Users/oobi/Documents/kan-sp1-lang-mech-pin` | 1e4f371 |

The veil submodule inside the mechanism-lang pin is NOT checked out.  The
clone of `https://github.com/MavenRain/veil.git` failed without network.
Stage 0 fixes it with one of:

```
git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule update --init --reference /Users/oobi/Documents/veil vendor/veil
git -C /Users/oobi/Documents/veil worktree add --detach /Users/oobi/Documents/kan-sp1-lang-veil-pin a7534cedeac82d396de8e23058ee6bc990560f65
```

Until then S1 reads veil's kernel at the main tree's checkout
`/Users/oobi/Documents/mechanism-lang/vendor/veil` (read only, never a
build there).

### 3.4 Local toolchain (verified)

| Tool | State |
|---|---|
| `cargo-prove` | present, `/Users/oobi/.sp1/bin/cargo-prove`, `cargo-prove sp1 (d454975 2026-04-11)` |
| `sp1up` | present, `/Users/oobi/.sp1/bin/sp1up` |
| rustup toolchains | stable, nightly (default), nightly-2025-11-25, 2026-02-05, 2026-03-20, 2026-04-10.  No `succinct` toolchain in the first six rows (S2 confirms) |
| rustup targets | aarch64-apple-darwin, thumbv7em-none-eabihf, wasm32-unknown-unknown |
| SP1 crate sources | NONE in `~/.cargo/registry/src` (no `sp1-zkvm`, no `sp1-sdk`), so every SP1 number below stays believed |
| clang | `/usr/bin/clang` (can assemble `--target=riscv32-unknown-elf -c` for reference objects) |
| lld | `/opt/homebrew/bin/lld` and `ld.lld` |
| OCaml | opam switch zxcaml-p1, `dune` and `ocamlfind` at `/Users/oobi/.opam/zxcaml-p1/bin`, NOT on PATH in agent shells |
| absent | bend, hvm, riscv32/64-unknown-elf-gcc, qemu-riscv32/64, spike |
| disk | 23 GiB free on the Data volume, below the 30 GiB floor |

### 3.5 SP1 (believed, S2 pins every row)

| Claim | Status |
|---|---|
| Guests are RV32IM ELF32 little-endian executables, target `riscv32im-succinct-zkvm-elf`, bare metal, single thread, deterministic, no A, F, D or C extensions | believed, S2 pins from the installed version.  SP1 Hypercube may have moved the ISA to 64 bits |
| Syscalls go through `ecall` with the code in `t0` and arguments in `a0` and `a1`: HALT, WRITE, COMMIT, HINT_LEN, HINT_READ, and precompiles SHA_EXTEND, SHA_COMPRESS, KECCAK_PERMUTE, UINT256_MUL, BN254 and SECP256K1 ops | believed, S2 pins the exact codes with a file path |
| `sp1_zkvm::entrypoint!` supplies `_start`, stack setup and the halt, and a linker script fixes the load address and the stack top | believed, S2 pins the addresses |
| Public values go through COMMIT and are hashed into the public-values digest | believed, S2 pins |
| `ProverClient::execute` runs the guest without proving and returns public values plus a cycle count | believed, S2 pins and writes the harness shape |
| Core proofs on Apple Silicon take minutes and gigabytes | believed, S2 measures once on a hello guest |

### 3.6 Bend 2 (believed, S2 pins every row)

| Claim | Status |
|---|---|
| Bend 2 is HigherOrderCO's 2025 rewrite of Bend, dependently typed with a checker inherited from Kind, compiling to HVM4 | believed |
| The compiler is written in Haskell and installs through cabal or a release binary.  Bend 1 was the Rust crate `bend-lang` on HVM2 | believed |
| The twin denominator is the wall-clock of `bend check` plus the HVM generation command on the twin program | believed, S2 names the exact commands |
| Installing Bend 2 is a USER step (Stage 0a), as wasmtime was for kanon | policy |

### 3.7 Prior art (believed, S3 pins)

Juvix (compiles to Cairo and to RISC Zero and Anoma targets), Kind2 and
Bend2 typed cores, Lurk, Noir, Leo, CompCert and CakeML RISC-V backends,
Lean 4 compiled code inside zkVMs, verified ELF emitters.  S3 states for
each: what it proves, what it erases, how it treats I/O and precompiles,
and its compile speed per line if published.

## 4.  Strawman calculus and target contract

The strawman is a starting point for P1.  P2 and P3 may replace any part
of it.  The attacks must try to break every part of it.

### 4.1 Kernel

- Terms: variables, universes with prenex levels, `Lan_s`, `Ran_s`, their
  introduction and elimination forms, `Global`, literals, annotations.
- Shapes: the closed grammar of R0 (`pi_A`, discrete collapse, parallel
  pair, `mu_P`, `nu_P`).
- Ambient: `Prop` with proof irrelevance, subsingleton large elimination,
  `Quot.sound` as a tracked axiom, literal accelerators for `Nat`,
  `Word32`, `Word64`, `U256` and `Bytes` with checked overflow proofs.
- Conversion: typed, with the three named non-schema rules kanon ratified
  (proof irrelevance, subsingleton large elimination, literal fast path),
  memoised over hashconsed terms if Q6 puts that lever at M0.
- Quantities: 0 for proofs and types, 1 for runtime values.  The erased
  term IR (assay's `eterm`) carries only quantity-1 terms.

### 4.2 Program boundary

A program is a closed first-order effect program (assay Stage E form): a
sequence of `Host` operations with pure erased terms between them.  The
`Host` sum has one constructor per SP1 syscall and precompile:

```
Host = Read Bytes | Commit Bytes | Halt Word32
     | Keccak Bytes | Sha256 Bytes | U256Mul U256 U256 U256
     | Bn254 Op | Secp256k1 Op
```

Nothing here is a shape.  The kernel never sees `Host`.  The erasure pass
maps each constructor to one `ecall` sequence.

### 4.3 Runtime model on the guest

- Memory: one bump allocator, no collector.  The guest runs once and
  cycles are the cost, so a bump pointer is the cheapest correct policy.
  Inductive values are tagged heap nodes.  `Nat` uses `Word32` when a
  bound proof is in scope and the bignum runtime otherwise.  `U256`
  multiplication uses the UINT256_MUL precompile.
- Calls: the standard RV32 calling convention (`a0` to `a7` arguments,
  `sp` frames, `ra` return) so clang-assembled reference objects
  cross-check our encoding in gates.
- No traps by construction where a proof is in scope.  A bound proof lets
  the compiler emit the bare instruction without a check.

### 4.4 Pipeline

```
parse -> elaborate -> check -> erase -> lower -> encode -> execute
```

- elaborate: bidirectional, first-order pattern unification only, no
  instance search and no `Auto` at M0.
- check: the Kan kernel of 4.1.
- erase: quantities to `eterm`, effect programs to `Host` sequences.
- lower: `eterm` to a small RV32IM IR (registers, frames, calls, `ecall`).
- encode: IR to ELF32 with our own encoder.  No LLVM, rustc, assembler or
  linker.
- execute: the SP1 executor harness and the OCaml RV32IM emulator twin.
  Both print cycle counts.

### 4.5 What is NOT in the kernel

ZK, cycles, I/O, precompiles, the allocator, the calling convention.  Each
of these is a target contract fact, checked by a gate, never a former or
a shape.

### 4.6 M0 gate battery sketch

| Leg | Checks |
|---|---|
| BUILD | dune build of the compiler under `-j 2` |
| CARRY | every carried kanon and assay suite still passes |
| R0-COUNT | SPEC.md prints two formers |
| R0-AUDIT | the term sum has no third former |
| SUITE-KERNEL | the kernel suite, timed |
| ELF-ACCEPTED | the SP1 executor loads every corpus ELF and halts with exit 0 |
| EXEC-DIFF | executor and emulator agree on public values and cycle counts for every corpus program |
| TRACE-ERASURE | proof terms present versus erased give byte-identical ELFs |
| CYCLE-BUDGET | cycle counts printed and pinned, informational at M0 |
| AXIOMS | `--axioms` lists exactly `Quot.sound` on the corpus |
| M0-TIME | the corpus compiles under a fixed wall-clock bound |
| M0-RATIO | the Bend 2 twin ratio, informational at M0 |
| TRUSTED-LINES | kernel and encoder line bounds |
| DENOMINATORS | `shasum -c DENOMINATORS.sha256` |
| PROVE-ONCE | one `prove` and `verify` on the smallest program at the milestone exit only |

## 5.  House rules

- OCaml: no exceptions (no `raise`, `failwith`, `assert`).  Combinators
  over `match` on `Option` and `Result`.  No `match` on `bool`.  Exhaustive
  matches with no `_` arms.  Indexing only through total combinators.  No
  mutation of vectors.  `match ()` guards over else-if chains.
- Rust (the executor harness only): newtypes and sum types, no `unwrap`,
  `expect`, `panic` or `unsafe`, hand-rolled `Error` enums, MIT OR
  Apache-2.0.
- Lean 4 (proof packages): kan-tactics only, no exceptions, every repo a
  reusable lakefile dependency.
- Git: never commit or push for the user.  Stage and print the commit
  command.  `git commit -s` for DCO.
- Prose: ASD-STE100 for repo-facing text, no em-dashes, no AI prose tells.
- Caps: 7 findings and 56 agents per workflow.
- Pins: probe a COMMIT in a detached worktree, never a main tree.
- Builds: OOM-safe, `-j 2`, one crate at a time.  Use cargocho, dunecho and
  kanoncho over raw cargo, dune and kanon.
- Disk: the 30 GiB floor holds new commands.  The user reclaims before the
  panel.

## 6.  Axes

Seven axes, 10 points each, 70 total.  The judge scores every proposal on
every axis and cites the dossier row or the live probe behind each score.

| # | Axis | What earns 10 |
|---|---|---|
| 1 | R0 honesty | two formers, closed grammar, ZK nowhere in the kernel, the smuggling attack refuted with a term walk |
| 2 | Lean 4 strength credibility | twin corpora designed, the import oracle scoped, every Lean 4 feature in the R0 table mapped |
| 3 | Bend 2 speed credibility | denominator commands named, twin corpus sketched, architecture levers costed, the 1.956 risk answered |
| 4 | SP1 target fidelity | ISA and syscalls pinned from the installed toolchain, ELF layout stated, executor harness designed, proving once |
| 5 | Proof-erasure soundness | TRACE-ERASURE argued from the quantity rules, not from testing alone |
| 6 | Kernel-choice justification | Q0 answered with S1's measurements and seam reads, not with taste |
| 7 | Staging realism | M0 in weeks with the assay gate patterns, every stage a workflow with gates and mutations |

## 7.  Panel mechanics

Ten agents.  The panel launches ONLY on the user's explicit "use a
workflow" opt-in.  (7 findings max, 56 agents max.)

### 7.1 Scouts (parallel, each writes one dossier)

- S1 kernels: `/Users/oobi/Documents/kan-sp1-lang-dossier-kernels.md`.
  Probes both pins with dunecho.  Measures both kernels' suite time on the
  SAME twin corpus.  Counts lib lines and the R0 count.  Reads the erase,
  quantity and totality seams in assay and the level overlay plus
  `import/` in mechanism-lang.  States the Q0 flip trigger result.
- S2 toolchain: `/Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md`.
  SP1: version, ISA, syscall table with codes, ELF layout, executor
  harness shape, one measured prove.  Bend 2: install path, check and
  compile commands, denominator design.  RISC-V: RV32IM encoding, ELF32
  layout, clang as a reference assembler for gate cross-checks only.
- S3 prior art: `/Users/oobi/Documents/kan-sp1-lang-dossier-priorart.md`.
  The list in 3.7 with the four questions per entry.

### 7.2 Proposals (parallel, opposed by construction)

- P1 Kan-honest, strength-first, on the assay kernel.
- P2 target-first and speed-first: the SP1 and Bend 2 lens, direct ELF
  encoder, cycle cost model, no optimizer, on whichever kernel S1 measures
  faster.
- P3 parity-first, on the mechanism-lang and veil kernel: the lean4export
  oracle and the level overlay lead.

Each proposal answers Q0 to Q7, gives an M0 stage list with gates, and
names the language.

### 7.3 Attacks

One attack per proposal, adversarial, with live probes on the pins.
Seven findings max each.  The R0 smuggling attack and the R2 speed attack
are mandatory findings.

### 7.4 Judge

Scores the seven axes, synthesises one design, writes
`/Users/oobi/Documents/kan-sp1-lang-design-verdict.md` with at most 7
open questions and a recommendation per question, plus
`/Users/oobi/Documents/kan-sp1-lang-design-panel.json`.

### 7.5 Tiers and files

Scouts and proposals Fable xhigh.  Attacks and judge Fable max.  Closer
Opus 5 medium.  If a Fable agent dies on the API classifier before its
first tool call, relaunch it once on Opus with the marker, then halt and
report the unmet tier.  Never sonnet for a builder or verifier.  Files:
`/Users/oobi/Documents/kan-sp1-lang-{dossier-kernels,dossier-toolchain,dossier-priorart,proposal-1..3,attack-1..3,design-verdict}.md`
and `kan-sp1-lang-design-panel.json`.

## 8.  Siblings and why not them

| Sibling | What it does with ZK or a VM | Why it is not this language |
|---|---|---|
| taciturn | ZK proofs are first-class values inside a WASM program.  The prover runs outside the program | here the program IS the guest and the prover proves the whole run |
| veil | `SZk` is a host shape with plaintext reactor twins.  ZK is an effect | a ZK shape in the kernel fails this brief's R0 stance |
| assay | EVM bytecode, executor differential, proof erasure over emitted bytes | the architecture we copy.  The target and the cost model change |
| trice | strength and speed pins in the measured twin form | the pins we copy in form.  Trice targets WASM and Agda parity |
| kanon | the kernel root, WasmGC target | the root.  This brief does not fork it directly, it starts from assay or mechanism-lang |

## 9.  Pre-panel open questions with defaults

The user may rule on any question now.  An unruled question takes its
default into the panel.  "Accept all" is a valid ruling.

### Q0.  Kernel base

DEFAULT: assay's kernel (the kanon fork at 2c2e6e6 plus quantity,
totality, positivity, erase, eterm, bignum and literal).  Reason: the
target shape matches.  assay already has bytecode emission, a
hand-assembled reference, executor differential gates, proof erasure over
emitted bytes and proof-supplied arithmetic.  Every one of those recurs in
R3.  mechanism-lang's `import/` (the lean4export importer) and its
PRELUDE-CHECKED gate are borrowed as an overlay for the R1 oracle.

Flip trigger: the judge may flip to P3's base (mechanism-lang over veil)
if S1 measures that kernel at least 2x faster than assay's on the shared
suite, or if the level overlay proves necessary for the import oracle.

Recorded risk: assay's M1 performance bound is open at ratio 1.956
against 1.0.  R2 inherits that risk under the default.

### Q1.  Target contract

DEFAULT: the exact ELF the installed `cargo-prove` toolchain's SDK
executor accepts, ISA per S2 (RV32IM believed), emitted by our own
encoder with no external tool in the path.

### Q2.  Execution oracle

DEFAULT: an SP1 executor harness (a pinned Rust crate of about 60 lines
on `sp1-sdk`, execute only) plus an OCaml RV32IM emulator twin.
Differential on every corpus program.  Cycle counts printed by both.
Proving once per milestone exit.

### Q3.  Cost model

DEFAULT: cycles.  CYCLE-BUDGET informational at M0, binding at M1.

### Q4.  Host boundary

DEFAULT: SP1 syscalls and precompiles as the `Host` sum, closed
first-order effect programs, no ZK shape anywhere.

### Q5.  R1 oracle

DEFAULT: Lean 4 twin corpora (ACCEPT and REFUSE, `lean` as the oracle) at
M0.  The lean4export import and PRELUDE-CHECKED at M1.

### Q6.  R2 denominator and levers

DEFAULT: the Bend 2 twin ratio frozen at Stage 0c.  Levers at M0: direct
encoding and no optimizer.  Levers at M1: memoised conversion over
hashconsed terms and per-definition fuel.

### Q7.  Name

Proposals propose.  Seeds: attest, warrant, vouch, cite.  The extension and
the driver follow the name.

### Stage 0 USER steps (before the panel or during it)

1. Reclaim disk to above 30 GiB: `diskfree --apply`.
2. Install Bend 2.  S2 names the exact command in its dossier.
3. Confirm or install the `succinct` rustup toolchain with `sp1up` (only
   needed for a Rust hello guest that S2 uses to read the ELF layout).
4. Optional: `brew install riscv-isa-sim` for a third emulator (spike).
5. Check out the veil submodule in the mechanism-lang pin (commands in
   3.3).

### Pin removal (after ratification)

```
git -C /Users/oobi/Documents/assay worktree remove /Users/oobi/Documents/kan-sp1-lang-assay-pin
git -C /Users/oobi/Documents/mechanism-lang worktree remove /Users/oobi/Documents/kan-sp1-lang-mech-pin
```

The pins stay through the panel and through M0 if the verdict cites their
lines.  Remove them only after the M0 exit stamp.

## 10.  Rulings

2026-09-21: the user opted in with "use a workflow" and gave no rulings on Q0 to Q7.  The defaults in section 9 stand for the panel.  The judge may reopen any of them as one of its open questions (at most 7).  Disk stood at 27 GiB free at launch, under the 30 GiB floor, so `diskfree --apply` is still a user step.  The panel script is `/Users/oobi/Documents/kan-sp1-lang-design-panel.js`, authored by copy then delta from the trawl panel script and shape checked before the run; the result file `kan-sp1-lang-design-panel.json` is written by the main loop from the panel's return value.

2026-09-22: the user ruled "ratify all" on the judge's open questions OQ1 to OQ7 in `kan-sp1-lang-design-verdict.md`.  The rulings now bind.  OQ1: the target is RV64IM and ELF64 for the installed SP1 v6.1.0 executor, with an RV64IM emulator twin (this replaces Q1 and Q2).  OQ2: M0-RATIO is informational at M0 with rung 3 at most 2.0 and binding at M1 with a printed OPEN exit;  `bend check` is the like-for-like row when `bend --help` shows no compile subcommand (this replaces Q6).  OQ3: PRELUDE-CHECKED is a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE) and fails closed at M2 on NAME_ONLY = 0 and UNMAPPED = 0 (this replaces Q5).  OQ4: TRUSTED-LINES kernel bound 4,100 at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100 (this replaces the brief's 3,000).  OQ5: Host at M0 is Read, Commit and Halt at Stage D and Keccak, Sha256 and U256Mul at Stage E;  Bn254 and Secp256k1 at M2;  UINT256_MUL 0x0001011D (this narrows Q4).  OQ6: the kernel base is assay;  the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms (this replaces Q0).  OQ7: TRACE-ERASURE compares an ELF with proof bodies against one with the same proofs replaced by opaque postulates, both erased through the evaluator that never unfolds a quantity-0 global, plus GUARD-TWIN (this replaces the text of section 4.6).  Where a ruling and an older section disagree, the ruling wins.  Stage 0 USER steps stay open: `diskfree --apply` (21 GiB free on 09-22), the veil submodule checkout in the mech pin, Bend 2 installed with the `bend --help` output recorded, the succinct toolchain check (USER step 3), and the mechanism-lang median (USER step 5).  The M0 plan starts on a new "use a workflow" opt-in.

2026-09-22, Stage 0 progress: the user ran step 1, step 2 and the checkout half of step 5 in one command line (the verdict's eight-step numbering binds;  the five-step list of section 9 is the older form).  Step 1: `diskfree --apply` reclaimed nothing (0K cold target dirs, 0K cargo caches;  9.2 GiB of target dirs under gpt3, gpt5 and gpt7 are HOT-fresh and stay), so free space stays at 21 GiB, under the 30 GiB floor, and every Bash command keeps the `# [skip-disk]` marker.  Step 5, first half: the veil submodule is checked out in the mech pin at a7534cedeac82d396de8e23058ee6bc990560f65, the PIN this brief already records;  `git submodule status` shows a clean checkout and vendor/veil/test holds the fixtures.  Step 2: `bend` is not on PATH (`zsh: command not found: bend`), so Bend 2 is not installed, `bend --help` is not recorded, the OQ2 like-for-like row stays undecided, and step 7 (the denominator freeze) waits on it.  On PATH today: `ghc` and `stack`;  not on PATH: `cabal`, `ghcup`, `bend`.  Open, in the verdict's numbering: step 2 (`curl -fsSL https://bend-lang.com/install.sh | sh`, then `bend --help` recorded into dev/bend-cli.txt), step 3 (hello guests for riscv64im and riscv32im, `llvm-readelf -h`, execute both), step 4 (optional spike), step 5 second half (`zsh -f dev/dunecho.sh build` in the mech pin, then `RUNS=7 zsh -f dev/bench.sh SUITE-KERNEL '_build/default/test/main.exe vendor/veil/test'` with the paths made absolute;  the flip to mechanism-lang needs a median under 211 ms), step 6 (`cargo fetch` of sp1-sdk 6.1.0), step 7 (the denominator freeze with DENOMINATORS.sha256), step 8 (the two A1 F2 fixtures and the erase diff on the pin).  M0-RATIO is informational at M0, so the M0 plan does not wait on Bend 2;  it starts on a new "use a workflow" opt-in.

2026-09-22, M0 plan runs: on the user's "use a workflow" opt-in the M0 plan workflow ran twice.  Run 1 (wf_86a88ed7-c13, 16 agents, 0 errors, 62 minutes) authored the child script kan-sp1-lang-m0-plan.js by copy then delta from the design panel script over two author and two shape rounds, wrote the 14 sections of /Users/oobi/Documents/attest-m0/M0-PLAN.md in the house shape of assay-m0/M0-PLAN.md, ran the three attacks K1 consistency (5 findings), K2 gate and budget feasibility (7) and K3 executability and house form (7), adjudicated 7 confirmed edits C1 to C7 (refuted K1-3 and K2-7;  below the cap K1-4, K1-5 and K3-7) and applied them (688 lines).  Run 2 (wf_8fb4e3d0-f4f, 5 agents) hit the Fable usage limit on the reverify and fix units, so both ran as the one opus retry the dead-unit rule allows;  the reverify found residuals of C1, C4, C5 and C7, the fix applied 6 items with 19 edits and appended Corrections rows R2-1 to R2-6, and the mechanical check plus a main-loop check on disk give 694 lines, 14 headings, 0 dashes, 0 PENDING and 0 hits of sp1-exec-harness (renamed attest-harness).  The run record is kan-sp1-lang-m0-plan.json.  Open: K3-7 (ASD-STE100 sentence-length pass, 33 clauses over 40 words) stays with the user;  the round-2 edits had a mechanical check only, no independent adversarial re-verify;  Stage 0 USER steps 2, 3, 4, the second half of 5, 6, 7 and 8 stay open;  Stage A of M0 (repository /Users/oobi/Documents/attest) starts on a new user ask.  Nothing was committed.
