# attest M0 plan

## 0 Bindings

Date: 2026-09-22.  Status: DRAFT, not ruled.  Nothing is committed.  This part and parts 1 to 3 are the skeleton;  later units write sections 4 to 13 by copy then delta from the assay M0 plan.

Binding inputs, each read once in the named windows on 2026-09-22: the verdict /Users/oobi/Documents/kan-sp1-lang-design-verdict.md (cited as verdict:N;  milestones at verdict:115-122, trusted lines at verdict:123-126, Stage 0 USER steps at verdict:127-137, the name at verdict:138-144), the brief /Users/oobi/Documents/kan-sp1-lang-design-brief.md (cited as brief:N;  the pins R0 to R4 at brief:31-131, the rulings at brief:537-543), the assay M0 plan /Users/oobi/Documents/assay-m0/M0-PLAN.md (cited as tpl:N;  the copy-then-delta template, sections 0 to 3 at tpl:21-135) and the mechanism-lang M0 plan /Users/oobi/Documents/mechanism-lang-m0/M0-PLAN.md (cited as tpl2:N;  section 11 at tpl2:188-195).  VERIFIED by the Read windows of this unit.

Where a ruling and an older section disagree, the ruling wins (brief:541, VERIFIED).  Every claim in this plan carries VERIFIED with the command, the path:line or the URL that proves it, or BELIEVED with what would settle it.  The user ruled "ratify all" on the judge's open questions OQ1 to OQ7 on 2026-09-22, so the seven rulings bind (brief:541, VERIFIED).  Each paragraph below quotes one ruling verbatim from brief:541, the OQ id first, and states its M0 consequence.

OQ1, binding 2026-09-22, brief:541: "OQ1: the target is RV64IM and ELF64 for the installed SP1 v6.1.0 executor, with an RV64IM emulator twin (this replaces Q1 and Q2)."  M0 consequence: Stage C lowers to RV64IM and encodes ELF64 only, Stage D writes the RV64IM emulator twin in OCaml, and the riscv32im hello guest of USER step 3 (verdict:131) is a toolchain probe and not a target.  VERIFIED at brief:541 and verdict:131.  The ELF32 and RV32IM words of brief:107 and brief:123 are superseded by this ruling (brief:541, VERIFIED).

OQ2, binding 2026-09-22, brief:541: "OQ2: M0-RATIO is informational at M0 with rung 3 at most 2.0 and binding at M1 with a printed OPEN exit;  `bend check` is the like-for-like row when `bend --help` shows no compile subcommand (this replaces Q6)."  M0 consequence: Stage F prints M0-RATIO and rung 3 as informational rows and the M0 gate of verdict:118 does not read them;  the like-for-like row stays undecided while `bend` is not on PATH (brief:543, VERIFIED);  M0 does not wait on Bend 2 (brief:543, VERIFIED).

OQ3, binding 2026-09-22, brief:541: "OQ3: PRELUDE-CHECKED is a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE) and fails closed at M2 on NAME_ONLY = 0 and UNMAPPED = 0 (this replaces Q5)."  M0 consequence: no PRELUDE-CHECKED gate runs at M0 and no M0 stage carries the lean4export importer of brief:77-81;  M1 borrows it from the mech pin.  VERIFIED at brief:541.

OQ4, binding 2026-09-22, brief:541: "OQ4: TRUSTED-LINES kernel bound 4,100 at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100 (this replaces the brief's 3,000)."  M0 consequence: TRUSTED-LINES prints four rows from Stage A onward, kernel at most 4,100, lower at most 1,100, encoder at most 800 and harness at most 100;  the lower, encoder and harness rows print 0 until the stage that writes each artifact.  VERIFIED at brief:541.  The carried kernel count at eebe37e is BELIEVED under 4,100;  `zsh -f dev/trusted-lines.sh` in the assay pin settles it and dev/trusted-lines.sh exists there (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev` on 2026-09-22).

OQ5, binding 2026-09-22, brief:541: "OQ5: Host at M0 is Read, Commit and Halt at Stage D and Keccak, Sha256 and U256Mul at Stage E;  Bn254 and Secp256k1 at M2;  UINT256_MUL 0x0001011D (this narrows Q4)."  M0 consequence: the Host sum type has three constructors at Stage D and six at Stage E, U256Mul lowers to syscall code 0x0001011D, and no M0 file names Bn254 or Secp256k1 as a constructor.  VERIFIED at brief:541.

OQ6, binding 2026-09-22, brief:541: "OQ6: the kernel base is assay;  the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms (this replaces Q0)."  M0 consequence: Stage A carries the assay pin at eebe37e (VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin rev-parse --short HEAD` on 2026-09-22);  the second half of USER step 5 is the flip trigger, and a median under 211 ms reopens Stage A as a re-carry from the mech pin 1e4f371.  The re-carry rule is a plan decision, BELIEVED until the user prints the median.

OQ7, binding 2026-09-22, brief:541: "OQ7: TRACE-ERASURE compares an ELF with proof bodies against one with the same proofs replaced by opaque postulates, both erased through the evaluator that never unfolds a quantity-0 global, plus GUARD-TWIN (this replaces the text of section 4.6)."  M0 consequence: Stage B ships the opaque-proof evaluator and the two A1 F2 fixtures of USER step 8 (verdict:136) are its seed;  GUARD-TWIN is a Stage E gate (verdict:117).  VERIFIED at brief:541, verdict:117 and verdict:136.

The five pins of brief section 2 (brief:31-131) stand under the rulings.  R0 to R3 come from the user's sentence and R4 from the user's offer of a kernel (brief:33-34, VERIFIED).

R0, brief:36-65, Kan extensions are the only type formers.  The kernel type formers are exactly Lan_s and Ran_s along a closed shape grammar of five shapes, pi_A, finite discrete collapse, parallel pair collapse, mu_P and nu_P (brief:38-47, VERIFIED).  Universes, contexts, substitution and literal accelerators are the ambient framework (brief:55-56).  A surface macro over a Pi, Sigma or inductive kernel fails R0 (brief:57).  R0-COUNT prints the former count of two from SPEC.md and R0-AUDIT walks the term sum and refuses a third former (brief:59-60).  ZK is not a former and not a shape;  the whole program is the zkVM guest (brief:61-64).  M0: Stage A runs R0-COUNT, R0-AUDIT and R0-DIFF on the carried tree (verdict:117, VERIFIED).

R1, brief:66-82, type strength at least Lean 4.  A Lean-class kernel meets the proof-theoretic half, with Quot.sound as a tracked axiom under --axioms (brief:68-71).  Expressiveness parity is measured two ways: twin ACCEPT and REFUSE corpora with lean as the oracle, where a divergent row is a gate failure (brief:73-76), and the import oracle PRELUDE-CHECKED borrowed from mechanism-lang (brief:77-81).  M0: LEAN-TWIN 24/24 12/12 at Stage B (verdict:117-118, VERIFIED);  PRELUDE-CHECKED starts at M1 (OQ3).

R2, brief:83-104, compilation speed at least Bend 2.  Measurement, the trice form: the twin-program ratio against the Bend 2 check-plus-compile wall clock, single core, medians over at least 5 runs, at most 1.0 per 1,000 lines, informational at M0 and binding at M1, denominators frozen at Stage 0 as dev/denominators.json and DENOMINATORS.sha256 (brief:87-93).  Architecture, the trawl form: the compiler prints the walks per definition, no optimizer pass, direct encoding with no LLVM, no rustc, no external assembler and no linker (brief:94-98).  Known risk: assay's own M1 ratio is 1.956099 against a limit of 1.0 (brief:100-103).  M0: the PASSES and DENOMINATORS rows at Stage F (verdict:117);  M0-RATIO informational (OQ2).  VERIFIED at brief:83-104.

R3, brief:105-126, the target is the RISC-V ELF that SP1 consumes.  The compiler emits the ELF with its own encoder (brief:107-108);  the SP1 syscalls for input read, public-value commit, halt and the precompiles are constructors of one Host sum type, never shapes (brief:109-112);  TRACE-ERASURE requires byte-identical ELFs (brief:113-116) in the OQ7 form;  the cost model is cycles under CYCLE-BUDGET (brief:117-120);  the execution oracle is SP1's executor without proving through a pinned Rust harness on sp1-sdk, differential against the OCaml emulator twin (brief:121-123);  proving runs once per milestone exit on the smallest program (brief:124-125).  Under OQ1 the ELF is ELF64 and the twin is RV64IM.  VERIFIED at brief:105-126 and brief:541.

R4, brief:127-131, the kernel base is assay or mechanism-lang.  The user offers the choice and both candidates are kanon descendants, so R0 holds under either (brief:129-130).  OQ6 rules assay with the flip open on USER step 5.  VERIFIED at brief:127-131 and brief:541.
## 1 M0 scope

M0 carries the assay pin eebe37e into a new tree, erases proof terms through an opaque-proof evaluator, lowers the erased term to RV64IM, encodes ELF64 with an in-tree encoder, runs the ELF under the SP1 v6.1.0 executor and under an OCaml RV64IM emulator twin, admits six Host constructors and freezes the budgets (verdict:117 and brief:541, VERIFIED).  The M1 rows of verdict:119, the overlay, the level-polymorphic row and the binding CYCLE-BUDGET are not M0 (verdict:119, VERIFIED).  The M0 spine is the smallest corpus program: it reads its input, commits a public value and halts, and PROVE-ONCE proves it once at the M0 exit (verdict:117 and brief:124-125;  the choice of the smallest program is a plan decision, BELIEVED until Stage D names it).

The milestone line, quoted verbatim from verdict:117:

- MILESTONES: M0 Stage A carry (BUILD CARRY R0-COUNT R0-AUDIT R0-DIFF SUITE-KERNEL AXIOMS-empty TRUSTED-LINES rung 1), B erase (TRACE-ERASURE via opaque-proof evaluator with the F2 seed, Acc fixture, LEAN-TWIN), C lower and encode (ENC-XCHECK, ELF-ACCEPTED on HALT), D emulator and harness (EXEC-DIFF HOST-ROSTER PUBVAL-DIGEST, Read Commit Halt), E effects (Keccak Sha256 U256Mul, GUARD-TWIN, LOWER-REFUSE), F freeze (CYCLE-BUDGET pinned, M0-TIME, rung 2 and rung 3 at most 2.0 informational, DENOMINATORS, PASSES, hashconsing bench, PROVE-ONCE smallest row);

The M0 gate line, quoted verbatim from verdict:118:

- M0 gate EXEC-DIFF and TRACE-ERASURE green on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN;

Both lines are VERIFIED by the Read window verdict:115-122 of 2026-09-22.  One paragraph per stage follows.  Each paragraph says what the stage delivers and which gate closes it.  The gate lists come from verdict:117;  the closing rule of each stage is a plan decision and is BELIEVED until that stage's build log prints the rows.

Stage A, carry.  Delivers the tree /Users/oobi/Documents/attest with lib/ and surface/ carried verbatim from the assay pin eebe37e, CARRIED.md and dev/PIN, the build through the dune wrapper, and the gate scripts BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS-empty and TRUSTED-LINES rung 1 (verdict:117, VERIFIED).  Closes on TRUSTED-LINES rung 1 green, kernel at most 4,100 (brief:541 OQ4, VERIFIED), with the seven gates before it green.  The assay pin holds dev/r0-count.sh, dev/r0-audit.sh, dev/carry-check.sh and dev/trusted-lines.sh to copy from (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev` on 2026-09-22).

Stage B, erase.  Delivers the opaque-proof evaluator that never unfolds a quantity-0 global, the F2 seed from the two A1 F2 fixtures of USER step 8, the Acc fixture and the Lean twin (verdict:117, verdict:136 and brief:541 OQ7, VERIFIED).  Closes on TRACE-ERASURE green on every corpus row present at Stage B and LEAN-TWIN 24/24 12/12 (verdict:118, VERIFIED);  the 16-row count is the M0 gate figure and Stage F, not Stage B, proves it.

Stage C, lower and encode.  Delivers the lowering from the erased term to RV64IM under the lower budget of 1,100 lines and the ELF64 encoder under the encoder budget of 800 lines (brief:541 OQ1 and OQ4, VERIFIED), with no LLVM, no rustc, no external assembler and no linker in the path (brief:94-98, VERIFIED), and the gates ENC-XCHECK and ELF-ACCEPTED on HALT (verdict:117, VERIFIED).  Closes on ELF-ACCEPTED on HALT green: the SP1 v6.1.0 executor accepts a halt-only ELF64 and runs it to HALT, with ENC-XCHECK green on every instruction the lowering emits.  The executor that ELF-ACCEPTED calls is BELIEVED to be the harness of Stage D run early on one ELF;  the Stage C brief settles it.

Stage D, emulator and harness.  Delivers the OCaml RV64IM emulator twin, the pinned Rust harness on sp1-sdk 6.1.0 under the harness budget of 100 lines, the Host constructors Read, Commit and Halt, and the gates EXEC-DIFF, HOST-ROSTER and PUBVAL-DIGEST (verdict:117 and brief:541 OQ1, OQ4 and OQ5, VERIFIED).  Closes on EXEC-DIFF green: the executor trace and the twin trace agree row for row on every corpus row present at Stage D, with HOST-ROSTER and PUBVAL-DIGEST green.

Stage E, effects.  Delivers Keccak, Sha256 and U256Mul as Host constructors, U256Mul at syscall 0x0001011D, and the gates GUARD-TWIN and LOWER-REFUSE (verdict:117 and brief:541 OQ5, VERIFIED).  Closes on GUARD-TWIN and LOWER-REFUSE green with EXEC-DIFF and TRACE-ERASURE still green over the six-constructor roster.  Bn254 and Secp256k1 are M2 (brief:541 OQ5, VERIFIED).

Stage F, freeze.  Delivers CYCLE-BUDGET pinned per corpus program, M0-TIME, rung 2 and rung 3 at most 2.0 informational, DENOMINATORS, PASSES, the hashconsing bench and PROVE-ONCE on the smallest row (verdict:117, VERIFIED).  Closes on the M0 gate of verdict:118: EXEC-DIFF and TRACE-ERASURE green on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN.  M0-RATIO and rung 3 print and do not gate (brief:541 OQ2, VERIFIED);  the DENOMINATORS row prints OPEN while `bend` is not on PATH (brief:543, VERIFIED;  `command -v bend` printed nothing on 2026-09-22, VERIFIED).

Out at M0, each with its milestone (verdict:119-121, VERIFIED).

- M1: rung 4 at most 1.0 binding with OPEN allowed and printed, CYCLE-BUDGET binding, the overlay merged with one level-polymorphic row, PRELUDE-CHECKED in check mode, kernel at most 4,400, 8 more rows (verdict:119).
- M2: SPar admitted, AXIOMS exactly Quot.sound, 48 rows, fail-closed PRELUDE-CHECKED, the full roster against software twins in cycles, rung 5 (verdict:120).
- M3: SNu admitted with the EXTRA corpus, a proved encoder replaces ENC-XCHECK, PROVE-ONCE on the largest row (verdict:121).
## 2 Stage 0

Stage 0 is the user's.  The verdict lists eight USER steps at verdict:129-136 and its numbering binds;  the five-step list of brief section 9 is the older form (brief:543, VERIFIED).  No agent installs anything: no brew, no sp1up, no cabal, no rustup, no cargo install and no opam install, and no agent runs a git command that writes in a pin (tpl:77 and tpl:100 carry the same rule for assay, VERIFIED).  The status of each step on 2026-09-22 comes from the brief tail paragraph at brief:543.

USER step 1: `diskfree --apply` to 30 GiB, 21 GiB at the verdict (verdict:129, VERIFIED).  Status: `diskfree --apply` RAN on 2026-09-22 and reclaimed 0K, so the 30 GiB floor stays OPEN at 21 GiB free (brief:543, VERIFIED).  The step is not a closed floor: the run reclaimed 0K of cold target dirs and 0K of cargo caches, 9.2 GiB of HOT-fresh target dirs under gpt3, gpt5 and gpt7 stay, free space stays at 21 GiB under the 30 GiB floor, and every Bash command keeps the `# [skip-disk]` marker (brief:543, VERIFIED).  `df -g /Users/oobi/Documents` printed 56 GiB available on 2026-09-22 (VERIFIED by that command);  the diskfree figure of 21 GiB is the floor measure and the two tools count differently (BELIEVED, settled by `diskfree` run beside `df -g`).

USER step 2: Bend 2 install by `curl -fsSL https://bend-lang.com/install.sh | sh`, then `bend --help` recorded into dev/bend-cli.txt (verdict:130, VERIFIED).  Status OPEN: `bend` is not on PATH (`zsh: command not found: bend`), Bend 2 is not installed, `bend --help` is not recorded, and the OQ2 like-for-like row is undecided (brief:543, VERIFIED;  `command -v bend` printed nothing on 2026-09-22, VERIFIED).  On PATH: ghc and stack;  not on PATH: cabal, ghcup and bend (brief:543, VERIFIED).

USER step 3: the MODIFIED toolchain present (probe 8), build hello guests for riscv64im and riscv32im, `llvm-readelf -h` on both, execute both (verdict:131, VERIFIED).  Status OPEN (brief:543, VERIFIED).  The riscv64im guest is the one that matches the OQ1 target;  the riscv32im guest is a toolchain probe only (brief:541, VERIFIED).

USER step 4: optional spike (verdict:132, VERIFIED).  Status OPEN and optional (brief:543, VERIFIED).  No M0 stage waits on it.

USER step 5: veil checkout (brief 216-217), then `zsh -f M/dev/dunecho.sh build` and `RUNS=7 zsh -f M/dev/bench.sh SUITE-KERNEL 'M/_build/default/test/main.exe M/vendor/veil/test'` with M the mech pin (verdict:133, VERIFIED).  Status: first half DONE, the veil submodule is checked out in the mech pin at a7534cedeac82d396de8e23058ee6bc990560f65, `git submodule status` shows a clean checkout and vendor/veil/test holds the fixtures (brief:543, VERIFIED;  `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` printed ` a7534cedeac82d396de8e23058ee6bc990560f65 vendor/veil (a7534ce)` on 2026-09-22, VERIFIED).  Second half OPEN: the build and the RUNS=7 bench with absolute paths;  the flip to mechanism-lang needs a median under 211 ms (brief:541 OQ6 and brief:543, VERIFIED).  dev/dunecho.sh and dev/bench.sh exist in the mech pin (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-mech-pin/dev` on 2026-09-22).

USER step 6: ADDED `cargo fetch` of sp1-sdk 6.1.0 (verdict:134, VERIFIED).  Status OPEN (brief:543, VERIFIED).  A cargo fetch writes the cargo home and a harness build writes a target dir;  both run under the open floor, so the user runs them (plan decision, BELIEVED until the user rules on it).

USER step 7: ADDED Stage 0c denominator.sh freeze with DENOMINATORS.sha256 (verdict:135, VERIFIED).  Status OPEN;  it waits on step 2 (brief:543, VERIFIED).  The assay pin holds dev/denominator.sh, dev/denominators.json and dev/DENOMINATORS.sha256 as the recipe to copy (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev` on 2026-09-22).

USER step 8: ADDED round 2, write the two A1 F2 fixtures (refl body vs opaque postulate) and diff the erase output on the pin before Stage B (verdict:136, VERIFIED).  Status OPEN (brief:543, VERIFIED).

Open on 2026-09-22, in the verdict's numbering: steps 2, 3, 4, the second half of 5, 6, 7 and 8 (brief:543, VERIFIED).  RAN, floor still OPEN: step 1, where `diskfree --apply` reclaimed 0K and free space stays at 21 GiB under the 30 GiB floor (brief:543, VERIFIED).  DONE: the first half of step 5 (brief:543, VERIFIED).

What each M0 stage waits on.  The rows below are plan decisions;  each is BELIEVED until the stage's build log records the step it read.

- Stage A waits on no open step.  It starts on the assay pin eebe37e today (brief:541 OQ6, VERIFIED).  The second half of step 5 is the flip trigger;  a median under 211 ms reopens Stage A as a re-carry from the mech pin 1e4f371, and a median at or above 211 ms closes the flip.
- Stage B waits on step 8, the two A1 F2 fixtures and the erase diff on the pin (verdict:136, VERIFIED).  The evaluator and the Acc fixture start without it;  TRACE-ERASURE does not print green before step 8 lands.
- Stage C starts its lowering and its encoder without any open step.  ENC-XCHECK waits on step 3, because the toolchain's hello guests and `llvm-readelf -h` are the reference bytes (BELIEVED, settled by the Stage C brief).  ELF-ACCEPTED on HALT waits on step 6 and on a harness build the user runs under the open floor, because the executor call runs through the sp1-sdk harness (BELIEVED, settled by the Stage C brief).
- Stage D starts the emulator twin without any open step.  The harness and EXEC-DIFF wait on step 6 (verdict:134, VERIFIED) and on a harness build the user runs under the open floor.
- Stage E waits on Stage D and on no open step.
- Stage F starts after Stage E.  Its DENOMINATORS row binds on the hash match;  its inner Bend 2 row prints OPEN until steps 2 and 7;  M0-RATIO is informational at M0, so M0 does not wait on Bend 2 (brief:541 OQ2 and brief:543, VERIFIED).  PROVE-ONCE waits on step 6.
- Step 4 blocks nothing.
## 3 Repository layout

The name is attest, the source extension is .att and the driver is attest with the verbs attest check, attest build, attest run, attest --axioms, attest --externs, attest --passes and attest spec-count, from P1:7, the same word P3 proposed (verdict:140, VERIFIED).  The collision note is information only;  every row of it is BELIEVED because no registry host answered from the verdict's sandbox, and curl on https://crates.io/api/v1/crates/attest, https://pypi.org/pypi/attest/json, https://registry.npmjs.org/attest, https://formulae.brew.sh/api/formula/attest.json and https://api.github.com/search/repositories?q=attest settles it (verdict:141, VERIFIED as the verdict's text).  vouch is the runner-up word if the user prefers a rarer one (verdict:143, VERIFIED).

The repository is /Users/oobi/Documents/attest.  Stage A creates it;  this plan does not.  This unit did not read, build in or touch that path, because peer sessions own it today (the unit's pin rules;  BELIEVED, settled by the unit's call log).  The tree mirrors the assay M0 layout at tpl:104-130 with the attest names.  The EVM directories of the assay pin, abi/, asm/, emit/, evm/, keccak/ and reference/, are not carried (VERIFIED that the pin lists them, by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin` on 2026-09-22;  the carry list itself is BELIEVED until Stage A writes CARRIED.md).  keccak/ is a candidate carry for the Stage E software twin of the Keccak host (BELIEVED, settled at Stage E).

dev/dunecho.sh is the dune wrapper: dunecho for every dune verb and leancho for every lake verb (tpl2:190, VERIFIED), run as `zsh -f dev/dunecho.sh build` (verdict:133 and brief:543, VERIFIED).  The mech pin holds dev/dunecho.sh and the assay pin holds dev/dune.sh (both VERIFIED by `ls` of each pin's dev/ on 2026-09-22).  The attest tree names it dev/dunecho.sh;  the two wrappers differ, VERIFIED by `diff` on 2026-09-22 (`2,30c2,8`);  A2 carries the mech dev/dunecho.sh and rewrites every dev/dune.sh call in the carried scripts (plan:563).  No cargo, forge or opam build runs in an agent's hands at any stage of M0 while the floor is open (tpl:100 for the assay form and brief:543 for the floor, VERIFIED).

The pins kept through M0: the assay pin at /Users/oobi/Documents/kan-sp1-lang-assay-pin, a worktree detached at eebe37e (VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin rev-parse --short HEAD` on 2026-09-22), and the mech pin at /Users/oobi/Documents/kan-sp1-lang-mech-pin, a worktree detached at 1e4f371 with the veil submodule at a7534ce (VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin rev-parse --short HEAD` and by `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` on 2026-09-22).  Every carry reads the assay pin only;  no unit builds in a pin and no unit runs a git command that writes there.  dev/carry-check.sh compares every carried file against the assay pin and fails on any difference that CARRIED.md does not name (tpl:134 for the assay form, VERIFIED;  the attest form is a Stage A deliverable).

M0-RATIO is informational at M0 with rung 3 at most 2.0, so M0 does not wait on Bend 2 (brief:541 OQ2 and brief:543, VERIFIED).  The DENOMINATORS row of Stage F prints OPEN until USER steps 2 and 7 land (plan decision, BELIEVED until the Stage F log).

The tree at the M0 exit, by copy then delta from tpl:104-130.  Each row names the stage that writes it;  the carried rows are Stage A.

```
attest/
  dune-project             (lang dune 3.24) (name attest)
  LICENSE-MIT LICENSE-APACHE README.md SPEC.md CARRIED.md
  dev/PIN                  eebe37e
  lib/                     library attest_lib, carried verbatim at eebe37e
  surface/                 library attest_surface, carried verbatim at eebe37e
  test/                    the kernel suite, carried verbatim at eebe37e, SUITE-KERNEL
  erase/                   library attest_erase, the opaque-proof evaluator, Stage B
  lower/                   library attest_lower, erased term to RV64IM, Stage C, at most 1,100 lines
  elf/                     library attest_elf, the ELF64 encoder, Stage C, at most 800 lines
  emu/                     library attest_emu, the RV64IM emulator twin, Stage D
  host/                    library attest_host, the Host sum type, Read Commit Halt at Stage D,
                           Keccak Sha256 U256Mul at Stage E
  harness/                 the pinned Rust harness on sp1-sdk 6.1.0, Stage C, at most 100 lines (D3 extends it at Stage D)
  bin/attest.ml            driver: check | build | run | spec-count
                           | --axioms | --externs | --passes
  corpus/                  the ACCEPT and REFUSE corpora and the EXEC-DIFF rows, .att files
  fixtures/                the two A1 F2 fixtures and the Acc fixture, Stage B
  twin/                    the Lean twin sources for LEAN-TWIN, Stage B
  dev/                     gates.sh dunecho.sh bench.sh carry-check.sh r0-count.sh r0-audit.sh
                           r0-diff.sh trusted-lines.sh house.sh denominator.sh denominators.json
                           DENOMINATORS.sha256 bend-cli.txt TOOLCHAIN.md
                           M0-BUILD-LOG.md MUTATION-LOG.md
```

The directory names erase/, lower/, elf/, emu/, host/, harness/, fixtures/ and twin/ are plan decisions (BELIEVED until the stage briefs pin them).  The budgets on the lower/, elf/ and harness/ rows are the OQ4 numbers (brief:541, VERIFIED).  The driver verbs are the verdict's (verdict:140, VERIFIED).  The dev/ scripts gates.sh, bench.sh, carry-check.sh, r0-count.sh, r0-audit.sh, trusted-lines.sh, house.sh, denominator.sh, denominators.json and DENOMINATORS.sha256 exist in the assay pin's dev/ to copy from, and dunecho.sh exists in the mech pin's dev/ (VERIFIED by `ls` of each pin's dev/ on 2026-09-22);  r0-diff.sh, bend-cli.txt and TOOLCHAIN.md are new at M0 (BELIEVED, settled by the same `ls`, which lists none of them in the assay pin).

What the carried tree supplies: lib/ at 6,193 lines whole-lib, informational (verdict:125, VERIFIED), and surface/ with its elaborator and grammar (BELIEVED for the assay pin, settled by `wc -l` at Stage A).  attest writes no copy of either.  The kernel row of TRUSTED-LINES prints the carried count against the 4,100 bound from Stage A (brief:541 OQ4, VERIFIED).
## 4 Trusted base and budgets

The trusted base at M0 is the kernel bucket carried from the assay pin eebe37e plus the three artifacts M0 writes: lower, encoder and harness.  OQ4 sets the bounds: "TRUSTED-LINES kernel bound 4,100 at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100 (this replaces the brief's 3,000)" (brief:541, VERIFIED).  This section replaces the six EVM artifact budgets of the template (tpl:140-147), because attest drops contract, recognize, model, abi, layout and keccak (verdict:106, VERIFIED).  The emulator emu/rv64im.ml, about 700 lines, is outside the base (verdict:106, VERIFIED);  gates, dev scripts and Lean proofs are outside the base (P1:133, VERIFIED).

### 4.1 The OQ4 bounds

| bucket | bound at M0 | bound at M1 | what it holds | first stage that measures it |
| --- | --- | --- | --- | --- |
| kernel | 4,100 | 4,400 | the 12 KERNEL files of the assay script (assay dev/trusted-lines.py:7) plus the literal kinds and their check rules (verdict:150) | Stage A, at 3,997 (verdict:117) |
| lower | 1,100 | 1,100 | lower.ml, about 900 lines by the design estimate (verdict:106) | Stage C (verdict:117) |
| encoder | 800 | 800 | rv64im.ml, elf64.ml and runtime.ml, about 700 lines by the design estimate (verdict:106) | Stage C (verdict:117) |
| harness | 100 | 100 | attest-harness, Rust on sp1-sdk = 6.1.0, execute only (verdict:106) | Stage C (pulled forward, plan:567) |

The bound of a bucket binds from the stage that first measures it;  before that stage the row prints 0/<bound> (00-bindings:17, VERIFIED).  The M1 lift from 4,100 to 4,400 holds the 267-line level overlay (verdict:150 and P1:59, VERIFIED);  M1 states that lift in its own plan, never silently (P1:133, VERIFIED).  The M0 headroom is 4,100 minus 3,997, which is 103 lines, for the literal kinds and their check rules (verdict:150, VERIFIED);  whether 103 lines hold Word32, Word64, U256 and Bytes behind `Lit of Literal.t` (P1:16) is BELIEVED, and the Stage B TRUSTED-LINES row settles it.  The M1 headroom is 4,400 minus 3,997 minus 267, which is 136 lines, BELIEVED until the M1 overlay merge measures it.

### 4.2 The measured baseline, probe 4

The verdict's trusted-lines section names "probe 4 rows verbatim plus whole-lib 6,193 informational plus the OQ4 bounds" (verdict:125, VERIFIED).  The probe 4 rows live in the verdict's probe list (verdict:33-35, VERIFIED) and read, verbatim:

- `zsh -f A/dev/r0-count.sh` R0-COUNT OK (verdict:33);
- `A/_build/default/bin/assay.exe spec-count`: formers 2 Lan Ran, shapes declared 5, admitted 3 SPi SColl SMu, named rules present 3 proof-irrelevance subsingleton-large-elimination literal-fast-path (verdict:34);
- `zsh -f A/dev/trusted-lines.sh`: kernel=3997 want=3997 bound=4000, emitter=1800/1800, assembler=238/600, keccak=89/250, abi=35/400, layout=8/250, listing=54/250, total=2224/3550 OK (verdict:35).

The third row was re-run read-only on 2026-09-22 by `zsh -f /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev/trusted-lines.sh`;  it printed the same seven rows, then `TRUSTED-LINES total=2224/3550 ratified=3550` and `TRUSTED-LINES OK`, exit 0 (VERIFIED by that command;  the script is `exec python3 -P dev/trusted-lines.py`, assay dev/trusted-lines.sh:3, and it reads files only).  The first two rows need the built assay.exe, which the pin rules forbid in the pin;  they stand VERIFIED at verdict:33-34 on the peer tree and are re-proved by the Stage A gate battery.

The whole lib is informational, not a bound: `wc -l /Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/*.ml` prints `6193 total` over 22 files (VERIFIED by that command on 2026-09-22;  verdict:32 records the same 6,193 and 22).  The 2,196 lines outside the kernel bucket are erase.ml 1,484, quantity.ml 158, prim.ml 139, eterm.ml 117, pp.ml 102, error.ml 82, spec_count.ml 62, budget.ml 27, literal.ml 14 and level.ml 11 (VERIFIED by the same wc);  1,484 + 158 + 139 + 117 + 102 + 82 + 62 + 27 + 14 + 11 = 2,196 and 3,997 + 2,196 = 6,193.

### 4.3 The TRUSTED-LINES arithmetic, row by row

The kernel bucket is the sum of the 12 names in `KERNEL = "shape term rules check value eval conv totality positivity global order bignum".split()` (assay dev/trusted-lines.py:7, VERIFIED), each read as lib/<name>.ml (assay dev/trusted-lines.py:28, VERIFIED).  The counts below are `wc -l` on the pin on 2026-09-22 (VERIFIED by `wc -l /Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/*.ml`).

| row | file | lines | running sum |
| --- | --- | --- | --- |
| 1 | lib/shape.ml | 60 | 60 |
| 2 | lib/term.ml | 133 | 193 |
| 3 | lib/rules.ml | 1,481 | 1,674 |
| 4 | lib/check.ml | 538 | 2,212 |
| 5 | lib/value.ml | 137 | 2,349 |
| 6 | lib/eval.ml | 297 | 2,646 |
| 7 | lib/conv.ml | 396 | 3,042 |
| 8 | lib/totality.ml | 146 | 3,188 |
| 9 | lib/positivity.ml | 118 | 3,306 |
| 10 | lib/global.ml | 130 | 3,436 |
| 11 | lib/order.ml | 510 | 3,946 |
| 12 | lib/bignum.ml | 51 | 3,997 |

The sum 3,997 equals `KERNEL_WANT = 3997` (assay dev/trusted-lines.py:22, VERIFIED) and sits under `KERNEL_BOUND = 4000` (assay dev/trusted-lines.py:23, VERIFIED).  The attest form of the script keeps the 12 names and makes three deltas, each a plan decision BELIEVED until the Stage A battery prints the new rows: (1) `KERNEL_BOUND` becomes 4100 and the equality test `kernel == KERNEL_WANT` (assay dev/trusted-lines.py:30) becomes `kernel <= KERNEL_BOUND`, with `want=3997` printed as the carried baseline;  (2) the six ARTIFACTS rows (assay dev/trusted-lines.py:9-14) become three, `("lower", 1100, "lower", ("lower.ml",))`, `("encoder", 800, "elf", ("rv64im.ml", "elf64.ml", "runtime.ml"))` and `("harness", 100, "harness", ("src/main.rs",))`, the folder names of part 3 (elf/ for the encoder and harness/ for the harness;  the crate is attest-harness as in part 8);  (3) the file walk `rglob("*.ml*")` (assay dev/trusted-lines.py:60) also matches `*.rs`, because the harness is Rust (verdict:106).  A row whose folder is absent prints 0/<bound> and does not fail before the stage of 4.1 that first measures it (00-bindings:17), and it prints FAIL on an absent folder from that stage onward;  the `ratified=` total row prints 4100 + 1100 + 800 + 100 = 6,100 at M0.

### 4.4 The disclosure commands

The verdict lists the disclosure set (verdict:113, VERIFIED): `attest check --axioms`, `attest check --externs`, `attest build --passes`, `attest spec-count`, `dev/r0-count.sh`, `dev/r0-audit.sh`, `dev/trusted-lines.sh` and `shasum -c dev/DENOMINATORS.sha256`.  Each row below names what the command prints and the M0 stage that first runs it (verdict:117, VERIFIED).  The `--axioms` and `--passes` forms of P1:134 are `attest --axioms FILE` and `attest --passes FILE`;  the verdict's `attest check` and `attest build` subcommand forms win (verdict:113).

| command | prints | first M0 stage | M0 rule |
| --- | --- | --- | --- |
| `attest check --axioms FILE` | the tracked postulates FILE uses, one per line | Stage A (AXIOMS-empty, verdict:117) | empty on every M0 row;  `Quot.sound` arrives at M2 (verdict:102, verdict:120) |
| `attest check --externs FILE` | the EXTERN-ROSTER, the precompile postulates FILE names (verdict:23) | Stage E (Keccak, Sha256, U256Mul, verdict:117) | each name must be an OQ5 constructor (brief:541) |
| `attest build --passes FILE` | `walks=5 conv_calls=<n> whnf_calls=<n>` per definition (P1:134) with the re-entry counters (verdict:112) | Stage F (PASSES, verdict:117) | walks at most 5, no optimizer pass (brief:94-98 by 00-bindings:31) |
| `attest spec-count` | the R0 block: formers 2 Lan Ran, shapes declared 5, admitted 3 SPi SColl SMu, named rules present 3 (verdict:34) | Stage A (R0-COUNT, verdict:117) | formers must read exactly 2 |
| `zsh -f dev/r0-count.sh` | R0-COUNT OK, exit 0, when the "## R0 counts" fenced block of SPEC.md diffs empty against spec-count (assay dev/r0-count.sh:3-5) | Stage A | exit 0 |
| `zsh -f dev/r0-audit.sh` | R0-AUDIT OK from `python3 -P dev/r0-audit.py` (assay dev/r0-audit.sh:3), the walk of the term sum | Stage A | exit 0, no third former |
| `zsh -f dev/trusted-lines.sh` | the four bucket rows of 4.1 and the `ratified=` total | Stage A | every measured row under its bound |
| `shasum -c dev/DENOMINATORS.sha256` | one OK line per frozen Bend 2 denominator row (brief:87-93 by 00-bindings:31) | Stage F (DENOMINATORS, verdict:117) | binding at M0 on the hash match (plan:450);  the inner Bend 2 row is the word OPEN until USER step 7 (brief:543) |

The commands `attest check --axioms`, `attest check --externs` and `attest build --passes` are BELIEVED as spellings until Stage A adapts bin/assay 221 lines to bin/attest with `--passes --axioms --externs spec-count` (verdict:106);  the assay pin spells the same disclosure as assay.exe subcommands (verdict:34).
## 5 The kernel term at M0

M0 adds no former and no shape constructor.  The kernel term is kanon R0: the type formers are exactly `Lan_s` and `Ran_s` along a closed shape grammar of five shapes (brief:38-47, VERIFIED).  In OCaml the two formers are `Lan of t Shape.t * t` and `Ran of t Shape.t * t` beside `Univ` in `Term.t` (A/lib/term.ml:48-50 by P1:13, VERIFIED at P1:13), and `Shape.t` is the closed variant `SPi of Quantity.t * string * 'a`, `SColl of int`, `SPar of 'a * 'a`, `SMu of string * 'a list`, `SNu of string * 'a list` (A/lib/shape.ml:11-15 by P1:14, VERIFIED at P1:14).  The term walk a reader reruns is `rg -n "^  \| " lib/term.ml` in the assay pin;  it lists 13 constructors, and only `Univ`, `Lan` and `Ran` produce types (P1:19, VERIFIED at P1:19).  The constructs of the template section 5 (tpl:153-161) are EVM namings that attest drops (verdict:106);  this section keeps the template's rule that a naming carries a refusal citation in SPEC.md and that dev/r0-audit.sh fails on a naming with no citation (tpl:161, VERIFIED).

### 5.1 The five shapes and their M0 standing

| shape (A/lib/shape.ml:11-15) | `Lan_s` gives | `Ran_s` gives | Lean 4 feature | standing at M0 |
| --- | --- | --- | --- | --- |
| `SPi`, weakening by A (brief:43) | Sigma | Pi | dependent pairs, dependent functions | admitted, construction (verdict:34) |
| `SColl`, finite discrete collapse (brief:44) | variants | records | enumerations, structures | admitted, construction (verdict:34) |
| `SPar`, parallel pair collapse (brief:45) | `Quot` | equalizer subtypes | `Quot`, subtypes | declared, not admitted;  M2 (verdict:100, verdict:120) |
| `SMu`, polynomial P (brief:46) | initial algebras, W types | none | inductive types and families | admitted, construction (verdict:34) |
| `SNu`, polynomial P (brief:47) | none | terminal coalgebras | coinductives | declared, not admitted;  M3 (verdict:100, verdict:121) |

The assay pin's own schedule admits `SPar` at M1 and `SNu` at M2 (A/lib/rules.ml:20-23 by verdict:36);  attest's milestones move them to M2 and M3 (verdict:120-121, VERIFIED), and the milestone list wins for this plan.  Rows 1 to 3 are constructions in the kernel;  rows 4 and 5 are the algebra and coalgebra universal properties in the kernel, Kan by an omega-chain theorem outside it (P1:80, BELIEVED, settled by Riehl chapter 6 as P1:70 states).  Universes, contexts, substitution and literal accelerators are the ambient framework (brief:55-56);  definitional eta holds only for functions and structures (brief:58);  a surface macro over a Pi, Sigma or inductive kernel fails R0 (brief:57);  ZK is not a former and not a shape (brief:61-64).  VERIFIED at brief:49-64.

### 5.2 The M0 constructs, construction or naming

Each row names one M0 construct, its kernel standing and the gate that catches a divergence.  No row is a former.

- Word32: the library global `Lan_SPi Nat (fun n => n < 2^32)` with the second component at quantity 0, erased by its Prop type (verdict:101, P1:80).  The TYPE is a naming over `SPi`;  the REPRESENTATION is an erase row, `RWord` in eterm (verdict:98).  Word64, U256 and Bytes follow the same form (P1:80).  Their literals extend `Literal.t` behind `Lit of Literal.t` (A/lib/term.ml:58 by P1:16), and the check rules of those literal kinds are what the OQ4 kernel headroom of 103 lines pays for (verdict:150).  Gates: TRACE-ERASURE, EXEC-DIFF (P1:74).
- Host: the library sum `Lan (SColl n)`, a naming over `SColl` (verdict:103).  Under OQ5, n is 3 at Stage D (Read, Commit, Halt) and 6 at Stage E (Keccak, Sha256, U256Mul), and no M0 file names Bn254 or Secp256k1 (00-bindings:19, VERIFIED);  the verdict's `SColl 8` is the M2 roster (verdict:103, verdict:120).  Gates: HOST-ROSTER, EXTERN-ROSTER (verdict:104, verdict:23).
- Prog: the free monad `Lan_SMu` over `1 + Sigma (h : Host) (Resp h -> X)`, a construction through the admitted `SMu` row (verdict:103).  Its `In` nodes lower to ecalls, which is an emission row and not a kernel rule (verdict:103).  Gates: EXEC-DIFF, PUBVAL-DIGEST (verdict:117).
- Bound proofs: quantity-0 inhabitants of `Ran_pi` types into Prop, a naming over an existing former (P1:16).  Gate: TRACE-ERASURE in the OQ7 form (brief:541).
- Ambient Prop, proof irrelevance and subsingleton large elimination: named rules present at the pin, with literal-fast-path (verdict:34, verdict:102).  `Quot.sound` arrives at M2 as the only tracked axiom (verdict:102, verdict:120).  Gate: AXIOMS empty at M0 (verdict:118).
- Precompile postulates: the extern kind tracked by `--externs` beside `--axioms`, a naming (P1:16, verdict:23).  Gate: HOST-ROSTER at Stage E, whose leg also runs `attest check --externs ROW` per row and fails on a name outside the OQ5 roster;  EXTERN-ROSTER names the `--externs` disclosure row of part 4 and is not a gate id, because verdict:117 names only GUARD-TWIN and LOWER-REFUSE at Stage E and part 8 has no such row;  the Gates list of the Host entry above reads the same way.
- Cycles, the allocator and the calling convention: framework facts printed by the executor and checked by ENC-XCHECK and EXEC-DIFF, never kernel (P1:16).

### 5.3 The R0 gates at Stage A

Stage A runs R0-COUNT, R0-AUDIT and R0-DIFF on the carried tree (verdict:117, VERIFIED), and every later stage exit runs them again.

| gate | command, from the attest root | pass rule | source |
| --- | --- | --- | --- |
| R0-COUNT | `zsh -f dev/r0-count.sh` | the fenced block under "## R0 counts" in SPEC.md diffs empty against `attest spec-count`, whose count line has the section 7 form `R0-COUNT formers=<n> shapes=<n>` (plan:362, the one binding form);  prints `R0-COUNT OK`, exit 0;  else prints the diff and `R0-COUNT FAIL`, exit 1 | assay dev/r0-count.sh:3-5 (VERIFIED by cat);  brief:59 |
| R0-AUDIT | `zsh -f dev/r0-audit.sh`, which is `exec python3 -P dev/r0-audit.py <root>` | the walk of the term sum finds no third former and every naming carries a SPEC.md citation;  prints `R0-AUDIT OK`, exit 0 | assay dev/r0-audit.sh:3 (VERIFIED by cat);  brief:60;  tpl:161 |
| R0-DIFF | `diff -q dev/r0-diff/term.ml lib/term.ml && diff -q dev/r0-diff/shape.ml lib/shape.ml && diff -q dev/r0-diff/spec_count.ml lib/spec_count.ml` | all three diffs empty at every stage exit;  dev/r0-diff/ holds the three files as `git show 2c2e6e6:lib/<name>.ml` from kanon, with their sha256 in dev/r0-diff/SHA256 | verdict:96;  P1:14 |

The R0-COUNT and R0-AUDIT rows print OK on the assay pin today (verdict:33-34, VERIFIED on the peer tree by the verdict's probe 4;  the pin rules forbid a build in the pin, so this unit did not rerun them).  The R0-DIFF row is a plan decision: the reference copy under dev/r0-diff/ is BELIEVED until Stage A vendors it from kanon 2c2e6e6, and the kanon tree is outside this unit's read set.  The R0-COUNT pass value quoted at P1:13 is `formers 2: Lan Ran` (VERIFIED at P1:13);  that text is the SPEC.md block, and the gate output line keeps the section 7 form `R0-COUNT formers=<n> shapes=<n>` (plan:362, the one binding form).

### 5.4 The base identity and the borrowed overlay

The base is assay at eebe37e: `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin rev-parse --short HEAD` prints `eebe37e` and `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin rev-parse --short HEAD` prints `1e4f371` (VERIFIED by those commands on 2026-09-22).  The veil submodule is checked out: `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` prints ` a7534cedeac82d396de8e23058ee6bc990560f65 vendor/veil (a7534ce)` (VERIFIED by that command;  brief:543 records the same checkout).  The term sum of the base is byte-identical to veil's: `diff -q /Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/term.ml /Users/oobi/Documents/kan-sp1-lang-mech-pin/vendor/veil/lib/term.ml` exits 0 with no output (VERIFIED by that command, read-only, on 2026-09-22;  verdict:30 records the same).  The shape grammars differ: veil adds `SZk`, `SFhc` and `SMpc` at V/lib/shape.ml:16-19 (verdict:29, VERIFIED at verdict:29), which is the counterexample R0 refuses (brief:61-64), so R0-DIFF pins shape.ml against kanon and never against veil.  The mech pin has no lib/term.ml and no lib/shape.ml of its own (verdict:31);  its kernel is veil's plus a level overlay, and its lib/ is check.ml 643, conv.ml 404, eval.ml 314, level_eq.ml 144, level_scope.ml 32, level_var.ml 53, level.ml 36, rules_lvl.ml 2 and rules.ml 2,116, total 3,744 over 9 files (VERIFIED by `wc -l /Users/oobi/Documents/kan-sp1-lang-mech-pin/lib/*.ml`;  verdict:32 records 3,744 in 9).

The overlay borrowed from mechanism-lang for the R1 import oracle (brief:77-81 by 00-bindings:29) has four measured pieces, none of them merged at M0 (OQ3, brief:541;  00-bindings:15):

| piece | path under the mech pin | lines | when attest takes it |
| --- | --- | --- | --- |
| level overlay | lib/level_eq.ml, lib/level_scope.ml, lib/level_var.ml, lib/level.ml, lib/rules_lvl.ml | 144 + 32 + 53 + 36 + 2 = 267 | M1, into the kernel bucket (verdict:150;  P1:59) |
| importer | import/*.ml, 10 files | 1,543 (with the 8 .mli files, 1,748) | M1, as the sibling M/import (verdict:106) |
| PRELUDE-CHECKED driver | dev/prelude-gates.py | 89 | M1, count mode then ratchet (OQ3, brief:541) |
| prelude map | map/prelude.map.tsv and map/NEVER.tsv | 2,478 + 186 = 2,664 rows | M1, with the map (verdict:23) |

All four counts are VERIFIED by `wc -l` on the mech pin on 2026-09-22, read-only.  The 267-line level overlay matches P1:59 and verdict:150;  the 1,543-line importer matches verdict:106.  The estimate of about 480 lines in this unit's brief matches no measured piece;  the measured rows above bind and the estimate is retired.  The mech pin's own gates name PRELUDE-CHECKED at its Stage D (mech dev/gates.sh:370, VERIFIED by rg).

### 5.5 The flip rule of OQ6 and its M0 moment

The ruling, verbatim from the brief's section 10: "OQ6: the kernel base is assay;  the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms (this replaces Q0)." (brief:541, VERIFIED).  The threshold is the 2x line: the assay side is pinned at 421.774 ms median over 7 runs on the 77 fixtures present in both trees (P1:58, VERIFIED at P1:58), and 421.774 divided by 2 is 210.887, so a median under 211 ms means mechanism-lang is at least twice as fast.

The second half of USER step 5 is the trigger and stays a USER step: `zsh -f dev/dunecho.sh build` in the mech pin, then `RUNS=7 zsh -f dev/bench.sh SUITE-KERNEL '_build/default/test/main.exe vendor/veil/test'` with the paths made absolute (brief:543, VERIFIED).  The first half, the veil checkout, is done (brief:543;  the submodule status above).  M0 checks the flip at two moments.  (1) Stage A entry: the CARRY gate reads dev/FLIP.md, which records the median or the word OPEN;  a median under 211 ms turns Stage A into a re-carry from the mech pin 1e4f371 with veil a7534ce, and a median at or over 211 ms or OPEN carries assay eebe37e (00-bindings:21).  (2) The M0-EXIT stamp: the stamp copies the dev/FLIP.md line, and a median printed after Stage A closed does not reopen M0;  it is an M1 decision.  Both moments are plan decisions, BELIEVED until the user prints the median;  the assay carry is the default under the ruling (brief:541).
## 6 Emission

Emission at M0 is the tail of the pipeline, erase then lower then encode (brief:318, VERIFIED), rewritten from tpl:163-171 for the RV64IM and ELF64 target of OQ1 (brief:541, VERIFIED).  TOOL is /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md, cited as tool:N;  its SP1 rows read the raw files of succinctlabs/sp1 at d454975 (tag v6.1.0), the commit that `/Users/oobi/.sp1/bin/cargo-prove prove --version` prints here (tool:3, tool:11, VERIFIED).  The words RV32IM and ELF32 at brief:325-328 are superseded by OQ1 (00-bindings.md:11, VERIFIED).  The EVM rows of tpl:165-171 (PUSH32, MLOAD, CODECOPY, the two codes, error selectors) have no counterpart on a zkVM guest and are dropped.

### 6.1 Erase

The erasure pass maps quantities to `eterm` and effect programs to `Host` sequences (brief:324, VERIFIED).  The `eterm` representation carries the RV64 reprs RWord, RStruct, RUnion, RFunc and RThunk plus KPrim, adapted from erase.ml:249, erase.ml:413 and eterm.ml:17-22 of the assay pin (verdict:98, VERIFIED at the verdict;  the pin line numbers are BELIEVED until Stage B opens those files).  Per OQ7 the evaluator inside erase never unfolds a quantity-0 global:  a proof body and an opaque postulate of the same type erase to the same `eterm`, so TRACE-ERASURE compares the two ELFs byte for byte (brief:541, VERIFIED).  The two A1 F2 fixtures of USER step 8 seed that gate (00-bindings.md:23, VERIFIED).  Word32 is Lan_SPi Nat with the bound n < 2^32 in the second component, erased because the component is a Prop (verdict:101, VERIFIED);  a Word32 value erases to one RWord and a Nat without a bound proof erases to the bignum runtime (brief:306-308, VERIFIED).  A bound proof in scope removes the range check;  without it the lowering emits the check plus a branch to Halt 1 (verdict:105, VERIFIED).

Host at M0 has three constructors at Stage D, Read, Commit and Halt, and six at Stage E with Keccak, Sha256 and U256Mul (brief:541 OQ5, VERIFIED).  Nothing in Host is a shape and the kernel never sees it (brief:299-300, VERIFIED).  Each constructor lowers to one ecall sequence of section 6.5.

### 6.2 Lower to the RV64IM IR

lower.ml rewrites the EVM emit.ml (493 lines) into about 900 lines and targets a small RV64IM IR with registers, frames, calls and ecall (verdict:106, VERIFIED;  brief:325 read with RV64IM under OQ1).  The IR uses the standard calling convention, a0 to a7 for arguments, sp frames and ra return, so clang-assembled objects cross-check the encoding (brief:309-311, VERIFIED).  Register numbers: ra = x1, sp = x2, t0 = x5, a0 = x10, a1 = x11, a2 = x12 (tool:239, VERIFIED).  Memory is one bump allocator with no collector;  inductive values are tagged heap nodes (brief:304-306, VERIFIED).  The stub at `_start` sets sp below 0x78000000 and the bump pointer (verdict:107, tool:95, VERIFIED).  div and rem never trap;  the only guest faults are bad memory and bad ecall (verdict:105, VERIFIED).  Every instruction is 4 bytes and there is no C extension (tool:31, VERIFIED).

The IR instruction set, one row per encoder row.  The base rows come from the 14-row RV32IM reference of tool:224-237 and stay valid RV64 words (tool:239, VERIFIED);  the RV64 rows come from the executor opcode list (tool:26, VERIFIED).  The word of a base row is the clang word of TOOL;  the word of a W-form or 64-bit memory row is BELIEVED until ENC-XCHECK prints it.

| IR op | Instruction | Format and opcode | Use | Source |
|---|---|---|---|---|
| Add, Mul, Mulh, Div, Rem | add, mul, mulh, div, rem rd, rs1, rs2 | R 0110011 | 64-bit arithmetic on RWord, pointers and bignum limbs | tool:224, tool:233-236 |
| Addi | addi rd, rs1, imm12 | I 0010011 | frame and bump pointer moves, constants under 2^11 | tool:225 |
| Lui, Auipc | lui rd, imm20;  auipc rd, imm20 | U 0110111, U 0010111 | 32-bit constants and pc-relative addresses | tool:229-230 |
| Lw, Lwu, Ld | lw, lwu, ld rd, imm12(rs1) | I 0000011 | field and word loads;  lw sign-extends, lwu zero-extends | tool:226, tool:26 |
| Sw, Sd | sw, sd rs2, imm12(rs1) | S 0100011 | field and word stores | tool:227, tool:26 |
| Beq | beq rs1, rs2, imm13 | B 1100011 | match arms and range checks | tool:228 |
| Jal, Jalr | jal rd, imm21;  jalr rd, imm12(rs1) | J 1101111, I 1100111 | calls, returns and thunk entry | tool:231-232 |
| Addw, Subw | addw, subw rd, rs1, rs2 | R 0111011 | Word32 add and sub, 32-bit result | tool:26, tool:239 |
| Sllw, Srlw, Sraw | sllw, srlw, sraw rd, rs1, rs2 | R 0111011 | Word32 shifts | tool:26, tool:239 |
| Mulw, Divw, Remw | mulw, divw, remw rd, rs1, rs2 | R 0111011 | Word32 mul, div and rem, never trapping | tool:26, verdict:105 |
| Ecall | ecall | I 1110011 | one Host step, code in t0 | tool:237, tool:38 |

The OP-IMM-32 forms at opcode 0011011 (addiw and the W shifts by immediate) appear at tool:239 but not in the executor list of tool:26, so the IR does not emit them;  BELIEVED absent from the executor, settle: `rg -n ADDIW` on crates/core/executor/src/opcode.rs at the pinned commit.  Gate ENC-XCHECK assembles every encoder row with `/opt/homebrew/opt/llvm/bin/clang --target=riscv64-unknown-elf -march=rv64im -mno-relax -c row.s -o row.o` and compares `llvm-objdump -d row.o` word by word against the encoder output;  the tool row is tool:220 with riscv32 swapped for riscv64, the Homebrew clang 22.1.8 has the riscv64 target (tool:263, VERIFIED), `-mno-relax` is required (tool:284, VERIFIED), and Apple clang has no RISC-V target (tool:262, VERIFIED).  The rv64 assembly itself is BELIEVED until Stage C runs it.  ENC-XCHECK covers the 14-row reference plus one rv64 object per W form (verdict:107, VERIFIED).

### 6.3 Encode ELF64

elf64.ml writes the bytes with no LLVM, rustc, assembler or linker (brief:326-327, VERIFIED);  clang, lld, llvm-objdump and llvm-readelf are gate tools only and never in the compile path (tool:220, VERIFIED).  The executor accepts ELF32 or ELF64 (tool:28, VERIFIED), so ELF64 is the OQ1 choice and not a constraint;  the class of the hello guest stays BELIEVED until `llvm-readelf -h` on it after USER step 3 (verdict:107, tool:104).  The layout rows, each with the executor check that binds it:

| Field | Value | Source |
|---|---|---|
| e_ident | 7f 45 4c 46, EI_CLASS 2 (ELF64), EI_DATA 1 (little endian), EI_VERSION 1, EI_OSABI 0, 7 pad bytes | tool:245, tool:29 |
| e_type, e_machine, e_version | 2 (ET_EXEC), 243 (EM_RISCV), 1;  the executor bails on any other type or machine | tool:246, tool:30 |
| e_entry | the address of `_start`, a multiple of 4, at least 32, at or above 0x78000000, not equal to the maximum memory | tool:247, tool:101, tool:97 |
| e_phoff, e_shoff, e_flags | 64, 0, 0;  e_flags is never read and the section table is never read | tool:248, tool:100 |
| e_ehsize, e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx | 64, 56, 1 or 2, 0, 0, 0 | tool:249 gives the ELF32 sizes 52 and 32;  the ELF64 sizes 64 and 56 are the ELF standard, BELIEVED until `llvm-readelf -h` on the emitted fixture |
| program header (text) | p_type 1 (PT_LOAD), p_offset, p_vaddr 0x78000000, p_paddr = p_vaddr, p_filesz, p_memsz, p_flags 5 (PF_R + PF_X), p_align 0x1000 | tool:250, tool:96 |
| program header (data) | p_type 1, p_vaddr 0x78100000, p_flags 6 (PF_R + PF_W), never PF_W with PF_X, p_align 0x1000 | tool:251, tool:99, verdict:107 |
| segment bounds | a segment below 0x78000000 is rejected;  p_filesz or p_memsz equal to 2^48 - 1 is rejected;  at most 256 program headers;  only PT_LOAD is loaded | tool:96, tool:97, tool:99 |
| stack | STACK_TOP 0x78000000;  the stack grows down from it and the text segment starts there | tool:95, tool:96 |

The first fixture is HALT: `addi t0, x0, 0` (13 02 00 00), `addi a0, x0, 0` (13 05 00 00), `ecall` (73 00 00 00), 12 code bytes at the text load address with e_entry 0x78000000 (tool:253, VERIFIED).  Under ELF64 with one program header the file is 64 + 56 + 12 = 132 bytes;  the 96-byte count of verdict:107 is the ELF32 form of tool:253 and the ELF64 count supersedes it under OQ1 (BELIEVED, settle: `wc -c` on the emitted fixture).

Gate ELF-ACCEPTED runs attest-harness, at most 100 Rust lines on `sp1-sdk = "=6.1.0"` in execute mode only (verdict:106, tool:109, tool:111-195, VERIFIED), on the HALT fixture and passes when the harness prints `EXEC cycles=<n> syscalls=<n> pv= exit=0` (verdict:108, VERIFIED).  Whether the executor accepts a HALT without the 8 COMMIT and 8 COMMIT_DEFERRED_PROOFS ecalls in execute mode is BELIEVED (tool:253);  when it refuses, the fixture grows by the halt sequence of tool:102 and the gate row records the refusal message verbatim.  The harness needs the `cargo fetch` of sp1-sdk 6.1.0 from USER step 6 (brief:543, VERIFIED).  The sync API names `Elf::from`, `SP1Stdin::write_slice` and `SP1PublicValues::as_slice` are BELIEVED (tool:109);  settle: `symx` on the sdk sources after the fetch.

### 6.4 W-form facts

The executor at v6.1.0 is a 64-bit VM: `_start` runs `ld sp, 0(sp)`, `pc_start_abs` is a u64 and the memory image maps u64 to u64 (tool:25, VERIFIED).  It decodes ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, REMW, LWU, LD and SD beside the RV32 base (tool:26, VERIFIED).  The 14 reference words stay valid RV64 instructions;  add, mul, div and rem without a W suffix become 64-bit, and the W forms at opcode 0111011 give 32-bit results (tool:239, VERIFIED).  The sign extension rule: a W-form result is the low 32 bits of the operation sign-extended to 64 bits, lw sign-extends and lwu zero-extends;  TOOL records only "32-bit results" at tool:239, so the rule is BELIEVED from the RISC-V unprivileged specification, and EXEC-DIFF settles it with an addw row on 0x7fffffff plus 1 where the harness and the emulator must print the same pv.  RV32IM ELFs are not a supported target on this executor because the registers are 64-bit and wrap-around differs (tool:27, BELIEVED there;  settle: the riscv32im hello guest of USER step 3, brief:543).  Consequence for lower: Word32 arithmetic emits the W forms, and pointers, lengths, bignum limbs and Nat under no bound proof use the 64-bit forms;  the emulator twin emu/rv64im.ml (about 700 lines outside the trusted base, verdict:106) implements exactly the rows of the section 6.2 table and no more.

### 6.5 Syscall codes

The code goes in t0 (x5), the arguments in a0 (x10) and a1 (x11), and WRITE also uses a2 (x12);  HINT_LEN returns its length in t0 (tool:38, VERIFIED).  Every code below is VERIFIED from both files of the pinned commit, column G the line in crates/zkvm/entrypoint/src/syscalls/mod.rs and column X the line in crates/core/executor/src/syscall_code.rs, quoted at the TOOL line named (tool:40).  The Host to ecall map is verdict:103 (VERIFIED) narrowed to the OQ5 constructors.

| Host step | Syscall and registers | Code | Source |
|---|---|---|---|
| Read | HINT_LEN (len in t0), then HINT_READ (a0 ptr, a1 len) | 0x000000F0, 0x000000F1 | tool:62, tool:63, tool:103 |
| Commit | WRITE (a0 = 13 FD_PUBLIC_VALUES, a1 buf, a2 nbytes) | 0x00000002 | tool:45, tool:88 |
| Halt, digest | SHA_EXTEND and SHA_COMPRESS over the committed bytes | 0x00300105, 0x00010106 | tool:48, tool:49, tool:102 |
| Halt, commit | 8 COMMIT (a0 = i, a1 = 32-bit word i of the digest) | 0x00000010 | tool:58, tool:102 |
| Halt, deferred | 8 COMMIT_DEFERRED_PROOFS (a1 = 0) | 0x0000001A | tool:59, tool:102 |
| Halt, stop | HALT (a0 = exit code) | 0x00000000 | tool:44, tool:102 |
| Keccak (Stage E) | KECCAK_PERMUTE | 0x00010109 | tool:52 |
| Sha256 (Stage E) | SHA_EXTEND and SHA_COMPRESS | 0x00300105, 0x00010106 | tool:48, tool:49 |
| U256Mul (Stage E) | UINT256_MUL | 0x0001011D | tool:64, brief:541 OQ5 |

Never emitted: ENTER_UNCONSTRAINED 0x00000003 (tool:46), EXIT_UNCONSTRAINED 0x00000004 (tool:47), VERIFY_SP1_PROOF 0x0000001B (tool:60), MPROTECT 0x00000132 (tool:85) and POSEIDON2 0x00000133 (tool:86);  gate HOST-ROSTER scans the t0 immediates of the ELF and fails on any code outside the table above (verdict:104, VERIFIED).  Bn254 and Secp256k1 are M2 constructors and no M0 file names them (brief:541 OQ5, VERIFIED).  The precompile pointer convention, a0 the first operand and a1 the second, is BELIEVED (tool:38);  settle: crates/zkvm/entrypoint/src/syscalls/keccak_permute.rs at the pinned commit.  The executor-side digest check at halt is BELIEVED (tool:102);  settle: crates/core/executor/src/minimal/ecall.rs.  The SHA-256 over the committed bytes runs in software at Stage D and through the two SHA precompiles at Stage E;  that split is a plan decision, BELIEVED until Stage D measures both forms on the smallest Commit fixture with the EXEC cycles row.
## 7 Driver

bin/attest.ml is bin/assay.ml of the assay pin (221 lines) adapted with the flags --passes, --axioms and --externs and the verb spec-count (verdict:106, VERIFIED);  the two-speed pipeline of tpl:175 stays, check as the fast path and build as the full path.  The source extension is .att and the driver word is attest (verdict:140, VERIFIED).  The verbs are attest check, attest build and attest run;  the flags are --axioms, --externs and --passes;  spec-count is a verb with no file argument (verdict:113, verdict:140, VERIFIED).  The assay driver today parses `assay check [--print|--erased] FILE | axioms FILE | spec-count` (kan-sp1-lang-assay-pin/bin/assay.ml:9, VERIFIED by `rg -n` on 2026-09-22), so the delta moves axioms from a verb to a flag of check, adds --externs and --passes, replaces emit, trace and diff with build and run, and keeps spec-count.  Every verb prints one summary line on stdout, one row form per verb, so gate scripts parse it by the first token;  diagnostics go to stderr with the prefix `attest: <verb>: ` (the assay form at bin/assay.ml:75, VERIFIED).  R3 binds check through build and never a deploy or prove phase (00-bindings.md:33, tpl:175, VERIFIED).  The driver never installs and never proves (section 7.4).

### 7.1 Exit codes

The codes 0, 1, 2 and 64 are the assay codes carried as they stand (bin/assay.ml:3-4, :14, :44, :75, VERIFIED);  codes 3 and 5 are plan decisions, BELIEVED until Stage A lands bin/attest.ml and dev/driver-exit.sh pins every code on one fixture each.  The assay code 3 for a declared and unimplemented verb (bin/assay.ml:199) is not carried:  M0 declares no verb it does not implement, and tpl:175's deferred verbs (deploy, test) have no attest counterpart.

| Code | Meaning | Source |
|---|---|---|
| 0 | success | bin/assay.ml:44, tpl:175 |
| 1 | a parse, elaboration or check error;  the kernel error printed on stderr | bin/assay.ml:44, tpl:175 |
| 2 | an emission error, including the named refusal of a higher-order Pi and a Nat literal at or above 2^64 with no bound | bin/assay.ml:75, tpl:175 |
| 3 | the guest halted with a nonzero exit code or faulted under attest run | verdict:105, verdict:108 |
| 5 | a residual: stack or memory exhaustion of the driver, never proved away by a gate | tpl:177 |
| 64 | a usage error: unknown verb, unknown flag, missing or unreadable file, an output path that exists, a suffix other than .att | bin/assay.ml:4, :14, :28, :83 |

### 7.2 Verbs

| Verb | Input | Output line | Exit |
|---|---|---|---|
| `attest check FILE.att` | one .att source | `CHECK FILE defs=<n> ok` or `CHECK FILE FAIL <line>:<col> <message>` | 0, 1, 64 |
| `attest build FILE.att -o OUT.elf` | one .att source and a new output path | `BUILD FILE elf=OUT bytes=<n> text=<n> data=<n> hosts=<n>` | 0, 1, 2, 64 |
| `attest run OUT.elf [--stdin BYTES]` | one ELF64 and an optional hint byte file | `EXEC cycles=<n> syscalls=<n> pv=<hex> exit=<n>` | 0, 3, 64 |
| `attest spec-count` | SPEC.md of the tree | `R0-COUNT formers=<n> shapes=<n>` | 0, 1 |

attest check runs parse, elaborate and check (brief:318-323, VERIFIED): bidirectional elaboration with first-order pattern unification only, no instance search and no Auto at M0, then the Kan kernel of Stage A.  `defs=<n>` counts the top-level definitions the kernel accepted.  On the first kernel error the driver prints the FAIL row on stdout, the error text on stderr and exits 1;  it never continues past a failed definition.

attest build runs check, then erase, lower and encode of section 6, and writes OUT.elf as the only file;  an existing OUT is a usage error (the assay rule at bin/assay.ml:83, VERIFIED).  `bytes=<n>` is the file size, `text=<n>` and `data=<n>` the p_filesz of the two PT_LOAD segments, and `hosts=<n>` the ecall count that HOST-ROSTER reads back from the t0 immediates (verdict:104, VERIFIED).  The HALT fixture of section 6.3 prints `hosts=1`.

attest run drives the OCaml RV64IM emulator twin emu/rv64im.ml (verdict:106, VERIFIED) and prints the same EXEC line as attest-harness (verdict:108, VERIFIED), so dev/exec-diff.py compares the two lines and gate EXEC-DIFF passes on equality.  Exit 0 when the guest halts with exit 0;  exit 3 on a nonzero guest exit or a fault, with `exit=fault` on both sides (verdict:108, VERIFIED).  `--stdin BYTES` feeds one hint buffer that Read consumes through HINT_LEN and HINT_READ (tool:103, VERIFIED);  without it Read faults with `exit=fault`.  attest run never spawns the SP1 harness:  the harness is the Rust binary and dev/exec-diff.py runs both sides.

attest spec-count prints the former count from SPEC.md and the shape count, and exits 1 when formers is not 2 or shapes is not 5 (00-bindings.md:27, VERIFIED);  gate R0-COUNT reads the row.

### 7.3 Flags

| Flag | Verb | Input | Output lines | Exit |
|---|---|---|---|---|
| `--axioms` | check | one .att source | `AXIOM <name>` per tracked axiom the file reaches, then `AXIOMS FILE count=<n>` | 0, 1 |
| `--externs` | check | one .att source | `EXTERN <name>` per Host constructor and KPrim accelerator the file reaches, then `EXTERNS FILE count=<n>` | 0, 1 |
| `--passes` | build | one .att source and -o OUT | `PASS <def> walks=<n> reentries=<n>` per definition, then `PASSES FILE defs=<n> walks=<n> max=<n>` | 0, 1, 2 |

--axioms is the R1 disclosure: Quot.sound is a tracked axiom under --axioms (00-bindings.md:29, VERIFIED) and arrives at M2 (verdict:102, VERIFIED), so every M0 fixture with proof bodies prints `count=0`, and the opaque-postulate twin of TRACE-ERASURE prints one AXIOM row per postulate;  the two rows together show that erasure ignored the postulates (brief:541 OQ7, VERIFIED).  The assay form prints one axiom name per line (tpl:175, bin/assay.ml:58, VERIFIED);  the count tail is the delta.

--externs is the R3 disclosure of the trusted base list at verdict:113 (VERIFIED): every name outside the kernel that the emitted ELF depends on, the Host constructors of section 6.1 and the KPrim accelerators of the runtime.  The HALT fixture prints `EXTERN Halt` and `count=1`.  A name outside the OQ5 six is an emission error under build and a printed row under check, never a silent pass.

--passes is the R2 architecture row: the compiler prints the walks per definition, no optimizer pass, direct encoding (00-bindings.md:31, VERIFIED).  The M0 lever is WALKS 5 with reentries (verdict:112, VERIFIED), so `max=<n>` above 5 fails gate PASSES at Stage F (00-bindings.md:31, VERIFIED).  `reentries=<n>` counts the walks a definition re-enters through a thunk;  that column is a plan decision, BELIEVED until Stage C prints it on the corpus fixtures.

### 7.4 What the driver never does

The driver never installs: no sp1up, no cargo prove, no brew, no opam, no cabal, no curl;  every install is a USER Stage 0 step (brief:541-543, VERIFIED).  The driver never proves: no `client.prove` and no `client.verify`;  PROVE-ONCE runs once per milestone exit on the smallest row through dev/prove-once.sh under `/usr/bin/time -l`, skipped with a printed reason under 30 GiB of disk or 16 GiB of memory, and the milestone prints OPEN on that row (verdict:109, VERIFIED).  The driver never spawns clang, lld, llvm-objdump or llvm-readelf;  those are gate tools (tool:220, VERIFIED).  The driver never opens the network and never writes a file other than -o OUT.  The driver never calls attest-harness;  dev/exec-diff.py does.  Stack and memory exhaustion of the driver stay residual under exit 5 and no gate proves them away (tpl:177, VERIFIED).  bin/attest.ml is outside the four TRUSTED-LINES buckets kernel, lower, encoder and harness (00-bindings.md:17, VERIFIED at the bucket list);  that the driver is not counted is BELIEVED, settle: the row list of dev/trusted-lines.sh at Stage A.
## 8 Gates

This part is section 8 of the assay M0 plan (tpl:179-203) rewritten for attest, with the leg list of the mechanism-lang plan as the second reference (tpl2:147-173).  dev/gates.sh prints one line per gate under a watchdog tier that is a hang ceiling and never a performance budget, then a MEASURE block, then GATES-OK or GATES-FAIL with exit 1 on any FAIL (tpl2:149, VERIFIED).  Every gate names its command and its printed line (tpl:181, VERIFIED), and every gate has a non-vacuity mutant in part 9.  The gate names come from the M0 milestone line at verdict:117 and the M0 exit line at verdict:118;  the user ratified both on 2026-09-22 (brief:541, VERIFIED).  A gate whose expected line is missing from the run prints `GATES-FAIL missing=NAME`, so an informational gate that prints nothing still fails the run.

### The three statuses

- binding: a FAIL line makes the run print GATES-FAIL and blocks M0-EXIT.
- informational: the line prints INFO with its numbers;  it never fails the run at M0;  the row becomes binding at the milestone the verdict names.
- OPEN-printing: the gate passes or prints OPEN with a reason;  OPEN does not fail the run at M0;  part 12 records every OPEN on the decision sheet.

The status words follow verdict:118 ("PROVE-ONCE done or OPEN") and brief:541 OQ2 ("informational at M0 with rung 3 at most 2.0 and binding at M1 with a printed OPEN exit"), VERIFIED.  Command paths are relative to the repo root of part 3.  `attest` has the four verbs of 7.2 and the three flags of 7.3 only (verdict:140, VERIFIED).  A command below in another form is a dev/gates.sh leg that runs the 7.2 forms per row and prints the row line:  r0-diff is `zsh dev/r0-diff.sh`;  axioms is `attest check --axioms ROW`;  enc-xcheck, emu, host-roster, cycles, `--erase` and `attest build corpus/` run `attest build ROW -o OUT` and `attest run OUT`;  lower is `attest build ROW -o OUT` with a refusal exit expected;  `--count-passes` is `--passes`.  `cargo run -p attest-harness` names the binary harness/target/release/attest-harness that the user builds under the open floor (part 2;  `cargocho build -- --release -j 2 --manifest-path harness/Cargo.toml`);  no agent compiles it (section 11).

### Stage A rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| BUILD | `zsh -f dev/dunecho.sh build` | exit 0 with warnings as errors;  a failure ends the run before any other leg (brief:341 and tpl2:151, VERIFIED) | binding |
| CARRY | `zsh dev/carry-check.sh` | `CARRY files=N diff=0 unlisted=0` then `PIN eebe37e`;  every carried file equals `git show eebe37e:PATH` in the assay pin and dev/PIN reads eebe37e (brief:342 and tpl:200-201 for the form, VERIFIED;  the sha from 00-bindings OQ6, VERIFIED) | binding |
| R0-COUNT | `zsh dev/r0-count.sh` | `R0-COUNT formers=2 schema=N shapes=N admitted=N`;  SPEC.md prints two formers and every number is exact at the pin's count, any growth fails (brief:343 and tpl:198, VERIFIED) | binding |
| R0-AUDIT | `zsh dev/r0-audit.sh` | `R0-AUDIT ok`;  the term sum has no third former and every naming in SPEC.md carries its refusal citation (brief:344 and tpl:199, VERIFIED) | binding |
| R0-DIFF | `attest r0-diff` against the kanon tree at 2c2e6e6 | `R0-DIFF vs=2c2e6e6 rows=N diff=0`;  the R0 walk of the carried kernel agrees row for row with kanon 2c2e6e6 (verdict:96 and verdict:117, VERIFIED;  2c2e6e6 is the assay plan's own pin at tpl:200-201, VERIFIED) | binding |
| SUITE-KERNEL | `RUNS=7 zsh -f dev/bench.sh SUITE-KERNEL '_build/default/test/main.exe test'` | `SUITE-KERNEL pass=N fail=0 median_ms=M`;  the carried kernel suite runs green through the attest tree, timed (brief:345 and tpl2:156, VERIFIED;  the bench form from brief:543, VERIFIED) | binding on fail=0;  the median is a MEASURE row |
| AXIOMS | `attest axioms corpus/` | `AXIOMS rows=N axioms=`;  the printed axiom set is empty on every ACCEPT row (verdict:118, VERIFIED);  brief:350 names exactly `Quot.sound`, which is the M2 form at verdict:120, and the ratified milestone line wins (00-bindings, VERIFIED) | binding |
| TRUSTED-LINES | `zsh dev/trusted-lines.sh` | `TRUSTED-LINES kernel=N/4100 lower=N/1100 encoder=N/800 harness=N/100 OK` then `TRUSTED-LINES whole_lib=N/6193 INFO`;  the four OQ4 bounds bind from Stage A and the lower, encoder and harness rows print 0 until their stage (brief:541 OQ4, verdict:126 and 00-bindings, VERIFIED) | binding on the four rows;  the whole-lib row is informational |

### Stage B rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| TRACE-ERASURE | `zsh dev/gates.sh TRACE-ERASURE`, which runs `attest build --erase` on corpus/ and on the opaque twin corpus, then `cmp` per row | `TRACE-ERASURE rows=16 identical=16`;  the ELF built from a row with proof bodies is byte-identical to the ELF built from the same row with every proof replaced by an opaque postulate, both erased through the evaluator that never unfolds a quantity-0 global (brief:541 OQ7 and brief:348, VERIFIED);  16 rows at M0 (verdict:118, VERIFIED);  the seed is the two A1 F2 fixtures and the Acc fixture of part 9 | binding |
| LEAN-TWIN | `zsh dev/lean-twin.sh`, which runs `lake env lean lean/Corpus/ROW.lean` per row | `LEAN-TWIN accept=24/24 refuse=12/12`;  every ACCEPT row elaborates in Lean and in attest, every REFUSE row is refused by both at the same site (verdict:111 and verdict:118, VERIFIED);  a missing `lake` prints FAIL and never SKIP because verdict:118 binds the counts;  `lake` is on PATH today (VERIFIED by `command -v lake` on 2026-09-22) | binding |

### Stage C rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| ENC-XCHECK | `attest enc-xcheck corpus/ref/` | `ENC-XCHECK rows=14 objects=N mismatch=0`;  every instruction the lowering emits matches the 14-row reference encoding plus one rv64 reference object per W form, assembled once and pinned;  no C extension (verdict:107, VERIFIED);  `llvm-readelf` is absent today (VERIFIED by `command -v llvm-readelf` on 2026-09-22), so the reference objects wait on USER step 3 (brief:543, VERIFIED) | binding |
| ELF-ACCEPTED | `cargo run -p attest-harness -- execute corpus/ROW.elf` per row | `ELF-ACCEPTED rows=N exit0=N`;  the SP1 v6.1.0 executor loads every corpus ELF64 and halts with exit 0 (brief:346, VERIFIED), starting with the 96-byte HALT fixture (verdict:107 and dossier:253, VERIFIED);  pc_base is at least 32 and a multiple of 4 (dossier:101, VERIFIED) | binding |

### Stage D rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| EXEC-DIFF | `zsh dev/gates.sh EXEC-DIFF`, which runs the harness `execute` and `attest emu` per row | `EXEC-DIFF rows=16 pubval=16 cycles=16`;  executor and emulator agree on public values and cycle counts for every corpus program (brief:347, VERIFIED) on 16 rows (verdict:118, VERIFIED) | binding |
| HOST-ROSTER | `attest host-roster corpus/ROW.elf` | `HOST-ROSTER ecalls=N roster=3 unknown=0` at Stage D and `roster=6` at Stage E;  the gate scans the t0 immediate before every ecall (verdict:104, VERIFIED) and admits only the roster codes.  Halt = HALT 0x00000000 (dossier:44, VERIFIED).  Commit = WRITE 0x00000002 on fd 13, then 8 COMMIT 0x00000010 and 8 COMMIT_DEFERRED_PROOFS 0x0000001A (dossier:45, dossier:58-59 and dossier:102, VERIFIED).  Read = HINT_LEN then HINT_READ (dossier:103, VERIFIED;  their codes BELIEVED, settle: `rg -n -e HINT_LEN -e HINT_READ /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md`).  Keccak = KECCAK_PERMUTE 0x00010109 (dossier:52, VERIFIED).  Sha256 = SHA_COMPRESS 0x00010106 (dossier:49, VERIFIED) with SHA_EXTEND (code BELIEVED, settle: the dossier table).  U256Mul = UINT256_MUL 0x0001011D, the TOOL line `\| UINT256_MUL \| 0x0001011D \| 128 \| 108 \|` (dossier:64, VERIFIED;  brief:541 OQ5, VERIFIED) | binding |
| PUBVAL-DIGEST | `zsh dev/gates.sh PUBVAL-DIGEST` | `PUBVAL-DIGEST rows=N match=N`;  the bytes the guest writes to fd 13 hash by SHA-256 to the 8 COMMIT words, and the harness's public values equal the emulator's (dossier:88 and dossier:102, VERIFIED;  the executor-side digest check is BELIEVED there, settle: crates/core/executor/src/minimal/ecall.rs) | binding |

### Stage E rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| GUARD-TWIN | `zsh dev/gates.sh GUARD-TWIN` | `GUARD-TWIN calls=N twin_agree=N guard_insns=0`;  for every Keccak, Sha256 and U256Mul call in the corpus the emulator's software twin returns the words the executor's precompile returns, and the guard proof on the call erases to zero instructions (brief:541 OQ7 and verdict:117, VERIFIED;  the exact statement of the twin is BELIEVED, settle: verdict:65 and the section 4.6 text that OQ7 replaces) | binding |
| LOWER-REFUSE | `attest lower corpus/refuse/ROW` per row | `LOWER-REFUSE rows=12 refused=12`;  one site per REFUSE row, the lowering refuses Word32 without proof and the pure Host call, and prints the row's expected text (verdict:86, VERIFIED) | binding |

### Stage F rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| CYCLE-BUDGET | `attest cycles corpus/` | `CYCLE-BUDGET row=R cycles=N syscalls=M` per row, pinned in dev/cycles.json;  cycle counts printed and pinned, informational at M0 (brief:349, VERIFIED;  cycles and syscalls per verdict:23, VERIFIED);  binding at M1 (verdict:119, VERIFIED);  a drift against the pin prints `INFO drift` and no FAIL | informational |
| M0-TIME | `RUNS=5 zsh -f dev/bench.sh M0-TIME 'attest build corpus/'` | `M0-TIME median_ms=M bound_ms=B`;  the corpus compiles under a fixed wall-clock bound (brief:351, VERIFIED);  Stage F pins B in dev/denominators.json as the first median times 1.5 (the factor is BELIEVED, settle: the Stage F decision sheet of part 12) | binding from the pin onward |
| M0-RATIO | `zsh dev/ratio.sh` | rung 1 `M0-RATIO rung=1 pass=P ms=N` per pass, the numerator's per-pass split, printed from Stage A (verdict:77, VERIFIED);  rung 2 `M0-RATIO rung=2 denominator_ms=D sha=H`, the Bend 2 denominator plus its hash from USER step 7 (verdict:77, VERIFIED);  rung 3 `M0-RATIO rung=3 ratio=R bound=2.0`, WARN above 2.0 and never FAIL (brief:541 OQ2, VERIFIED);  the like-for-like row runs `bend check` on the matched corpus once `bend --help` is recorded into dev/bend-cli.txt and shows no compile subcommand (brief:541 OQ2, VERIFIED);  `bend` is absent today (VERIFIED by `command -v bend` on 2026-09-22 and brief:543), so rung 2, rung 3 and the like-for-like row print `M0-RATIO rung=N OPEN reason=bend-absent` until USER steps 2 and 7 close | informational;  rungs 1 to 3 |
| DENOMINATORS | `shasum -a 256 -c dev/DENOMINATORS.sha256` | the frozen dev/denominators.json matches its hash before any ratio prints (brief:354 and tpl:203, VERIFIED);  Stage F freezes the rows it has (corpus sha, kernel suite median, cycle pins, M0-TIME bound) with the Bend 2 row written as the word OPEN until USER step 7, and the sha moves with that step (brief:543, VERIFIED) | binding |
| PASSES | `attest build --count-passes corpus/` | `PASSES walks=5 reentries=N`;  the pipeline walks the term exactly five times and prints every re-entry (verdict:75 and verdict:112, VERIFIED) | binding on walks=5;  reentries is a MEASURE row |
| HASHCONS-BENCH | `RUNS=7 zsh -f dev/bench.sh HASHCONS` | `HASHCONS-BENCH fixtures=77 plain_ms=A hashconsed_ms=B`;  the hashconsing bench on the 77 fixtures picks the M1 lever, memoised conversion over hashconsed terms first on proof_free and runtime_ty (verdict:112, VERIFIED) | informational |
| PROVE-ONCE | `cargo run -p attest-harness -- prove corpus/ROW.elf` then `verify`, on the smallest row, once at M0-EXIT only | `PROVE-ONCE row=R proof_bytes=N verify=ok` or `PROVE-ONCE OPEN reason=TEXT`;  the resource guard prints OPEN when free disk is under the 30 GiB floor or the prover is absent (verdict:23 and brief:543, VERIFIED);  the row is the smallest corpus program (brief:355 and verdict:117, VERIFIED) | OPEN-printing |

### Deferred to M1

| gate | M1 form | M0 status |
| --- | --- | --- |
| PRELUDE-CHECKED | a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE), fail-closed at M2 on NAME_ONLY = 0 and UNMAPPED = 0 (brief:541 OQ3, VERIFIED);  M1 borrows the lean4export importer from the mech pin (00-bindings OQ3, VERIFIED);  the "count mode M0" words of verdict:111 are superseded by OQ3 and the ruling wins (00-bindings, VERIFIED) | not run at M0;  no line prints and the row is outside the M0 count |

### Count

24 M0 gates.  20 binding: BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS, TRUSTED-LINES, TRACE-ERASURE, LEAN-TWIN, ENC-XCHECK, ELF-ACCEPTED, EXEC-DIFF, HOST-ROSTER, PUBVAL-DIGEST, GUARD-TWIN, LOWER-REFUSE, M0-TIME, DENOMINATORS, PASSES.  3 informational: CYCLE-BUDGET, M0-RATIO, HASHCONS-BENCH.  1 OPEN-printing: PROVE-ONCE.  PRELUDE-CHECKED is deferred and not counted.  The M0 exit reads EXEC-DIFF and TRACE-ERASURE on 16 rows, LEAN-TWIN 24/24 and 12/12, AXIOMS empty and PROVE-ONCE done or OPEN (verdict:118, VERIFIED);  every other binding row must also print PASS because GATES-FAIL blocks the stamp of part 12.
## 9 Mutants

This part is section 9 of the assay M0 plan (tpl:205-214) rewritten for attest.  One row per mutant in dev/MUTATION-LOG.md, each with the stage, the mutation, the gate that must catch it and the expected failure text (tpl:207, VERIFIED for the form).  A mutant is a one-site edit on a scratch copy of the tree;  the gate runs on the copy, the log records the printed FAIL line, and the copy is discarded.  A gate whose mutant does not fail is vacuous and blocks its stage (tpl:181, VERIFIED).  The erasure rule of the assay plan carries over: an erasure mutant changes the SHAPE of a proof term or the evaluator, never a second proof of a one-constructor family (tpl:195, VERIFIED).  Every expected failure text is the printed line of part 8 with the failing numbers;  the exact spelling settles when dev/gates.sh exists at Stage A (BELIEVED until then, settle: run the mutant on the Stage A tree).  N stands for the count the pinned run prints.

### Stage A

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| PIN | change one character of dev/PIN | CARRY | `PIN eebe37f FAIL expected=eebe37e` (tpl:209, VERIFIED for the form;  the assay pin's own dev/PIN reads 2c2e6e6, VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin show HEAD:dev/PIN` on 2026-09-22, so attest's dev/PIN carries eebe37e and its CARRIED.md names 2c2e6e6 as the kanon inside it) |
| CARRY | edit one carried line outside the one edit CARRIED.md lists | CARRY | `CARRY files=N diff=1 unlisted=0 FAIL path=PATH` (tpl:209, VERIFIED for the form) |
| BUILD | add one unused binding to a carried module | BUILD | the dune error text with `Error (warning 26 [unused-var])`, then the run stops (tpl2:151, VERIFIED for the stop rule) |
| SUITE-KERNEL | flip the expected verdict of one carried kernel test | SUITE-KERNEL | `SUITE-KERNEL pass=N-1 fail=1 median_ms=M FAIL` (brief:345) |
| R0 smuggling, former | add a third constructor to the term sum, a KHost former that carries an effect as a term, and route it through the checker | R0-COUNT | `R0-COUNT formers=3 expected=2 FAIL` (brief:343 and tpl:198, VERIFIED for the rule) |
| R0 smuggling, shape | keep two formers and add the effect as a new shape name inside the rules dispatch with no line in SPEC.md | R0-AUDIT | `R0-AUDIT FAIL name=KHost site=PATH:LINE citation=none` (brief:344 and tpl:199, VERIFIED for the rule) |
| R0 walk order | swap two children in the R0 walk | R0-DIFF | `R0-DIFF vs=2c2e6e6 rows=N diff=1 FAIL row=R` (verdict:96) |
| axiom | add `axiom smuggled : False` to one ACCEPT row | AXIOMS | `AXIOMS rows=N axioms=smuggled FAIL row=R` (verdict:118) |
| kernel growth | append 200 non-blank lines to the kernel | TRUSTED-LINES | `TRUSTED-LINES kernel=N+200/4100 FAIL` with N+200 above 4,100 (brief:541 OQ4) |

### Stage B: the F2 seed and the Acc fixture

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| F2 seed, evaluator | delete the quantity guard at its one site so the evaluator unfolds a quantity-0 global | TRACE-ERASURE | `TRACE-ERASURE rows=16 identical=14 FAIL row=f2-a first_diff=OFFSET` on the two A1 F2 fixtures of USER step 8 (parts/01-scope.md:17 and parts/03-layout.md:33, VERIFIED by rg on 2026-09-22, both citing verdict:136) |
| F2 seed, shape | replace the proof body of fixture f2-a by a proof of a different shape, an extra case split, and keep the guard | TRACE-ERASURE | no FAIL, `TRACE-ERASURE rows=16 identical=16`;  this control row proves the ELF does not move when only the proof shape moves (tpl:195, VERIFIED for the rule);  a FAIL here is a Stage B defect, not a caught mutant |
| Acc fixture, evaluator | mark Acc.rec as quantity 1 in the mutant evaluator so it unfolds the accessibility proof of a well-founded recursion | TRACE-ERASURE | `TRACE-ERASURE rows=16 identical=15 FAIL row=acc unfolded=Acc.rec`, or `TRACE-ERASURE row=acc WATCHDOG FAIL` when the opaque twin has no body to unfold and the mutant evaluator stalls (tpl2:149 for the watchdog, VERIFIED) |
| Acc fixture, twin | move the Acc row from corpus/accept/ to corpus/refuse/ with no other change | LEAN-TWIN | `LEAN-TWIN accept=23/24 refuse=12/13 FAIL row=acc lean=accepted attest=accepted` (verdict:111) |
| LEAN-TWIN | move one REFUSE row into corpus/accept/ with no other change | LEAN-TWIN | `LEAN-TWIN accept=24/25 refuse=11/12 FAIL row=R lean=refused attest=refused` (verdict:118) |

### Stage C: the encoder mutants

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| funct3 | set bit 12 in the `addi` encoder | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=addi ours=0x00001513 ref=0x00000513` (the reference word is `13 05 00 00` at dossier:253, VERIFIED) |
| immediate field | place the I-type immediate at bit 19 instead of bit 20 | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=addi-neg ours=HEX ref=0xfff50513` (the reference is `addi a0, x0, -1`, BELIEVED for the hex, settle: the 14-row reference of verdict:107) |
| register fields | swap rs1 and rs2 in the R-type encoder | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=add ours=HEX ref=HEX` (verdict:107) |
| compressed | emit a 16-bit `c.addi` for a small immediate | ENC-XCHECK | `ENC-XCHECK FAIL insn=c.addi width=16 allowed=32` (no C extension, verdict:107, VERIFIED) |
| W form object | drop the `addiw` reference object | ENC-XCHECK | `ENC-XCHECK rows=14 objects=N-1 FAIL missing=addiw` (one rv64 object per W form, verdict:107, VERIFIED) |
| entry alignment | set e_entry to 0x78000002 | ELF-ACCEPTED | `ELF-ACCEPTED rows=N exit0=N-1 FAIL row=halt96 error=TEXT`;  the executor rejects a pc_base that is not a multiple of 4 (dossier:101, VERIFIED;  the executor's text is BELIEVED, settle: run the mutant through the harness) |
| halt code | lower Halt with a0 = 1 | ELF-ACCEPTED | `ELF-ACCEPTED rows=N exit0=N-1 FAIL row=halt96 exit=1` (brief:346) |

### Stage D and Stage E: the host-roster mutants

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| roster D | lower Keccak at Stage D, t0 = 0x00010109 before an ecall | HOST-ROSTER | `HOST-ROSTER ecalls=N roster=3 unknown=1 FAIL t0=0x00010109` (KECCAK_PERMUTE at dossier:52, VERIFIED) |
| roster E | lower U256Mul with t0 = 0x00010131, UINT256_MUL_CARRY, instead of 0x0001011D | HOST-ROSTER | `HOST-ROSTER ecalls=N roster=6 unknown=1 FAIL t0=0x00010131` (dossier:84 and dossier:64, VERIFIED) |
| roster name | add Bn254 as a seventh Host constructor | HOST-ROSTER | `HOST-ROSTER roster=7 expected=6 FAIL` (00-bindings OQ5: no M0 file names Bn254 or Secp256k1, VERIFIED) |
| fd | write the public values to fd 12 | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R fd=12 expected=13` (FD_PUBLIC_VALUES = 13 at dossier:88, VERIFIED) |
| commit count | emit 7 COMMIT ecalls | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R commits=7 expected=8` (dossier:102, VERIFIED) |
| digest | commit the SHA-256 words in big-endian order | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R word=0` (the entrypoint commits 32-bit words, dossier:102, VERIFIED;  the byte order is BELIEVED, settle: halt.rs:20-60) |
| cycles | insert one `nop` in the emulator's Halt path only | EXEC-DIFF | `EXEC-DIFF rows=16 pubval=16 cycles=15 FAIL row=R exec=N emu=N+1` (brief:347) |
| twin | make the U256Mul software twin return the low 128 bits | GUARD-TWIN | `GUARD-TWIN calls=N twin_agree=N-1 FAIL call=u256mul row=R` (brief:541 OQ7) |
| guard | let the lowering emit a runtime bounds check for a guard that carries a proof | GUARD-TWIN | `GUARD-TWIN calls=N twin_agree=N guard_insns=3 FAIL row=R` (brief:541 OQ7) |
| refuse | delete the Word32 proof check in the lowering | LOWER-REFUSE | `LOWER-REFUSE rows=12 refused=11 FAIL row=word32-no-proof accepted` (verdict:86) |
| pure host | let a Host call type as a pure term | LOWER-REFUSE | `LOWER-REFUSE rows=12 refused=11 FAIL row=pure-host accepted` (verdict:86) |

### Stage F

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| denominators | edit one byte of dev/denominators.json after the freeze | DENOMINATORS | `dev/denominators.json: FAILED` from shasum, then `DENOMINATORS FAIL` (tpl:214, VERIFIED for the form) |
| passes | add a sixth walk | PASSES | `PASSES walks=6 reentries=N FAIL expected=5` (verdict:75) |
| cycle pin | edit one pinned count in dev/cycles.json | CYCLE-BUDGET | `CYCLE-BUDGET row=R cycles=N pinned=N+1 INFO drift` and no FAIL at M0;  the same mutant prints FAIL at M1 (verdict:119) |
| time bound | halve bound_ms in dev/denominators.json and refreeze the sha | M0-TIME | `M0-TIME median_ms=M bound_ms=B/2 FAIL` (brief:351) |
| missing line | delete the M0-RATIO rung 1 print from dev/ratio.sh | the run itself | `GATES-FAIL missing=M0-RATIO` (part 8, the missing-line rule) |

### Count

37 rows: 9 at Stage A, 5 at Stage B, 7 at Stage C, 11 at Stage D and E, 5 at Stage F.  36 must print FAIL and one control row (F2 seed, shape) must not.  Every binding gate of part 8 has at least one row here;  the informational gates CYCLE-BUDGET and M0-RATIO carry a print-shape row each, and HASHCONS-BENCH and PROVE-ONCE carry none because an OPEN or INFO line is their pass form (part 8, the three statuses).  The R0 smuggling pair is the row the ratified pins protect: two formers at R0 (brief:343-344, VERIFIED) and no third former by name or by shape.
## 10 Stages and the build workflow shape

Six stages after Stage 0, A to F, in dependency order (verdict:117, VERIFIED).  Each stage is one Workflow run that opens on the user's "use a workflow" opt-in (brief:541 tail, VERIFIED;  the per-stage opt-in is a plan decision by delta from tpl2:177, BELIEVED until the user rules a standing opt-in as at tpl:288).  Every agent prompt in every stage carries the string "(7 findings max, 56 agents max)" (tpl:218 and brief:371, VERIFIED).  Each stage has builders that write code in chunks of at most 8 KB per tool call, a verifier that runs the stage gates and the stage mutants and returns at most 7 findings, one fix round, and a review-kit close that ends in a printed commit command (tpl2:177, VERIFIED as the house shape).  No agent commits at any stage;  the user commits after every stage (tpl:218 and brief:368-369, VERIFIED).

### Tiers

Builder units run on Fable at xhigh effort.  Verifier units run on Fable at max effort.  Closer units run on Opus at medium effort.  Finder units of the review kit run at the builder tier.  The tiers are the caller's roster for this workflow (the task text of this plan's writers, VERIFIED as that text);  each stage brief repeats them in its roster.

### Handoff files

Every unit writes its handoff file as its FIRST tool call, three lines: goal, inputs, output paths.  The unit appends one progress line after every file write, so a cut-off unit leaves a trail.  The handoff directory is /Users/oobi/Documents/attest-m0/handoff/stage-X/ with one file per unit, UNIT.md (plan decision by delta from this plan's own /Users/oobi/Documents/kan-sp1-lang-m0-handoff/, BELIEVED until the Stage A brief pins it).  A unit whose prompt starts with a RETRY marker reads its handoff file and the files it names first and continues;  it does not restart.

### Dead-unit rule

A null builder or verifier, a unit that returns no result, retries ONCE on opus with a RETRY marker in its prompt;  a second null halts the stage, and the stage reports both request ids.  A null finder or closer is reported as unmet;  the stage does not retry it and the close prints UNMET on that row.  The rule is the caller's, quoted from the task text of this plan's writers (VERIFIED as that text).

### Review-kit close

The close of each stage is a review kit over the staged tree: finders return at most 7 findings each, one fix round applies them, a verify-final reruns every gate leg of the stage on the staged tree and refuses any finding still open, then the closer writes the dated entry in dev/M0-BUILD-LOG.md, the mutation rows in dev/MUTATION-LOG.md, stages the tree and prints one commit command of this form and stops (tpl:229-233 and tpl2:177, VERIFIED as the two forms;  the attest paths are this plan's).

```
git -C /Users/oobi/Documents/attest commit -s -F /Users/oobi/Documents/attest-m0/stage-A-commit-msg.txt
```

Stage F opens only after A to E are committed by the user (tpl:229, VERIFIED as the assay rule;  the attest form is a plan decision).

### Stages A to F

Each stage below names its units with one-line briefs, its gate ids from verdict:117 (VERIFIED) and what it waits on (part 2).  The unit split is a plan decision (BELIEVED until each stage brief pins it).  Every unit name is STAGE plus a number;  the verifier, the fixer and the close are the last three units of every stage.

Stage A, carry.  Units: A1 builder, clone lib/, surface/ and test/ verbatim from the assay pin eebe37e into /Users/oobi/Documents/attest and write CARRIED.md, dev/PIN, dev/TOOLCHAIN.md (the eight USER steps of part 2 with their status;  every review-kit close refreshes the status column), dune-project, LICENSE-MIT, LICENSE-APACHE, README.md and SPEC.md with the R0 block marked inherited;  A2 builder, copy dev/dunecho.sh from the mech pin with MECH_OPAM_SWITCH renamed to ATTEST_OPAM_SWITCH (the assay dev/dune.sh differs from it, VERIFIED by `diff` on 2026-09-22;  A2 rewrites every `dev/dune.sh` call inside the carried scripts to `dev/dunecho.sh`) and dev/gates.sh, carry-check.sh, r0-count.sh, r0-audit.sh, trusted-lines.sh, house.sh and bench.sh from the assay pin, write dev/r0-diff.sh, and make TRUSTED-LINES print the four OQ4 rows;  A3 verifier, run BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS-empty and TRUSTED-LINES rung 1 and the Stage A mutants of section 9;  A4 fixer, one round;  A5 review-kit close.  Gate ids: BUILD CARRY R0-COUNT R0-AUDIT R0-DIFF SUITE-KERNEL AXIOMS-empty TRUSTED-LINES rung 1.  Waits on no open USER step (part 2).  Commit message: /Users/oobi/Documents/attest-m0/stage-A-commit-msg.txt.

Stage B, erase.  Units: B1 builder, erase/ with the opaque-proof evaluator that never unfolds a quantity-0 global (brief:541 OQ7, VERIFIED);  B2 builder, fixtures/ with the two A1 F2 fixtures of USER step 8 and the Acc fixture, and twin/ with the Lean twin sources;  B3 builder, the TRACE-ERASURE and LEAN-TWIN legs in dev/gates.sh;  B4 verifier, TRACE-ERASURE in its Stage B term form and LEAN-TWIN 24/24 12/12 and the Stage B mutants (the Stage B leg prints the erased term of each fixtures/ row twice, with proof bodies and with opaque postulates, and runs `cmp` per row, rows = the fixtures/ count, because lower/ and elf/ land at Stage C;  the ELF form of the part 8 row and of OQ7 binds from Stage C onward, when elf/ exists, and reruns at Stages E and F);  B5 fixer;  B6 review-kit close.  Gate ids: TRACE-ERASURE LEAN-TWIN.  Waits on USER step 8 for the green TRACE-ERASURE row (part 2, verdict:136).  Commit message: stage-B-commit-msg.txt beside the Stage A one.

Stage C, lower and encode.  Units: C1 builder, lower/ from the erased term to RV64IM at most 1,100 lines (brief:541 OQ1 and OQ4, VERIFIED);  C2 builder, elf/ the ELF64 encoder at most 800 lines, with no LLVM, no rustc, no external assembler and no linker (brief:94-98, VERIFIED);  C3 builder, harness/ the execute-only Rust harness on sp1-sdk 6.1.0 at most 100 lines under the Rust rules of section 11, pulled forward from Stage D because ELF-ACCEPTED runs the SP1 executor through it (D3 extends it for EXEC-DIFF and PROVE-ONCE), then the ENC-XCHECK and ELF-ACCEPTED legs;  C4 verifier, ELF-ACCEPTED on a halt-only ELF64 through the SP1 v6.1.0 executor and ENC-XCHECK on every emitted instruction and the Stage C mutants;  C5 fixer;  C6 review-kit close.  Gate ids: ENC-XCHECK ELF-ACCEPTED.  Starts without any open step;  ENC-XCHECK waits on USER step 3, and ELF-ACCEPTED waits on USER step 6 and on the harness build the user runs under the open floor (part 2).

Stage D, emulator and harness.  Units: D1 builder, emu/ the OCaml RV64IM emulator twin (brief:541 OQ1, VERIFIED);  D2 builder, host/ with Read, Commit and Halt and the SHA-256 commit path of Halt (brief:541 OQ5 and verdict:151, VERIFIED);  D3 builder, extends harness/ for the EXEC-DIFF and PROVE-ONCE modes, still at most 100 lines under the Rust rules of section 11 (C3 wrote it at Stage C);  D4 builder, the EXEC-DIFF, HOST-ROSTER and PUBVAL-DIGEST legs;  D5 verifier, EXEC-DIFF row for row on every corpus row present, HOST-ROSTER, PUBVAL-DIGEST and the Stage D mutants;  D6 fixer;  D7 review-kit close.  Gate ids: EXEC-DIFF HOST-ROSTER PUBVAL-DIGEST.  Starts after Stage C;  the `cargo fetch` of sp1-sdk 6.1.0 is USER step 6 (brief:543, VERIFIED).

Stage E, effects.  Units: E1 builder, Keccak, Sha256 and U256Mul as Host constructors, U256Mul at syscall 0x0001011D, and their software twins in emu/ (brief:541 OQ5, VERIFIED);  E2 builder, the GUARD-TWIN and LOWER-REFUSE legs;  E3 verifier, GUARD-TWIN and LOWER-REFUSE green with EXEC-DIFF and TRACE-ERASURE still green over the six-constructor roster and the Stage E mutants;  E4 fixer;  E5 review-kit close.  Gate ids: GUARD-TWIN LOWER-REFUSE.  Waits on Stage D and on no open step (part 2).  Bn254 and Secp256k1 stay out until M2 (brief:541 OQ5, VERIFIED).

Stage F, freeze.  Units: F1 builder, corpus/ frozen at 16 EXEC-DIFF rows with CYCLE-BUDGET pinned per program;  F2 builder, dev/denominator.sh, dev/denominators.json and DENOMINATORS.sha256 frozen at Stage F over the rows it has, with the Bend 2 row written as the word OPEN until USER step 7 (plan:450), M0-TIME, rung 2 and rung 3 at most 2.0 informational, PASSES and the hashconsing bench;  F3 builder, PROVE-ONCE on the smallest row, done or OPEN;  F4 verifier, the whole battery of section 8 and every mutant of section 9 (an informational row passes its mutant on its expected INFO line);  F5 fixer;  F6 review-kit close, which also writes the MEASURE table of dev/M0-BUILD-LOG.md.  Gate ids: CYCLE-BUDGET M0-TIME M0-RATIO DENOMINATORS PASSES HASHCONS-BENCH PROVE-ONCE and the M0 gate of verdict:118.  Starts after Stage E;  M0-RATIO and rung 3 print and do not gate (brief:541 OQ2, VERIFIED);  CYCLE-BUDGET and HASHCONS-BENCH print and do not gate (plan:447 and plan:452, VERIFIED);  DENOMINATORS binds on the hash match and prints PASS while `bend` is not on PATH, because the Bend 2 row inside dev/denominators.json is the word OPEN until USER step 7 (brief:543, VERIFIED);  'prints OPEN' in parts 2, 3 and 12 names that inner row.

Order: A, B, C, D, E, F in sequence, each on the user's opt-in.  Each brief quotes this plan's section numbers and the verdict's lines, and every builder reads the assay pin for the seam it carries (tpl2:186, VERIFIED as the form).  If USER step 5 prints a mechanism-lang median under 211 ms before Stage A closes, Stage A reopens as a re-carry from the mech pin 1e4f371 (brief:541 OQ6, VERIFIED;  the re-carry rule is BELIEVED until the median prints).
## 11 House rules

House rules for every file an agent writes at M0, by delta from tpl:235-247 and tpl2:188-195 with the brief's section 5 (brief:357-377, VERIFIED).  dev/house.sh checks the OCaml rules and the verifier of every stage scans for each banned form with rg;  a hit is a finding (tpl2:190, VERIFIED as the form;  the attest script is a Stage A deliverable, part 3).

### OCaml

- Every dune verb runs through dev/dunecho.sh, as `zsh -f dev/dunecho.sh build` and `zsh -f dev/dunecho.sh test` (part 3, tpl2:190 and brief:373-374, VERIFIED).  No agent calls raw dune.
- No exceptions.  No `raise`, no `failwith`, no `assert`.  Every partial step returns a `result` (tpl:239 and brief:359, VERIFIED).
- Total combinators only for indexing and division.  No `List.nth`, no `arr.(i)`, no bare `/` or `mod` (tpl:240 and brief:361, VERIFIED).
- Option and Result through combinators, never a `match` on them (brief:359-360, VERIFIED).
- Exhaustive matches.  No `_` arm, so a new constructor of the term sum or of Host is a compile error in every pass (tpl:241, VERIFIED).
- No `match` on a bool.  Write if and else (tpl:242, VERIFIED).
- `match ()` with guards over an else-if chain of three or more (brief:362, VERIFIED).
- Fold and map, never a loop keyword, and no mutation of vectors (tpl:243 and brief:361-362, VERIFIED).

### Rust, the harness only

The harness under harness/ is the one Rust artifact at M0 (part 3).  Newtypes and sum types, no `unwrap`, `expect`, `panic` or `unsafe`, hand-rolled `Error` enums, MIT OR Apache-2.0 (brief:363-365, VERIFIED).  Every cargo verb runs through cargocho, OOM-safe at `-j 2` and one crate at a time (brief:373-374, VERIFIED), and only when the disk floor allows a build (brief:375-376 and brief:543, VERIFIED);  the Stage D brief records the `cargo fetch` of USER step 6 as the user's step.

### Lean, the twin

The Lean twin under twin/ uses kan-tactics only, no exceptions, and is a reusable lakefile dependency;  every lake verb runs through leancho (brief:366-367 and tpl2:190, VERIFIED).

### Drivers and pins

- kanoncho over raw kanon (brief:373-374, VERIFIED).  At M0 the carried kernel suite runs through the dune wrapper, and no agent calls a raw kanon or attest binary outside dev/gates.sh (plan decision, BELIEVED until the Stage A brief pins it).
- Pin a commit, never a tree.  Every probe of assay or mechanism-lang reads the detached worktree at /Users/oobi/Documents/kan-sp1-lang-assay-pin (eebe37e) or /Users/oobi/Documents/kan-sp1-lang-mech-pin (1e4f371, veil at a7534ce), never a main tree (brief:372 and part 3, VERIFIED).  No unit builds in a pin and no unit runs a git command that writes there.
- Never install a tool, never call brew, sp1up, cabal, rustup, cargo install or opam install, never start a daemon;  those are USER Stage 0 steps that the plan records (tpl:247 and brief:543, VERIFIED).

### Git

Never commit and never push, in any tree.  Every closer stages the tree and prints the commit command with `git commit -s` for DCO;  the user runs it (brief:368-369 and tpl:218, VERIFIED).

### Prose

- ASD-STE100 for repo-facing text: short declarative sentences, one instruction per sentence, active voice, two spaces after each sentence period and after each semicolon (tpl:247 and brief:370, VERIFIED).
- No em dashes and no en dashes, in files, in prompts and in return text;  ASCII only (brief:370, VERIFIED).
- No AI prose tells (brief:370, VERIFIED).
- An unstamped field reads "to be stamped at M0 exit";  no other placeholder word appears in a plan, a part or a report (the task text of this plan's writers, VERIFIED as that text).

### Caps and gates

- Every agent prompt carries "(7 findings max, 56 agents max)" (brief:371, VERIFIED).
- Every gate has a non-vacuity mutant in section 9 (tpl:247, VERIFIED as the form).
- Denominators are frozen as hashed artifacts before any ratio binds (tpl:247 and brief:87-93, VERIFIED);  at M0 no ratio binds (brief:541 OQ2, VERIFIED).
## 12 M0-EXIT stamp, decisions, corrections

M0-EXIT criteria, by delta from tpl:251 (VERIFIED as the assay form): Stage 0 USER steps 1 to 8 recorded in dev/TOOLCHAIN.md, with the DENOMINATORS row green or printed OPEN (brief:541 OQ2 and brief:543, VERIFIED);  Stages A to F committed by the user with the printed lines;  every leg of section 8 green or printed as declared on the committed tree;  the M0 gate of verdict:118 green, EXEC-DIFF and TRACE-ERASURE on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN (VERIFIED);  TRUSTED-LINES kernel at most 4,100, lower at most 1,100, encoder at most 800, harness at most 100 (brief:541 OQ4, VERIFIED);  dev/M0-BUILD-LOG.md holds the MEASURE table with the M0-TIME, CYCLE-BUDGET, M0-RATIO and rung 3 rows;  dev/MUTATION-LOG.md holds every row of section 9 with its caught leg;  the seven rulings below stand.

### M0-EXIT stamp

The user writes the stamp;  nothing else counts (tpl:253, VERIFIED as the form).  Every field below reads "to be stamped at M0 exit" until then.

| field | value |
| --- | --- |
| date | to be stamped at M0 exit |
| ratified by | to be stamped at M0 exit |
| Stage F commit | to be stamped at M0 exit |
| EXEC-DIFF rows green | to be stamped at M0 exit |
| TRACE-ERASURE rows green | to be stamped at M0 exit |
| LEAN-TWIN | to be stamped at M0 exit |
| AXIOMS | to be stamped at M0 exit |
| PROVE-ONCE | to be stamped at M0 exit |
| TRUSTED-LINES kernel, lower, encoder, harness | to be stamped at M0 exit |
| M0-RATIO and rung 3, informational | to be stamped at M0 exit |
| DENOMINATORS | to be stamped at M0 exit |

### Decision sheet

Each row is one ruling of the user on 2026-09-22, "ratify all" on OQ1 to OQ7 (brief:541 and verdict:155, VERIFIED).  No row reopens a ratification;  where a ruling and an older section disagree, the ruling wins (brief:541, VERIFIED).  The ruling text is quoted in one line from brief:541.

| id | ruled | ruling | replaces |
| --- | --- | --- | --- |
| OQ1 | 2026-09-22 | the target is RV64IM and ELF64 for the installed SP1 v6.1.0 executor, with an RV64IM emulator twin | Q1 and Q2 |
| OQ2 | 2026-09-22 | M0-RATIO is informational at M0 with rung 3 at most 2.0 and binding at M1 with a printed OPEN exit;  `bend check` is the like-for-like row when `bend --help` shows no compile subcommand | Q6 |
| OQ3 | 2026-09-22 | PRELUDE-CHECKED is a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE) and fails closed at M2 on NAME_ONLY = 0 and UNMAPPED = 0 | Q5 |
| OQ4 | 2026-09-22 | TRUSTED-LINES kernel bound 4,100 at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100 | the brief's 3,000 |
| OQ5 | 2026-09-22 | Host at M0 is Read, Commit and Halt at Stage D and Keccak, Sha256 and U256Mul at Stage E;  Bn254 and Secp256k1 at M2;  UINT256_MUL 0x0001011D | Q4, narrowed |
| OQ6 | 2026-09-22 | the kernel base is assay;  the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms | Q0 |
| OQ7 | 2026-09-22 | TRACE-ERASURE compares an ELF with proof bodies against one with the same proofs replaced by opaque postulates, both erased through the evaluator that never unfolds a quantity-0 global, plus GUARD-TWIN | the text of brief section 4.6 |

Recorded, not a ruling (by delta from tpl:277, VERIFIED as the form).  Every name in this list is a convention of this plan and not a fact from a source, and a stage brief may rename any of them without a new ruling: the directories erase/, lower/, elf/, emu/, host/, harness/, fixtures/ and twin/ (part 3);  the files bin/attest.ml, dev/r0-diff.sh, dev/bend-cli.txt, dev/TOOLCHAIN.md, dev/M0-BUILD-LOG.md and dev/MUTATION-LOG.md;  the unit split of section 10 and the handoff directory /Users/oobi/Documents/attest-m0/handoff/;  the commit message path /Users/oobi/Documents/attest-m0/stage-A-commit-msg.txt.  The gate ids BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS, TRUSTED-LINES, TRACE-ERASURE, LEAN-TWIN, ENC-XCHECK, ELF-ACCEPTED, EXEC-DIFF, HOST-ROSTER, PUBVAL-DIGEST, GUARD-TWIN, LOWER-REFUSE, CYCLE-BUDGET, M0-TIME, DENOMINATORS, PASSES and PROVE-ONCE come from verdict:117-118 and are not conventions of this plan (VERIFIED).

### Corrections

C-1 (2026-09-22) K2-1 K3-2: 10 Stages A to F, Stage C: C3 also writes harness/ (pulled forward from Stage D);  ELF-ACCEPTED waits on USER step 6 and on the harness build the user runs.
C-2 (2026-09-22) K3-1: 10 Stages A to F, Stage B: B4 runs TRACE-ERASURE in its Stage B term form on the fixtures/ rows;  the ELF form binds from Stage C onward.
C-3 (2026-09-22) K1-1 K3-4 K3-3: 8 Gates against 7 Driver and 11 House rules: every gate command maps to the four 7.2 verbs and the three 7.3 flags;  `cargo run -p attest-harness` names the binary the user builds.
C-4 (2026-09-22) K1-2 K2-3 K2-6 K2-5: 10 Stages A to F, Stage F: the gate ids add M0-RATIO and HASHCONS-BENCH as printed rows;  DENOMINATORS binds on the hash match with the inner Bend 2 row OPEN;  an informational row passes its mutant on the INFO line.
C-5 (2026-09-22) K2-2: 4.3 The TRUSTED-LINES arithmetic: the ARTIFACTS folder names are elf and harness;  an absent folder prints FAIL from its 4.2 stage onward.
C-6 (2026-09-22) K2-4: 5.2 The M0 constructs: the Stage E gate is HOST-ROSTER with the `--externs` leg;  EXTERN-ROSTER is the disclosure row of part 4 and not a gate id.
C-7 (2026-09-22) K3-5 K3-6: 10 Stages A to F, Stage A units: A1 also writes dev/TOOLCHAIN.md;  A2 renames MECH_OPAM_SWITCH to ATTEST_OPAM_SWITCH and rewrites every dev/dune.sh call to dev/dunecho.sh.
R2-1 (2026-09-22, round 2) K1-4: plan:71, plan:87 and plan:679 now read that `diskfree --apply` RAN on 2026-09-22 and reclaimed 0K, so the 30 GiB floor stays OPEN at 21 GiB free;  no line of the plan calls the floor closed (brief:543, VERIFIED).
R2-2 (2026-09-22, round 2) K1-5: the section 7 form `R0-COUNT formers=<n> shapes=<n>` at plan:362 is the one binding output form;  plan:239 and plan:243 now cite it and keep their own text as the SPEC.md block and the gate status word (VERIFIED on the plan).
R2-3 (2026-09-22, round 2) C1 rider: the harness is a Stage C artifact at plan:126, plan:152 and plan:569, where D3 only extends it for EXEC-DIFF and PROVE-ONCE;  plan:93 adds the wait on the harness build the user runs under the open floor (plan:567, VERIFIED).
R2-4 (2026-09-22, round 2) C4 rider: plan:202 and plan:96 make DENOMINATORS binding at M0 on the hash match with the inner Bend 2 row OPEN until USER step 7;  the F2 clause of plan:573 freezes the rows it has, and its informational citation splits to brief:541 OQ2 for M0-RATIO and rung 3 and to plan:447 and plan:452 for CYCLE-BUDGET and HASHCONS-BENCH (VERIFIED).
R2-5 (2026-09-22, round 2) C5 rider: plan:187 points at the stage column of section 4.1, not 4.2, and the crate name is attest-harness at plan:152, plan:315, plan:368 and plan:388 (VERIFIED, 0 hits of the old name).
R2-6 (2026-09-22, round 2) C7 rider: plan:104 now reads that the two wrappers differ, VERIFIED by `diff` on 2026-09-22 (`2,30c2,8`), and that A2 carries the mech dev/dunecho.sh and rewrites every dev/dune.sh call in the carried scripts (plan:563).
## 13 What happens next

By delta from tpl:279-288 and tpl2:218-223 (VERIFIED as the two forms).

1.  RULED 2026-09-22: OQ1 to OQ7 stand as ratified (brief:541 and verdict:155, VERIFIED).  The decision sheet of section 12 records them;  no stage reopens one.
2.  Stage 0 is the user's list.  The checkout half of step 5 and the probe of step 2 are done;  step 1 RAN and reclaimed 0K, so the 30 GiB floor stays OPEN at 21 GiB free (brief:543, VERIFIED);  open in the verdict's numbering are step 2 (Bend 2 and dev/bend-cli.txt), step 3 (the hello guests and `llvm-readelf -h`), step 4 (an optional spike), the second half of step 5 (the mechanism-lang median), step 6 (the `cargo fetch` of sp1-sdk 6.1.0), step 7 (the denominator freeze) and step 8 (the two A1 F2 fixtures) (brief:543, VERIFIED).  Part 2 names which stage waits on which step.
3.  Stage A opens as one Workflow run on the user's "use a workflow" opt-in, with "(7 findings max, 56 agents max)" on every agent prompt;  it waits on no open step (part 2 and brief:541 tail, VERIFIED).
4.  Stages B to F follow, each as its own Workflow run in the shape of section 10, each ending with a commit command the user runs.  No agent commits.
5.  The assay pin, the mech pin and the trees /Users/oobi/Documents/assay, /Users/oobi/Documents/mechanism-lang, /Users/oobi/Documents/veil and /Users/oobi/Documents/kanon stay read only for the whole of M0 (section 11).
6.  If USER step 5 prints a mechanism-lang median under 211 ms, Stage A reopens as a re-carry from the mech pin 1e4f371 (brief:541 OQ6, VERIFIED;  the re-carry rule is BELIEVED until the median prints).
7.  After Stage F the user stamps M0-EXIT in section 12 and the M1 plan opens on a new opt-in.

### M1 preview

M1 lands rung 4 at most 1.0 binding, with an OPEN exit allowed and printed (verdict:119 and brief:541 OQ2, VERIFIED);  CYCLE-BUDGET binding (verdict:119, VERIFIED);  the overlay merged with one level-polymorphic row, about 480 lines under either base (verdict:119 and verdict:152, VERIFIED);  PRELUDE-CHECKED in check mode as the ratchet, NEVER named and at least 40 percent NAME_AND_TYPE, with the lean4export importer borrowed from the mech pin (verdict:119 and brief:541 OQ3, VERIFIED);  the kernel at most 4,400 lines (brief:541 OQ4, VERIFIED);  8 more corpus rows (verdict:119, VERIFIED).  Memoised conversion stays at M1 (verdict:148, VERIFIED).  M0-RATIO binds from M1 with the printed OPEN exit, and `bend check` is the like-for-like row while `bend --help` shows no compile subcommand (brief:541 OQ2, VERIFIED).

### M2 and M3

M2: SPar admitted, AXIOMS exactly Quot.sound, 48 rows, fail-closed PRELUDE-CHECKED on NAME_ONLY = 0 and UNMAPPED = 0, the full Host roster with Bn254 and Secp256k1 against software twins in cycles, rung 5 (verdict:120, brief:541 OQ3 and OQ5, VERIFIED).

M3: SNu admitted with the EXTRA corpus, a proved encoder (the riscv-coq decode_encode port, S3 finding 5, BELIEVED) replaces ENC-XCHECK, PROVE-ONCE on the largest row (verdict:121, VERIFIED as the verdict's text).
