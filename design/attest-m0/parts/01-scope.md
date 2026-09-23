## 1 M0 scope

M0 carries the assay pin eebe37e into a new tree, erases proof terms through an opaque-proof evaluator, lowers the erased term to RV64IM, encodes ELF64 with an in-tree encoder, runs the ELF under the SP1 v6.1.0 executor and under an OCaml RV64IM emulator twin, admits six Host constructors and freezes the budgets (verdict:117 and brief:541, VERIFIED).  The M1 rows of verdict:119, the overlay, the level-polymorphic row and the binding CYCLE-BUDGET are not M0 (verdict:119, VERIFIED).  The M0 spine is the smallest corpus program: it reads its input, commits a public value and halts, and PROVE-ONCE proves it once at the M0 exit (verdict:117 and brief:124-125;  the choice of the smallest program is a plan decision, BELIEVED until Stage D names it).

The milestone line, quoted verbatim from verdict:117:

- MILESTONES: M0 Stage A carry (BUILD CARRY R0-COUNT R0-AUDIT R0-DIFF SUITE-KERNEL AXIOMS-empty TRUSTED-LINES rung 1), B erase (TRACE-ERASURE via opaque-proof evaluator with the F2 seed, Acc fixture, LEAN-TWIN), C lower and encode (ENC-XCHECK, ELF-ACCEPTED on HALT), D emulator and harness (EXEC-DIFF HOST-ROSTER PUBVAL-DIGEST, Read Commit Halt), E effects (Keccak Sha256 U256Mul, GUARD-TWIN, LOWER-REFUSE), F freeze (CYCLE-BUDGET pinned, M0-TIME, rung 2 and rung 3 at most 2.0 informational, DENOMINATORS, PASSES, hashconsing bench, PROVE-ONCE smallest row);

The M0 gate line, quoted verbatim from verdict:118:

- M0 gate EXEC-DIFF and TRACE-ERASURE green on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN;

Both lines are VERIFIED by the Read window verdict:115-122 of 2026-09-22.  One paragraph per stage follows.  Each paragraph says what the stage delivers and which gate closes it.  The gate lists come from verdict:117;  the closing rule of each stage is a plan decision and is BELIEVED until that stage's build log prints the rows.

Stage A, carry.  Delivers the tree /Users/oobi/Documents/attest with lib/ and surface/ carried at eebe37e, adaptations listed in CARRIED.md, CARRIED.md and dev/PIN, the build through the dune wrapper, and the gate scripts BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS-empty and TRUSTED-LINES rung 1 (verdict:117, VERIFIED).  Closes on TRUSTED-LINES rung 1 green, kernel at most 4,100 (brief:541 OQ4, VERIFIED), with the seven gates before it green.  The assay pin holds dev/r0-count.sh, dev/r0-audit.sh, dev/carry-check.sh and dev/trusted-lines.sh to copy from (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev` on 2026-09-22).

Stage B, erase.  Delivers the opaque-proof evaluator that never unfolds a quantity-0 global, the F2 seed from the two A1 F2 fixtures of USER step 8, the Acc fixture and the Lean twin (verdict:117, verdict:136 and brief:541 OQ7, VERIFIED).  Closes on TRACE-ERASURE green on every corpus row present at Stage B and LEAN-TWIN 24/24 12/12 (verdict:118, VERIFIED);  the 16-row count is the M0 gate figure and Stage F, not Stage B, proves it.

Stage C, lower and encode.  Delivers the lowering from the erased term to RV64IM under the lower budget of 1,100 lines and the ELF64 encoder under the encoder budget of 800 lines (brief:541 OQ1 and OQ4, VERIFIED), with no LLVM, no rustc, no external assembler and no linker in the path (brief:94-98, VERIFIED), and the gates ENC-XCHECK and ELF-ACCEPTED on HALT (verdict:117, VERIFIED).  Closes on ELF-ACCEPTED on HALT green: the SP1 v6.1.0 executor accepts a halt-only ELF64 and runs it to HALT, with ENC-XCHECK green on every instruction the lowering emits.  The executor that ELF-ACCEPTED calls is BELIEVED to be the harness of Stage D run early on one ELF;  the Stage C brief settles it.

Stage D, emulator and harness.  Delivers the OCaml RV64IM emulator twin, the pinned Rust harness on sp1-sdk 6.1.0 under the harness budget of 100 lines, the Host constructors Read, Commit and Halt, and the gates EXEC-DIFF, HOST-ROSTER and PUBVAL-DIGEST (verdict:117 and brief:541 OQ1, OQ4 and OQ5, VERIFIED).  Closes on EXEC-DIFF green: the executor trace and the twin trace agree row for row on every corpus row present at Stage D, with HOST-ROSTER and PUBVAL-DIGEST green.

Stage E, effects.  Delivers Keccak, Sha256 and U256Mul as Host constructors, U256Mul at syscall 0x0001011D, and the gates GUARD-TWIN and LOWER-REFUSE (verdict:117 and brief:541 OQ5, VERIFIED).  Closes on GUARD-TWIN and LOWER-REFUSE green with EXEC-DIFF and TRACE-ERASURE still green over the six-constructor roster.  Bn254 and Secp256k1 are M2 (brief:541 OQ5, VERIFIED).

Stage F, freeze.  Delivers CYCLE-BUDGET pinned per corpus program, M0-TIME, rung 2 and rung 3 at most 2.0 informational, DENOMINATORS, PASSES, the hashconsing bench and PROVE-ONCE on the smallest row (verdict:117, VERIFIED).  Closes on the M0 gate of verdict:118: EXEC-DIFF and TRACE-ERASURE green on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN.  M0-RATIO and rung 3 print and do not gate (brief:541 OQ2, VERIFIED);  the DENOMINATORS row prints OPEN while `bend` is not on PATH (brief:543, VERIFIED;  `command -v bend` printed nothing on 2026-09-22, VERIFIED).

Out at M0, each with its milestone (verdict:119-121, VERIFIED).

- M1: rung 4 at most 1.0 binding with OPEN allowed and printed, CYCLE-BUDGET binding, the overlay merged with one level-polymorphic row, PRELUDE-CHECKED in check mode, kernel at most 4,400, 8 more rows (verdict:119).
- M2: SPar admitted, AXIOMS exactly Quot.sound, 48 rows, fail-closed PRELUDE-CHECKED, the full roster against software twins in cycles, rung 5 (verdict:120).
- M3: SNu admitted with the EXTRA corpus, a proved encoder replaces ENC-XCHECK, PROVE-ONCE on the largest row (verdict:121).
