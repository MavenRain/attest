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

None yet.
