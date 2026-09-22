# kan-sp1-lang design verdict

Date: 2026-09-21.  Status: ASSEMBLED 2026-09-22 from the judge return by a closer unit, not re-judged.  RATIFIED 2026-09-22 by the user (ratify all, OQ1 to OQ7).  Judge round 2: the round 1 judge scored P2 and P3 and fixed the design;  this round adds P1 and A1, re-scores all three, and writes the file.  Paths: A = /Users/oobi/Documents/kan-sp1-lang-assay-pin (eebe37e), M = /Users/oobi/Documents/kan-sp1-lang-mech-pin (1e4f371), V = /Users/oobi/Documents/mechanism-lang/vendor/veil (read only), S1 = /Users/oobi/Documents/kan-sp1-lang-dossier-kernels.md, S2 = /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md, S3 = /Users/oobi/Documents/kan-sp1-lang-dossier-priorart.md, P1 to P3 = /Users/oobi/Documents/kan-sp1-lang-proposal-N.md, A1 to A3 = /Users/oobi/Documents/kan-sp1-lang-attack-N.md.  Tags: VERIFIED carries the command or the path:line;  BELIEVED carries what settles it.

## Ratification

The user ratifies or amends this verdict.  Nothing here is committed.  Every Stage 0 step is a USER step.  Each open question carries a recommended answer.  The rulings of brief section 10 (the defaults of section 9) bind this verdict;  a changed default is marked REOPENED in the open questions.

## Scores

Seven axes, 10 points each, 70 total.  The tiebreak is what this machine VERIFIED.

| Proposal | r0 | strength | speed | target | erasure | kernelchoice | staging | total |
|---|---|---|---|---|---|---|---|---|
| P1 attest (Kan-honest, strength-first, assay kernel, Host after erase) | 7 | 7 | 5 | 9 | 7 | 8 | 7 | 50 |
| P2 vouch (target-first, speed-first, assay kernel byte-exact, Host as Lan SColl 8) | 8 | 6 | 5 | 8 | 7 | 7 | 8 | 49 |
| P3 attest (parity-first, concedes the flip, assay base plus overlay port and M/import) | 6 | 6 | 4 | 6 | 6 | 8 | 5 | 41 |

Score evidence per axis is in the per-proposal verdict.  P2 and P3 keep the round 1 scores except P2 erasure, which drops from 8 to 7 on a seam this round CONFIRMED (finding F2).  P1 was absent on disk in round 1 and is scored here from P1 and A1.

## Winner

P1 attest wins by one point, 50 to 49.  Reasons.  (1) Target: P1 states the RV64IM W forms, the ELF64 layout and the syscall sequence as VERIFIED S2 rows, and this machine confirmed the encodings with clang (probe 9);  P2 marks the W forms, the ELF class and the pointer convention BELIEVED.  (2) Strength: P1 designs 24 ACCEPT and 12 REFUSE rows with the Lean 4 feature named per row and every R0 row mapped (P1:25-28, :72-78);  P2 has 10 and 6.  (3) Erasure: P1 and P2 both argue from the quantity rules, and both arguments break on the same pin seam (F2), so both stand at 7.  P1 loses to P2 on r0 (the precompile postulate route, F3) and on staging (the TRUSTED-LINES headroom, F6).  Grafted from P2 and P3: Host as the library sum Lan (SColl 8) and Prog as the free monad Lan_SMu over Host, EXTERN-ROSTER with --externs beside --axioms, the five-rung M0-RATIO ladder with the denominator hash, M/import as a sibling directory with PRELUDE-CHECKED count mode at M0 and check mode at M1, CYCLE-BUDGET printing cycles and syscalls, one rv64 reference object per W form, KPrim in eterm.  Kept from P1: R0-DIFF, LEAN-TWIN, ENC-XCHECK, HOST-ROSTER, PUBVAL-DIGEST, GUARD-TWIN, PASSES with the re-entry counters, the PROVE-ONCE resource guard, the trap story, the erasure theorem restated (the F2 fix), and the name attest.

## Probes

- PROBES (all ran 09-21/22, VERIFIED unless marked): 1 rg -n '^  \| ' A/lib/term.ml prints 13 constructors at :47-59, type-building Univ Lan Ran.
- 2 A/lib/shape.ml:10-15 five shapes;
- V/lib/shape.ml:16-19 adds SZk SFhc SMpc;
- diff -q term.ml A vs V identical, shape.ml differ;
- M/lib has no term.ml or shape.ml.
- 3 wc: A/lib 6,193 lines 22 files, M/lib 3,744 in 9, V/lib 7,576 in 23.
- 4 zsh -f A/dev/r0-count.sh R0-COUNT OK;
- A/_build/default/bin/assay.exe spec-count: formers 2 Lan Ran, shapes declared 5, admitted 3 SPi SColl SMu, named rules present 3 proof-irrelevance subsingleton-large-elimination literal-fast-path;
- zsh -f A/dev/trusted-lines.sh: kernel=3997 want=3997 bound=4000, emitter=1800/1800, assembler=238/600, keccak=89/250, abi=35/400, layout=8/250, listing=54/250, total=2224/3550 OK;
- A/lib/rules.ml:20-23 SPar arrives at M1, SNu at M2;
- A/dev has denominator.sh, denominators.json, gates.sh (gates.sh has no TRACE-ERASURE line, so P2's Stage F precedent stays BELIEVED).
- 5 A/lib/erase.ml:173-177 proof_free = Eval.quote then Check.infer_univ;
- :182-187 runtime_ty = Eval.whnf then as_univ, width_zero, proof_free;
- :191-193 point_runtime;
- A/lib/eval.ml:84-93 unfolds a reducible non-recursive Def, keeps Axiom and Prim neutral.
- 6 A/lib/literal.ml:5-7 LString or LInt;
- A/lib/check.ml:183 types LInt by a kernel name;
- check.ml:61-62 readable;
- A/lib/rules.ml:215 SPi quantity on the first component;
- M/lib/check.ml:43 Level_scope.check per checked term.
- 7 A/dev/M1-CLOSE.md:58-59 attempt 01 ratio 1.163762 load 14.57, attempt 02 ratio 1.956099 load 32.99.
- 8 /Users/oobi/.sp1/bin/cargo-prove prove --version prints cargo-prove sp1 (d454975 2026-04-11);
- plain --version refused.
- 9 clang rv64im: addi a0,a0,1 00150513, addw 00b5053b, mulw 02b5053b, lui t0,0x10 000102b7, addi t0,t0,0x109 10928293, ecall 00000073, ld sp,0(sp) 00013103;
- rv32im add 00b50533, mul 02b50533, lw 00012103.
- 10 cut -f3 M/map/prelude.map.tsv: 19 NAME_ONLY, 185 NEVER, 2273 UNMAPPED, 0 NAME_AND_TYPE.
- 11 cached bend_README.md:122-124 names only bend guide and bend PROOF.bend;
- raw.githubusercontent.com fetch refused;
- check and compile subcommands BELIEVED, settled by bend --help after USER step 2.
- 12 df -g: 21 GiB free.
- 13 no registry host answered, name rows BELIEVED.

## Per-proposal verdict

- PER-PROPOSAL: P1 r0 7 (walk holds, R0-DIFF real;
- minus postulate route A1 F3, literal kinds as kernel rules, SPi quantity wording), strength 7 (24+12+8 rows, every R0 row mapped P1:25-28 :72-78;
- minus five REFUSE rows without a site, two unrefusable, Word32 twin exits 0, M0 monomorphic), speed 5 (recipe A/dev/denominator.sh, commands marked BELIEVED P1:32, six twins, Q6 levers, counters, UNMET path P1:37;
- minus lone 1.956, walks=5 hides reentries, no per-pass split, two twins not like for like, 3-rung ladder), target 9 (all S2 rows VERIFIED, 15 codes matched by A1 F5, probe 9;
- minus Q2 wording, UINT256 variant), erasure 7 (E1-E3 by line, theorem stated, GUARD-TWIN;
- minus false as stated F2), kernelchoice 8 (P1:58-61), staging 7 (six stages, one mutation per gate;
- minus 3 lines TRUSTED-LINES headroom, moved gate texts, M0 exit waits on USER step 1);
- no BELIEVED cited as fact.
- P2 49: round 1 kept except erasure 8 to 7 (P2:75 'not on the proof content' and --trust-proofs replacing arguments only;
- probe 5 shows runtime_ty unfolds a reducible global proof, so a binder's erasure can turn on a global proof body under subsingleton large elimination).
- P3 41 unchanged.

## Findings

- FINDINGS A1: F1 STANDS IN PART NOT FATAL (reentries hidden, fix PASSES prints walks=5 reentries=<n>;
- 1.956 quoted alone, quote both rows and the load;
- Bend command BELIEVED for every proposal, rung 1 numerator per-pass split at Stage A, rung 2 denominator plus hash at Stage 0c, if no compile subcommand then attest check vs bend check is the like-for-like row;
- twins pinned per pair, Word32 over Fin with a proof in both, keccak row on the pure core in both;
- REFUTED 'unreachable on any measured number' since no denominator exists, ratio informational at M0 and binding at M1 with a printed UNMET path, same as round 1 on A2 F1).
- F2 STANDS SURVIVABLE, reaches P2 and P3, mechanism CONFIRMED probe 5, fixture BELIEVED;
- fix: erasure decides positions with an evaluator that never unfolds a quantity-0 global, TRACE-ERASURE on proof bodies through it, A1 F2 term is the seed mutation.
- F3 STANDS: literal kinds as named rules in spec-count;
- SPi wording fixed;
- postulates dropped for Prog free monad plus EXTERN-ROSTER and --externs;
- --axioms empty at M0 and M1, exactly Quot.sound from M2.
- F4 STANDS: a site per REFUSE row, LOWER-REFUSE gate for Word32 without proof and the pure Host call (also fails by type once Prog is a type), Word32 twin over Fin, Acc erasure fixture at Stage B.
- F5 IN PART: Q2 wording REOPENED (OQ1);
- pick UINT256_MUL 0x0001011D, MUL_CARRY 0x00010131 an M2 option;
- refuted for Q1 (default text says ISA per S2).
- F6 STANDS CONFIRMED kernel=3997/4000, OQ4 bounds 4,100 M0 and 4,400 M1.
- F7 IN PART: TRACE-ERASURE on bodies REOPENED (OQ7), PROVE-ONCE OPEN until USER step 1, weeks BELIEVED.
- A2 and A3 rulings of round 1 unchanged.

## The synthesized design

- DESIGN: round 1 design (A/lib eebe37e byte-exact term.ml shape.ml spec_count.ml with R0-DIFF vs kanon 2c2e6e6;
- level overlay merge at M1;
- erase and eterm RV64 reprs erase.ml:249 :413 eterm.ml:17-22 RWord RStruct RUnion RFunc RThunk plus KPrim;
- budget counter;
- R0 table five rows SPi SColl SPar(M2) SMu SNu(M3) with Lean features, lowering and gates per P1:72-80;
- Word32 = Lan_SPi Nat (n < 2^32) second component erased by Prop type;
- ambient Prop, proof irrelevance, subsingleton large elimination, Quot.sound from M2;
- Host = Lan (SColl 8), Prog = Lan_SMu over 1 + Sigma (h : Host) (Resp h -> X), In nodes lowered to ecalls, code in t0, a0 a1, a2 for WRITE: Read HINT_LEN 0xF0 HINT_READ 0xF1, Commit WRITE 0x02 fd 13, Halt SHA_EXTEND 0x00300105 SHA_COMPRESS 0x00010106 then 8 COMMIT 0x10, 8 COMMIT_DEFERRED_PROOFS 0x1A a1=0, HALT 0x00, Keccak KECCAK_PERMUTE 0x00010109, Sha256, U256Mul UINT256_MUL 0x0001011D, Bn254 ADD 0x0001010E DOUBLE 0x0000010F, Secp256k1 ADD 0x0001010A DOUBLE 0x0000010B DECOMPRESS 0x0000010C;
- never ENTER_UNCONSTRAINED EXIT_UNCONSTRAINED VERIFY_SP1_PROOF MPROTECT POSEIDON2, HOST-ROSTER scans the ELF t0 immediates;
- traps: div rem never trap, guest faults only bad memory and bad ecall, bound proof removes a check else check plus branch to Halt 1;
- pipeline carry surface 183+143+620+302+1,179 and lib, M/import 1,543 sibling, adapt level erase 1,484 eterm 117 budget 27 bin/assay 221 to attest with --passes --axioms --externs spec-count, differential 88 and diff.py 272 to dev/exec-diff.py, proofs/ reference/ templates, rewrite emit 493 to lower.ml about 900 and asm 238 plus listing 54 to rv64im.ml elf64.ml runtime.ml about 700, drop contract 894 recognize 254 model 143 abi 35 layout 8 keccak 89, new emu/rv64im.ml about 700 outside the base and sp1-exec-harness at most 100 Rust lines on sp1-sdk = 6.1.0 execute only;
- ELF64 class BELIEVED until llvm-readelf on the hello guest (elf.rs:84-85 accepts both), little endian, e_machine 243, e_type 2, two PT_LOAD 0x78000000 RX and 0x78100000 RW, p_align 0x1000, no section table, stub sets sp and bump pointer, 96-byte HALT fixture first, no C extension, ENC-XCHECK from the 14-row reference plus one rv64 object per W form;
- harness prints EXEC cycles=<n> syscalls=<n> pv=<hex> exit=<n> from ExecutionReport report.rs:40-41, emulator prints the same, EXEC-DIFF compares, exit=fault both sides;
- PROVE-ONCE core then verify on the smallest row per milestone under /usr/bin/time -l, skipped with a reason under 30 GiB disk or 16 GiB memory, milestone OPEN on that row;
- cost = total_instruction_count plus syscalls, informational M0 binding M1;
- R1 LEAN-TWIN 24 ACCEPT 12 REFUSE at M0 with the F4 fixes, 8 more at M1, 48 by M2, coinductives M3, PRELUDE-CHECKED count mode M0, ratchet M1, fail-closed M2;
- R2 rows bend_check and bend_compile ms per kloc frozen Stage 0c with DENOMINATORS.sha256 by the A/dev/denominator.sh recipe, twins main.bend with main.lean (S3 finding 2) plus six corpus pairs with lines pinned, M0 levers direct encoding no optimizer fuel WALKS 5 with reentries, M1 levers memoised conversion over hashconsed terms first on proof_free and runtime_ty after a hashconsing bench on the 77 fixtures at Stage F;
- trusted base kernel bucket 4,100 M0 4,400 M1, lower 1,100, encoder 800, harness 100, disclosure attest check --axioms, attest check --externs, attest build --passes, attest spec-count, dev/r0-count.sh, dev/r0-audit.sh, dev/trusted-lines.sh, shasum -c dev/DENOMINATORS.sha256).

## Milestones M0 to M3

- MILESTONES: M0 Stage A carry (BUILD CARRY R0-COUNT R0-AUDIT R0-DIFF SUITE-KERNEL AXIOMS-empty TRUSTED-LINES rung 1), B erase (TRACE-ERASURE via opaque-proof evaluator with the F2 seed, Acc fixture, LEAN-TWIN), C lower and encode (ENC-XCHECK, ELF-ACCEPTED on HALT), D emulator and harness (EXEC-DIFF HOST-ROSTER PUBVAL-DIGEST, Read Commit Halt), E effects (Keccak Sha256 U256Mul, GUARD-TWIN, LOWER-REFUSE), F freeze (CYCLE-BUDGET pinned, M0-TIME, rung 2 and rung 3 at most 2.0 informational, DENOMINATORS, PASSES, hashconsing bench, PROVE-ONCE smallest row);
- M0 gate EXEC-DIFF and TRACE-ERASURE green on 16 rows, LEAN-TWIN 24/24 12/12, AXIOMS empty, PROVE-ONCE done or OPEN;
- M1 rung 4 at most 1.0 binding OPEN allowed and printed, CYCLE-BUDGET binding, overlay merged with one level-polymorphic row, PRELUDE-CHECKED check mode, kernel at most 4,400, 8 more rows;
- M2 SPar admitted, AXIOMS exactly Quot.sound, 48 rows, fail-closed PRELUDE-CHECKED, full roster vs software twins in cycles, rung 5;
- M3 SNu admitted with EXTRA corpus, proved encoder (riscv-coq decode_encode port, S3 finding 5 BELIEVED) replaces ENC-XCHECK, PROVE-ONCE on the largest row.

## Trusted lines

- TRUSTED LINES section: probe 4 rows verbatim plus whole-lib 6,193 informational plus the OQ4 bounds.

## Stage 0 USER steps

- STAGE 0 USER (brief 517-526): 1 diskfree --apply to 30 GiB (21 today);
- 2 Bend 2 install curl -fsSL https://bend-lang.com/install.sh | sh then bend --help recorded into dev/bend-cli.txt;
- 3 MODIFIED toolchain present (probe 8), build hello guests for riscv64im and riscv32im, llvm-readelf -h, execute both;
- 4 optional spike;
- 5 veil checkout (brief 216-217) then zsh -f M/dev/dunecho.sh build and RUNS=7 zsh -f M/dev/bench.sh SUITE-KERNEL 'M/_build/default/test/main.exe M/vendor/veil/test';
- 6 ADDED cargo fetch sp1-sdk 6.1.0;
- 7 ADDED Stage 0c denominator.sh freeze with DENOMINATORS.sha256;
- 8 ADDED round 2: write the two A1 F2 fixtures (refl body vs opaque postulate) and diff the erase output on the pin before Stage B.

## Name

- attest, extension .att, driver attest (attest check, attest build, attest run, attest --axioms, attest --externs, attest --passes, attest spec-count), from P1:7, the same word P3 proposed
- collision note INFORMATION only, every row BELIEVED because no registry host answered from this sandbox: settle with curl on https://crates.io/api/v1/crates/attest, https://pypi.org/pypi/attest/json, https://registry.npmjs.org/attest, https://formulae.brew.sh/api/formula/attest.json and https://api.github.com/search/repositories?q=attest
- attest is a common English word and a probable crate and test-library name
- vouch (P2:7) is the runner-up word if the user prefers a rarer one

## Open questions

- OQ1 (reopens Q1 and Q2): target RV64IM and ELF64 for the installed v6.1.0 executor, emulator twin RV64IM.  Recommended: yes;  USER step 3 settles the ELF class and the RV32 refusal (crates/build/src/lib.rs:16 VERIFIED, RV32 refusal BELIEVED).
- OQ2 (reopens Q6): M0-RATIO informational at M0 (rung 3 at most 2.0) and binding at M1 with an OPEN exit allowed and printed;  if bend --help shows no compile subcommand, the like-for-like row is attest check against bend check and the full-compile row is informational.  Recommended: yes;  memoised conversion stays at M1.
- OQ3 (reopens Q5): PRELUDE-CHECKED as a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE) and fail-closed on NAME_ONLY = 0 and UNMAPPED = 0 at M2, because today's counts are 0 NAME_AND_TYPE, 19 NAME_ONLY, 2273 UNMAPPED, 185 NEVER (probe 10).  Recommended: yes.
- OQ4 (reopens none, TRUSTED-LINES): kernel bucket bound 4,100 at M0 (the literal kinds and their check rules) and 4,400 at M1 (the 267-line overlay), lower 1,100, encoder 800, harness 100;  the gate prints kernel=3997/4000 today (probe 4) and the whole lib is 6,193 lines, informational;  the brief's 3,000 is a kanon-era number neither candidate meets.  Recommended: ratify.
- OQ5 (reopens Q4 in part): Host at M0 is Read, Commit and Halt at Stage D and Keccak, Sha256 and U256Mul at Stage E;  Bn254 and Secp256k1 at M2;  Halt carries the SHA-256 commit path (8 COMMIT, 8 COMMIT_DEFERRED_PROOFS, HALT);  UINT256_MUL 0x0001011D chosen over MUL_CARRY 0x00010131.  Recommended: yes.
- OQ6 (reopens Q0): the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures.  Recommended: keep assay unless that median is under 211 ms, because the overlay costs about 480 lines under either base and term.ml is byte-identical between the assay pin and veil (probe 2).
- plus OQ7 (reopens the TRACE-ERASURE text of brief 4.6): the gate compares an ELF with proof bodies against one with the same proofs replaced by opaque postulates, both erased through the evaluator that never unfolds a quantity-0 global, plus GUARD-TWIN;  recommended ratify, because a bound proof binder changes the instruction (addLt) by design.

RATIFIED 2026-09-22: the user ruled "ratify all" on OQ1 to OQ7.  Every recommendation above now binds;  the rulings are recorded in section 10 of the brief.
