# kan-sp1-lang proposal P3: parity-first, the lean4export lens

P3, 2026-09-21.  A = /Users/oobi/Documents/kan-sp1-lang-assay-pin.  M = /Users/oobi/Documents/kan-sp1-lang-mech-pin.  V = /Users/oobi/Documents/mechanism-lang/vendor/veil (read only).  S1, S2, S3 = the dossiers, cited as S1:ROW for a row line.  Every claim is VERIFIED (command, path:line, URL) or BELIEVED (with what settles it).  Panel caps: 7 findings, 56 agents.

## 0.  Name, extension, driver, thesis

Name: attest.  Extension: `.att`.  Driver: `attest`.  Reason: the SP1 proof attests to one run of the guest, and the PRELUDE-CHECKED line attests to Lean 4 parity with counts.  The seed `cite` names only the import side.  Collision note: `attest` is a common word and some test libraries use it (BELIEVED, a registry search settles it).  That is information, not a decision.

Thesis.  Parity is the first design input.  The lean4export importer (M/import, 1,543 lines in 10 modules, VERIFIED S1:158) names every Lean 4 declaration kind and level form a Kan kernel must receive, and PRELUDE-CHECKED over 2,477 names (M/map/prelude.map.tsv, VERIFIED S1:162) is the only measurable R1 oracle in the family.  So every R0 row is mapped through the importer before the target is designed, the level overlay (267 lines, VERIFIED S1:154) lands in the kernel at M0, and the PRELUDE-CHECKED counts print at M0 in count mode.  The honest cost: the Q0 flip to mechanism-lang over veil DOES NOT HOLD on S1's numbers (section 6).  attest keeps assay's kernel and ports the overlay and the importer onto it.  P3's contribution is the parity spine: import-first mapping, the overlay port, count-mode PRELUDE-CHECKED at M0, and twin corpora derived from the prelude map.

## 1.  R0 honesty

Two formers.  The term sum has `Lan of t Shape.t * t` and `Ran of t Shape.t * t` plus the schema constructors In, Elim, Sec, Out (A/lib/term.ml:46-59, VERIFIED S1:119).  V/lib/term.ml is byte-identical to A/lib/term.ml (VERIFIED S1:120), so the former count is two under either kernel.  Closed grammar.  attest's shape sum is A/lib/shape.ml:10-15 exactly: SPi, SColl, SPar, SMu, SNu (VERIFIED S1:118).  veil adds `SZk of Quantity.t * string * 'a` at V/lib/shape.ml:16, `SFhc of 'a` at :18 and `SMpc of 'a * 'a` at :19 (VERIFIED, read this session, span V/lib/shape.ml:10-20).  A ZK shape fails R0 (brief lines 61-64).  Under a mechanism-lang base the three constructors, their 103 lines of arms (shape.ml 19, circuit.ml 21, erase.ml 20, pp.ml 8, rules.ml 35, VERIFIED S1:173 and S1:179), the named rules zk-fhc, zk-mpc, fhc-mpc (M/SPEC.md:12-17, VERIFIED S1 section 5) and circuit.ml (563 lines, VERIFIED S1:175) are excised before the first gate.  Under the assay base none of them exists (five shapes only, VERIFIED S1:118).

The smuggling list in plain words.  None of these is a former or a shape in attest:
- Host: a family of extern globals in the prelude.  Each constructor is a `Global` of the extern kind with a Kan type (`Commit : Bytes -> Prog Unit`) and no body.  The kernel sees a global whose definition is absent.  It is tracked as a postulate and printed by `--externs` beside `--axioms`.  Framework.
- syscalls and precompiles: rows of the erasure table (section 9), one ecall sequence per extern.  Framework.
- cycles: a number the executor prints and CYCLE-BUDGET pins.  The kernel has no cycle type.  Framework.
- the allocator and the calling convention: `lower` facts, checked by EXEC-DIFF against clang reference objects.  Framework.
- Word32, Word64, U256, Bytes literals: constructors of `Literal.t` (today `LString | LInt`, A/lib/literal.ml:5-7, VERIFIED S1:132), a leaf of the term sum.  The literal fast path is the third named rule already in the ledger (brief lines 281-283).  Adding LWord32, LWord64, LU256, LBytes extends the literal alphabet, not the former count.  Literal accelerators.
- bound proofs: quantity-0 terms of Prop types built from Ran over pi and Ran over the parallel pair.  Ordinary terms, erased (section 5).  Not a shape.
- ZK: nowhere.  attest has no proof type, no circuit module, no witness quantity.  The prover proves the guest run from outside.

Term walk.  R0-AUDIT walks the term sum and refuses any constructor beside the 13 named at A/lib/term.ml:47-59, then walks the shape sum and refuses any constructor beside the five at A/lib/shape.ml:11-15.  R0-COUNT prints `formers 2: Lan Ran` and `shapes 5` through spec_count (A/lib/spec_count.ml:14-19, VERIFIED S1:115).  A mechanism-lang base prints `shapes declared 8` today (M/SPEC.md:12-17, VERIFIED S1 section 5).  That is the R0 failure the excision removes.

Per row (full table in section 8).  Rows 1 to 3 are real constructions: Lan or Ran applied to a finite shape, the pointwise formula is the kernel rule.  Rows 4 and 5 implement the algebra and coalgebra universal properties with P inside the shape.  Their Kan reading goes through Adamek's chain, which the kernel does not compute (BELIEVED, S3 finding 7, Riehl chapter 6 settles it).  For rows 4 and 5 R0 rests on three facts: the constructor is `Lan (SMu ...)` and not a third former, the shape grammar is closed and printed, and SPEC.md states the admitted reading.  P3 says so plainly: mu and nu are Kan by naming plus universal property, not by a chain the checker computes.

## 2.  Lean 4 strength credibility

Import oracle scoped.  M/import parses lean4export ndjson (ndjson.ml 295 lines), lowers levels (`type t = Zero | Succ of int | Max of int * int | Imax of int * int | Param of int`, M/import/levels.ml:1, VERIFIED read this session), translates declarations (translate.ml 352 lines, `Max` to `Level.max` at :250, VERIFIED S1:160) and reports (`PARITY-KIND declared= scoped_types= kernel_types= deferred=` at M/import/report.ml:58 and `PARITY-STATUS NEVER=0` at :63, VERIFIED read this session).  The line `PRELUDE-CHECKED external=2477 NAME_AND_TYPE= NAME_ONLY= UNMAPPED= NEVER=` is stated at M/README.md:25-26 (VERIFIED S1:163).  Its counts are UNMEASURED, the mechanism-lang build is blocked on the submodule (VERIFIED S1:36, S1:164).  attest runs the oracle in two modes.  Count mode at M0: parse the export, map names through prelude.map.tsv, print the four counts and the covered percentage, no kernel check, fail when NAME_ONLY or UNMAPPED is above zero.  Check mode at M1: every NAME_AND_TYPE row is re-checked by attest's kernel.  Count mode needs no level overlay.  Check mode needs it: `Param`, `Max` and `Imax` cannot land in assay's `type t = int` (A/lib/level.ml:2, 11 lines, VERIFIED S1:157).

The R0 rows through the importer.  Lean `forallE` maps to Ran over SPi, structures to Ran over SColl, `inductive` to Lan over SMu with the positivity record (A/lib/positivity.ml, VERIFIED S1:131), `Quot` plus `Quot.sound` to Lan over SPar plus the tracked axiom, `Prop` to the level-zero universe with proof irrelevance, universe polymorphism to prenex `Param` levels through the overlay.  Coinductives have no Lean 4 source row and stay a local extension through Ran over SNu.  Which of these translate.ml does today and which are UNMAPPED is the first count-mode run at M0 (BELIEVED until that run).

ACCEPT corpus (Lean 4 accepts, attest must accept, `lean` is the oracle), 24 files at M0: dependent pair and function, a two-constructor enum, a record with eta, `Quot` with `Quot.lift` and `Quot.sound`, a subtype with a decidable predicate, `Nat` as mu, `List` and `Vec` as families, structural recursion, proof-irrelevant `Prop` equality, subsingleton elimination into `Type`, a Word32 literal with a bound proof, a universe-polymorphic identity at `Param 0`, and one file per prelude.map.tsv module group.
REFUSE corpus (Lean 4 rejects, attest must reject), 16 files: a non-positive inductive, non-structural recursion without a measure, large elimination from a non-subsingleton `Prop`, `Type u : Type u`, `Quot.lift` without its soundness obligation, a runtime use of a quantity-0 binder, an unproved Word32 addition, an `Auto` at M0 (brief line 322).
Each row is a pair FILE.lean and FILE.att with the same declaration list.  The gate runs `lean FILE.lean` and `attest check FILE.att`.  A divergence on either corpus fails the gate.  `lean` on PATH is BELIEVED (`command -v lean` settles it, else a USER step).

## 3.  Bend 2 speed credibility

Denominator commands.  Bend 2 is absent (VERIFIED S2:209).  The USER installs it with `curl -fsSL https://bend-lang.com/install.sh | sh` (VERIFIED S2:210, cache/bend_README.md:113).  `bend FILE.bend` checks and runs (VERIFIED S2:214, README:124).  The compiler emits one C file that clang compiles (VERIFIED S3 section 2, bend-guide.md:584-585).  The check and compile subcommand names are BELIEVED until `bend --help` after the install (S2 finding 6).  Denominator = median of 7 single-core runs of `bend check TWIN.bend` plus the C-emission subcommand on TWIN.bend, WITHOUT the clang step, because attest has no C compiler in its path and the pin measures checker plus code generator.  Frozen at Stage 0c into `dev/denominators.json` with `DENOMINATORS.sha256` (brief lines 91-93).  Timer: `RUNS=7 zsh -f dev/bench.sh NAME CMD`, identical in A and M (VERIFIED S1:49).

Twin corpus.  Eight pairs at M0, 40 to 400 lines each: nat arithmetic, list fold, tree map, record update, a sum-typed interpreter, dependent vector append, a keccak program with one Host call, and a generated 1,000-line definition ladder for the per-1,000-line ratio.  Bend 2's core has All, Lam, App, Adt, Ctr, Mat, Eql, Rfl, Rwt, Let (VERIFIED S3, bend.lean:197), so every twin uses only features both sides have.

Walks per definition.  attest prints `WALKS name=N`.  assay does elaborate then check as two walks (surface/elab.ml:1171, Check.check_decls at :1126, VERIFIED S1:141), then erase (erase.ml:1459, VERIFIED S1:128), then lower, then encode: five walks.  mechanism-lang adds a sixth, `Level_scope.check` on every check (M/lib/check.ml:43, VERIFIED S1:156).  attest's overlay port folds the level scope check into the elaboration walk.  Five stays the number and a WALKS gate pins it.

The 1.956 risk.  assay's frozen M1 ratio is 1.956099 against 1.0 (VERIFIED brief lines 100-101).  It was measured against assay's own denominator, so it does not transfer as a number, only as a lineage warning.  attest answers it three ways.  Direct encoding: no C file, no clang, no linker on our side, and the clang step is excluded on the Bend side too.  The M0-RATIO ladder (section 12) records every rung so the band is visible before M1 binds.  The M1 levers (memoised conversion over hashconsed terms, per-definition fuel) do not depend on the kernel choice: A/lib/conv.ml and V/lib/conv.ml are both 396 lines (VERIFIED S1:201, S1:225).  The R2 number P3 reaches today: NONE.  assay's suite median is 421.774 ms over 7 runs (VERIFIED S1:52), the mechanism-lang median is UNMEASURED, and no Bend 2 run exists.  P3 cites no Bend 2 ratio it has not measured.

## 4.  SP1 target fidelity

ISA.  The installed cargo-prove is `cargo-prove sp1 (d454975 2026-04-11)`, tag v6.1.0 (VERIFIED S2:11-12).  Its default target is `riscv64im-succinct-zkvm-elf` (VERIFIED S2, crates/build/src/lib.rs:16) and the VM is 64-bit: `ld sp, 0(sp)` in `_start` and `memory_image: HashMap<u64, u64>` (VERIFIED S2:25).  RV32IM ELFs on this executor are BELIEVED unsupported (S2:27, a riscv32im hello guest settles it).  attest targets RV64IM at v6.1.0 and marks Q1 REOPENED (section 11).  Instruction words are 4 bytes, no C, A, F or D (VERIFIED S2:31).  The S2 section 8 encodings are valid RV64 words, with the W forms for 32-bit results (VERIFIED S2 line 239).
Syscall codes (crates/zkvm/entrypoint/src/syscalls/mod.rs and crates/core/executor/src/syscall_code.rs at v6.1.0, VERIFIED S2 section 3): HALT 0x00000000, WRITE 0x00000002, ENTER_UNCONSTRAINED 0x00000003, SHA_EXTEND 0x00300105, SHA_COMPRESS 0x00010106, KECCAK_PERMUTE 0x00010109, SECP256K1_ADD 0x0001010A, SECP256K1_DOUBLE 0x0000010B, SECP256K1_DECOMPRESS 0x0000010C, BN254_ADD 0x0001010E, BN254_DOUBLE 0x0000010F, COMMIT 0x00000010, COMMIT_DEFERRED_PROOFS 0x0000001A, HINT_LEN 0x000000F0, HINT_READ 0x000000F1, UINT256_MUL 0x0001011D, UINT256_MUL_CARRY 0x00010131.  Convention: code in t0 (x5), arguments a0 (x10) and a1 (x11), WRITE also a2 (x12), HINT_LEN returns the length in t0 (VERIFIED S2 section 3).
ELF layout.  The executor accepts ELF32 or ELF64, little endian, e_machine 243, e_type 2, PT_LOAD at or above 0x78000000, no W+X segment, entry a multiple of 4, no section table read (VERIFIED S2 elf.rs:81-89, finding 3).  attest emits ELF64: 64-byte header, two PT_LOAD headers (text R+X at 0x78000000, data R+W on the next 0x1000 boundary), the bump heap after data, the stack top at the address the entrypoint uses (BELIEVED, crates/zkvm/entrypoint/src/lib.rs:230-250 settles it).  The 96-byte minimal ELF of S2 line 253, re-emitted as ELF64, is the first ELF-ACCEPTED fixture.
Executor harness.  S2 section 5 verbatim: `sp1-sdk = "=6.1.0"`, `ProverClient::from_env()`, `client.execute(Elf::from(bytes), stdin).run()`, JSON with `public_values_hex`, `cycles` from `report.total_instruction_count()`, `syscalls`, `exit_code` (VERIFIED S2 lines 111-195).  The OCaml twin `emu/rv64im.ml` runs the same ELF and prints the same JSON.  EXEC-DIFF compares the two lines per program.  Public values are the bytes written to fd 13 and the guest commits their SHA-256 digest through 8 COMMIT ecalls before HALT (VERIFIED S2 finding 4), so the runtime carries SHA-256 through SHA_EXTEND and SHA_COMPRESS.  No sp1 crate source is on disk (VERIFIED S2:16), so the first harness build is a USER step.  Proving runs once per milestone exit on the smallest program (S2:203).

## 5.  Proof-erasure soundness

The rule.  `quantity_runtime q = not (Quantity.equal q Quantity.Zero)` (A/lib/erase.ml:102-104, VERIFIED S1:128) is the single predicate that keeps or drops a binder.  `Quantity.t = Zero | One | Many` and `mul` sends any Zero factor to Zero (A/lib/quantity.ml:7-22, VERIFIED S1:129), so a term under a proof binder is Zero by multiplication and no runtime position can depend on it.  Types and proofs are checked at Zero.  `eterm` carries only quantity-1 terms: `ktm` has no type or proof constructor (A/lib/eterm.ml:24-38, VERIFIED S1:127).  The argument, not the test: `lower` and `encode` are functions of `ktm` alone.  Two source programs that differ only in Zero-quantity subterms erase to the same `ktm` (erase is a fold over the term that emits nothing at Zero), so they lower to the same IR and encode to the same bytes.  TRACE-ERASURE checks the theorem on every corpus program by `cmp` of the two ELFs, and a differing byte names the erase arm that leaked a Zero term.  Bound proofs are the special case: a proof `h : a + b < 2^32` at Zero lets `lower` pick the bare `addw` over the checked sequence.  The choice reads only the TYPE of the proof, never its term, and the type is present in both compilations, so the bytes stay identical.  Extern bodies are absent, so no proof can hide in a Host call.  `Quot.sound` is an axiom at Zero and is never a runtime value.

## 6.  Kernel-choice justification

Flip trigger 1 (2x on the shared suite).  UNMEASURED.  assay: median 421.774 ms over 7 runs on the 77-fixture suite (VERIFIED S1:52, S1:48).  mechanism-lang: no build, `ls -d M/vendor/veil/lib` prints No such file (VERIFIED S1:36).  Direction of the prediction: the shared suite exercises term.ml, shape.ml and conv.ml that are the same files, and mechanism-lang adds `Level_scope.check` on every check (M/lib/check.ml:43, VERIFIED S1:156).  A kernel that does strictly more work per check is not 2x faster.  BELIEVED until Stage 0 step 5 and one `RUNS=7` bench.
Flip trigger 2 (the level overlay is necessary for the import oracle).  HELD as a code fact: `Param`, `Max`, `Imax` cannot land in `type t = int` (VERIFIED S1:157, M/import/levels.ml:1).  REFUTED as a kernel-choice fact: the overlay is 267 new lines plus a 212-line delta over files assay and veil share byte for byte, about 480 lines to port (VERIFIED S1 Q0 statement, line 233).
Cost of the mechanism-lang base: 0 backend lines (VERIFIED S1:229), 103 host-shape lines plus circuit.ml 563 to excise (VERIFIED S1:173-177), an active kernel of 7,938 to 11,320 lines against a 3,000-line bound it exceeds (M/README.md:47, VERIFIED S1 line 233), the submodule not checked out (VERIFIED S1:13), and lower plus encode written from scratch at 1,300 to 1,700 lines (S1 estimate, line 230).  Cost of the assay base: the same 1,300 to 1,700 new lines, plus the 480-line overlay port, plus M/import carried as is (1,543 lines, zero host-shape references, VERIFIED S1:179).
Verdict.  P3 CONCEDES the flip.  Q0 DEFAULT KEPT.  The ports P3 takes from assay: everything in A/lib (6,193 lines), asm/asm.ml 238 as the encoder template, emit/emit.ml 493 as the lower template, bin/differential.ml 88 and evm/diff.py 272 as the EXEC-DIFF template, dev/bench.sh and dev/stage-a-gates.py as the gate runner.  What P3 still contributes is the parity spine of section 0.

## 7.  Staging realism

M0 is six workflows over about six weeks, each a copy-then-delta of an assay stage runner (A/dev/stage-a-gates.py:61 BUILD leg, VERIFIED S1:38) with gates and a mutation log.  Stage 0 is USER work (disk, Bend 2, the succinct toolchain, the harness crate fetch, the submodule).  Stages A to F in section 12 each end on one gate row that fails closed.  The two rewrites (lower, encode) are bounded by S1's 1,300 to 1,700 line estimate and land before any Host call beyond HALT, WRITE and COMMIT.  The precompiles land at M1.  Nothing in M0 needs a prove.

## 8.  The R0 shape table

| Shape | Lan role | Ran role | Lean 4 feature | Kan reading | Lowering emits on the guest | Divergence gate |
|---|---|---|---|---|---|---|
| SPi (pi_A) | Sigma | Pi | dependent pairs, functions | real construction, pointwise formula | pair = 2-word heap node (KStruct), function = closure KClos fid env, call = jalr through ra | EXEC-DIFF on apply and proj fixtures, repr from erase.ml:249 |
| SColl (discrete) | variants | records | enums, structures | real construction, finite (co)limit | variant = tagged node KTag tid i, record = KStruct with n words, match = KCase jump table | EXEC-DIFF, R0-AUDIT rejects a sixth shape |
| SPar (parallel pair) | Quot | equalizer subtype | Quot, subtypes | real construction, finite (co)limit | Quot.mk = identity on the carrier, Quot.lift = the function, subtype = the carrier, proof gone | TRACE-ERASURE (with and without Quot.sound uses) |
| SMu (mu_P) | initial algebra | none | inductive types and families | universal property, Kan by Adamek naming (BELIEVED, S3 finding 7) | node per constructor by mu_layout (erase.ml:413), Elim = KCase plus KTail recursion | TOTALITY (A/lib/totality.ml) plus CYCLE-BUDGET |
| SNu (nu_P) | none | terminal coalgebra | none in Lean 4 | universal property, dual naming | thunk KDelay fid env, Out = KForce | EXEC-DIFF, a productivity check is BELIEVED absent in totality.ml (rg 'nu' settles it) |

Admitted counts differ today: veil admits 6 of 8 shapes and leaves SPar and SNu declared only (M/SPEC.md:12-17, VERIFIED S1 section 5).  assay's admitted count is BELIEVED and R0-COUNT prints it at BUILD.

## 9.  The Host sum roster

Every constructor is an extern global.  `li t0, CODE` is `lui` plus `addiw` for codes above 12 bits.  Pointers are 8-byte aligned heap words.
| Constructor | Syscall and code | Registers | Ecall sequence the erasure emits |
|---|---|---|---|
| Read Bytes | HINT_LEN 0xF0, HINT_READ 0xF1 | t0 out len, then a0 ptr, a1 len | `li t0,0xF0` `ecall` `mv a1,t0` bump-alloc a0 `li t0,0xF1` `ecall` |
| Commit Bytes | WRITE 0x02 fd 13 | a0 13, a1 ptr, a2 len | `li t0,2` `li a0,13` `mv a1,ptr` `mv a2,len` `ecall`, the runtime also feeds the bytes to SHA-256 |
| Halt Word32 | COMMIT 0x10 x8, HALT 0x00 | a0 word index i, a1 digest word i, then a0 exit code | 8 times `li t0,0x10` `li a0,i` `lw a1,i*4(digest)` `ecall`, then `li t0,0` `mv a0,code` `ecall` |
| Keccak Bytes | KECCAK_PERMUTE 0x00010109 | a0 state ptr (25 words) | pad in the runtime, per block xor then `li t0,0x10109` `mv a0,st` `ecall` |
| Sha256 Bytes | SHA_EXTEND 0x00300105, SHA_COMPRESS 0x00010106 | a0 w ptr, then a0 w ptr a1 state ptr | per block `li t0,0x300105` `ecall` then `li t0,0x10106` `ecall` |
| U256Mul x y m | UINT256_MUL 0x0001011D | a0 x ptr (result in place), a1 y ptr with m adjacent | `li t0,0x1011D` `mv a0,x` `mv a1,y` `ecall` (layout of y and m BELIEVED, syscalls/uint256_mul.rs settles it) |
| Bn254 Op | BN254_ADD 0x0001010E, BN254_DOUBLE 0x0000010F | a0 p ptr, a1 q ptr | `li t0,CODE` `mv a0,p` `mv a1,q` `ecall` |
| Secp256k1 Op | SECP256K1_ADD 0x0001010A, DOUBLE 0x0000010B, DECOMPRESS 0x0000010C | a0 ptr, a1 q ptr or is_odd | `li t0,CODE` `mv a0,p` `mv a1,q` `ecall` |

Not in the sum: ENTER_UNCONSTRAINED, COMMIT_DEFERRED_PROOFS, UINT256_MUL_CARRY.  Trap story.  The guest has no trap handler.  An unproved arithmetic step emits the checked sequence and on overflow jumps to a fixed `li t0,0` `li a0,1` `ecall` (HALT with exit 1).  A proved step emits the bare instruction.  A misaligned or out-of-range access is an executor error (BELIEVED, crates/core/executor/src/minimal/ecall.rs and memory.rs settle it), and the twin reports the same class, so EXEC-DIFF catches a divergence in exit_code.

## 10.  The pipeline, stage by stage

`parse -> elaborate -> check -> erase -> lower -> encode -> execute` (brief 4.4).  Line counts from S1 section 10 (VERIFIED wc unless marked).
| Stage | Carried as is | Adapted | Rewritten or new | Dropped |
|---|---|---|---|---|
| parse | A/surface lexer 183, token 143, parser 620, syntax 302 | parser: `.att` extern declarations, Word literals | none | EVM contract syntax (emit/contract.ml 894, recognize.ml 254) |
| elaborate | A/surface/elab.ml 1,179 | level scope folded into the elaboration walk (M/lib/level_scope.ml 32, level_var.ml 53) | none | `Auto` at M0 |
| check | A/lib check 538, conv 396, eval 297, rules 1,481, value 137, global 130, order 510, prim 139, error, pp, term 133, shape 60, spec_count 62, quantity 158, totality 146, positivity 118 | the overlay delta: check plus 102 lines, conv plus 8, eval plus 17 (M overlays 643, 404, 314 over veil 573, 396, 297, VERIFIED S1:155, S1:225), level.ml 11 replaced by M/lib/level.ml 36, level_eq.ml 144, rules_lvl.ml 2 | none | V/lib/circuit.ml 563, the 103 host-shape lines, the 3 named rules |
| erase | A/lib/erase.ml 1,484, eterm.ml 117, literal.ml 14, bignum.ml 51 | literal.ml gains LWord32, LWord64, LU256, LBytes, erase gains the extern-to-Host table | none | veil erase.ml host arms (20 lines) |
| lower | none | emit/emit.ml 493 as the template only | `lower/rv64.ml` about 900 lines: registers a0 to a7, sp frames, ra, bump allocator, ecall table, SHA-256 runtime | EVM stack lowering |
| encode | none | asm/asm.ml 238 and listing.ml 54 as the template | `encode/elf64.ml` about 300 lines and `encode/rv64im.ml` about 400 lines (S1 estimate 1,300 to 1,700 for lower plus encode) | Cancun opcodes, keccak/keccak.ml 89 |
| execute | bin/differential.ml 88, evm/diff.py 272 as the template | budget.ml 27 becomes a counter (a poll, not a counter today, VERIFIED S1:135) | `harness/` Rust crate of S2 section 5, `emu/rv64im.ml` about 700 lines | geth `evm run` |
| import (M1 check mode, M0 count mode) | M/import 1,543 lines, 10 modules | mapping.ml 81 reads a `.att` prelude map | none | none |
Trusted after the cut: kernel about 6,700 lines (A/lib 6,193 plus the 480 overlay lines), encoder about 700 lines, lower about 900 lines.

## 11.  Answers to Q0 to Q7

- Q0 DEFAULT KEPT.  assay's kernel plus the overlay port and M/import.  Trigger 1 is unmeasured and predicted against the flip, trigger 2 holds as code and fails as a kernel choice (section 6).
- Q1 REOPENED.  The installed v6.1.0 executor is a 64-bit VM with default target riscv64im (VERIFIED S2:24-25).  attest emits RV64IM ELF64 for that executor.  The RV32IM text of R3, 3.5 and Q1 is the reopened part.  The alternative, a pinned RV32IM SP1 v4.x, is a USER install and is not proposed.
- Q2 DEFAULT KEPT.  The S2 harness and an OCaml RV64IM twin, cycles from both, prove once per milestone.
- Q3 DEFAULT KEPT.  Cycles, informational at M0, binding at M1.
- Q4 DEFAULT KEPT.  The Host sum of section 9, closed first-order effect programs, no ZK shape.  The constructors are extern globals, which is the framework reading of the default.
- Q5 REOPENED in part.  Twin corpora at M0 as the default says.  The import oracle runs in count mode at M0 (no kernel check) and in check mode at M1.  Reason: the four counts are the cheapest parity number and the count-mode run needs only M/import, which is carried unchanged.
- Q6 DEFAULT KEPT.  Direct encoding and no optimizer at M0, memoised conversion and per-definition fuel at M1.  The denominator excludes the clang step on the Bend side (section 3), which is a Stage 0c freeze decision and not a reopen.
- Q7 attest, `.att`, driver `attest`.

## 12.  M0 stages, gates and milestones

| Stage | Content | Exit gate |
|---|---|---|
| 0 (USER) | `diskfree --apply`, Bend 2 install, `sp1up` check, harness crate fetch, submodule checkout, DENOMINATORS frozen | `shasum -c DENOMINATORS.sha256` |
| A kernel | assay lib carried, overlay ported, R0 gates, ACCEPT and REFUSE corpora | BUILD, CARRY, R0-COUNT, R0-AUDIT, SUITE-KERNEL, AXIOMS, TWIN-LEAN (48 rows agree with `lean`) |
| B erase | Word literals, extern table, Host as externs | TRACE-ERASURE on the ACCEPT corpus, EXTERNS (`--externs` lists exactly the Host constructors used) |
| C lower and encode | rv64 IR, ELF64 encoder, the 96-byte fixture | ELF-ACCEPTED, ENCODE-DIFF (our bytes equal clang `--target=riscv64` reference objects for 14 instruction fixtures), TRUSTED-LINES |
| D execute | harness crate, OCaml twin, differential runner | EXEC-DIFF on every corpus program, CYCLE-BUDGET printed and pinned |
| E effects | Read, Commit, Halt end to end, SHA-256 runtime | EXEC-DIFF with public values, PRELUDE-CHECKED count mode |
| F freeze | frozen corpus, compile time, ratio ladder | M0-TIME, M0-RATIO rungs, WALKS, PROVE-ONCE |
M0-RATIO ladder: rung 1 the 8 twins compile, rung 2 medians printed both sides, rung 3 ratio per 1,000 lines printed, rung 4 ratio at most 2.0 (informational), rung 5 ratio at most 1.0 (M1 binding).  Each rung prints the Bend 2 denominator hash beside the attest median.
Milestones, one measurable gate each: M0 EXEC-DIFF green on the full corpus with TRACE-ERASURE byte-identical.  M1 PRELUDE-CHECKED check mode with NAME_ONLY=0 and UNMAPPED=0 and M0-RATIO rung 5 at most 1.0, CYCLE-BUDGET binding.  M2 the precompile constructors (Keccak, Sha256, U256Mul, Bn254, Secp256k1) with EXEC-DIFF and a pinned cycle table.  M3 PROVE-ONCE on the largest corpus program with `verify` green and the wall-clock and peak memory recorded.

## 13.  Trusted base and disclosure

Commands: `attest check --axioms FILE` prints exactly `Quot.sound` on the corpus.  `attest check --externs FILE` prints the Host constructors used.  `attest build --passes FILE` prints the seven stages and `WALKS` per definition.  `dev/trusted-lines.sh` prints kernel, lower and encoder line counts against the bounds.  `shasum -c DENOMINATORS.sha256` for DENOMINATORS.
Bounds P3 commits to: kernel (A/lib plus the overlay) 7,000 lines, the brief's 3,000 is a kanon-era number neither candidate meets (assay 6,193, VERIFIED S1:64, mechanism-lang 7,938 to 11,320, VERIFIED S1 line 233).  lower 1,000.  encode 800 (elf64 plus rv64im).  emulator twin 800, a gate tool outside the trusted base.  harness crate 100 lines of Rust.  Total trusted 8,800 with the twin outside.  A bound that moves up is a finding, never a silent edit.

## 14.  The three weakest points

1. No R2 number exists.  Neither Bend 2 nor the mechanism-lang kernel has been run here, so section 3 is design and section 6 is prediction plus one assay median.  Stage 0 and one bench settle both.
2. The ISA reopen rests on S2's reading of v6.1.0 (64-bit VM) and on a BELIEVED row that RV32 ELFs fail there.  If a riscv32im guest executes, the brief's RV32IM pin can stand and the lower stage shrinks.
3. The parity spine is carried code with UNMEASURED counts.  PRELUDE-CHECKED has never printed NAME_AND_TYPE, NAME_ONLY, UNMAPPED or NEVER on any build, and translate.ml's coverage of the R0 rows is BELIEVED until the first count-mode run.
