# kan-sp1-lang proposal P2: target-first and speed-first

Author P2, 2026-09-21.  Lens: SP1 and Bend 2.  Caps: 7 findings, 56 agents.  A = /Users/oobi/Documents/kan-sp1-lang-assay-pin.  M = /Users/oobi/Documents/kan-sp1-lang-mech-pin.  V = /Users/oobi/Documents/mechanism-lang/vendor/veil.  S1, S2, S3 = the three dossiers.  Every claim is VERIFIED (command, path:line or URL) or BELIEVED (with what settles it).

## 0.  Name, extension, driver, thesis

Name: vouch.  Extension: `.vch`.  Driver: `vouch`.  Reason: the guest vouches for its own run, and the SP1 proof is the receipt of that run.  The word is one syllable, it is not a verb assay or trice already use, and it reads well as a gate prefix (`VOUCH-EXEC-DIFF`).  Collision check: BELIEVED clean on this machine.  Settle: `command -v vouch` after Stage 0.

Thesis: every line that the compiler reads costs one bounded set of walks, and every instruction the guest runs costs one cycle.  The design fixes both budgets before the surface.  The kernel is assay's kernel carried byte-exact (provisional, section 6).  The pipeline is five walks per definition and no optimizer.  The encoder writes the ELF bytes itself.  The cost model is the SP1 executor's instruction count.  Proof terms vanish at erase by the quantity rules, so they never touch the bytes.  The Kan kernel stays two formers on the closed shape grammar, and ZK, cycles, syscalls and the allocator are gate facts on the far side of erase.

## 1.  R0 honesty

The kernel is assay's kernel at eebe37e.  VERIFIED, A/lib/term.ml:49-50 has `Lan of t Shape.t * t` and `Ran of t Shape.t * t` as the only formers, and A/lib/term.ml:63 pins `formers = [ "Lan"; "Ran" ]`.  VERIFIED, A/lib/shape.ml:10-15 is the closed grammar `SPi | SColl | SPar | SMu | SNu` and A/lib/shape.ml:19 pins the five names.  VERIFIED, S1 section 5 ran `A/dev/r0-count.sh` (R0-COUNT OK) and `A/dev/r0-audit.sh` (R0-AUDIT OK) on the built pin, and `assay.exe spec-count` prints `formers 2: Lan Ran`, `shapes declared 5`, `shapes admitted 3: SPi SColl SMu`.

This proposal adds no former and no shape.  The term sum, the shape sum and `formers` are carried unchanged.  R0-COUNT and R0-AUDIT run as the first two gates of every stage.

The smuggling table.  Each row says where the target fact lives and why it is not a former or a shape.

| Fact | Where it lives | Former or shape |
|---|---|---|
| `Host` | one library inductive, `Lan` over a discrete collapse (`SColl 8`), declared in the prelude of `.vch`.  The kernel checks it as any inductive | no.  A real `Lan_SColl` construction |
| the `extern` kind | a lowering table keyed by global name, `lower/host_table.ml`, outside `lib/` | no.  Framework, like assay's selector table |
| syscalls and precompiles | rows of that table, one ecall sequence per `Host` constructor | no.  Emitted bytes |
| cycles | a number the executor and the emulator print, pinned by CYCLE-BUDGET | no.  A gate value |
| the bump allocator | a runtime stub the encoder prepends, `encode/runtime.ml` | no.  Emitted bytes |
| the RV64 calling convention | a rule of `lower` | no.  Framework |
| `Word32`, `Word64`, `U256`, `Bytes` literals | literal accelerators, an extension of `Literal.t` (A/lib/literal.ml:5-7 has `LString | LInt` today) with a conversion fast path | no.  Ambient framework by brief R0 lines 55-56 and 4.1 |
| bound proofs | `Prop` globals at quantity Zero, for example `addLt` | no.  Erased terms |
| ZK | nowhere.  The whole ELF is the guest.  No `SZk` (V/lib/shape.ml:16 has it, we never carry it) | no |

Term walk against the smuggling attack.  A `Host` program is `Ran_pi` over a `Lan_SColl` value with a continuation.  The checker sees `Lan (SColl 8, _)` and its `In` and `Elim` schema forms only.  The `extern` attribute is read by `lower`, after `erase`, from a table that cannot add a constructor to `Term.t` (the table is a `(string * ecall_seq) list` and `Term.t` is closed).  The R0-AUDIT walk over `Term.t` therefore cannot find a third former no matter what the table holds.  What R0 does NOT rest on in this design: the two shapes assay declares but does not admit.  See section 8.

## 2.  Lean 4 strength credibility

Honest position: strength is a Lean-class kernel plus expressiveness parity, and at M0 this proposal spends its budget on the target and the ratio, so several Lean 4 rows move to M1 and M2.  The twin corpora and the oracle are designed now, and every deferred row is listed.

ACCEPT corpus at M0 (each row a `.lean` file and a `.vch` twin, `lean` as the oracle, VERIFIED shape from brief R1): `nat-add-comm` (a Pi over an inductive with structural recursion), `list-map-length` (mu with a parameter), `pair-swap` (Sigma and eta on pairs), `sum-elim` (discrete collapse, variants), `record-proj` (Ran over a discrete collapse), `vec-head` (an indexed family, fibered `mu`), `prop-irrel` (two proofs of the same `Prop` are convertible), `subsingleton-elim` (large elimination of a subsingleton), `word64-add-lt` (a bound proof then an unchecked add), `bytes-keccak-commit` (a `Host` program).  Ten rows.

REFUSE corpus at M0: `nonpositive-mu` (an occurrence to the left of an arrow, refused by A/lib/positivity.ml), `nonstructural-rec` (refused by A/lib/totality.ml), `proof-in-runtime` (a quantity-Zero binder used at One, refused by A/lib/quantity.ml), `wrong-index` (a family index mismatch), `large-elim-prop` (a non-subsingleton `Prop` eliminated into `Type`), `host-in-kernel` (a `Host` value in a type).  Six rows.  Each `.lean` twin must fail under `lean` as well, or the row is dropped.

Rows deferred to reach the ratio (each is a gate failure if listed in the corpus, so none is listed at M0): universe level variables and `imax` (A/lib/level.ml is `type t = int`, 11 lines, VERIFIED S1 section 7).  `Quot` (`SPar` is declared but not admitted, VERIFIED S1 section 5).  Coinductives (`SNu` not admitted).  Well-founded recursion (A/lib/totality.ml is structural, BELIEVED from S1 section 6, settle by reading the module).  Mutual and nested inductives (BELIEVED unsupported, settle: `rg -n mutual A/lib/positivity.ml`).  Instance search, `Auto`, `do` notation (brief 4.4 excludes them at M0).  Definitional eta for structures (BELIEVED absent from A/lib/conv.ml, settle: `rg -n eta A/lib/conv.ml`).  REFUSE rows deferred: `type-in-type` and level cycles (need levels), `quot-sound-misuse` (needs `Quot`).

Import oracle scope: at M1 the `import/` tree of M (1,543 lines in 10 modules, VERIFIED S1 section 7) is copied as a sibling directory, not a kernel overlay.  Its `levels.ml` parses `max` and `imax` (S1 section 7), which our M0 kernel cannot represent, so at M1 the level overlay (267 lines, five files, VERIFIED S1 section 7) is ported first and the PRELUDE-CHECKED gate runs second.  The gate prints `covered%` beside `NEVER` and fails on `NAME_ONLY > 0` or `UNMAPPED > 0` (brief R1).  Commit: M1 exit needs `NAME_AND_TYPE >= 40%` of external=2,477 with `NEVER` listed by name.  M2 exit needs 70%.

## 3.  Bend 2 speed credibility

Denominator commands (from S2 section 7).  `command -v bend` prints nothing, VERIFIED S2.  The install is a USER step: `curl -fsSL https://bend-lang.com/install.sh | sh`, VERIFIED S2 from the Bend README line 113.  The check and compile subcommands are BELIEVED: `bend check FILE.bend` and a compile subcommand that emits the one C file (VERIFIED S3 from GUIDE.md:584-585 that Bend 2 emits one C file and clang compiles it).  Settle: `bend --help` after the install.  Denominator rows, the assay recipe copied in shape (VERIFIED S2, A/dev/denominator.sh:1-30, :139-153, :171): `bend_check_ms_per_kloc` = the check command on the twin, `bend_compile_ms_per_kloc` = check plus the compile command with clang EXCLUDED (clang is not Bend's checker, and our path has no clang).  One warm run, five timed runs, a fresh scratch directory per run, the median, `uptime` printed beside, single core.  Frozen in `dev/denominators.json` with `version`, `stage`, `date` keys and checked by `shasum -c DENOMINATORS.sha256` at Stage 0c.

Numerator commands: `vouch check FILE.vch` (elaborate + check) against `bend_check_ms_per_kloc`, and `vouch build FILE.vch` (all five walks to the ELF) against `bend_compile_ms_per_kloc`.  Ratio = numerator ms per kloc / denominator ms per kloc.  Two ratios, both printed.  M0-RATIO reports the larger.

Twin corpus: the ten ACCEPT rows of section 2 written in Bend 2 too (`.bend`), so each program has three twins, `.lean`, `.bend`, `.vch`.  Bend 2 has `All`, `Adt`, `Ctr`, `Mat`, `Eql` (VERIFIED S3 from bend.lean:197), so every ACCEPT row maps.  The `Host` row maps to Bend I/O calls and is counted for lines but not for cycles.  Lines are counted the same way on both sides: non-blank, non-comment.

Walks per definition, bounded by construction: elaborate (A/surface/elab.ml:1171), check (A/lib/check.ml:302), erase (A/lib/erase.ml:1427), lower, encode.  Five.  VERIFIED S1 section 6 counts the same five in assay plus a sixth text walk `Contract.lower` (A/emit/contract.ml:888) that this design drops.  `vouch --passes FILE.vch` prints one line per definition with the five walk names and the node count each walk visited.  A walk may not re-enter a definition.  The check walk carries a per-definition fuel counter at M1 (Q6); at M0 the counter is printed and never binding.  There is no optimizer and no peephole pass.  `lower` is one syntax-directed function from `Eterm.ktm` to the IR.  `encode` is one fold over the IR that appends bytes.

Numbers I commit to.  SUITE-KERNEL: assay measured `median_ms=421.774` over 7 runs (VERIFIED S1 section 3, `RUNS=7 zsh -f A/dev/bench.sh SUITE-KERNEL ...`).  Commit: the carried kernel suite stays under 480 ms median after the port, or the port is wrong.  M0-RATIO: at most 2.0, informational.  M1: at most 1.0, binding.  M2: at most 1.0 on a corpus three times larger.  M3: at most 1.0 with the level overlay on.  M0-TIME: the ten-row corpus builds to ten ELFs in under 3 s wall on one core.

The 1.956 risk.  assay's frozen ratio is 1.956099 against a bound of 1.0 (VERIFIED brief lines 100-101, 181-182).  That ratio measures assay's whole path, which includes the sixth text walk and the EVM listing.  My answer has four parts.  First, the sixth walk is gone.  Second, the ELF encoder writes bytes once and never regenerates a listing in the timed path (`--listing` is a separate command).  Third, the denominator here is Bend 2's checker, which also runs a termination check (VERIFIED S3, README:223), so the twin is not a trivial parser.  Fourth, if M1 still prints above 1.0, the lever is memoised conversion over hashconsed terms (Q6, M1), and the cut is honest: the M1 exit stays OPEN, as assay's is, and the number is printed.  The Bend 2 checker is Haskell (BELIEVED S2 section 7, settle by the language mix on GitHub), so the 1.0 bound is a real risk, not a formality.  I do not promise 1.0 at M0.

## 4.  SP1 target fidelity

ISA.  The installed toolchain is `cargo-prove sp1 (d454975 2026-04-11)`, tag v6.1.0, VERIFIED S2 section 1.  The default target is `riscv64im-succinct-zkvm-elf` (VERIFIED S2, crates/build/src/lib.rs:16), `_start` runs `ld sp, 0(sp)` and the executor memory image is `HashMap<u64, u64>` (VERIFIED S2, entrypoint lib.rs:238-240, program.rs:38-44).  So the guest ISA is RV64IM, not RV32IM.  This proposal targets RV64IM.  The `im` extensions only, every instruction 4 bytes (VERIFIED S2, consts.rs:22).  RV32IM ELFs on this executor are BELIEVED unsupported (S2 section 2, settle with a riscv32im hello guest).  The RV32 wording of brief R3 and Q2 is therefore REOPENED in section 11.

Encodings.  The RV32 rows of S2 section 8 (add, addi, lw, sw, beq, lui, auipc, jal, jalr, mul, mulh, div, rem, ecall) are VERIFIED against Homebrew clang and are valid RV64 words.  The 64-bit loads and stores (`ld`, `sd`), `addiw` and the W forms (opcode 0111011 and 0011011) are BELIEVED from the RISC-V spec (S2 section 8 note).  Settle at Stage C: `/opt/homebrew/opt/llvm/bin/clang --target=riscv64-unknown-elf -march=rv64im -mno-relax -c ref64.s` and `llvm-objdump -d`, gate ENC-XCHECK.  clang is a gate tool only, never in the path.

ELF layout.  The executor accepts ELF32 or ELF64, little endian, `e_machine` 243, `e_type` 2 (VERIFIED S2, elf.rs:81-89).  Only PT_LOAD segments load, at most 256 program headers, no W+X segment, every segment at or above `STACK_TOP = 0x78000000`, entry a multiple of 4, no section table read, no symbols needed (VERIFIED S2 section 4).  The encoder writes ELF64 (the class `cargo prove build` emits for riscv64im, BELIEVED, settle: `llvm-readelf -h` on the hello guest) with two PT_LOAD segments: text at 0x78000000 with PF_R|PF_X, data and bump heap at 0x78100000 with PF_R|PF_W, and `e_entry` = the first text word.  The stack grows down from a fixed top inside the data segment.  Our `_start` (the runtime stub) sets `sp`, sets the bump pointer, calls `main`, hashes the committed bytes, and halts.

Public values.  The guest writes public bytes to fd 13 through WRITE, then at halt emits 8 COMMIT ecalls with the SHA-256 words, 8 COMMIT_DEFERRED_PROOFS with a1 = 0, then HALT (VERIFIED S2, halt.rs:20-60).  The stub computes SHA-256 with SHA_EXTEND and SHA_COMPRESS, so the runtime stub holds a SHA-256 padding loop and two ecalls per block.  This is the one piece of fixed guest code the encoder trusts.

Executor harness: S2 section 5, `sp1-exec-harness`, `sp1-sdk = "=6.1.0"`, `ProverClient::from_env().execute(Elf::from(bytes), stdin).run()` returning public values and an `ExecutionReport` (VERIFIED S2 for `blocking::ProverClient`, `.run()`, `total_instruction_count()`, `total_syscall_count()`, `exit_code`; BELIEVED for `Elf::from(Vec<u8>)`, `write_slice`, `as_slice`, settle by `symx` on the crate).  Output: one JSON line `{public_values_hex, cycles, syscalls, exit_code}`.  Pinned in `harness/` with a lockfile.  Build with `cargocho build --manifest-path harness/Cargo.toml -j 2`.  The emulator twin `bin/rv64emu.ml` prints the same JSON line.  EXEC-DIFF compares the lines byte for byte.  Proving: once per milestone exit, `prove` then `verify` on the smallest corpus program, with `/usr/bin/time -l`, the published minimum is 16 GB memory for a core proof (VERIFIED S2 section 6), so PROVE-ONCE may print SKIPPED with the memory reading when the machine is under the floor.

## 5.  Proof-erasure soundness

The argument runs from three rules, not from the gate.  Rule 1: `Quantity.mul` sends any `Zero` factor to `Zero` (VERIFIED A/lib/quantity.ml:14-22, the `Zero, _` and `_, Zero` arms).  Rule 2: `quantity_runtime q = not (Quantity.equal q Quantity.Zero)` (VERIFIED A/lib/erase.ml:102-104), so a `Zero` binder is never a runtime parameter and its argument is never erased into `ktm`.  Rule 3: proofs and types live at `Zero` (brief 4.1, and `proof_free` :173, `runtime_ty` :182, `point_runtime` :191 decide per binder, VERIFIED S1 section 6).  Hence the erased program is a function of the quantity-One skeleton alone.  `lower` reads `ktm` only and `encode` reads the IR only.  So the bytes are `encode (lower (erase p))`, and `erase p` cannot mention a proof term.

TRACE-ERASURE, made precise.  Run 1 builds the program.  Run 2 builds the same source under `--trust-proofs`, which replaces every quantity-Zero argument by an opaque hole and skips its check.  The two ELFs must be byte-identical.  This shows the bytes depend on the One skeleton and not on the proof content.  Proof-supplied arithmetic is consistent with this: `addLt : (a b : Word64) -> (p : a + b < 2^64) -> Word64` is a distinct global whose erasure is the bare `add`, and its choice is part of the One skeleton.  The proof `p` decides nothing at lower time.  The precedent is assay Stage F (brief 3.2 and 4.6), BELIEVED to use the same two-run form, settle: `rg -n TRACE-ERASURE A/dev/gates.sh`.

What the rules do not cover: a literal accelerator that chooses an instruction from a TYPE (Word32 versus Word64).  The type is One-relevant data of the global, not a proof, so the argument holds, but the AXIOMS and R0-AUDIT gates must confirm that no accelerator reads a `Prop`.  Gate ACCEL-TYPES lists every accelerator with the type it reads.

## 6.  Kernel-choice justification

S1 measured assay's shared suite at `median_ms=421.774 min_ms=334.754 max_ms=582.340 runs=7` (VERIFIED S1 section 3).  S1 left mechanism-lang UNMEASURED, blocked on Stage 0 user step 5 (the veil submodule is not checked out, `ls M/vendor/veil | wc -l` prints 0, VERIFIED S1 section 1).  The Q0 flip trigger needs mechanism-lang at least 2x faster.  No measurement exists, so the trigger is not met and the choice is PROVISIONAL.

Argument from lib line counts and conv.ml.  A/lib is 6,193 lines in 22 files and the trusted kernel is 3,997 lines under a 4,000 bound (VERIFIED, `wc -l A/lib/*.ml` in my probe and S1 section 4, `zsh -f A/dev/trusted-lines.sh` printed `kernel=3997 want=3997 bound=4000`).  M's active kernel is 3,744 own lines plus veil's 7,576, linked to about 7,938 (BELIEVED S1 section 4, settle after the checkout) against a 3,000 bound that M's README says it already exceeds (VERIFIED M/README.md:47-48).  conv.ml: A is 396 lines, M is 404 (veil 396 plus a 36-line diff), and M's check.ml:43 runs `Level_scope.check` on every checked term plus `Level.equal_budget` and `Level.le_budget` at every universe comparison (VERIFIED S1 section 7).  That is one extra walk per term and one solver call per comparison on a speed-first path.  veil also carries `SZk`, `SFhc`, `SMpc` (VERIFIED V/lib/shape.ml:16-19 per S1) and 35 host rule rows we would delete.  Fewer lines, fewer walks, no shapes to delete: assay.  The choice flips if S1's mech median lands under 211 ms on the same 77 fixtures.

## 7.  Staging realism

M0 is six stages in the assay pattern, each a workflow with gates and a mutation.  Stage 0 is USER work (brief lines 517-526): `diskfree --apply` (disk is at 23 GiB free, VERIFIED `df -g` in my probe), the Bend 2 install, the hello guest build, the veil checkout.  Stages A to F below carry the assay gate scripts (`dev/stage-a-gates.py`, `dev/trusted-lines.sh`, `dev/r0-count.sh`, `dev/r0-audit.sh`, `dev/bench.sh`, `dev/denominator.sh`, all VERIFIED present by S1) by copy then delta.  Weeks: A one, B one, C two, D one, E one, F one.  Seven weeks to the M0 exit.

## 8.  The R0 shape table

| Shape | Lan role | Ran role | Lean 4 feature | Guest lowering | Real or naming at eebe37e | Divergence gate |
|---|---|---|---|---|---|---|
| `SPi` | Sigma | Pi | dependent pairs and functions | Sigma = 2-word heap node.  Pi = closure node (`KClos`) or a direct `jal` when the callee is a known global | real, admitted | EXEC-DIFF on `pair-swap`, `nat-add-comm` |
| `SColl n` | variants | records | enumerations, structures | tag word plus fields (`KTag`), field block (`KStruct`), `KCase` = tag load plus a branch chain | real, admitted | EXEC-DIFF on `sum-elim`, `record-proj` |
| `SPar` | `Quot` | equalizer subtypes | `Quot`, subtypes | `Quot.mk` = identity on the carrier, the subtype = the carrier | declared, NOT admitted (`shapes admitted 3`).  A library naming today.  R0 rests on the closed grammar plus R0-AUDIT, and on M2 admitting `SPar` in the kernel | AXIOMS lists `Quot.sound` from M2 |
| `SMu P` | initial algebras | none | inductive types and families | tagged heap nodes from `mu_layout` (A/lib/erase.ml:413), recursion = structural loop through `KCase` | real, admitted | EXEC-DIFF on `list-map-length`, `vec-head` |
| `SNu P` | none | terminal coalgebras | coinductives | `KDelay` and `KForce` thunk nodes | declared, NOT admitted.  A naming today, M3 admits it | EXEC-DIFF on a stream row at M3 |

The divergence gate in every row is the same fact: the emitted representation of a construction is checked by running the program on two independent executors and comparing public values and cycles.  A representation that diverges from the kernel definition shows up as a public-values mismatch on the row that exercises it, because each ACCEPT row commits its result bytes.

## 9.  The Host sum roster

`Host` is the prelude inductive `Lan (SColl 8)`.  Every code is VERIFIED from S2 section 3 (both `syscalls/mod.rs` and `syscall_code.rs` at d454975).  The register convention is VERIFIED S2 section 3: code in `t0`, arguments in `a0` and `a1`, `a2` for WRITE, HINT_LEN returns in `t0`.  The precompile pointer convention (`a0` = first operand, `a1` = second) is BELIEVED, settle: `crates/zkvm/entrypoint/src/syscalls/keccak_permute.rs`.  The ecall sequence is `li t0, CODE` (lui plus addi when the code exceeds 12 bits), moves into `a0`, `a1`, `a2`, then `ecall`.

| Constructor | Syscall and code | Register sequence | Emitted ecalls |
|---|---|---|---|
| `Read : Bytes` | HINT_LEN 0xF0, HINT_READ 0xF1 | `t0 = 0xF0; ecall; len = t0; a0 = bump(len); a1 = len; t0 = 0xF1; ecall` | 2 |
| `Commit : Bytes -> Host` | WRITE 0x2 with fd 13 | `t0 = 2; a0 = 13; a1 = ptr; a2 = len; ecall` | 1 |
| `Halt : Word32 -> Host` | COMMIT 0x10 x8, COMMIT_DEFERRED_PROOFS 0x1A x8, HALT 0x0 | the stub: 8 times `a0 = i; a1 = digest[i]; ecall`, 8 times `a1 = 0; ecall`, then `a0 = code; ecall` | 17 |
| `Keccak : Bytes -> Bytes` | KECCAK_PERMUTE 0x00010109 | pad in software, then per block `a0 = state; ecall` | 1 per block |
| `Sha256 : Bytes -> Bytes` | SHA_EXTEND 0x00300105, SHA_COMPRESS 0x00010106 | per block `a0 = w; ecall`, then `a0 = state; a1 = w; ecall` | 2 per block |
| `U256Mul : U256 -> U256 -> U256 -> U256` | UINT256_MUL 0x0001011D | `a0 = x; a1 = y_and_modulus; ecall` | 1 |
| `Bn254 : Op -> Host` | BN254_ADD 0x0001010E, BN254_DOUBLE 0x0000010F, BN254_FP_ADD 0x00010126, FP_SUB 0x00010127, FP_MUL 0x00010128 | `a0 = p; a1 = q; ecall` | 1 |
| `Secp256k1 : Op -> Host` | SECP256K1_ADD 0x0001010A, DOUBLE 0x0000010B, DECOMPRESS 0x0000010C | `a0 = p; a1 = q; ecall` | 1 |

Trap story on the guest.  There is no trap instruction in the emitted code.  RV64 integer division by zero returns all ones and does not trap (BELIEVED from the RISC-V unprivileged spec, settle: https://riscv.org/specifications/ratified/ chapter M).  Every failure the language can express ends in `Halt` with a nonzero exit code, which the executor reports as `exit_code` (VERIFIED S2, report.rs:32).  Where a bound proof is in scope, `lower` emits the bare instruction.  Where none is, the source model refuses the program at check time (`Word64` arithmetic without a proof does not typecheck), so the guest never carries a runtime check.  An out-of-range memory access is an executor error, not a guest trap, and EXEC-DIFF treats it as a FAIL row.  The emulator twin returns the same exit code and a reason string.

## 10.  The pipeline, module by module

`parse -> elaborate -> check -> erase -> lower -> encode -> execute`, brief 4.4.  Line counts VERIFIED from S1 section 10 and my `wc -l A/lib/*.ml`.

| Stage | Modules | Lines | Verdict |
|---|---|---|---|
| parse, elaborate | surface/lexer, token, parser, syntax, elab | 183, 143, 620, 302, 1,179 | carry |
| check | lib/term, shape, spec_count, check, conv, eval, rules, value, global, order, prim, error, pp, quantity, totality, positivity, literal, bignum | 133, 60, 62, 538, 396, 297, 1,481, 137, 130, 510, 139, 82, 102, 158, 146, 118, 14, 51 | carry, byte-exact |
| check | lib/level | 11 | adapt at M1 (the 267-line overlay from M) |
| check | lib/budget | 27 | adapt, poll to counter |
| erase | lib/erase, eterm | 1,484, 117 | adapt, `repr` :17-22 becomes RV64 word and heap reprs, `repr_of` :249 and `mu_layout` :413 follow |
| lower | emit/emit | 493 | rewrite as `lower/lower.ml`, `ktm` to an RV64IM IR |
| lower | emit/contract, recognize, model, abi/abi, layout, keccak/keccak | 894, 254, 143, 35, 8, 89 | drop (assay's keccak moves to the emulator host side) |
| encode | asm/asm, listing | 238, 54 | rewrite as `encode/rv64.ml`, `encode/elf.ml`, `encode/runtime.ml`, `encode/listing.ml` |
| execute | bin/assay, differential, trace, evm/diff.py | 221, 88, 117, 272 | adapt, `compile` :71 gains `--passes`, diff.py becomes `dev/exec-diff.py` over the harness and the emulator |
| oracle | new `bin/rv64emu.ml`, `harness/` | 0 today | new, bounds in section 13 |

## 11.  Answers to Q0 to Q7

- Q0 kernel base: DEFAULT KEPT, assay, PROVISIONAL.  Reason: S1's assay median is 421.774 ms and the mech side is UNMEASURED, so the flip trigger is unmet by absence.  The judge should hold the flip open until Stage 0 step 5 lands and S1's command reruns on M.
- Q1 target contract: DEFAULT KEPT in letter, REOPENED in wording.  The default says "ISA per S2" and S2 pins RV64IM at v6.1.0 (crates/build/src/lib.rs:16).  The brief's R3 text says RV32IM and ELF32.  I take the installed executor as the contract: RV64IM, ELF64 emitted by our encoder, no external tool.  Reason: a v4.x RV32 pin would be a second USER install and a stale target.
- Q2 execution oracle: DEFAULT KEPT for the harness, REOPENED for the twin's ISA.  The OCaml emulator is RV64IM, about 700 lines, house rules.  Cycles printed by both.  Proving once per milestone exit.
- Q3 cost model: DEFAULT KEPT.  Cycles = `ExecutionReport::total_instruction_count()` (VERIFIED S2, report.rs:40-41).  Precompile chip cost is not in that count (BELIEVED, settle: report.rs and the syscall chips), so CYCLE-BUDGET prints `cycles` and `syscalls` side by side.  Informational at M0, binding at M1.
- Q4 host boundary: DEFAULT KEPT.  `Host` as in section 9.  No ZK shape.  One addition inside the default: the SHA-256 commit path is part of `Halt`, because the executor requires it (S2 finding 4).
- Q5 R1 oracle: DEFAULT KEPT.  Twin corpora at M0 (section 2).  lean4export import and PRELUDE-CHECKED at M1, after the level overlay port.
- Q6 denominator and levers: DEFAULT KEPT.  Ratio frozen at Stage 0c.  M0 levers: direct encoding, no optimizer, the sixth walk dropped.  M1 levers: memoised conversion over hashconsed terms, per-definition fuel.
- Q7 name: vouch, `.vch`, driver `vouch`.

## 12.  M0 stages, gates and milestones

| Stage | Work | Gates (the 4.6 battery plus additions) |
|---|---|---|
| 0 (USER) | disk, Bend 2, hello guest, veil checkout, denominators frozen | DENOMINATORS, a hello guest ELF read by `llvm-readelf -h` |
| A | copy A into `vouch/`, rename the driver, drop emit/contract, abi, keccak guest code, add `--passes` | BUILD (`zsh -f dev/dune.sh build -j 2`), CARRY, R0-COUNT, R0-AUDIT, SUITE-KERNEL (under 480 ms), TRUSTED-LINES, AXIOMS (empty list at M0) |
| B | `lower/`: RV64IM IR, frame slots, the calling convention, `host_table.ml` | BUILD, CARRY, R0-*, LOWER-DET (the same `ktm` lowers to the same IR twice), PASSES (exactly 5 walks per definition) |
| C | `encode/`: instruction words, ELF64 writer, runtime stub, listing.  `bin/rv64emu.ml` | ENC-XCHECK (clang reference objects, 40 instruction rows), ELF-ACCEPTED (harness loads every corpus ELF, exit 0), EMU-ACCEPTED |
| D | `harness/` on sp1-sdk 6.1.0, `dev/exec-diff.py`, one hand-encoded reference ELF `reference/hello.elf` | EXEC-DIFF (harness = emulator on public values, cycles, exit code), REF-BYTES (`cmp` of our hello ELF and the hand-encoded one) |
| E | `Host` programs: `Read`, `Commit`, `Halt`, `Keccak`, `Sha256`, `U256Mul` | EXEC-DIFF over the six effect rows, CYCLE-BUDGET printed, ACCEL-TYPES |
| F | frozen corpus of 16 rows (10 ACCEPT, 6 REFUSE), Bend and Lean twins, time and ratio | TRACE-ERASURE, CYCLE-BUDGET pinned, M0-TIME (under 3 s), M0-RATIO (under 2.0 informational), LEAN-TWINS (`lean` accepts 10, rejects 6), PROVE-ONCE |

Dropped from 4.6 at M0: nothing.  Added: LOWER-DET, PASSES, ENC-XCHECK, EMU-ACCEPTED, REF-BYTES, ACCEL-TYPES, LEAN-TWINS.

Milestones, one measurable gate each.  M0 exit: EXEC-DIFF green on all 16 rows with M0-RATIO printed under 2.0 and PROVE-ONCE run or SKIPPED with the memory reading.  M1 exit: M0-RATIO under 1.0 binding on both ratio rows, CYCLE-BUDGET binding (no row above its pin), PRELUDE-CHECKED at 40% NAME_AND_TYPE with the level overlay ported.  M2 exit: `SPar` admitted, AXIOMS prints exactly `Quot.sound`, the corpus at 48 rows, ratio still under 1.0, PRELUDE-CHECKED at 70%.  M3 exit: `SNu` admitted, the full precompile roster (BN254 FP2, BLS12381, SECP256R1) in `Host`, PROVE-ONCE on three programs.

M0-RATIO ladder: rung 1 = the numerator printed with no denominator (Stage A, denominators absent).  Rung 2 = both ratios printed, informational (Stage F).  Rung 3 = under 2.0 (M0 exit).  Rung 4 = under 1.0 binding (M1 exit).

## 13.  The trusted base

Disclosure commands: `vouch --axioms FILE.vch` prints the tracked postulates used (empty on the M0 corpus, `Quot.sound` from M2).  `vouch --passes FILE.vch` prints the five walks per definition with node counts.  `zsh -f dev/trusted-lines.sh` prints one row per trusted directory and FAILs above a bound.  `shasum -c DENOMINATORS.sha256` checks the frozen Bend 2 rows.

Line bounds I commit to: kernel (lib/) 4,000, assay stands at 3,997 (VERIFIED S1 section 4).  lower/ 900.  encode/rv64 600.  encode/elf 200.  encode/runtime 300.  encode/listing 250.  Non-kernel trusted total 2,250.  The emulator (700) and the harness (120) are oracles, listed by TRUSTED-LINES but outside the trusted total, because a wrong oracle fails EXEC-DIFF loudly instead of passing a wrong program.  The trusted base also includes the SP1 executor at d454975 and the RISC-V spec, neither of which we verify.

## 14.  The three weakest points

1. The kernel choice is provisional.  S1 could not build mechanism-lang, so the flip trigger rests on line counts and one seam read.  A mech median under 211 ms on the same 77 fixtures flips it, and the whole section 10 table shifts to the V rows of S1 section 10.
2. The ISA is RV64IM and the brief's RV32 rows are stale.  My ELF64 choice, the W-form encodings, the precompile pointer convention and the ELF class of the hello guest are BELIEVED until Stage 0 step 3 and Stage C ENC-XCHECK run.  If the executor rejects ELF64 from a hand encoder for a reason S2 did not read, Stage C slips a week.
3. Strength is deferred to reach the ratio.  Levels, `Quot`, coinductives and well-founded recursion are M1 to M3 rows, so at M0 this language is weaker than Lean 4 on exactly those rows, and the ACCEPT corpus is chosen to avoid them.  The Bend 2 checker is a Haskell program with a termination check, and no Bend 2 number exists on this machine, so the 1.0 bound may fail at M1 even with the sixth walk gone, and the M1 exit would then stay OPEN as assay's does.
