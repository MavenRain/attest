# kan-sp1-lang attack 2: P2 (vouch), target-first and speed-first

Attacker, 2026-09-21.  A = /Users/oobi/Documents/kan-sp1-lang-assay-pin.  P2 = /Users/oobi/Documents/kan-sp1-lang-proposal-2.md (P2:N = line N).  S1, S2, S3 = the dossiers.  P1 was absent on disk at run time.  P3 was read (147 lines).  Probe transcripts T1 to T6 are at the tail.  Findings are ranked by lethality.

## 1.  R2-SPEED (fatal): the byte-exact checker keeps the 1.956 deficit and no M0 lever touches it

- P2:9 carries assay's kernel byte-exact and P2:143 keeps the Q6 default.  The one extra M0 lever is dropping the `Contract.lower` text walk (P2:53, A/emit/contract.ml:888).  That walk is backend work and is not in `vouch check`, so the check ratio of P2:49 has no lever at all.  VERIFIED P2:49, P2:53, P2:143.
- The lineage's only compile-speed number is 1.956099 against 1.0 (brief:100-101, A HEAD eebe37e).  P2 never answers it with a number.  P2:160 asserts "ratio still under 1.0" at the M2 exit with no measurement.  VERIFIED P2:160.
- The denominator is BELIEVED twice: Bend 2 is not installed (S2:211) and the check and compile command names are guessed (S2:215, "not in the README").  P2:47 cites the recipe as VERIFIED S2.  A believed row cited as fact loses the axis point (brief:134-136).
- The ratio is ms per kloc over ms per kloc (P2:49) with lines counted per twin.  A terse Bend twin raises the denominator and a padded .vch twin lowers the numerator.  The corpus is not comparable line for line until lines are pinned per program pair.  Derivation from P2:47-51.
- S1 gives 421.774 ms median for 77 fixtures and no line count, so no assay ms per kloc exists (T4 prints the test tree total, not the 77-file figure).
- At M1 a walk returns: M/lib/check.ml:43 runs `Level_scope.check` on every checked term (S1 section 7, VERIFIED) and P2:118-134 adapts lib/level at M1.  Five walks (P2:53) become six exactly when the ratio turns binding.  Memoisation over hashconsed terms allocates per node before it saves, and P2 prices neither.
- Fix: measure the Bend 2 denominator at Stage 0c before M0 opens, print ms per kloc for S1's 77 fixtures, pin lines per program pair, and either move memoised conversion to M0 with Q6 marked REOPENED or make M1-RATIO informational and M2-RATIO binding with Q6 REOPENED.  As written the M1 exit is unreachable on every number in the dossiers.

## 2.  R0-SMUGGLE (survivable): two formers hold, two R0 rows are names, the extern table has no gate

- Term walk: A/lib/term.ml:49-50 has `Lan` and `Ran` and no third former, A/lib/shape.ml:10-15 is the closed five-shape grammar (S1 section 5, P3:13, P2:13 agree).  A third former would be a sixth shape keyed by a string, exactly veil's `SZk of Quantity.t * string * 'a` at V/lib/shape.ml:16 (S1 section 8).  P2 adds none.
- Rows 3 and 5 are names at the pin.  A/lib/erase.ml:567 "SPar and SNu keep [refused]", :581 and :583 return None for `Out` on SPar and SNu, :684 and :686 for `Sec`.  `spec-count` prints `shapes admitted 3` (P2:13).  P2:93-99 defers Quot to M2 and coinductives to M3.  So the AXIOMS row "exactly Quot.sound" (brief:350) is vacuous at M0 and M1.  VERIFIED pb.sh.
- `Host = Lan (SColl 8)` (P2:103) is a construction.  The smuggle moves to `lower`: each constructor is recognised by the NAME of a prelude global and mapped to an ecall sequence.  That string-keyed table is `SZk`'s string moved out of the kernel.  R0-AUDIT walks term.ml and never sees it.  Not a former, but ungated.
- Row verdicts: SPi, SColl constructions with rules.  SMu a construction read as Kan by naming plus the universal property (P3:26 says so, P2 does not).  SPar, SNu decorations until M2 and M3.
- Fix: an EXTERN-ROSTER gate that prints the by-name table in lower and refuses any global outside it, R0-COUNT printing `shapes admitted 3` beside `formers 2`, AXIOMS printing an empty list at M0 and M1.

## 3.  R1-REFUSE (survivable): one REFUSE row is unrefusable and two name no site

- `host-in-kernel` (P2:41) cannot be refused.  Under P2:103 `Host` is an ordinary prelude inductive, so a `Host` value in a type is well typed, sits at quantity Zero, and never reaches lower.  Its Lean twin (an inductive value in a type) is accepted by `lean`, so by P2's own rule (P2:41) the row is dropped.  The corpus has five rows, not six.  Derivation.
- `wrong-index` and `large-elim-prop` name no refusal site (P2:41), against `positivity.ml`, `totality.ml`, `quantity.ml` for the others.  T1 shows what the pin has for proof irrelevance and subsingleton elimination.
- Universe polymorphism is absent at M0: A/lib/level.ml is 11 lines with `type t = int` (S1 section 7, VERIFIED) and P2 adapts levels at M1.  Every ACCEPT row is monomorphic, so R1's "prenex universe polymorphism as Lean 4 has it" (brief:68-69) is untested until M1.  P2:174 admits the deferral.
- Fix: replace `host-in-kernel` with a quantity row (`Host` value read at quantity One inside a Zero binder) refused by A/lib/check.ml:61-62 `readable`, name the site for the two rows, add one level-polymorphic ACCEPT row at M1.

## 4.  R3-ISA (survivable): RV64IM and ELF64 rest on one S2 row, the W-form encodings have no reference object, the cost model omits precompile cost

- P2:138 reopens Q1 in wording to RV64IM on S2:24 `DEFAULT_TARGET = "riscv64im-succinct-zkvm-elf"` (crates/build/src/lib.rs:16, VERIFIED by S2).  The succinct toolchain also ships riscv32im-succinct-zkvm-elf (S2 section 1).  Whether the v6.1.0 executor accepts ELF64 only, or both, is S2 section 4's row and P2:173 calls it a weak point.  BELIEVED, settle: `llvm-readelf -h` on a `cargo prove build` hello guest at Stage 0 step 3.
- S2's encoding table (S2 section 8) was assembled with `--target=riscv32-unknown-elf -march=rv32im`.  P2's W-form encodings (P2:173) have no reference object in any dossier.  T6 assembles the W-forms and the ecall prologue with rv64im so the author can diff.
- Syscall codes: P2:110 KECCAK_PERMUTE 0x00010109 and P2:112 UINT256_MUL 0x0001011D match the cached syscall_code.rs (pb.sh `## codes`).  The lui plus addi split is sound for every code whose low 12 bits are under 0x800, which holds for the roster.  Hand derivation.
- Cost: P2:140 sets cycles = `ExecutionReport::total_instruction_count()` and admits precompile chip cost is outside it.  Then the UINT256_MUL lever counts as one instruction and CYCLE-BUDGET cannot see its proving cost.  T5 checks whether report.rs at d454975 carries a `gas` field.
- Fix: print both the instruction count and the SP1 gas figure in CYCLE-BUDGET, assemble one rv64im reference object per emitted instruction form, and pin ELF class from the hello guest before encode/elf.ml is written.

## 5.  ERASE-LEVER (survivable): TRACE-ERASURE is a test, and the proof-supplied lever has no site in the five walks

- The theorem part is real: A/lib/erase.ml:102-104 `quantity_runtime` drops Zero binders and A/lib/check.ml:61-62 `readable` refuses a Zero read at One, so bytes cannot depend on a proof TERM (P2:73).  The gate itself (P2:75) is two builds compared, and its precedent is BELIEVED by P2 itself.  T2 shows gates.sh has no TRACE-ERASURE row, the artifact is dev/validation/2026-09-11-m1-emission/ERASED-BYTES.log.
- "Without its proof terms" is undefined: a program with proofs deleted does not type check.  The gate needs the transform stated (each proof replaced by a postulate of the same type, listed by AXIOMS).
- The `word64-add-lt` row needs a decision that only a Zero binder's TYPE carries.  At the pin that decision lives in the dropped module: A/emit/contract.ml:311 matches `op.text = "addLt" || op.text = "subLe"` and :721 builds `AddFits` by op text.  P2:151 drops emit/contract.  A/lib/eterm.ml:24-38 `ktm` has no constructor for "bound holds", so the lever has no carrier after erase.
- Fix: add `KPrim of prim * ktm list` with a closed prim roster to eterm, decide it in erase from the extern's type, and define the TRACE-ERASURE input transform.

## 6.  Q0-PROVISIONAL (survivable): the flip is unmeasured and the trusted bound is unstated in what was read

- P2:137 keeps assay because the mech side is UNMEASURED (S1 section 3, blocked on Stage 0 step 5).  P2:83 sets the flip at a mech median under 211 ms on the same 77 fixtures.  That is the ruling applied, not measured.  P2:172 says the trigger "rests on line counts".
- A/lib is 6,193 lines (S1 section 4) against veil's 5,250 bound and mech's 3,000 bound (brief:197-202).  P2 section 13 states bounds this run could not read in full.  BELIEVED, settle: P2:164-169.
- Fix: run the S1 suite on mech after step 5 and print both medians beside the 211 ms line, and print the TRUSTED-LINES bound per module in the M0 gate row.

## 7.  STAGING (survivable): three new trusted components and an M2 exit that assumes the open ratio is closed

- New code: lower (P2 replaces emit/emit 493 lines), encode (rv64.ml, elf.ml, runtime.ml, listing.ml), an RV64IM emulator (bin/rv64emu.ml, 0 lines today) and a Rust harness.  Every W-form and the M extension is new twice, in the encoder and in the twin.  VERIFIED P2:118-134.
- P2:160 M2 exit needs `SPar` admitted, PRELUDE-CHECKED at 70 percent and the ratio under 1.0 at once, while assay's own M1 ratio is open at 1.956 (brief:181-182).  No stage names a fallback when M1-RATIO fails.
- Fix: a RATIO-FAIL branch in the M1 stage (freeze, profile with `--passes` node counts, reopen Q6), and an emulator conformance row against T6-style clang objects before EXEC-DIFF.

## Verdict

P2 is R0-honest and target-literate, but its speed-first thesis rests on the unchanged 1.956 checker, a believed denominator and an M2 assertion, so R2 fails as written.  Fix finding 1 before the judge scores axis 3, the rest are survivable with the fixes above.

## Probe transcripts (2026-09-21, whitespace normalised)
T1 rg -n -i irrelev|subsingleton A/lib/*.ml | head -3
/Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/conv.ml:3:    Step one is proof irrelevance:  when the type of the type is the
/Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/conv.ml:19:    carries proof irrelevance into an argument position.
/Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/conv.ml:65:      let* sub = subsingleton_step ops ctx w in
T2 rg -n -i erasure|ERASED A/dev/gates.sh | head -2
T3 check.ml walk calls
91:    o_conv = (fun (c : ctx) ~(ty : Value.t) (a : Value.t) (b : Value.t) -> Conv.conv ops c ~ty a b);
92:    o_conv_type = (fun (c : ctx) (a : Value.t) (b : Value.t) -> Conv.conv_type ops c a b);
249:  let* eq = Conv.conv_type ops c got expected in
346:  fam_params : Positivity.telescope;
T4 non-ml test files and lines
/Users/oobi/Documents/kan-sp1-lang-assay-pin/test/agreement/agreement-natAdd.kan
     539
   88623 total
T5 rg -n gas cache/*report*
14:/// This constant is chosen for backwards compatibility with the V4 gas model: with this factor,
15:/// the gas costs of op-succinct blocks in V6 will approximately match those in V4.
33:    /// The unnormalized gas, if it was calculated.  Should not be accessed directly.  Use `gas()` instead.
T6 clang --target=riscv64-unknown-elf -march=rv64im W-forms
       0: 00b5053b     	addw	a0, a0, a1
       4: 02b5053b     	mulw	a0, a0, a1
       8: 00013503     	ld	a0, 0x0(sp)
       c: 00a13423     	sd	a0, 0x8(sp)
      10: 000102b7     	lui	t0, 0x10
      14: 10928293     	addi	t0, t0, 0x109
      18: 00000073     	ecall
