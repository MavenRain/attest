# kan-sp1-lang dossier S1: the two candidate kernels

Scout S1, 2026-09-21, panel caps 7 findings and 56 agents.  Every row is VERIFIED (command or path:line) or BELIEVED (with the step that settles it).  A = /Users/oobi/Documents/kan-sp1-lang-assay-pin.  M = /Users/oobi/Documents/kan-sp1-lang-mech-pin.  V = /Users/oobi/Documents/mechanism-lang/vendor/veil (read only).  Scratch and logs: /private/tmp/claude/kan-sp1-lang-panel.

## 1.  Pin state

| Row | Value | Evidence |
|---|---|---|
| assay HEAD | `eebe37e M1: enforce the closure performance bound` | VERIFIED `git -C A log --oneline -1` |
| assay porcelain | 0 lines before the build, clean | VERIFIED `git -C A status --porcelain \| wc -l` |
| mech HEAD | `1e4f371 M0 Stage C / U1: horizontal associativity` | VERIFIED `git -C M log --oneline -1` |
| mech porcelain | 0 lines, clean | VERIFIED `git -C M status --porcelain \| wc -l` |
| veil submodule in M | NOT checked out, `ls M/vendor/veil \| wc -l` prints 0 | VERIFIED |
| disk | `df -g /Users/oobi/Documents`: 460 GiB size, 26 GiB free, 94 percent used, under the 30 GiB floor | VERIFIED |

Every mechanism-lang BUILD row below is BLOCKED on Stage 0 user step 5 (brief lines 524 to 525).  The user runs one of the two commands the brief gives at lines 216 to 217, quoted verbatim:

```
git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule update --init --reference /Users/oobi/Documents/veil vendor/veil
git -C /Users/oobi/Documents/veil worktree add --detach /Users/oobi/Documents/kan-sp1-lang-veil-pin a7534cedeac82d396de8e23058ee6bc990560f65
```

S1 never ran either command and never cloned.  The assay build wrote only A/_build (31 MB, `du -sh A/_build`).  M has no _build.

## 2.  Builds

| Row | Value | Evidence |
|---|---|---|
| dunecho | `/Users/oobi/.local/bin/dunecho`, synopsis `dunecho [--full=FILE:LINE] [--warn] [OPTION]... MODE`, exit 124 on a parse error | VERIFIED `dunecho --help \| head -20` |
| dunecho and `-j 2` | `dunecho build -j 2` prints `dunecho: unknown option -j` and builds nothing | VERIFIED, both wrappers |
| A/dev/dune.sh | `set -eu`, `cd` to the repo root, `exec dune "$@"` from PATH, no chpwd guard | VERIFIED A/dev/dune.sh:6-9 |
| A/dev/pin-dune.sh | clears chpwd, adds the zxcaml-p1 switch, then `cd /Users/oobi/Documents/kan-lang-tot-pin`, a stale root, unusable for A | VERIFIED A/dev/pin-dune.sh:17-19 |
| M/dev/dunecho.sh | clears chpwd, adds `$HOME/.opam/zxcaml-p1/bin`, `cd` to its own root, `exec dunecho "$@"` when dunecho is on PATH, else `exec dune "$@"` | VERIFIED M/dev/dunecho.sh:15-31 |
| assay build, attempt 1 | `zsh A/dev/dune.sh build -j 2` with the switch on PATH: exit 1 in 0 s, text `_telcoin_shared_target:7: CARGO_TARGET_DIR: parameter not set` (the user chpwd hook under `set -u`) | VERIFIED build-assay.log |
| assay build, attempt 2 | `PATH=/Users/oobi/.opam/zxcaml-p1/bin:$PATH zsh -f A/dev/dune.sh build -j 2`: exit 0, wall 9 s, empty log, `_build/default/bin/assay.exe` 3,370,312 bytes, `_build/default/test/main.exe` 2,603,160 bytes | VERIFIED p8.sh |
| mech build | BLOCKED: `ls -d M/vendor/veil/lib` prints `No such file or directory`, and M/lib/dune copies 20 veil files by `copy_files ../vendor/veil/lib/...` (M/lib/dune:7-26) | VERIFIED |
| mech build with `-j 2` after the checkout | BELIEVED to need `zsh -f M/dev/dunecho.sh build` with `dunecho` off PATH or a dune config with `(jobs 2)`, because dunecho refuses `-j`.  Settle by running it after step 5 | BELIEVED |
| A gates BUILD leg | `("BUILD", 120, ("zsh", "-f", "dev/dune.sh", "build"), "")`, no `-j` | VERIFIED A/dev/stage-a-gates.py:61 |

## 3.  The shared twin suite, timed

| Row | Value | Evidence |
|---|---|---|
| suite program | kanon's M0 kernel suite `test/main.ml`, six groups PARSE, CHECK, ERASE, NEG, ERASE-NEG and MIGRATED, one argument, the test root | VERIFIED A/test/main.ml:1-21 |
| assay copy | A/test/main.ml, 456 lines, run as `_build/default/test/main.exe test` | VERIFIED A/dev/stage-a-gates.py:67 |
| mech copy | `(copy_files ../vendor/veil/test/main.ml)`, run as `_build/default/test/main.exe $ROOT/vendor/veil/test` | VERIFIED M/test/dune:98, M/dev/gates.sh:197-198 |
| the two main.ml differ | V/test/main.ml is 463 lines, `cmp` differs at line 44 | VERIFIED `cmp A/test/main.ml V/test/main.ml` |
| fixtures | A/test/fixtures = 77 files, V/test/fixtures = 81 files, all 77 of A are in V, V adds 4 | VERIFIED `comm -12` count 77, `comm -23` count 0, `comm -13` count 4 |
| bench.sh | identical in A and M, `RUNS` timed runs after one warm-up, perf_counter_ns around `zsh -f -c CMD`, prints `BENCH NAME median_ms=... min_ms=... max_ms=... runs=N` | VERIFIED `cmp A/dev/bench.sh M/dev/bench.sh`, A/dev/bench.sh:1-10 |
| single core | no `Domain.` or `Thread.` in A/lib or M/lib, the suite process is one OCaml thread | VERIFIED `rg -c 'Domain\.\|Thread\.'` empty |
| assay timer command | `RUNS=7 zsh -f A/dev/bench.sh SUITE-KERNEL "A/_build/default/test/main.exe A/test"` | VERIFIED p8.sh |
| assay run 1 | `BENCH SUITE-KERNEL median_ms=421.774 min_ms=334.754 max_ms=582.340 runs=7` | VERIFIED |
| assay run 2 | `BENCH SUITE-KERNEL-2 median_ms=432.098 min_ms=377.833 max_ms=974.232 runs=7` | VERIFIED |
| assay verdict line | `SUITE-KERNEL OK`, after `MIGRATED-OK 4/4` | VERIFIED |
| mech median | UNMEASURED, BLOCKED on Stage 0 user step 5 | VERIFIED blocker, section 1 |
| ratio | UNMEASURED | |

Q0 flip trigger 1: mechanism-lang over veil at least 2x faster than assay on the shared suite is UNMEASURED, blocked on Stage 0 user step 5 (the veil submodule checkout), with the assay side pinned at a median of 421.774 ms over 7 runs and the same fixture set of 77 files present in both trees.

## 4.  Lib line counts and TRUSTED-LINES

| Row | Value | Evidence |
|---|---|---|
| A/lib/*.ml | 6,193 lines in 22 files (the brief says 25 files, the extra 3 are not .ml) | VERIFIED `wc -l A/lib/*.ml`, `ls A/lib/*.ml \| wc -l` |
| M/lib/*.ml | 3,744 lines in 9 files (the brief says 11) | VERIFIED `wc -l M/lib/*.ml` |
| V/lib/*.ml | 7,576 lines in 23 files (the brief says 7,578) | VERIFIED `wc -l V/lib/*.ml` |
| M active kernel, naive | 3,744 + 7,576 = 11,320 | VERIFIED arithmetic |
| M active kernel, linked | M/lib/dune builds `mechanism_kernel` from 20 copied veil files plus its own 9, and overlays veil's check, conv, eval, rules and level: 3,744 + 7,576 - (573 + 396 + 297 + 2,105 + 11) = 7,938 | BELIEVED, settle by `ls M/_build/default/lib/*.ml \| xargs wc -l` after the build |
| M bound | `kernel_bound=3000`, `encoder_bound=900` | VERIFIED M/dev/trusted-lines.sh:40-41 |
| M README | "The active kernel still exceeds the unchanged 3,000-line bound, so TRUSTED-LINES also awaits the existing kernel-limit ruling." | VERIFIED M/README.md:47-48 |
| M trusted-lines.sh run | `wc: M/dev/../vendor/veil/lib/shape.ml: open: No such file or directory` (also term.ml, value.ml), then `trusted-lines: a trusted file is missing under M/dev/..` and `TRUSTED-LINES FAIL`, exit 1 | VERIFIED `zsh -f M/dev/trusted-lines.sh` |
| A trusted-lines.sh run | verbatim below, exit 0 | VERIFIED `zsh -f A/dev/trusted-lines.sh` |

```
TRUSTED-LINES kernel=3997 want=3997 bound=4000
TRUSTED-LINES emitter=1800/1800
TRUSTED-LINES assembler=238/600
TRUSTED-LINES keccak=89/250
TRUSTED-LINES abi=35/400
TRUSTED-LINES layout=8/250
TRUSTED-LINES listing=54/250
TRUSTED-LINES total=2224/3550 ratified=3550
TRUSTED-LINES OK
```

## 5.  The R0 former count

Outputs verbatim (`zsh -f`, the assay rows after the build):

```
A/dev/r0-count.sh before the build: R0-COUNT FAIL: /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev/../_build/default/bin/assay.exe is not built
A/dev/r0-count.sh after the build:  R0-COUNT OK
A/dev/r0-audit.sh:                  R0-AUDIT OK
M/dev/r0-count.sh: R0-COUNT FAIL: /Users/oobi/Documents/kan-sp1-lang-mech-pin/_build/default/bin/mech.exe is not built
M/dev/r0-audit.sh: R0-AUDIT FAIL: build mechanism with dev/dunecho.sh build first
```

`A/_build/default/bin/assay.exe spec-count` prints, and A/SPEC.md:186-194 pins, this block (VERIFIED, diffed by A/dev/r0-count.sh:17-40):

```
formers 2: Lan Ran
schema constructors 4: In Elim Sec Out
shapes declared 5: SPi SColl SPar SMu SNu
shapes admitted 3: SPi SColl SMu
named rules declared 3: proof-irrelevance subsingleton-large-elimination literal-fast-path
named rules present 3: proof-irrelevance subsingleton-large-elimination literal-fast-path
eta rows 3: Ran-SPi Lan-SPi Ran-SColl
no eta 3: Lan-SColl Ran-SMu Lan-SMu
```

M/SPEC.md:12-17 pins the veil block instead (VERIFIED by reading, the driver is not built): `formers 2: Lan Ran`, `schema constructors 4: In Elim Sec Out`, `shapes declared 8: SPi SColl SPar SMu SNu SZk SFhc SMpc`, `shapes admitted 6: SPi SColl SMu SZk SFhc SMpc`, `named rules declared 6: proof-irrelevance subsingleton-large-elimination literal-fast-path zk-fhc zk-mpc fhc-mpc`, `named rules present 3`.  M/SPEC.md:5-7 says the block "is inherited from Veil at PIN" and "adds Veil's three private-computation shapes".

| Row | Value | Evidence |
|---|---|---|
| A/lib/spec_count.ml | 62 lines, reads `Term.formers`, `Rules.admitted`, `Rules.named_declared`, `Rules.named_present` | VERIFIED A/lib/spec_count.ml:14-19 |
| A SPEC.md sections | 1 The claim (:7), 2 The closed grammar (:18), R0 counts (:178), 4 The eta table (:201), 5 The named rules ledger (:247), 6 The framework axiom (:304), 7 The sugar table (:323), 8 Historical Kanon encoder subset (:381), 9 The surface grammar (:530), 10 Obligations at M0 (:600) | VERIFIED `rg -n '^## ' A/SPEC.md` |
| M SPEC.md sections | R0 counts (:3), D3: prenex universe levels (:28), Overlay and trusted-source accounting (:75), Lean export import foundation (:91), Stage C prelude foundation (:154), Stage C family templates (:194), Stage C dependent function and pair catalog (:230), Stage C ordered family groups and congruence (:251), Stage C textual prenex definitions (:283), Stage C textual polymorphic families (:319), Stage C textual ordered groups and members (:362), Stage C closed family reuse (:538), Stage C symbolic family reuse (:561) | VERIFIED `rg -n '^## ' M/SPEC.md` |
| A shape grammar | A/lib/shape.ml (60 lines): `type 'a t =` at :10, `SPi of Quantity.t * string * 'a` :11, `SColl of int` :12, `SPar of 'a * 'a` :13, `SMu of string * 'a list` :14, `SNu of string * 'a list` :15 | VERIFIED |
| A term sum | A/lib/term.ml (133 lines): `and t =` :46, `Var` :47, `Univ of Level.t` :48, `Lan of t Shape.t * t` :49, `Ran of t Shape.t * t` :50, `In` :51, `Elim of elim` :52, `Sec` :53, `Out` :54, `Let` :55, `Ann` :56, `Global` :57, `Lit of Literal.t` :58, `Auto` :59 | VERIFIED |
| M term sum | none in M/lib, it is V/lib/term.ml (133 lines), byte-identical to A/lib/term.ml, same constructors at the same lines :46-59 | VERIFIED `diff A/lib/term.ml V/lib/term.ml` empty |
| M shape grammar | V/lib/shape.ml (87 lines): SPi :11, SColl :12, SPar :13, SMu :14, SNu :15, plus `SZk of Quantity.t * string * 'a` :16, `SFhc of 'a` :18, `SMpc of 'a * 'a` :19 | VERIFIED |

## 6.  assay seams for an RV32IM ELF target

| Seam | Lines | Reading | Evidence |
|---|---|---|---|
| lib/eterm.ml | 117 | erased alphabet: `repr = RI31 \| RStruct of tid \| RUnion of tid \| RFunc of tid \| RThunk of tid` (:17-22), `ktm = KVar of int \| KLit of Literal.t \| KGlobal of string \| KErased \| KLet \| KClos of fid * int * ktm list \| KApp \| KTail \| KStruct of tid * ktm list \| KProj of tid * int * ktm \| KTag of tid * int * ktm list \| KCase of tid * ktm * kbranch list \| KDelay of fid * ktm list \| KForce of ktm` (:24-38), `kdecl = KFun of fid * repr list * repr * ktm \| KRec of tid list` (:48-50) | VERIFIED |
| lib/erase.ml | 1,484 | entry `program ?budget globals` :1459 calls `decl` :1427 once per global.  `quantity_runtime q = not (Quantity.equal q Quantity.Zero)` :102-104 is the rule that drops proofs.  `proof_free` :173, `runtime_ty` :182, `point_runtime` :191 decide per binder.  `repr_of` :249 maps a value to a `repr`, `mu_layout` :413 lays out inductives | VERIFIED |
| lib/quantity.ml | 158 | `t = Zero \| One \| Many` :7-10, `mul` :14-22 sends any Zero factor to Zero | VERIFIED |
| lib/totality.ml | 146 | structural termination check for mu eliminators | VERIFIED wc, BELIEVED role from the name and check.ml use |
| lib/positivity.ml | 118 | `telescope`, `family`, `ctor` records that check.ml:361-444 and erase.ml:384-413 walk | VERIFIED |
| lib/literal.ml | 14 | `t = LString of string \| LInt of Bignum.t` (:5-7).  No Word32 or U256 accelerator lives here | VERIFIED |
| lib/bignum.ml | 51 | a Zarith wrapper, `of_int`, `zero`, `one`, `equal`, `compare`, `sign`, `add`, `mul` (:5-12).  No Word32 or U256 type | VERIFIED |
| Word32 and U256 | in the backend only: emit/model.ml 2 hits, emit/contract.ml 1, abi/abi.ml 3, abi/layout.ml 2, zero hits in lib/ | VERIFIED `rg -c -i 'word32\|u256\|uint256\|word256'` |
| lib/budget.ml | 27 | `t = { poll : unit -> bool }` :23, `unlimited` :25, `of_poll` :26, `exhausted` :27.  A poll, not a counter.  A cycle budget needs a counter | VERIFIED |
| asm/ | asm.ml 238, listing.ml 54 | the Cancun assembler and the bytecode listing, the ELF encoder precedent, trusted rows assembler=238/600 and listing=54/250 | VERIFIED wc, section 4 |
| emit/ | contract.ml 894, emit.ml 493, model.ml 143, recognize.ml 254 | `Contract.lower source` :888 (text level), `Emit.program` :490 selects `program_m1` :482 or `program_m0` :214, `assemble` :156 calls `A.assemble` | VERIFIED |
| evm/ and reference/ | evm/diff.py 272, bin/differential.ml 88, reference/ = abi.json, counter, layout.json, ref20-init.evm, ref20.evm | the geth differential and the hand-assembled reference | VERIFIED ls, wc |
| proofs/ and verification/ | Lean: proofs/KanEvmProofs, Axioms.lean, FIDELITY.md; verification/AssayProofs, Main.lean | the Stage F erasure precedent | VERIFIED ls |
| call order | bin/assay.ml: `Assay_emit.Contract.lower` :36, `Kanon_surface.Elab.check_in` :38, `Kanon_kernel.Erase.program` :52 and :65, `Assay_emit.Emit.program` :73 inside `let compile` :71 | VERIFIED |
| elaborate and check | surface/elab.ml `check_in` :1171 elaborates one row, then `Check.check_decls ~budget g [ row ]` :1126 checks it, so elaborate and check are two walks | VERIFIED |
| walks per definition | 5 kernel-side walks: elaborate (elab.ml:1171), check (check.ml:302 `check_decl`), erase (erase.ml:1427), lower (emit.ml:214 or :482), encode (emit.ml:156 then asm/asm.ml).  A sixth text-level walk is `Contract.lower` (emit/contract.ml:888) | VERIFIED by reading the call sites |
| `--passes` hook | bin/assay.ml:71, `let compile (command : string) (path : string) (export : string)`, the one function that sequences check_in, Erase.program and Emit.program | VERIFIED |

## 7.  mechanism-lang seams

| Seam | Lines | Reading | Evidence |
|---|---|---|---|
| lib/level_var.ml | 53 | the level term: `Zero`, `offset` :10, `Max`, `IMax`, level variables with `valid` :17, `well_formed` :25, `in_scope arity` :27, `subst arguments` :39 | VERIFIED |
| lib/level_eq.ml | 144 | `equal`, `le`, `always_positive`, `always_zero`, the budgeted forms | VERIFIED via lib/level.ml:10-15 |
| lib/level_scope.ml | 32 | `check budget arity term` :2, one scope walk over a term's levels | VERIFIED |
| lib/level.ml | 36 | the facade: `zero` :5, `one` :6, `succ` :7, `max` :8, `imax` :9, `equal` :10, `le` :11, `equal_budget` :12, `le_budget` :13, `in_scope` :16, `subst` :17 | VERIFIED |
| lib/rules_lvl.ml | 2 | `let imax : Level.t -> Level.t -> Level.t = Level.imax` | VERIFIED :2 |
| overlay total | 267 lines in the five level files | VERIFIED `cat ... \| wc -l` |
| overlaid kernel files | check.ml 643 (veil 573, diff 102 lines), conv.ml 404 (veil 396, diff 36), eval.ml 314 (veil 297, diff 21), rules.ml 2,116 (veil 2,105, diff 53).  Against assay: check diff 139, conv 36, eval 21, rules 715 (assay's rules.ml is 1,481, without the 3 host shapes) | VERIFIED `diff ... \| rg -c '^[<>]'` |
| per-definition cost | check.ml:43 `Level_scope.check c.budget c.level_arity t` on every checked term, check.ml:265 `Level.equal_budget`, :448 and :527 `Level.le_budget` on universe comparisons.  One extra level walk per term plus a level solver call per universe comparison | VERIFIED |
| assay and veil levels | A/lib/level.ml = V/lib/level.ml = 11 lines, `type t = int` :2, `max` :7.  No level variables, no imax, no prenex binder | VERIFIED |
| import/ | 1,543 lines in 10 modules: translate.ml 352, mapping.ml 81, names.ml 19, report.ml 153, plus decls, export, exprs, io, levels, ndjson | VERIFIED wc |
| import/levels.ml | `type t = Zero \| Succ of int \| Max of int * int \| Imax of int * int \| Param of int` :1, parses the lean4export `max` and `imax` tags :13-14 | VERIFIED |
| import/translate.ml | 43 level hits, lowers `Max` to `Level.max` :250 and `Imax` to `Level.imax` :251, links `mechanism_kernel` | VERIFIED import/dune:3 |
| prelude/ | aggregate, cat, charter, congruence, dependent, equality modules and more | VERIFIED ls |
| map/prelude.map.tsv | 2,478 lines = header `lean_name target verdict` + 2,477 names, first rows `Acc - UNMAPPED`, `Acc.intro - UNMAPPED` | VERIFIED head -3 |
| PRELUDE-CHECKED | M/README.md:25-26 states the line shape `PRELUDE-CHECKED external=2477 NAME_AND_TYPE=n1 NAME_ONLY=n2 UNM...` and `covered=(n1+n4)/2477`.  M/dev/prelude-gates.py runs `_build/default/bin/mech.exe` :11, `_build/default/test/prelude.exe` :12 and `test/mapping.exe` :62.  M/dev/import-gates.sh runs `test/import.exe --corpus` :24 and `test/import_types.exe` :25 | VERIFIED |
| counts | NAME_AND_TYPE, NAME_ONLY, UNMAPPED and NEVER: UNMEASURED, every gate needs the build, BLOCKED on Stage 0 user step 5 | VERIFIED |

Is the level overlay NECESSARY for the import oracle?  YES for the level part, and it is portable.  The importer consumes `Param`, `Max` and `Imax` levels (import/levels.ml:1) and lowers them through `Level.max` and `Level.imax` (translate.ml:250-251), which assay's `type t = int` (A/lib/level.ml:2) cannot represent.  So assay has no prenex levels to carry the importer.  The overlay itself is 267 new lines plus a 102 + 36 + 21 + 53 = 212 line delta over veil's check, conv, eval and rules (VERIFIED diffs above).  Because A/lib/term.ml is byte-identical to V/lib/term.ml, the same delta applies to assay's check, conv and eval (diffs 139, 36, 21) and the rules delta shrinks to the level rows (BELIEVED: settle by porting rules_lvl and the 53 veil rows onto A/lib/rules.ml and running R0-COUNT).  The overlay is necessary as CODE, not as a KERNEL CHOICE.

## 8.  veil host shapes (read only at V)

| Row | Value | Evidence |
|---|---|---|
| declarations | `SZk of Quantity.t * string * 'a` V/lib/shape.ml:16, `SFhc of 'a` :18, `SMpc of 'a * 'a` :19, admitted rows :33 and :44-46 | VERIFIED |
| footprint by file | shape.ml 19 lines, circuit.ml 21, erase.ml 20, pp.ml 8, rules.ml 35, total 103 lines that name a host shape.  Zero in check.ml, conv.ml, eval.ml | VERIFIED `rg -c 'SZk\|SFhc\|SMpc' V/lib/*.ml` |
| rules rows | V/lib/rules.ml:251 SZk equality, :256 SFhc, :260 SMpc, :265-281 five mixed-shape refusal arms | VERIFIED |
| circuit.ml | 563 lines, the ZK circuit backend, absent from assay | VERIFIED wc, `ls A/lib` |
| erase.ml | veil 1,610 against assay 1,484: 126 more lines, 20 of them host-shape arms | VERIFIED wc |
| excision cost | remove 103 lines of arms, 3 shape constructors, 3 named rules (zk-fhc, zk-mpc, fhc-mpc) and circuit.ml (563), and repin M/SPEC.md:14-16 to 5 declared, 3 admitted, 3 named rules | VERIFIED counts, BELIEVED effort |
| is the residue veil? | No.  With the 3 shapes, circuit.ml and the 3 named rules gone, V/lib is assay's lib plus 8 lines of pp.ml (110 against 102): the kanon 2c2e6e6 kernel that A/CARRIED.md:10 pins byte-exact | VERIFIED per-file wc equality on 18 of 23 files |
| M refs | M/lib/rules.ml carries the 35 host-shape rows unchanged, M/import has zero | VERIFIED `rg -c` |

## 9.  The gate batteries

| Row | Value | Evidence |
|---|---|---|
| A/dev/gates.sh | `exec python3 -P dev/stage-a-gates.py --m1-close` :7 | VERIFIED |
| A leg count | 38 static leg tuples in `legs = [` :60, plus `legs.extend` at :75, :80, :88, :101, :121 and `legs.append` at :134.  README.md:8 and :340 say 75 legs.  The 75 is BELIEVED, settle by one full `zsh -f A/dev/gates.sh` MEASURE block | VERIFIED count, BELIEVED total |
| M leg count | 78 `leg ` rows in M/dev/gates.sh, SUITE-KERNEL at :197 | VERIFIED `rg -c '^leg '` |
| A DENOMINATORS.sha256 | 122 rows, `shasum -c dev/DENOMINATORS.sha256` from A: 122 OK, 0 FAILED | VERIFIED |
| A denominators.json | 34,893 bytes, no `ratio` or `1.956` key.  dev/denominators-m1.json:15 `"ratio_bound": 2.000,` | VERIFIED rg |
| frozen ratio row | A/dev/M1-CLOSE.md:59 `\| 02, active \| 44.217 \| 2133.327 \| 1090.603 \| 1.956099 \| 32.99 \|` | VERIFIED |
| A README status | :3 "M1 remains open on performance: the current frozen ratio is 1.956099", :8 "`zsh -f dev/gates.sh` runs all 75 checks.", :10 "Assay is a Kanon language fork for EVM contracts." | VERIFIED |
| M README status | :47-48 quoted in section 4, :25-26 the PRELUDE-CHECKED line shape | VERIFIED |

## 10.  Verdict tables and the Q0 statement

assay (A/lib, A/emit, A/asm, A/abi, A/keccak, A/surface, A/bin) for the SP1 ELF target:

| Module | Lines | Verdict | Reason |
|---|---|---|---|
| lib/term, shape, spec_count | 133, 60, 62 | carry | the R0 sum and grammar, byte-exact kanon (A/CARRIED.md:10) |
| lib/check, conv, eval, rules, value, global, order, prim, error, pp | 538, 396, 297, 1,481, 137, 130, 510, 139, 82, 102 | carry | kernel, unchanged by the target |
| lib/level | 11 | adapt | `type t = int` cannot carry Lean levels, port the 267-line overlay at M1 (section 7) |
| lib/quantity, totality, positivity | 158, 146, 118 | carry | the erasure rules TRACE-ERASURE argues from |
| lib/erase | 1,484 | adapt | `decl` :1427 stays, `repr_of` :249 and `mu_layout` :413 target Wasm reprs (`RI31`, `RStruct`) that become RV32 word and heap reprs |
| lib/eterm | 117 | adapt | keep `ktm`, replace `repr` :17-22 with RV32 reprs |
| lib/literal, bignum | 14, 51 | carry | `LInt of Bignum.t`, Zarith stays host-side |
| lib/budget | 27 | adapt | poll to counter for CYCLE-BUDGET |
| emit/contract, recognize, model | 894, 254, 143 | drop | `.asy` contract surface, Solidity-shaped |
| emit/emit | 493 | rewrite | `program_m0` :214 and `program_m1` :482 lower to EVM blocks, the new `lower` targets an RV32IM IR |
| asm/asm, listing | 238, 54 | rewrite | Cancun opcodes to RV32IM encodings plus an ELF32 writer, same shape (blocks, labels, listing) |
| abi/abi, layout | 35, 8 | drop | EVM ABI |
| keccak/keccak | 89 | drop | SP1 keccak is a `Host` syscall |
| surface/elab, parser, lexer, syntax, token | 1,179, 620, 183, 302, 143 | carry | the kanon surface |
| bin/assay, differential, trace | 221, 88, 117 | adapt | `compile` :71 gains `--passes`, differential.ml and evm/diff.py (272) become the SP1 executor harness twin |
| evm/, reference/, proofs/, verification/ | 272 py, 5 files, 9, 8 | adapt | the geth differential, hand-assembled ref20.evm and the Lean Stage F erasure proofs are the templates |

mechanism-lang (M/lib, M/import, V/lib) for the SP1 ELF target:

| Module | Lines | Verdict | Reason |
|---|---|---|---|
| V/lib/term, shape | 133, 87 | adapt | shape.ml drops SZk, SFhc, SMpc (:16-19), 19 lines |
| V/lib/rules | 2,105 (M overlay 2,116) | adapt | drop 35 host rows (:251-281) and 3 named rules |
| V/lib/erase, pp | 1,610, 110 | adapt | drop 20 and 8 host arms, then the same RV32 repr work as assay |
| V/lib/circuit | 563 | drop | the ZK circuit backend, R0 forbids it |
| V/lib/check, conv, eval (M overlays 643, 404, 314) | 573, 396, 297 | carry | with the level overlay applied |
| M/lib/level, level_eq, level_scope, level_var, rules_lvl | 36, 144, 32, 53, 2 | carry | the R1 import oracle needs them |
| M/import (10 modules) | 1,543 | carry | the lean4export importer, the R1 oracle |
| M/prelude, map/prelude.map.tsv | 2,478 rows | carry | the PRELUDE-CHECKED denominator |
| backend | 0 | rewrite | mechanism-lang has no bytecode emitter, assembler, reference or executor differential |

Estimate for the new `lower` and `encode` stages: 1,300 to 1,700 lines of OCaml.  Evidence: assay's EVM lower is emit/emit.ml 493 lines and its encoder plus listing is asm/asm.ml 238 + asm/listing.ml 54 (VERIFIED wc), 785 lines for a stack machine with no registers, frames or relocations.  RV32IM adds register allocation over a0 to a7, sp frames, `ecall` sequences for the `Host` sum (brief 4.2), a bump allocator prologue, PC-relative branch fixups and an ELF32 header plus program header writer, so S1 doubles the lower and sizes the encoder at 400 to 600 lines (BELIEVED, settle by S2's RV32IM encoding table row count).  The assay TRUSTED-LINES emitter row already ratifies 1,800 lines (section 4), so the estimate fits the existing bound.

Q0 statement.  Default assay stands.  Flip trigger 1 (2x on the shared suite) is UNMEASURED: assay's median is 421.774 ms over 7 runs on the 77-fixture kernel suite, and mechanism-lang's build is blocked on Stage 0 user step 5, so no ratio exists.  Flip trigger 2 (the level overlay necessary for the import oracle) is HELD as a code fact and REFUTED as a kernel-choice fact: the importer needs `Param`, `Max` and `Imax` levels that assay's 11-line `type t = int` cannot hold, but the overlay is 267 new lines plus a 212-line delta over a term.ml that assay and veil share byte for byte, so it ports onto assay at M1 for about 480 lines.  The numbers that decide: assay carries 4,972 backend and surface lines (emit, asm, abi, keccak, surface, bin, VERIFIED wc) of which the 785-line lower and encode pair is the template for the ELF path, while mechanism-lang carries 0 backend lines, 103 host-shape lines plus a 563-line circuit backend to excise, and an active kernel of 7,938 to 11,320 lines against a 3,000-line bound it already exceeds (M/README.md:47).
