## 4 Trusted base and budgets

The trusted base at M0 is the kernel bucket carried from the assay pin eebe37e plus the three artifacts M0 writes: lower, encoder and harness.  OQ4 sets the bounds: "TRUSTED-LINES kernel bound 4,100 at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100 (this replaces the brief's 3,000)" (brief:541, VERIFIED).  This section replaces the six EVM artifact budgets of the template (tpl:140-147), because attest drops contract, recognize, model, abi, layout and keccak (verdict:106, VERIFIED).  The emulator emu/rv64im.ml, about 700 lines, is outside the base (verdict:106, VERIFIED);  gates, dev scripts and Lean proofs are outside the base (P1:133, VERIFIED).

### 4.1 The OQ4 bounds

| bucket | bound at M0 | bound at M1 | what it holds | first stage that measures it |
| --- | --- | --- | --- | --- |
| kernel | 4,100 | 4,400 | the 12 KERNEL files of the assay script (assay dev/trusted-lines.py:7) plus the literal kinds and their check rules (verdict:150) | Stage A, at 3,997 (verdict:117) |
| lower | 1,100 | 1,100 | lower.ml, about 900 lines by the design estimate (verdict:106) | Stage C (verdict:117) |
| encoder | 800 | 800 | rv64im.ml, elf64.ml and runtime.ml, about 700 lines by the design estimate (verdict:106) | Stage C (verdict:117) |
| harness | 100 | 100 | sp1-exec-harness, Rust on sp1-sdk = 6.1.0, execute only (verdict:106) | Stage D (verdict:117) |

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

The sum 3,997 equals `KERNEL_WANT = 3997` (assay dev/trusted-lines.py:22, VERIFIED) and sits under `KERNEL_BOUND = 4000` (assay dev/trusted-lines.py:23, VERIFIED).  The attest form of the script keeps the 12 names and makes three deltas, each a plan decision BELIEVED until the Stage A battery prints the new rows: (1) `KERNEL_BOUND` becomes 4100 and the equality test `kernel == KERNEL_WANT` (assay dev/trusted-lines.py:30) becomes `kernel <= KERNEL_BOUND`, with `want=3997` printed as the carried baseline;  (2) the six ARTIFACTS rows (assay dev/trusted-lines.py:9-14) become three, `("lower", 1100, "lower", ("lower.ml",))`, `("encoder", 800, "encode", ("rv64im.ml", "elf64.ml", "runtime.ml"))` and `("harness", 100, "sp1-exec-harness", ("src/main.rs",))`;  (3) the file walk `rglob("*.ml*")` (assay dev/trusted-lines.py:60) also matches `*.rs`, because the harness is Rust (verdict:106).  A row whose folder is absent prints 0/<bound> and does not fail (00-bindings:17);  the `ratified=` total row prints 4100 + 1100 + 800 + 100 = 6,100 at M0.

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
| `shasum -c dev/DENOMINATORS.sha256` | one OK line per frozen Bend 2 denominator row (brief:87-93 by 00-bindings:31) | Stage F (DENOMINATORS, verdict:117) | informational at M0 (OQ2, brief:541);  waits on USER step 2 and step 7 (brief:543) |

The commands `attest check --axioms`, `attest check --externs` and `attest build --passes` are BELIEVED as spellings until Stage A adapts bin/assay 221 lines to bin/attest with `--passes --axioms --externs spec-count` (verdict:106);  the assay pin spells the same disclosure as assay.exe subcommands (verdict:34).
