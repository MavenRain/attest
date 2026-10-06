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

The first fixture is HALT: `addi t0, x0, 0` (93 02 00 00), `addi a0, x0, 0` (13 05 00 00), `ecall` (73 00 00 00), 12 code bytes at the text load address with e_entry 0x78000000 (tool:253, VERIFIED). Under ELF64 with one program header and p_align 0x1000, the file is 64 + 56 + 3976 zero padding + 12 = 4108 bytes. Text starts at file offset 0x1000, congruent to its virtual address modulo p_align as required by the [ELF program-header specification](https://gabi.xinuos.com/elf/07-pheader.html). This supersedes the unpadded 132-byte draft and the 96-byte ELF32 count of verdict:107 (VERIFIED 2026-10-06 by ENC-XCHECK on corpus/halt.elf). The bytes 13 02 00 00 of tool:253 encode `addi tp, x0, 0` (rd = x4); clang VERIFIED 2026-10-06 that `addi t0, x0, 0` is 93 02 00 00.

Gate ELF-ACCEPTED runs sp1-exec-harness, at most 100 Rust lines on `sp1-sdk = "=6.1.0"` in execute mode only (verdict:106, tool:109, tool:111-195, VERIFIED), on the HALT fixture and passes when the harness prints `EXEC cycles=<n> syscalls=<n> pv= exit=0` (verdict:108, VERIFIED).  Whether the executor accepts a HALT without the 8 COMMIT and 8 COMMIT_DEFERRED_PROOFS ecalls in execute mode is BELIEVED (tool:253);  when it refuses, the fixture grows by the halt sequence of tool:102 and the gate row records the refusal message verbatim.  The harness needs the `cargo fetch` of sp1-sdk 6.1.0 from USER step 6 (brief:543, VERIFIED).  The sync API names `Elf::from`, `SP1Stdin::write_slice` and `SP1PublicValues::as_slice` are BELIEVED (tool:109);  settle: `symx` on the sdk sources after the fetch.

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
