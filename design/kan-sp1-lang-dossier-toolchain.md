# kan-sp1-lang dossier: toolchain (scout S2)

Date: 2026-09-21.  Scope: the SP1, Bend 2 and RISC-V facts a proposal needs.  Every row is VERIFIED (with the command, the path:line or the URL) or BELIEVED (with what settles it).  Source cache: /private/tmp/claude/kan-sp1-lang-panel/cache; the SP1 files there are raw files of https://github.com/succinctlabs/sp1 at commit d454975ac7c1126097e36eceda9bce2cb9899da4 (tag v6.1.0), so a path:line below reads as https://raw.githubusercontent.com/succinctlabs/sp1/d454975ac7c1126097e36eceda9bce2cb9899da4/PATH.  Nothing was installed and nothing was built.  Network note: curl in the agent sandbox cannot read /etc/ssl/cert.pem, so every fetch used `--cacert` on an export of the system root keychain (`security find-certificate -a -p /System/Library/Keychains/SystemRootCertificates.keychain`).

## 1.  SP1 installed here

| Row | Result | Status |
|---|---|---|
| `/Users/oobi/.sp1/bin/cargo-prove --version` | `error: unexpected argument '--version' found` | VERIFIED, command run; the binary is a cargo subcommand and wants `prove` first |
| `/Users/oobi/.sp1/bin/cargo-prove sp1 --version` | `error: unrecognized subcommand 'sp1'` | VERIFIED, command run |
| `/Users/oobi/.sp1/bin/cargo-prove prove --version` | `cargo-prove sp1 (d454975 2026-04-11T01:51:47.829463000Z)` | VERIFIED, command run |
| Commit d454975 | full sha d454975ac7c1126097e36eceda9bce2cb9899da4, committed 2026-04-11T01:43:22Z; tag `v6.1.0` points at it | VERIFIED, https://api.github.com/repos/succinctlabs/sp1/tags (cache/tags.json) |
| Workspace version | `version = "6.1.0"`; `rust-version = "1.91"`; sp1-sdk, sp1-zkvm and sp1-core-executor take the workspace version | VERIFIED, Cargo.toml:2, Cargo.toml:9, crates/sdk/Cargo.toml:5 |
| `rustup toolchain list` | 18 rows: stable, nightly (default), 11 dated nightlies, 1.94, 1.95.0, 1.98, 1.98.1, solana, succinct.  The `succinct` toolchain IS present; brief 3.4 said absent | VERIFIED, command run |
| succinct toolchain targets | `ls /Users/oobi/.rustup/toolchains/succinct/lib/rustlib/` prints aarch64-apple-darwin, riscv32im-succinct-zkvm-elf, riscv64im-succinct-zkvm-elf | VERIFIED, command run |
| `ls /Users/oobi/.cargo/registry/src/*/ \| rg sp1` | empty.  No sp1 crate source is on disk | VERIFIED, command run |
| `/Users/oobi/.sp1` | bin/cargo-prove (34 MB, 2026-04-10), bin/sp1up, toolchains/, rust-toolchain-aarch64-apple-darwin.tar.gz (308 MB, 2026-04-30), circuits/ (empty) | VERIFIED, `ls -la /Users/oobi/.sp1 /Users/oobi/.sp1/bin` |
| Install command (USER step) | `curl -L https://sp1up.succinct.xyz \| bash` then `sp1up`; it installs the succinct toolchain with the riscv64im-succinct-zkvm-elf target and `cargo prove` | VERIFIED, https://docs.succinct.xyz/docs/sp1/getting-started/install (cache/docs_install.html) |

## 2.  SP1 guest ISA at v6.1.0

| Fact | Value | Status |
|---|---|---|
| Default build target | `pub const DEFAULT_TARGET: &str = "riscv64im-succinct-zkvm-elf";` | VERIFIED, crates/build/src/lib.rs:16 |
| Hypercube and 64 bits | YES.  The installed v6.1.0 is a 64-bit VM: `_start` runs `ld sp, 0(sp)`; `pc_start_abs: u64`; `memory_image: HashMap<u64, u64>`; the docs install page names only the riscv64im target | VERIFIED, crates/zkvm/entrypoint/src/lib.rs:238-240, crates/core/executor/src/program.rs:38-44, cache/docs_install.html |
| RV64 opcodes in the executor | ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, REMW, LWU, LD, SD beside the RV32 base (JAL, JALR, AUIPC, LUI, ECALL) | VERIFIED, crates/core/executor/src/opcode.rs:86-126, :140-148 |
| RV32IM ELFs on the v6.1.0 executor | not a supported target.  The riscv32im rustlib directory still ships, but the VM registers are 64-bit, so RV32 wrap-around semantics differ | BELIEVED; settle: build a hello guest with `cargo prove build --target riscv32im-succinct-zkvm-elf` and execute it |
| ELF class accepted | ELF32 or ELF64: `must be a 32-bit or 64-bit elf` | VERIFIED, crates/core/executor/src/disassembler/elf.rs:84-85 |
| Endianness | little endian: `ElfBytes::<LittleEndian>::minimal_parse(input)` | VERIFIED, elf.rs:81 |
| Machine and type | `e_machine == EM_RISCV` (243) and `e_type == ET_EXEC` (2), else bail | VERIFIED, elf.rs:86-89 |
| Extensions | `im` only.  A: `-C passes=lower-atomic` lowers atomics.  C: `INSTRUCTION_WORD_SIZE = 4`, every instruction is 4 bytes.  F and D: not in the target name | VERIFIED, crates/build/src/command/utils.rs:55, crates/primitives/src/consts.rs:22 |
| Single thread, deterministic | one interpreter loop over one register file and one memory map; the syscall table has no thread or clock syscall; sys_rand is a hint | BELIEVED; settle: read crates/core/executor/src/minimal/ecall.rs and crates/zkvm/entrypoint/src/syscalls/sys.rs:27 |
| Target triple for our encoder | none.  The encoder writes ELF bytes.  The triple matters only for `cargo prove build` | VERIFIED by construction |
| Consequence for R3 and Q1 | the pin "RV32IM ELF32" in brief R3 and 3.5 does not match the installed toolchain.  The panel picks RV64IM at v6.1.0 (then `lower` targets a small RV64IM IR) or pins an older RV32IM SP1 (v4.x Turbo) that the user installs on purpose | VERIFIED consequence of the rows above |

## 3.  Syscall table with codes (v6.1.0)

Register convention: the code is in t0 (x5); arguments are in a0 (x10) and a1 (x11); WRITE also uses a2 (x12); HINT_LEN returns its length in t0 (`lateout("t0") len`).  VERIFIED: crates/core/executor/src/syscall_code.rs:12 (`invoked by the ecall instruction with a specific value in register t0`), crates/zkvm/entrypoint/src/syscalls/io.rs:19-22 (WRITE: t0, a0 fd, a1 buf, a2 nbytes), io.rs:46-49 (HINT_LEN), io.rs:64-68 (HINT_READ: a0 ptr, a1 len), halt.rs (COMMIT: a0 word index, a1 word; HALT: a0 exit code), crates/core/executor/src/register.rs:14-36 (x1 ra, x2 sp, x5 t0, x10 a0, x11 a1, x12 a2).  Precompiles take a0 = pointer to the first operand and a1 = pointer to the second: BELIEVED; settle: crates/zkvm/entrypoint/src/syscalls/keccak_permute.rs.  The low byte of a code is the syscall id; the upper bytes carry chip metadata (`syscall_id`, `should_send`, `count_map`): BELIEVED; settle: syscall_code.rs:233-246.

Column G = line in crates/zkvm/entrypoint/src/syscalls/mod.rs (guest constants).  Column X = line in crates/core/executor/src/syscall_code.rs (executor enum `SyscallCode`, :45).  Every row VERIFIED from both cached raw files.

| Syscall | Code | G | X |
|---|---|---|---|
| HALT | 0x00000000 | 56 | 48 |
| WRITE | 0x00000002 | 59 | 51 |
| ENTER_UNCONSTRAINED | 0x00000003 | 62 | 54 |
| EXIT_UNCONSTRAINED | 0x00000004 | 65 | 57 |
| SHA_EXTEND | 0x00300105 | 68 | 60 |
| SHA_COMPRESS | 0x00010106 | 71 | 63 |
| ED_ADD | 0x00010107 | 74 | 66 |
| ED_DECOMPRESS | 0x00000108 | 77 | 69 |
| KECCAK_PERMUTE | 0x00010109 | 80 | 72 |
| SECP256K1_ADD | 0x0001010A | 83 | 75 |
| SECP256K1_DOUBLE | 0x0000010B | 86 | 78 |
| SECP256K1_DECOMPRESS | 0x0000010C | 89 | 81 |
| BN254_ADD | 0x0001010E | 104 | 84 |
| BN254_DOUBLE | 0x0000010F | 107 | 87 |
| COMMIT | 0x00000010 | 110 | 90 |
| COMMIT_DEFERRED_PROOFS | 0x0000001A | 113 | 93 |
| VERIFY_SP1_PROOF | 0x0000001B | 116 | 96 |
| BLS12381_DECOMPRESS | 0x0000011C | 125 | 99 |
| HINT_LEN | 0x000000F0 | 119 | 102 |
| HINT_READ | 0x000000F1 | 122 | 105 |
| UINT256_MUL | 0x0001011D | 128 | 108 |
| U256XU2048_MUL | 0x0001012F | 101 | 111 |
| BLS12381_ADD | 0x0001011E | 131 | 114 |
| BLS12381_DOUBLE | 0x0000011F | 134 | 117 |
| BLS12381_FP_ADD | 0x00010120 | 137 | 120 |
| BLS12381_FP_SUB | 0x00010121 | 140 | 123 |
| BLS12381_FP_MUL | 0x00010122 | 143 | 126 |
| BLS12381_FP2_ADD | 0x00010123 | 146 | 129 |
| BLS12381_FP2_SUB | 0x00010124 | 149 | 132 |
| BLS12381_FP2_MUL | 0x00010125 | 152 | 135 |
| BN254_FP_ADD | 0x00010126 | 155 | 138 |
| BN254_FP_SUB | 0x00010127 | 158 | 141 |
| BN254_FP_MUL | 0x00010128 | 161 | 144 |
| BN254_FP2_ADD | 0x00010129 | 164 | 147 |
| BN254_FP2_SUB | 0x0001012A | 167 | 150 |
| BN254_FP2_MUL | 0x0001012B | 170 | 153 |
| SECP256R1_ADD | 0x0001012C | 92 | 156 |
| SECP256R1_DOUBLE | 0x0000012D | 95 | 159 |
| SECP256R1_DECOMPRESS | 0x0000012E | 98 | 162 |
| UINT256_ADD_CARRY | 0x00010130 | 173 | 165 |
| UINT256_MUL_CARRY | 0x00010131 | 176 | 168 |
| MPROTECT | 0x00000132 | 180 | 172 |
| POSEIDON2 | 0x00000133 | 183 | 175 |

File descriptors for WRITE: `LOWEST_ALLOWED_FD = 10`; FD_PUBLIC_VALUES = 3 + 10 = 13; FD_HINT = 4 + 10 = 14; FD_ECRECOVER_HOOK = 15; FD_EDDECOMPRESS = 16.  VERIFIED, crates/primitives/src/consts.rs:52-66.  Stdout and stderr as fd 1 and 2: BELIEVED; settle: crates/core/executor/src/minimal/write.rs.

## 4.  ELF layout the v6.1.0 executor requires

| Fact | Value | Status |
|---|---|---|
| `_start` from `sp1_zkvm::entrypoint!` | global asm: `la gp, __global_pointer$` under `.option norelax`; `la sp, _STACK_TOP`; `ld sp, 0(sp)`; `call __start`.  `__start` inits the allocator and the public-values hasher (SHA-256, or blake3 under a feature), calls `main`, then `syscall_halt(0)` | VERIFIED, crates/zkvm/entrypoint/src/lib.rs:196-243, :269-280 |
| Stack top | `STACK_TOP: u64 = 0x78000000`; the stack grows down from it | VERIFIED, crates/primitives/src/consts.rs:44 |
| Load address | the linker gets `--image-base=STACK_TOP`, so the first PT_LOAD segment starts at 0x78000000; a segment with vaddr below STACK_TOP is rejected (`ELF has a segment that is below the STACK_TOP`) | VERIFIED, crates/build/src/command/utils.rs:66, elf.rs:203-206 |
| Maximum memory | `MAXIMUM_MEMORY_SIZE: u64 = (1 << 48) - 1`; a segment file_size or mem_size equal to it is rejected; the entry must differ from it and be a multiple of 4 | VERIFIED, consts.rs:4, elf.rs:96-97, :184-191 |
| Heap and input region | the default allocator is the embedded one (`MAX_MEMORY` and `INPUT_REGION_SIZE` come from a `configs` module); inputs are copied into `MAX_MEMORY - INPUT_REGION_SIZE`; a `bump` feature swaps in a bump allocator | VERIFIED shape, crates/zkvm/entrypoint/src/lib.rs:34-45; the two numbers BELIEVED; settle: crates/zkvm/entrypoint/src/allocators/embedded.rs (cached) |
| Program headers | at most 256; only PT_LOAD is loaded; PT_NOTE is read for the untrusted-program flag; a segment that is both PF_W and PF_X is rejected; page protection follows p_flags | VERIFIED, elf.rs:98-125, :207-209, :293 |
| Section table and symbols | the section table is not read; the symbol table is optional and feeds `function_symbols` for profiling only; `e_flags` is never read (no hit in elf.rs) | VERIFIED, elf.rs:144-149 and the absence of `e_flags` in elf.rs |
| pc_base | must be at least 32 and a multiple of 4 | VERIFIED, crates/core/executor/src/program.rs:82-86 |
| Public values | the guest writes bytes to fd 13 through WRITE; the entrypoint hashes them; at halt it emits 8 COMMIT ecalls (a0 = i, a1 = 32-bit word i of the SHA-256 digest), then 8 COMMIT_DEFERRED_PROOFS ecalls (a1 = 0 without the verify feature), then HALT with a0 = exit code.  A hand-written guest must compute SHA-256 over its committed bytes itself, in software or with SHA_EXTEND and SHA_COMPRESS | VERIFIED, crates/zkvm/entrypoint/src/syscalls/halt.rs:20-60; the digest check on the executor side BELIEVED; settle: crates/core/executor/src/minimal/ecall.rs |
| Input | each `SP1Stdin` buffer is one hint; the guest calls HINT_LEN (length in t0), allocates, then HINT_READ (a0 ptr, a1 len), in order | VERIFIED, io.rs:42-68 |
| Hello guest, objdump and readelf | SKIPPED.  `df -g /Users/oobi/Documents` prints 26 GiB available, below the 30 GiB floor | BELIEVED; settle after `diskfree --apply`: `cargo prove new hello` under /private/tmp/claude/kan-sp1-lang-panel, `cargo prove build`, then `/opt/homebrew/opt/llvm/bin/llvm-objdump -h` and `llvm-readelf -l` on the ELF |
| Build flags of `cargo prove build` | `-C passes=lower-atomic`, `-C link-arg=--image-base=0x78000000`, `-C panic=abort`, plus user rustflags | VERIFIED, crates/build/src/command/utils.rs:55-77 |

## 5.  Executor harness sketch (execute only)

API at v6.1.0.  VERIFIED: `sp1_sdk::blocking::ProverClient` (crates/sdk/src/blocking/mod.rs:14); `client.execute(elf, stdin).run()` returns a `Result` of `(SP1PublicValues, ExecutionReport)` (blocking/mod.rs:57, :77 shows `.cycle_limit(n)`); `ExecutionReport::total_instruction_count()` sums `opcode_counts` (crates/core/executor/src/report.rs:40-41); `total_syscall_count()` (report.rs:46); `exit_code: u64` (report.rs:32); `gas()` (report.rs:33); `sp1_sdk` re-exports `ProverClient`, `include_elf`, `ExecutionReport`, `SP1Stdin`, `SP1PublicValues`, `Elf` (crates/sdk/src/lib.rs:53-69); the async form is `ProverClient::from_env().await` then `client.execute(ELF, stdin).await` (examples/fibonacci/script/src/main.rs).  BELIEVED: `Elf::from(Vec<u8>)`, `SP1Stdin::write_slice`, `SP1PublicValues::as_slice` and a sync `blocking::ProverClient::from_env()`; settle: `symx` on crates/primitives/src/lib.rs, crates/core/machine/src/io.rs and crates/sdk/src/blocking/client.rs.  Pin: `sp1-sdk = "=6.1.0"` from https://github.com/succinctlabs/sp1/blob/v6.1.0/crates/sdk/Cargo.toml; MSRV 1.91; license MIT OR Apache-2.0.

```rust
// Cargo.toml: name = "sp1-exec-harness", edition = "2021", license = "MIT OR Apache-2.0"
// [dependencies] sp1-sdk = "=6.1.0", serde_json = "1"
use sp1_sdk::blocking::ProverClient;
use sp1_sdk::{Elf, ExecutionReport, SP1PublicValues, SP1Stdin};
use std::path::PathBuf;

struct ElfPath(PathBuf);
struct StdinPath(Option<PathBuf>);
struct CycleCount(u64);

enum HarnessError {
    Args,
    ReadElf(std::io::Error),
    ReadStdin(std::io::Error),
    Execute(String),
    Json(serde_json::Error),
}

impl std::fmt::Display for HarnessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HarnessError::Args => write!(f, "usage: sp1-exec-harness ELF [STDIN_BYTES]"),
            HarnessError::ReadElf(e) => write!(f, "read elf: {e}"),
            HarnessError::ReadStdin(e) => write!(f, "read stdin: {e}"),
            HarnessError::Execute(e) => write!(f, "execute: {e}"),
            HarnessError::Json(e) => write!(f, "json: {e}"),
        }
    }
}

fn parse_args(args: &[String]) -> Result<(ElfPath, StdinPath), HarnessError> {
    args.get(1)
        .map(|e| (ElfPath(PathBuf::from(e)), StdinPath(args.get(2).map(PathBuf::from))))
        .ok_or(HarnessError::Args)
}

fn load_stdin(path: &StdinPath) -> Result<SP1Stdin, HarnessError> {
    path.0.as_ref().map_or(Ok(SP1Stdin::new()), |p| {
        std::fs::read(p).map_err(HarnessError::ReadStdin).map(|bytes| {
            let mut stdin = SP1Stdin::new();
            stdin.write_slice(&bytes);
            stdin
        })
    })
}

fn execute(elf: &ElfPath, stdin: SP1Stdin) -> Result<(SP1PublicValues, ExecutionReport), HarnessError> {
    let bytes = std::fs::read(&elf.0).map_err(HarnessError::ReadElf)?;
    let client = ProverClient::from_env();
    client.execute(Elf::from(bytes), stdin).run().map_err(|e| HarnessError::Execute(e.to_string()))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn render(pv: &SP1PublicValues, report: &ExecutionReport) -> Result<String, HarnessError> {
    let cycles = CycleCount(report.total_instruction_count());
    let doc = serde_json::json!({
        "public_values_hex": hex(pv.as_slice()),
        "cycles": cycles.0,
        "syscalls": report.total_syscall_count(),
        "exit_code": report.exit_code,
    });
    serde_json::to_string(&doc).map_err(HarnessError::Json)
}

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let out = parse_args(&args)
        .and_then(|(elf, stdin)| load_stdin(&stdin).and_then(|s| execute(&elf, s)))
        .and_then(|(pv, report)| render(&pv, &report));
    out.map_or_else(
        |e| {
            eprintln!("{e}");
            std::process::ExitCode::FAILURE
        },
        |json| {
            println!("{json}");
            std::process::ExitCode::SUCCESS
        },
    )
}
```

## 6.  One measured prove

| Row | Result | Status |
|---|---|---|
| Local prove and verify | SKIPPED: no hello guest exists (section 4), the disk is 26 GiB (floor 30), `sysctl hw.memsize` is denied in the sandbox, and `vm_stat` shows 4333 free pages of 16 KiB (68 MiB) plus 412679 inactive pages (6.3 GiB), under the 16 GiB floor | VERIFIED skip conditions, commands run |
| Published minimums | Core and Compress proofs: CPU 16+ cores, memory 16 GB+, disk 10 GB+.  Mock and Network: 1+ core, 8 GB+, 10 GB+.  Groth16 16 GB+, PLONK 64 GB+ | VERIFIED, https://docs.succinct.xyz/docs/sp1/getting-started/hardware-requirements (cache/docs_hw.html) |
| Wall-clock and peak memory of a core prove on this machine | unknown | BELIEVED "minutes and gigabytes" per the brief; settle: `/usr/bin/time -l` around `client.prove(&pk, stdin).core()` then `client.verify(&proof, pk.verifying_key(), None)` (examples/fibonacci/script/src/main.rs), once, at the milestone exit |

## 7.  Bend 2

| Row | Result | Status |
|---|---|---|
| `command -v bend hvm` | prints nothing, rc=1.  Both absent | VERIFIED, command run |
| Install (USER step) | `curl -fsSL https://bend-lang.com/install.sh \| sh` | VERIFIED, https://raw.githubusercontent.com/HigherOrderCO/Bend/main/README.md line 113 (cache/bend_README.md) |
| Install through cabal or a release binary | the README names only the install script; the GitHub releases and contents API calls returned nothing usable in the sandbox and https://hackage.haskell.org/package/bend returned a 1219 byte page (no package) | BELIEVED; settle: https://github.com/HigherOrderCO/Bend/releases and https://github.com/HigherOrderCO/Bend/tree/main/bend2 |
| Written in Haskell, checker from Kind | the README cites the BendTT paper and a Lean formalization at bend2/bend.lean, not Kind | BELIEVED; settle: the language mix at https://github.com/HigherOrderCO/Bend |
| Compiles to HVM4 | NO per the README: `Bend 2 is a new language.  Bend 1 programs and HVM do not carry over` (README:217); the runtime is BendRT (paper, README:202).  https://raw.githubusercontent.com/HigherOrderCO/HVM/main/README.md is HVM2 (`cargo install hvm`, `hvm run <file.hvm>`, lines 35 and 41), the Bend 1 lineage | VERIFIED, cache/bend_README.md:196-232, cache/hvm_README.md:32-42 |
| Commands the README names | `bend guide` (README:122), `bend base` (README:200), `bend PROOF.bend` to check and run a file (README:124) | VERIFIED, cache/bend_README.md |
| Check command, compile command, version command | not in the README | BELIEVED: `bend check FILE.bend`, `bend --version`, and a compile subcommand that emits the BendRT C or CUDA target; settle: `bend --help` after the user install |
| Denominator design | the assay recipe copied verbatim in shape: one warm run, then 5 timed runs with a fresh scratch directory per run, the median of five (`median_of`), one line `DENOM <row> value=<n> median_ms=<n> min_ms=<n> max_ms=<n> runs=5 lines=<n>` per row, value = median_ms / lines * 1000, `uptime` printed beside the run.  Rows here: `bend_check_ms_per_kloc` (the check command on the twin) and `bend_compile_ms_per_kloc` (check plus the compile command), single core, both frozen in dev/denominators.json with `version`, `stage`, `date` keys and DENOMINATORS.sha256 checked by `shasum -c` | VERIFIED recipe, /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev/denominator.sh:1-30, :139-153, :171, dev/denominators.json:1-4 |

## 8.  RV32IM encoding reference

Reference object: /private/tmp/claude/kan-sp1-lang-panel/ref.s assembled with `/opt/homebrew/opt/llvm/bin/clang --target=riscv32-unknown-elf -march=rv32im -mno-relax -c ref.s -o ref.o` (Homebrew clang 22.1.8), read back with `/opt/homebrew/opt/llvm/bin/llvm-objdump -d -r ref.o` and `llvm-readelf -h ref.o`.  Apple clang 21 at /usr/bin/clang has no RISC-V target (`clang --print-targets` lists none) and fails on the same command, so brief 3.4 must name the Homebrew clang.  clang, lld, llvm-objdump and llvm-readelf are cross-check tools for gates only and never in the compile path.  All rows VERIFIED, command run.

| Instruction | Format | opcode | funct3 | funct7 or imm | Word | Bytes (LE) |
|---|---|---|---|---|---|---|
| add a0, a1, a2 | R | 0110011 | 000 | 0000000 | 00c58533 | 33 85 c5 00 |
| addi a0, a1, 5 | I | 0010011 | 000 | imm 5 | 00558513 | 13 85 55 00 |
| lw a0, 8(a1) | I | 0000011 | 010 | imm 8 | 0085a503 | 03 a5 85 00 |
| sw a0, 12(a1) | S | 0100011 | 010 | imm 12 | 00a5a623 | 23 a6 a5 00 |
| beq a0, a1, +36 | B | 1100011 | 000 | imm 36 | 02b50263 | 63 02 b5 02 |
| lui a0, 0x12345 | U | 0110111 | none | imm 0x12345 | 12345537 | 37 55 34 12 |
| auipc a0, 0x1 | U | 0010111 | none | imm 0x1 | 00001517 | 17 15 00 00 |
| jal ra, +24 | J | 1101111 | none | imm 24 | 018000ef | ef 00 80 01 |
| jalr ra, 4(a1) | I | 1100111 | 000 | imm 4 | 004580e7 | e7 80 45 00 |
| mul a0, a1, a2 | R | 0110011 | 000 | 0000001 | 02c58533 | 33 85 c5 02 |
| mulh a0, a1, a2 | R | 0110011 | 001 | 0000001 | 02c59533 | 33 95 c5 02 |
| div a0, a1, a2 | R | 0110011 | 100 | 0000001 | 02c5c533 | 33 c5 c5 02 |
| rem a0, a1, a2 | R | 0110011 | 110 | 0000001 | 02c5e533 | 33 e5 c5 02 |
| ecall | I | 1110011 | 000 | imm 0 | 00000073 | 73 00 00 00 |

Registers: ra = x1, sp = x2, t0 = x5, a0 = x10, a1 = x11, a2 = x12 (register.rs:14-36).  Note for RV64IM: the same words are valid RV64 instructions; `add`, `mul`, `div` and `rem` become 64-bit, and the W forms (opcode 0111011 and 0011011) give 32-bit results.  The object header: Class ELF32, Data little endian, Machine RISC-V, Type REL, Flags 0x0 (no RVC, soft float ABI).

ELF32 header fields a hand encoder writes (52 byte header, 32 byte program header; all little endian; VERIFIED against the executor checks in elf.rs and the readelf output above; the byte layout itself is the ELF standard, BELIEVED to the extent it is not re-derived here):

| Field | Value |
|---|---|
| e_ident | 7f 45 4c 46, EI_CLASS 1 (ELF32; 2 for ELF64), EI_DATA 1 (little endian), EI_VERSION 1, EI_OSABI 0, 7 pad bytes |
| e_type, e_machine, e_version | 2 (ET_EXEC), 243 (EM_RISCV), 1 |
| e_entry | the address of `_start`, a multiple of 4, at least 32, at or above 0x78000000 for v6.1.0 |
| e_phoff, e_shoff, e_flags | 52, 0, 0 |
| e_ehsize, e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx | 52, 32, 1 or 2, 0, 0, 0 |
| program header (text) | p_type 1 (PT_LOAD), p_offset, p_vaddr 0x78000000, p_paddr = p_vaddr, p_filesz, p_memsz, p_flags 5 (PF_R + PF_X), p_align 0x1000 |
| program header (data) | p_type 1, p_flags 6 (PF_R + PF_W), never PF_W with PF_X, p_align 0x1000 |

Minimal loadable ELF: 52 + 32 = 84 header bytes, then 12 code bytes at file offset 84 loaded at 0x78000000 with e_entry 0x78000000: `addi t0, x0, 0` (13 02 00 00), `addi a0, x0, 0` (13 05 00 00), `ecall` (73 00 00 00), which is HALT with exit code 0.  Total 96 bytes.  Whether the executor accepts a HALT without the 16 COMMIT ecalls in execute mode: BELIEVED; settle: run the section 5 harness on these 96 bytes.

## 9.  Local tool matrix

| Tool | Version command | Result | Status |
|---|---|---|---|
| cargo-prove | `/Users/oobi/.sp1/bin/cargo-prove prove --version` | `cargo-prove sp1 (d454975 2026-04-11T01:51:47.829463000Z)` | VERIFIED |
| rustup | `rustup --version` | `rustup 1.29.1 (d95a37b6a 2026-08-13)` | VERIFIED |
| cargo | `cargo --version` | `cargo 1.96.0-nightly (e84cb639e 2026-03-21)`; `cargocho` at /Users/oobi/.cargo/bin/cargocho | VERIFIED |
| clang (Apple) | `clang --version` | `Apple clang version 21.0.0 (clang-2100.0.123.102)`, /usr/bin/clang, no RISC-V target | VERIFIED |
| clang (Homebrew) | `/opt/homebrew/opt/llvm/bin/clang --version` | `Homebrew clang version 22.1.8`, RISC-V targets riscv32, riscv32be, riscv64, riscv64be | VERIFIED |
| lld | `ld.lld --version` | `Homebrew LLD 22.1.8`, /opt/homebrew/bin/ld.lld, lld, ld64.lld | VERIFIED |
| llvm-objdump, llvm-readelf | `/opt/homebrew/opt/llvm/bin/llvm-objdump --version` | present in /opt/homebrew/opt/llvm/bin (also llvm@16, @19, @22); not on PATH; Apple's /Library/Developer/CommandLineTools/usr/bin/llvm-objdump is version 21 without RISC-V | VERIFIED |
| wasmtime | `wasmtime --version` | `wasmtime 48.0.1 (7bac2c277 2026-08-24)` | VERIFIED |
| qemu-riscv32 | `command -v qemu-riscv32` | absent, rc=1 | VERIFIED |
| spike | `command -v spike` | absent, rc=1; USER step: `brew install riscv-isa-sim` | VERIFIED |
| ocaml | `/Users/oobi/.opam/zxcaml-p1/bin/ocaml -version` | `The OCaml toplevel, version 5.2.1` | VERIFIED |
| dune | `/Users/oobi/.opam/zxcaml-p1/bin/dune --version` | `3.24.2`; `dunecho --help` prints the DUNECHO(1) manual | VERIFIED |
| python3 | `python3 -P --version` | `Python 3.14.7` | VERIFIED |
| node | `node --version` | `v23.10.0` | VERIFIED |
| disk | `df -g /Users/oobi/Documents` | `/dev/disk3s5 460 394 26 94% /System/Volumes/Data`: 26 GiB available, below the 30 GiB floor | VERIFIED |
| bend, hvm | `command -v bend hvm` | absent | VERIFIED |

## 10.  Findings for the panel (7 max)

1. The installed SP1 is v6.1.0 (Hypercube era) and its default target is riscv64im-succinct-zkvm-elf; the executor is a 64-bit VM.  Brief R3, 3.5 and Q1 say RV32IM.  A proposal must pick RV64IM at v6.1.0 or a pinned RV32IM SP1 the user installs.
2. The succinct toolchain is present, with both riscv32im and riscv64im rustlib targets; brief 3.4 is wrong on that row.
3. The executor accepts ELF32 or ELF64, little endian, EM_RISCV, ET_EXEC, PT_LOAD segments at or above 0x78000000, no W+X segment, entry a multiple of 4; it reads no section table and needs no symbols.
4. Public values are the bytes written to fd 13; the guest itself must commit the SHA-256 digest through 8 COMMIT ecalls before HALT, so the compiler's runtime needs SHA-256 (software or the SHA precompiles).
5. All 43 syscall codes are pinned from two files of the installed commit (section 3).
6. Bend 2 does not compile to HVM per its own README; the denominator is `bend` check plus its compile command on the twin, exact subcommands to be read from `bend --help` after the user install.
7. Apple clang cannot assemble RISC-V; the gate cross-check tool is /opt/homebrew/opt/llvm/bin/clang 22.1.8 with `-mno-relax`.
