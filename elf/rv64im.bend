import Base
import ../lib/foundation.bend as F

# RV64IM instruction encoder. One constructor per IR row of
# design/attest-m0/parts/06-emission.md section 6.2 and no more.
# Bend 2 has no hex literal, so each literal shows its hex value in a comment.
# An immediate is a U32 in two's complement form: -1 is 4294967295 (Rv.neg(1)).
# Every instruction is 4 bytes. There is no C extension, so every row states
# width 32n and the ENC-XCHECK leg refuses any other width.

type Rv.reg is Data:
  Rv.Reg{index: U32}

type Rv.word is Data:
  Rv.Word{mnemonic: String, width: Nat, bits: U32}

type Rv.insn is Data:
  Rv.Add{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Mul{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Mulh{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Div{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Rem{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Addi{rd: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Lui{rd: Rv.reg, imm: U32}
  Rv.Auipc{rd: Rv.reg, imm: U32}
  Rv.Lw{rd: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Lwu{rd: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Ld{rd: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Sw{rs2: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Sd{rs2: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Beq{rs1: Rv.reg, rs2: Rv.reg, imm: U32}
  Rv.Jal{rd: Rv.reg, imm: U32}
  Rv.Jalr{rd: Rv.reg, rs1: Rv.reg, imm: U32}
  Rv.Addw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Subw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Sllw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Srlw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Sraw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Mulw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Divw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Remw{rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg}
  Rv.Ecall{}

# The registers the lowering uses (06-emission.md:13).
def Rv.x0() -> Rv.reg:
  Rv.Reg{0}

def Rv.ra() -> Rv.reg:
  Rv.Reg{1}

def Rv.sp() -> Rv.reg:
  Rv.Reg{2}

def Rv.t0() -> Rv.reg:
  Rv.Reg{5}

def Rv.a0() -> Rv.reg:
  Rv.Reg{10}

def Rv.a1() -> Rv.reg:
  Rv.Reg{11}

def Rv.a2() -> Rv.reg:
  Rv.Reg{12}

# Two's complement negation of a small magnitude.
def Rv.neg(n: U32) -> U32:
  (0 - n : U32)

def Rv.bits(word: Rv.word) -> U32:
  match word:
    case Rv.Word{mnemonic, width, bits}: bits

def Rv.check(ok: Bool, what: String, value: U32) -> Result<&2, &2, F.Error.t, U32>:
  match ok:
    case True{}: Done{value}
    case False{}: Fail{F.Error.Overflow{what}}

# value in [0, bound]
def Rv.unsigned(bound: U32, +value: U32, what: String) -> Result<&2, &2, F.Error.t, U32>:
  Rv.check((value <= bound : U32), what, value)

# value in [-bound, bound - 1] in two's complement form
def Rv.signed(+bound: U32, +value: U32, what: String) -> Result<&2, &2, F.Error.t, U32>:
  Rv.check(Bool.or((value < bound : U32), (value >= (0 - bound) : U32)), what, value)

def Rv.even(+value: U32, what: String) -> Result<&2, &2, F.Error.t, U32>:
  Rv.check(U32.is_eq((value .&. 1 : U32), 0), what, value)

def Rv.offset_even(bound: U32, even: Result<&2, &2, F.Error.t, U32>, what: String) -> Result<&2, &2, F.Error.t, U32>:
  match even:
    case Fail{error}: Fail{error}
    case Done{value}: Rv.signed(bound, value, what)

# A branch or jump offset: even and in signed range.
def Rv.offset(bound: U32, value: U32, +what: String) -> Result<&2, &2, F.Error.t, U32>:
  Rv.offset_even(bound, Rv.even(value, what), what)

def Rv.reg_bits(reg: Rv.reg) -> Result<&2, &2, F.Error.t, U32>:
  match reg:
    case Rv.Reg{index}: Rv.unsigned(31, index, "register index above 31")

# Place a field: acc .|. (part << shift). The first failure wins.
def Rv.field(acc: Result<&2, &2, F.Error.t, U32>, part: Result<&2, &2, F.Error.t, U32>, shift: Nat) -> Result<&2, &2, F.Error.t, U32>:
  match acc part:
    case Done{a} Done{p}: Done{(a .|. (p << shift) : U32)}
    case Done{a} Fail{error}: Fail{error}
    case Fail{error} Done{p}: Fail{error}
    case Fail{error} Fail{later}: Fail{error}

def Rv.base(opcode: U32, f3: U32, f7: U32) -> Result<&2, &2, F.Error.t, U32>:
  Done{(opcode .|. (f3 << 12n) .|. (f7 << 25n) : U32)}

# R: f7[31:25] rs2[24:20] rs1[19:15] f3[14:12] rd[11:7] opcode[6:0]
def Rv.r_type(opcode: U32, f3: U32, f7: U32, rd: Rv.reg, rs1: Rv.reg, rs2: Rv.reg) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.field(Rv.base(opcode, f3, f7), Rv.reg_bits(rd), 7n), Rv.reg_bits(rs1), 15n), Rv.reg_bits(rs2), 20n)

def Rv.i_bits(opcode: U32, f3: U32, rd: Rv.reg, rs1: Rv.reg, i: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.field(Rv.base(opcode, f3, 0), Rv.reg_bits(rd), 7n), Rv.reg_bits(rs1), 15n), Done{(i .&. 4095 : U32)}, 20n)

def Rv.i_checked(opcode: U32, f3: U32, rd: Rv.reg, rs1: Rv.reg, imm: Result<&2, &2, F.Error.t, U32>) -> Result<&2, &2, F.Error.t, U32>:
  match imm:
    case Fail{error}: Fail{error}
    case Done{i}: Rv.i_bits(opcode, f3, rd, rs1, i)

# I: imm[31:20] rs1[19:15] f3[14:12] rd[11:7] opcode[6:0]
def Rv.i_type(opcode: U32, f3: U32, rd: Rv.reg, rs1: Rv.reg, imm: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.i_checked(opcode, f3, rd, rs1, Rv.signed(2048, imm, "imm12 out of range"))

def Rv.s_bits(opcode: U32, f3: U32, rs2: Rv.reg, rs1: Rv.reg, +i: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.field(Rv.field(Rv.base(opcode, f3, 0), Done{(i .&. 31 : U32)}, 7n), Rv.reg_bits(rs1), 15n), Rv.reg_bits(rs2), 20n), Done{((i >> 5n) .&. 127 : U32)}, 25n)

def Rv.s_checked(opcode: U32, f3: U32, rs2: Rv.reg, rs1: Rv.reg, imm: Result<&2, &2, F.Error.t, U32>) -> Result<&2, &2, F.Error.t, U32>:
  match imm:
    case Fail{error}: Fail{error}
    case Done{i}: Rv.s_bits(opcode, f3, rs2, rs1, i)

# S: imm[11:5] at [31:25], rs2[24:20] rs1[19:15] f3[14:12] imm[4:0] at [11:7] opcode[6:0]
def Rv.s_type(opcode: U32, f3: U32, rs2: Rv.reg, rs1: Rv.reg, imm: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.s_checked(opcode, f3, rs2, rs1, Rv.signed(2048, imm, "store imm12 out of range"))

def Rv.b_bits(opcode: U32, f3: U32, rs1: Rv.reg, rs2: Rv.reg, +i: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.field(Rv.field(Rv.field(Rv.field(Rv.base(opcode, f3, 0), Done{((i >> 11n) .&. 1 : U32)}, 7n), Done{((i >> 1n) .&. 15 : U32)}, 8n), Rv.reg_bits(rs1), 15n), Rv.reg_bits(rs2), 20n), Done{((i >> 5n) .&. 63 : U32)}, 25n), Done{((i >> 12n) .&. 1 : U32)}, 31n)

def Rv.b_checked(opcode: U32, f3: U32, rs1: Rv.reg, rs2: Rv.reg, imm: Result<&2, &2, F.Error.t, U32>) -> Result<&2, &2, F.Error.t, U32>:
  match imm:
    case Fail{error}: Fail{error}
    case Done{i}: Rv.b_bits(opcode, f3, rs1, rs2, i)

# B: imm[12] at 31, imm[10:5] at [30:25], rs2 rs1 f3, imm[4:1] at [11:8], imm[11] at 7, opcode
def Rv.b_type(opcode: U32, f3: U32, rs1: Rv.reg, rs2: Rv.reg, imm: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.b_checked(opcode, f3, rs1, rs2, Rv.offset(4096, imm, "branch imm13 odd or out of range"))

# U: imm20 at [31:12], rd, opcode
def Rv.u_type(opcode: U32, rd: Rv.reg, imm: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.base(opcode, 0, 0), Rv.reg_bits(rd), 7n), Rv.unsigned(1048575, imm, "imm20 out of range"), 12n)

def Rv.j_bits(opcode: U32, rd: Rv.reg, +i: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.field(Rv.field(Rv.field(Rv.field(Rv.field(Rv.base(opcode, 0, 0), Rv.reg_bits(rd), 7n), Done{((i >> 12n) .&. 255 : U32)}, 12n), Done{((i >> 11n) .&. 1 : U32)}, 20n), Done{((i >> 1n) .&. 1023 : U32)}, 21n), Done{((i >> 20n) .&. 1 : U32)}, 31n)

def Rv.j_checked(opcode: U32, rd: Rv.reg, imm: Result<&2, &2, F.Error.t, U32>) -> Result<&2, &2, F.Error.t, U32>:
  match imm:
    case Fail{error}: Fail{error}
    case Done{i}: Rv.j_bits(opcode, rd, i)

# J: imm[20] at 31, imm[10:1] at [30:21], imm[11] at 20, imm[19:12] at [19:12], rd, opcode
def Rv.j_type(opcode: U32, rd: Rv.reg, imm: U32) -> Result<&2, &2, F.Error.t, U32>:
  Rv.j_checked(opcode, rd, Rv.offset(1048576, imm, "jump imm21 odd or out of range"))

def Rv.done(mnemonic: String, width: Nat, bits: Result<&2, &2, F.Error.t, U32>) -> Result<&2, &2, F.Error.t, Rv.word>:
  match bits:
    case Fail{error}: Fail{error}
    case Done{b}: Done{Rv.Word{mnemonic, width, b}}

# Opcodes: 51 = 0x33 OP, 19 = 0x13 OP-IMM, 55 = 0x37 LUI, 23 = 0x17 AUIPC,
# 3 = 0x03 LOAD, 35 = 0x23 STORE, 99 = 0x63 BRANCH, 111 = 0x6f JAL,
# 103 = 0x67 JALR, 59 = 0x3b OP-32, 115 = 0x73 SYSTEM. f7 32 = 0100000.
def Rv.encode(insn: Rv.insn) -> Result<&2, &2, F.Error.t, Rv.word>:
  match insn:
    case Rv.Add{rd, rs1, rs2}: Rv.done("add", 32n, Rv.r_type(51, 0, 0, rd, rs1, rs2))
    case Rv.Mul{rd, rs1, rs2}: Rv.done("mul", 32n, Rv.r_type(51, 0, 1, rd, rs1, rs2))
    case Rv.Mulh{rd, rs1, rs2}: Rv.done("mulh", 32n, Rv.r_type(51, 1, 1, rd, rs1, rs2))
    case Rv.Div{rd, rs1, rs2}: Rv.done("div", 32n, Rv.r_type(51, 4, 1, rd, rs1, rs2))
    case Rv.Rem{rd, rs1, rs2}: Rv.done("rem", 32n, Rv.r_type(51, 6, 1, rd, rs1, rs2))
    case Rv.Addi{rd, rs1, imm}: Rv.done("addi", 32n, Rv.i_type(19, 0, rd, rs1, imm))
    case Rv.Lui{rd, imm}: Rv.done("lui", 32n, Rv.u_type(55, rd, imm))
    case Rv.Auipc{rd, imm}: Rv.done("auipc", 32n, Rv.u_type(23, rd, imm))
    case Rv.Lw{rd, rs1, imm}: Rv.done("lw", 32n, Rv.i_type(3, 2, rd, rs1, imm))
    case Rv.Lwu{rd, rs1, imm}: Rv.done("lwu", 32n, Rv.i_type(3, 6, rd, rs1, imm))
    case Rv.Ld{rd, rs1, imm}: Rv.done("ld", 32n, Rv.i_type(3, 3, rd, rs1, imm))
    case Rv.Sw{rs2, rs1, imm}: Rv.done("sw", 32n, Rv.s_type(35, 2, rs2, rs1, imm))
    case Rv.Sd{rs2, rs1, imm}: Rv.done("sd", 32n, Rv.s_type(35, 3, rs2, rs1, imm))
    case Rv.Beq{rs1, rs2, imm}: Rv.done("beq", 32n, Rv.b_type(99, 0, rs1, rs2, imm))
    case Rv.Jal{rd, imm}: Rv.done("jal", 32n, Rv.j_type(111, rd, imm))
    case Rv.Jalr{rd, rs1, imm}: Rv.done("jalr", 32n, Rv.i_type(103, 0, rd, rs1, imm))
    case Rv.Addw{rd, rs1, rs2}: Rv.done("addw", 32n, Rv.r_type(59, 0, 0, rd, rs1, rs2))
    case Rv.Subw{rd, rs1, rs2}: Rv.done("subw", 32n, Rv.r_type(59, 0, 32, rd, rs1, rs2))
    case Rv.Sllw{rd, rs1, rs2}: Rv.done("sllw", 32n, Rv.r_type(59, 1, 0, rd, rs1, rs2))
    case Rv.Srlw{rd, rs1, rs2}: Rv.done("srlw", 32n, Rv.r_type(59, 5, 0, rd, rs1, rs2))
    case Rv.Sraw{rd, rs1, rs2}: Rv.done("sraw", 32n, Rv.r_type(59, 5, 32, rd, rs1, rs2))
    case Rv.Mulw{rd, rs1, rs2}: Rv.done("mulw", 32n, Rv.r_type(59, 0, 1, rd, rs1, rs2))
    case Rv.Divw{rd, rs1, rs2}: Rv.done("divw", 32n, Rv.r_type(59, 4, 1, rd, rs1, rs2))
    case Rv.Remw{rd, rs1, rs2}: Rv.done("remw", 32n, Rv.r_type(59, 6, 1, rd, rs1, rs2))
    case Rv.Ecall{}: Done{Rv.Word{"ecall", 32n, 115}}
