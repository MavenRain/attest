import Base
import ../lib/foundation.bend as F
import ../elf/rv64im.bend as R
import ../elf/elf64.bend as E

# ENC-XCHECK dump: one `ROW name mnemonic width word` line per reference row
# (14 dossier rows, then 13 object rows), then one `HALT b0 .. b4107` line.
# dev/enc-xcheck.py reads this output.

type Enc.row is Data:
  Enc.Row{name: String, insn: R.Rv.insn}

def Enc.rows() -> List<&2, Enc.row>:
  [Enc.Row{"add", R.Rv.Add{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"addi", R.Rv.Addi{R.Rv.a0(), R.Rv.a1(), 5}},
   Enc.Row{"lw", R.Rv.Lw{R.Rv.a0(), R.Rv.a1(), 8}},
   Enc.Row{"sw", R.Rv.Sw{R.Rv.a0(), R.Rv.a1(), 12}},
   Enc.Row{"beq", R.Rv.Beq{R.Rv.a0(), R.Rv.a1(), 36}},
   Enc.Row{"lui", R.Rv.Lui{R.Rv.a0(), 74565}},
   Enc.Row{"auipc", R.Rv.Auipc{R.Rv.a0(), 1}},
   Enc.Row{"jal", R.Rv.Jal{R.Rv.ra(), 24}},
   Enc.Row{"jalr", R.Rv.Jalr{R.Rv.ra(), R.Rv.a1(), 4}},
   Enc.Row{"mul", R.Rv.Mul{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"mulh", R.Rv.Mulh{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"div", R.Rv.Div{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"rem", R.Rv.Rem{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"ecall", R.Rv.Ecall{}},
   Enc.Row{"addi-neg", R.Rv.Addi{R.Rv.a0(), R.Rv.a0(), R.Rv.neg(1)}},
   Enc.Row{"lwu", R.Rv.Lwu{R.Rv.a0(), R.Rv.a0(), 0}},
   Enc.Row{"ld", R.Rv.Ld{R.Rv.a0(), R.Rv.sp(), 0}},
   Enc.Row{"sd", R.Rv.Sd{R.Rv.a0(), R.Rv.sp(), 0}},
   Enc.Row{"addw", R.Rv.Addw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"subw", R.Rv.Subw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"sllw", R.Rv.Sllw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"srlw", R.Rv.Srlw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"sraw", R.Rv.Sraw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"mulw", R.Rv.Mulw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"divw", R.Rv.Divw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"remw", R.Rv.Remw{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}},
   Enc.Row{"halt-addi", R.Rv.Addi{R.Rv.t0(), R.Rv.x0(), 0}}]

def Enc.line(name: String, word: R.Rv.word) -> String:
  match word:
    case R.Rv.Word{mnemonic, width, bits}: "ROW " ++ name ++ " " ++ mnemonic ++ " " ++ Nat.show(width) ++ " " ++ U32.show(bits) ++ "\n"

def Enc.join(name: String, word: Result<&2, &2, F.Error.t, R.Rv.word>, rest: Result<&2, &2, F.Error.t, String>) -> Result<&2, &2, F.Error.t, String>:
  match word rest:
    case Done{w} Done{text}: Done{Enc.line(name, w) ++ text}
    case Done{w} Fail{error}: Fail{error}
    case Fail{error} Done{text}: Fail{error}
    case Fail{error} Fail{later}: Fail{error}

def Enc.dump_row(row: Enc.row, rest: Result<&2, &2, F.Error.t, String>) -> Result<&2, &2, F.Error.t, String>:
  match row:
    case Enc.Row{name, insn}: Enc.join(name, R.Rv.encode(insn), rest)

def Enc.dump(rows: List<&2, Enc.row>) -> Result<&2, &2, F.Error.t, String>:
  match rows:
    case Nil{}: Done{""}
    case Con{row, rest}: Enc.dump_row(row, Enc.dump(rest))

def Enc.bytes(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{}: "\n"
    case Con{b, rest}: " " ++ U32.show(b) ++ Enc.bytes(rest)

def Enc.report(dump: Result<&2, &2, F.Error.t, String>, image: Result<&2, &2, F.Error.t, List<&2, U32>>) -> Result<&2, &2, F.Error.t, String>:
  match dump image:
    case Done{text} Done{bytes}: Done{text ++ "HALT" ++ Enc.bytes(bytes)}
    case Done{text} Fail{error}: Fail{error}
    case Fail{error} Done{bytes}: Fail{error}
    case Fail{error} Fail{later}: Fail{error}

def Enc.emit(report: Result<&2, &2, F.Error.t, String>) -> IO(Unit):
  match report:
    case Fail{error}: IO.die(Unit, 1, F.Error.to_string(error))
    case Done{text}: IO.write(text)

def main() -> IO(Unit):
  Enc.emit(Enc.report(Enc.dump(Enc.rows()), E.Elf.halt_image()))
