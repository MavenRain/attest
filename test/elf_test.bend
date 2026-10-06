import Base
import ../lib/foundation.bend as F
import ../elf/rv64im.bend as R
import ../elf/elf64.bend as E

# Encoder self-test with no external tool: the 14 dossier words
# (kan-sp1-lang-dossier-toolchain.md:222-237) and the 4108-byte HALT image.

def ElfTest.word_is(encoded: Result<&2, &2, F.Error.t, R.Rv.word>, expected: U32) -> Bool:
  match encoded:
    case Fail{error}: False{}
    case Done{word}: U32.is_eq(R.Rv.bits(word), expected)

def ElfTest.word(insn: R.Rv.insn, expected: U32) -> Bool:
  ElfTest.word_is(R.Rv.encode(insn), expected)

def ElfTest.same(left: List<&2, U32>, right: List<&2, U32>) -> Bool:
  match left right:
    case Nil{} Nil{}: True{}
    case Nil{} Con{r, rs}: False{}
    case Con{l, ls} Nil{}: False{}
    case Con{l, ls} Con{r, rs}: Bool.and(U32.is_eq(l, r), ElfTest.same(ls, rs))

# header 64, text PT_LOAD header 56, padding to 4096, then the 12 code bytes
# (addi t0, x0, 0 is 0x00000293: rd = x5; the 13 02 00 00 of the dossier is addi tp, x0, 0)
def ElfTest.halt_expected() -> List<&2, U32>:
  E.Elf.cat([[127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 243, 0, 1, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 56, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0], E.Elf.zeros(3976n), [147, 2, 0, 0, 19, 5, 0, 0, 115, 0, 0, 0]])

def ElfTest.halt_is(image: Result<&2, &2, F.Error.t, List<&2, U32>>) -> Bool:
  match image:
    case Fail{error}: False{}
    case Done{bytes}: ElfTest.same(bytes, ElfTest.halt_expected())

def ElfTest.halt() -> Bool:
  ElfTest.halt_is(E.Elf.halt_image())

def ElfTest.length_is(image: Result<&2, &2, F.Error.t, List<&2, U32>>) -> Bool:
  match image:
    case Fail{error}: False{}
    case Done{bytes}: Nat.is_eq(List.length(&2, U32, bytes), 4108n)

def ElfTest.halt_length() -> Bool:
  ElfTest.length_is(E.Elf.halt_image())

def ElfTest.offsets() -> Bool:
  Bool.and(U32.is_eq(E.Elf.text_offset(0, 0), 120), Bool.and(U32.is_eq(E.Elf.text_offset(0, 1), 120), Bool.and(U32.is_eq(E.Elf.text_offset(0, 4), 120), Bool.and(U32.is_eq(E.Elf.text_offset(2013265920, 4096), 4096), U32.is_eq(E.Elf.text_offset(2013265924, 4096), 4100)))))

def ElfTest.checks() -> List<&2, Bool>:
  [ElfTest.word(R.Rv.Add{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}, 12944691)  # add 0x00c58533,
   ElfTest.word(R.Rv.Addi{R.Rv.a0(), R.Rv.a1(), 5}, 5604627)  # addi 0x00558513,
   ElfTest.word(R.Rv.Lw{R.Rv.a0(), R.Rv.a1(), 8}, 8758531)  # lw 0x0085a503,
   ElfTest.word(R.Rv.Sw{R.Rv.a0(), R.Rv.a1(), 12}, 10855971)  # sw 0x00a5a623,
   ElfTest.word(R.Rv.Beq{R.Rv.a0(), R.Rv.a1(), 36}, 45417059)  # beq 0x02b50263,
   ElfTest.word(R.Rv.Lui{R.Rv.a0(), 74565}, 305419575)  # lui 0x12345537,
   ElfTest.word(R.Rv.Auipc{R.Rv.a0(), 1}, 5399)  # auipc 0x00001517,
   ElfTest.word(R.Rv.Jal{R.Rv.ra(), 24}, 25166063)  # jal 0x018000ef,
   ElfTest.word(R.Rv.Jalr{R.Rv.ra(), R.Rv.a1(), 4}, 4554983)  # jalr 0x004580e7,
   ElfTest.word(R.Rv.Mul{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}, 46499123)  # mul 0x02c58533,
   ElfTest.word(R.Rv.Mulh{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}, 46503219)  # mulh 0x02c59533,
   ElfTest.word(R.Rv.Div{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}, 46515507)  # div 0x02c5c533,
   ElfTest.word(R.Rv.Rem{R.Rv.a0(), R.Rv.a1(), R.Rv.a2()}, 46523699)  # rem 0x02c5e533,
   ElfTest.word(R.Rv.Ecall{}, 115)  # ecall 0x00000073,
   ElfTest.halt_length(),
   ElfTest.halt(),
   ElfTest.offsets()]

def ElfTest.add(result: Bool, total: Nat) -> Nat:
  match result:
    case True{}: (1n + total : Nat)
    case False{}: total

def ElfTest.count(results: List<&2, Bool>) -> Nat:
  match results:
    case Nil{}: 0n
    case Con{result, rest}: ElfTest.add(result, ElfTest.count(rest))

def ElfTest.exit(passed: Bool) -> IO(Unit):
  match passed:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.die(Unit, 1, "")

def main() -> IO(Unit):
  +passed: Nat = ElfTest.count(ElfTest.checks())
  do IO<Unit>:
    a: Unit <- IO.print("ELF-ENCODER pass=" ++ Nat.show(passed) ++ " total=17")
    ElfTest.exit(Nat.is_eq(passed, 17n))
