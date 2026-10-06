import Base
import ../lib/foundation.bend as F
import ./rv64im.bend as R

# ELF64 image writer for the layout of design/attest-m0/parts/06-emission.md
# section 6.3. The output is a byte list: each cell is a U32 in 0..255, little
# endian, and every 8-byte field is written as a low and a high 32-bit half.
# One PT_LOAD header carries the text. The data header is a lower/ concern.
# No LLVM, rustc, assembler or linker takes part in this path.
#
# Text follows the headers and zero padding, with p_offset congruent to
# p_vaddr modulo p_align. The default text offset is 0x1000.

def Elf.byte(+value: U32, shift: Nat) -> U32:
  ((value >> shift) .&. 255 : U32)

def Elf.le16(+value: U32) -> List<&2, U32>:
  [Elf.byte(value, 0n), Elf.byte(value, 8n)]

def Elf.le32(+value: U32) -> List<&2, U32>:
  [Elf.byte(value, 0n), Elf.byte(value, 8n), Elf.byte(value, 16n), Elf.byte(value, 24n)]

def Elf.le64(low: U32, high: U32) -> List<&2, U32>:
  List.append(&2, U32, Elf.le32(low), Elf.le32(high))

def Elf.cat(parts: List<&2, List<&2, U32>>) -> List<&2, U32>:
  List.concat(&2, U32, parts)

# 7f 45 4c 46, EI_CLASS 2, EI_DATA 1, EI_VERSION 1, EI_OSABI 0, 8 zero bytes
def Elf.ident() -> List<&2, U32>:
  [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# e_type 2, e_machine 243, e_version 1, e_entry, e_phoff 64, e_shoff 0,
# e_flags 0, e_ehsize 64, e_phentsize 56, e_phnum, e_shentsize 0, e_shnum 0,
# e_shstrndx 0: 64 bytes.
def Elf.header(entry: U32, phnum: U32) -> List<&2, U32>:
  Elf.cat([Elf.ident(), Elf.le16(2), Elf.le16(243), Elf.le32(1), Elf.le64(entry, 0), Elf.le64(64, 0), Elf.le64(0, 0), Elf.le32(0), Elf.le16(64), Elf.le16(56), Elf.le16(phnum), Elf.le16(0), Elf.le16(0), Elf.le16(0)])

# p_type 1, p_flags, p_offset, p_vaddr, p_paddr = p_vaddr, p_filesz, p_memsz = p_filesz, p_align: 56 bytes.
def Elf.load_header(flags: U32, offset: U32, +vaddr: U32, +size: U32, align: U32) -> List<&2, U32>:
  Elf.cat([Elf.le32(1), Elf.le32(flags), Elf.le64(offset, 0), Elf.le64(vaddr, 0), Elf.le64(vaddr, 0), Elf.le64(size, 0), Elf.le64(size, 0), Elf.le64(align, 0)])

def Elf.code_bytes(words: List<&2, U32>) -> List<&2, U32>:
  match words:
    case Nil{}: []
    case Con{word, rest}: List.append(&2, U32, Elf.le32(word), Elf.code_bytes(rest))

# The first offset after both headers with the requested address residue.
# ELF alignments are zero, one, or powers of two.
def Elf.offset_checked(zero: Bool, vaddr: U32, align: U32) -> U32:
  match zero:
    case True{}: 120
    case False{}: (120 + ((vaddr - 120) .&. (align - 1)) : U32)

def Elf.text_offset(vaddr: U32, +align: U32) -> U32:
  Elf.offset_checked(U32.is_eq(align, 0), vaddr, align)

def Elf.zeros(count: Nat) -> List<&2, U32>:
  match count:
    case 0n: []
    case 1n+ rest: 0 <> Elf.zeros(rest)

def Elf.padded(+text: List<&2, U32>, entry: U32, text_vaddr: U32, align: U32, +offset: U32) -> List<&2, U32>:
  Elf.cat([Elf.header(entry, 1), Elf.load_header(5, offset, text_vaddr, U32.from_nat(List.length(&2, U32, text)), align), Elf.zeros(U32.to_nat((offset - 120 : U32))), text])

# header (64) + text PT_LOAD header (56) + alignment padding + text
def Elf.layout(text: List<&2, U32>, entry: U32, +text_vaddr: U32, +align: U32) -> List<&2, U32>:
  Elf.padded(text, entry, text_vaddr, align, Elf.text_offset(text_vaddr, align))

def Elf.image(code: List<&2, U32>, entry: U32, text_vaddr: U32, align: U32) -> List<&2, U32>:
  Elf.layout(Elf.code_bytes(code), entry, text_vaddr, align)

# 0x78000000
def Elf.text_base() -> U32:
  2013265920

# 0x1000
def Elf.page() -> U32:
  4096

def Elf.word_cons(word: Result<&2, &2, F.Error.t, R.Rv.word>, rest: Result<&2, &2, F.Error.t, List<&2, U32>>) -> Result<&2, &2, F.Error.t, List<&2, U32>>:
  match word rest:
    case Done{w} Done{tail}: Done{R.Rv.bits(w) <> tail}
    case Done{w} Fail{error}: Fail{error}
    case Fail{error} Done{tail}: Fail{error}
    case Fail{error} Fail{later}: Fail{error}

def Elf.words(insns: List<&2, R.Rv.insn>) -> Result<&2, &2, F.Error.t, List<&2, U32>>:
  match insns:
    case Nil{}: Done{[]}
    case Con{insn, rest}: Elf.word_cons(R.Rv.encode(insn), Elf.words(rest))

# HALT: addi t0, x0, 0; addi a0, x0, 0; ecall (06-emission.md:49)
def Elf.halt() -> List<&2, R.Rv.insn>:
  [R.Rv.Addi{R.Rv.t0(), R.Rv.x0(), 0}, R.Rv.Addi{R.Rv.a0(), R.Rv.x0(), 0}, R.Rv.Ecall{}]

def Elf.text_image(words: Result<&2, &2, F.Error.t, List<&2, U32>>) -> Result<&2, &2, F.Error.t, List<&2, U32>>:
  match words:
    case Fail{error}: Fail{error}
    case Done{code}: Done{Elf.image(code, Elf.text_base(), Elf.text_base(), Elf.page())}


# 64 + 56 + 3976 padding + 12 = 4108 bytes, e_entry 0x78000000
def Elf.halt_image() -> Result<&2, &2, F.Error.t, List<&2, U32>>:
  Elf.text_image(Elf.words(Elf.halt()))
