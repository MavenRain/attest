import Base

import ../lib/foundation.bend as F

import token.bend as T

type Lexer.word is Data:
  Lexer.Word{text: String, kind: T.Token.kind}

type Lexer.span_result is Data:
  Lexer.Span{text: String, loc: T.Token.loc, rest: String}

type Lexer.bytes_result is Data:
  Lexer.BytesResult{bytes: List<&2, U32>, loc: T.Token.loc, rest: String}

type Lexer.job1 is Data:
  Lexer.Job1_0{equal: Bool, s: String, tail: List<&2, Lexer.word>, kind: T.Token.kind}
  Lexer.Job1_1{words: List<&2, Lexer.word>, s: String}


type Lexer.job2 is Data:
  Lexer.Job2_0{take: Bool, mode: Bool, loc: T.Token.loc, head: Char, tail: String, acc: String}
  Lexer.Job2_1{mode: Bool, cs: String, loc: T.Token.loc, acc: String}


type Lexer.job3 is Data:
  Lexer.Job3_0{cs: String, loc: T.Token.loc, acc: List<&2, U32>}
  Lexer.Job3_1{code: U32, loc: T.Token.loc, acc: List<&2, U32>, escaped: Char, rest: String}
  Lexer.Job3_2{hi: Maybe<&2, U32>, lo: Maybe<&2, U32>, loc: T.Token.loc, acc: List<&2, U32>, rest3: String}
  Lexer.Job3_3{value: Maybe<&2, U32>, loc: T.Token.loc, acc: List<&2, U32>, escaped: Char, rest: String}
  Lexer.Job3_4{c: U32, loc: T.Token.loc, acc: List<&2, U32>, tail: String}


type Lexer.job4 is Data:
  Lexer.Job4_0{cs: String, loc: T.Token.loc}
  Lexer.Job4_1{newline: Bool, loc: T.Token.loc, tail: String}


type Lexer.job5 is Data:
  Lexer.Job5_0{quote: Bool, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char, tail: String}
  Lexer.Job5_1{comment: Bool, arrow: Bool, loc: T.Token.loc, acc: List<&2, T.Token.t>, tail: String}
  Lexer.Job5_2{arrow: Bool, loc: T.Token.loc, acc: List<&2, T.Token.t>, tail: String}
  Lexer.Job5_3{assign: Bool, loc: T.Token.loc, acc: List<&2, T.Token.t>, tail: String}
  Lexer.Job5_4{unit: Bool, loc: T.Token.loc, acc: List<&2, T.Token.t>, tail: String}
  Lexer.Job5_5{tokens: Result<&2, &2, F.Error.t, List<&2, T.Token.t>>, acc: List<&2, T.Token.t>, after: T.Token.loc, rest: String}
  Lexer.Job5_6{digit: Bool, ident: Bool, c: U32, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char, tail: String}
  Lexer.Job5_7{bytes: Result<&2, &2, F.Error.t, Lexer.bytes_result>, loc: T.Token.loc, acc: List<&2, T.Token.t>}
  Lexer.Job5_8{n: Result<&2, &2, F.Error.t, String>, loc: T.Token.loc, acc: List<&2, T.Token.t>, after: T.Token.loc, rest: String}
  Lexer.Job5_9{lifted: Lexer.span_result, loc: T.Token.loc, acc: List<&2, T.Token.t>}
  Lexer.Job5_10{lifted: Lexer.span_result, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char}
  Lexer.Job5_11{lifted: Lexer.span_result, acc: List<&2, T.Token.t>}
  Lexer.Job5_12{lifted: Lexer.span_result, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char}
  Lexer.Job5_13{lifted: Lexer.span_result, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char}
  Lexer.Job5_14{c: U32, loc: T.Token.loc, acc: List<&2, T.Token.t>, head: Char, tail: String}
  Lexer.Job5_15{cs: String, loc: T.Token.loc, acc: List<&2, T.Token.t>}


def Lexer.error(-A: Data, +loc: T.Token.loc, +message: String) -> Result<&2, &2, F.Error.t, A>:
  T.Token.Loc{+line, +col} = loc
  Fail{F.Error.Parse{message,line,col}}

def Lexer.is_digit(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57))

def Lexer.is_ident_start(+c: U32) -> Bool:
  Bool.or(Bool.or(Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)), Bool.and(U32.is_ge(c, 65), U32.is_le(c, 90))), U32.is_eq(c, 95))

def Lexer.is_ident_char(+c: U32) -> Bool:
  Bool.or(Bool.or(Lexer.is_ident_start(c), Lexer.is_digit(c)), U32.is_eq(c, 39))

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Lexer.dispatch1(+job: Lexer.job1) -> T.Token.kind:
  match job:
    case Lexer.Job1_0{+equal, +s, +tail, +kind}:
      match equal:
        case True{}: kind
        case False{}: Lexer.dispatch1(Lexer.Job1_1{tail, s})
    case Lexer.Job1_1{+words, +s}:
      match words:
        case Nil{}: T.Token.Ident{s}
        case Con{+head, +tail}:
          Lexer.Word{+word, +kind} = head
          +equal : Bool = String.eq(word, s)
          Lexer.dispatch1(Lexer.Job1_0{equal, s, tail, kind})


def Lexer.ident_kind(+s: String) -> T.Token.kind:
  Lexer.dispatch1(Lexer.Job1_1{[Lexer.Word{"def", T.Token.KDef{}}, Lexer.Word{"axiom", T.Token.KAxiom{}}, Lexer.Word{"fun", T.Token.KFun{}}, Lexer.Word{"inj", T.Token.KInj{}}, Lexer.Word{"of", T.Token.KOf{}}, Lexer.Word{"case", T.Token.KCase{}}, Lexer.Word{"match", T.Token.KMatch{}}, Lexer.Word{"as", T.Token.KAs{}}, Lexer.Word{"return", T.Token.KReturn{}}, Lexer.Word{"with", T.Token.KWith{}}, Lexer.Word{"tuple", T.Token.KTuple{}}, Lexer.Word{"sum", T.Token.KSum{}}, Lexer.Word{"prod", T.Token.KProd{}}, Lexer.Word{"absurd", T.Token.KAbsurd{}}, Lexer.Word{"Prop", T.Token.KProp{}}, Lexer.Word{"Type", T.Token.KType{}}, Lexer.Word{"let", T.Token.KLet{}}, Lexer.Word{"in", T.Token.KIn{}}, Lexer.Word{"auto", T.Token.KAuto{}}, Lexer.Word{"mu", T.Token.KMu{}}, Lexer.Word{"mutual", T.Token.KMutual{}}, Lexer.Word{"end", T.Token.KEnd{}}, Lexer.Word{"nu", T.Token.KNu{}}, Lexer.Word{"and", T.Token.KAnd{}}, Lexer.Word{"rec", T.Token.KRec{}}, Lexer.Word{"natAdd", T.Token.KNatAdd{}}, Lexer.Word{"natSub", T.Token.KNatSub{}}, Lexer.Word{"natMul", T.Token.KNatMul{}}, Lexer.Word{"natEq", T.Token.KNatEq{}}, Lexer.Word{"natLt", T.Token.KNatLt{}}], s})

def Lexer.accept(+c: U32, +mode: Bool) -> Bool:
  match mode:
    case True{}: Lexer.is_digit(c)
    case False{}: Lexer.is_ident_char(c)

def Lexer.cont3(+valid: Bool, +loc: T.Token.loc, +digits: String) -> Result<&2, &2, F.Error.t, String>:
  match valid:
    case False{}: Lexer.error(String, loc, "invalid natural literal")
    case True{}: Done{digits}

# The lexer checks the digits and keeps the text.  The parser converts
# the text only where it needs the value (T.Token.nat_value).
def Lexer.nat_of_digits(+loc: T.Token.loc, +digits: String) -> Result<&2, &2, F.Error.t, String>:
  +valid : Bool = Bool.and(Bool.not(String.is_empty(digits)), F.Bignum.all_digits(digits, True{}))
  Lexer.cont3(valid, loc, digits)

def Lexer.cont20(+upper: Bool, +c: U32) -> Maybe<&2, U32>:
  match upper:
    case True{}: Some{(c - 55 : U32)}
    case False{}: None{}

def Lexer.cont10(+lower: Bool, +c: U32) -> Maybe<&2, U32>:
  match lower:
    case True{}: Some{(c - 87 : U32)}
    case False{}:
      +upper : Bool = Bool.and(U32.is_ge(c, 65), U32.is_le(c, 70))
      Lexer.cont20(upper, c)

def Lexer.cont4(+digit: Bool, +c: U32) -> Maybe<&2, U32>:
  match digit:
    case True{}: Some{(c - 48 : U32)}
    case False{}:
      +lower : Bool = Bool.and(U32.is_ge(c, 97), U32.is_le(c, 102))
      Lexer.cont10(lower, c)

def Lexer.hex_digit(+c: U32) -> Maybe<&2, U32>:
  +digit : Bool = Lexer.is_digit(c)
  Lexer.cont4(digit, c)

def Lexer.escape(+c: U32) -> Maybe<&2, U32>:
  match c:
    case 110: Some{10}
    case 114: Some{13}
    case 116: Some{9}
    case 48: Some{0}
    case 92: Some{92}
    case 34: Some{34}
    case _: None{}

def Lexer.cont7(+printable: Bool, +c: U32) -> String:
  match printable:
    case True{}: "'" ++ SCon{Chr{c}, "'"}
    case False{}:
      +digits : String = U32.show(c)
      +n : Nat = String.length(digits)
      "'" ++ "\\" ++ String.repeat("0", Nat.sub(3n, n)) ++ digits ++ "'"

def Lexer.char_text(+c: U32) -> String:
  match c:
    case 9: "'\\t'"
    case 10: "'\\n'"
    case 13: "'\\r'"
    case 8: "'\\b'"
    case 92: "'\\\\'"
    case 39: "'\\\''"
    case _:
      +printable : Bool = Bool.and(U32.is_ge(c, 32), U32.is_le(c, 126))
      Lexer.cont7(printable, c)

def Lexer.cont12(+value: Result<&2, &2, F.Error.t, String>, +loc: T.Token.loc) -> Result<&2, &2, F.Error.t, List<&2, T.Token.t>>:
  match value:
    case Fail{+error}: Fail{error}
    case Done{+n}: Done{[T.Token.Token{T.Token.Dot{}, loc}, T.Token.Token{T.Token.Nat{n}, T.Token.next_col(loc)}]}

def Lexer.cont8(+one: Bool, +two: Bool, +empty: Bool, +loc: T.Token.loc, +digits: String) -> Result<&2, &2, F.Error.t, List<&2, T.Token.t>>:
  match one two empty:
    case True{} _ _: Done{[T.Token.Token{T.Token.Dot1{}, loc}]}
    case _ True{} _: Done{[T.Token.Token{T.Token.Dot2{}, loc}]}
    case _ _ True{}: Done{[T.Token.Token{T.Token.Dot{}, loc}]}
    case _ _ _:
      +value : Result<&2, &2, F.Error.t, String> = Lexer.nat_of_digits(loc, digits)
      Lexer.cont12(value, loc)

def Lexer.dot_tokens(+loc: T.Token.loc, +digits: String) -> Result<&2, &2, F.Error.t, List<&2, T.Token.t>>:
  +one : Bool = String.eq(digits, "1")
  +two : Bool = String.eq(digits, "2")
  +empty : Bool = String.is_empty(digits)
  Lexer.cont8(one, two, empty, loc, digits)


# Spans return suffixes of cs, but the checker cannot track that relation.

# Moves the characters of cs in reverse order onto the front of acc.
def Lexer.reverse_onto(+cs: String, +acc: String) -> String:
  match cs:
    case SNil{}: acc
    case SCon{+head, +tail}: Lexer.reverse_onto(tail, SCon{head, acc})

# The span collects accepted characters in reverse order in acc.
# Every recursive call is a tail call, so a long span uses constant stack depth.
@unsafe
def Lexer.dispatch2(+job: Lexer.job2) -> Lexer.span_result:
  match job:
    case Lexer.Job2_0{+take, +mode, +loc, +head, +tail, +acc}:
      match take:
        case False{}: Lexer.Span{Lexer.reverse_onto(acc, ""), loc, SCon{head,tail}}
        case True{}:
          Lexer.dispatch2(Lexer.Job2_1{mode, tail, T.Token.next_col(loc), SCon{head, acc}})
    case Lexer.Job2_1{+mode, +cs, +loc, +acc}:
      match cs:
        case SNil{}: Lexer.Span{Lexer.reverse_onto(acc, ""), loc, ""}
        case SCon{+head, +tail}:
          +take : Bool = Lexer.accept(Char.to_u32(head), mode)
          Lexer.dispatch2(Lexer.Job2_0{take, mode, loc, head, tail, acc})


# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Lexer.dispatch3(+job: Lexer.job3) -> Result<&2, &2, F.Error.t, Lexer.bytes_result>:
  match job:
    case Lexer.Job3_0{+cs, +loc, +acc}:
      match cs:
        case SNil{}: Lexer.error(Lexer.bytes_result, loc, "unterminated byte literal")
        case SCon{+head, +tail}:
          +c : U32 = Char.to_u32(head)
          Lexer.dispatch3(Lexer.Job3_4{c, loc, acc, tail})
    case Lexer.Job3_1{+code, +loc, +acc, +escaped, +rest}:
      match code:
        case 120:
          match rest:
            case SCon{+a, +rest2}:
              match rest2:
                case SCon{+b, +rest3}:
                  +hi : Maybe<&2, U32> = Lexer.hex_digit(Char.to_u32(a))
                  +lo : Maybe<&2, U32> = Lexer.hex_digit(Char.to_u32(b))
                  Lexer.dispatch3(Lexer.Job3_2{hi, lo, loc, acc, rest3})
                case SNil{}: Lexer.error(Lexer.bytes_result, loc, "invalid byte escape \\x")
            case SNil{}: Lexer.error(Lexer.bytes_result, loc, "invalid byte escape \\x")
        case _:
          +value : Maybe<&2, U32> = Lexer.escape(code)
          Lexer.dispatch3(Lexer.Job3_3{value, loc, acc, escaped, rest})
    case Lexer.Job3_2{+hi, +lo, +loc, +acc, +rest3}:
      match hi lo:
        case Some{+h} Some{+l}: Lexer.dispatch3(Lexer.Job3_0{rest3, T.Token.advance(loc, 4n), Con{(h * 16 + l : U32),acc}})
        case _ _: Lexer.error(Lexer.bytes_result, loc, "byte escape requires two hexadecimal digits")
    case Lexer.Job3_3{+value, +loc, +acc, +escaped, +rest}:
      match value:
        case None{}: Lexer.error(Lexer.bytes_result, loc, "invalid byte escape \\" ++ SCon{escaped, ""})
        case Some{+byte}: Lexer.dispatch3(Lexer.Job3_0{rest, T.Token.advance(loc, 2n), Con{byte,acc}})
    case Lexer.Job3_4{+c, +loc, +acc, +tail}:
      match c:
        case 34: Done{Lexer.BytesResult{List.reverse(&2, U32, acc), T.Token.next_col(loc),tail}}
        case 10: Lexer.error(Lexer.bytes_result, loc, "unescaped newline in byte literal")
        case 13: Lexer.error(Lexer.bytes_result, loc, "unescaped newline in byte literal")
        case 92:
          match tail:
            case SNil{}: Lexer.error(Lexer.bytes_result, loc, "unterminated byte escape")
            case SCon{+escaped, +rest}:
              +code : U32 = Char.to_u32(escaped)
              Lexer.dispatch3(Lexer.Job3_1{code, loc, acc, escaped, rest})
        case _: Lexer.dispatch3(Lexer.Job3_0{tail, T.Token.next_col(loc), Con{c,acc}})


# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Lexer.dispatch4(+job: Lexer.job4) -> Lexer.span_result:
  match job:
    case Lexer.Job4_0{+cs, +loc}:
      match cs:
        case SNil{}: Lexer.Span{"",loc, ""}
        case SCon{+head, +tail}:
          +newline : Bool = Char.is_eq(head, '\n')
          Lexer.dispatch4(Lexer.Job4_1{newline, loc, tail})
    case Lexer.Job4_1{+newline, +loc, +tail}:
      match newline:
        case True{}: Lexer.Span{"", T.Token.next_line(loc),tail}
        case False{}: Lexer.dispatch4(Lexer.Job4_0{tail, T.Token.next_col(loc)})


# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Lexer.dispatch5(+job: Lexer.job5) -> Result<&2, &2, F.Error.t, List<&2, T.Token.t>>:
  match job:
    case Lexer.Job5_0{+quote, +loc, +acc, +head, +tail}:
      match quote:
        case True{}:
          +bytes : Result<&2, &2, F.Error.t, Lexer.bytes_result> = Lexer.dispatch3(Lexer.Job3_0{String.drop(tail, 1n), T.Token.advance(loc, 2n), Nil{}})
          Lexer.dispatch5(Lexer.Job5_7{bytes, loc, acc})
        case False{}:
          Lexer.dispatch5(Lexer.Job5_10{Lexer.dispatch2(Lexer.Job2_1{False{}, tail, T.Token.next_col(loc), ""}), loc, acc, head})
    case Lexer.Job5_1{+comment, +arrow, +loc, +acc, +tail}:
      match comment arrow:
        case True{} _:
          Lexer.dispatch5(Lexer.Job5_11{Lexer.dispatch4(Lexer.Job4_0{String.drop(tail, 1n), T.Token.advance(loc, 2n)}), acc})
        case _ True{}: Lexer.dispatch5(Lexer.Job5_15{String.drop(tail, 1n), T.Token.advance(loc, 2n), Con{T.Token.Token{T.Token.Arrow{}, loc}, acc}})
        case _ _: Lexer.error(List<&2, T.Token.t>, loc, "unexpected character '-'")
    case Lexer.Job5_2{+arrow, +loc, +acc, +tail}:
      match arrow:
        case True{}: Lexer.dispatch5(Lexer.Job5_15{String.drop(tail, 1n), T.Token.advance(loc, 2n), Con{T.Token.Token{T.Token.DArrow{}, loc}, acc}})
        case False{}: Lexer.error(List<&2, T.Token.t>, loc, "unexpected character '='")
    case Lexer.Job5_3{+assign, +loc, +acc, +tail}:
      match assign:
        case True{}: Lexer.dispatch5(Lexer.Job5_15{String.drop(tail, 1n), T.Token.advance(loc, 2n), Con{T.Token.Token{T.Token.ColonEq{}, loc}, acc}})
        case False{}: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.Colon{}, loc}, acc}})
    case Lexer.Job5_4{+unit, +loc, +acc, +tail}:
      match unit:
        case True{}: Lexer.dispatch5(Lexer.Job5_15{String.drop(tail, 1n), T.Token.advance(loc, 2n), Con{T.Token.Token{T.Token.Unit{}, loc}, acc}})
        case False{}: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.LParen{}, loc}, acc}})
    case Lexer.Job5_5{+tokens, +acc, +after, +rest}:
      match tokens:
        case Fail{+error}: Fail{error}
        case Done{+tokens}: Lexer.dispatch5(Lexer.Job5_15{rest, after, List.append(&2, T.Token.t, List.reverse(&2, T.Token.t, tokens), acc)})
    case Lexer.Job5_6{+digit, +ident, +c, +loc, +acc, +head, +tail}:
      match digit ident:
        case True{} _:
          Lexer.dispatch5(Lexer.Job5_12{Lexer.dispatch2(Lexer.Job2_1{True{}, tail, T.Token.next_col(loc), ""}), loc, acc, head})
        case _ True{}:
          Lexer.dispatch5(Lexer.Job5_13{Lexer.dispatch2(Lexer.Job2_1{False{}, tail, T.Token.next_col(loc), ""}), loc, acc, head})
        case _ _: Lexer.error(List<&2, T.Token.t>, loc, "unexpected character " ++ Lexer.char_text(c))
    case Lexer.Job5_7{+bytes, +loc, +acc}:
      match bytes:
        case Fail{+error}: Fail{error}
        case Done{+value}:
          Lexer.BytesResult{+bs, +after, +rest} = value
          Lexer.dispatch5(Lexer.Job5_15{rest, after, Con{T.Token.Token{T.Token.Bytes{bs}, loc}, acc}})
    case Lexer.Job5_8{+n, +loc, +acc, +after, +rest}:
      match n:
        case Fail{+error}: Fail{error}
        case Done{+value}: Lexer.dispatch5(Lexer.Job5_15{rest, after, Con{T.Token.Token{T.Token.Nat{value}, loc}, acc}})
    case Lexer.Job5_9{+lifted, +loc, +acc}:
      Lexer.Span{+digits, +after, +rest} = lifted
      +tokens : Result<&2, &2, F.Error.t, List<&2, T.Token.t>> = Lexer.dot_tokens(loc, digits)
      Lexer.dispatch5(Lexer.Job5_5{tokens, acc, after, rest})
    case Lexer.Job5_10{+lifted, +loc, +acc, +head}:
      Lexer.Span{+text, +after, +rest} = lifted
      Lexer.dispatch5(Lexer.Job5_15{rest, after, Con{T.Token.Token{Lexer.ident_kind(SCon{head, text}), loc}, acc}})
    case Lexer.Job5_11{+lifted, +acc}:
      Lexer.Span{+text, +after, +rest} = lifted
      Lexer.dispatch5(Lexer.Job5_15{rest, after, acc})
    case Lexer.Job5_12{+lifted, +loc, +acc, +head}:
      Lexer.Span{+text, +after, +rest} = lifted
      +n : Result<&2, &2, F.Error.t, String> = Lexer.nat_of_digits(loc, SCon{head, text})
      Lexer.dispatch5(Lexer.Job5_8{n, loc, acc, after, rest})
    case Lexer.Job5_13{+lifted, +loc, +acc, +head}:
      Lexer.Span{+text, +after, +rest} = lifted
      Lexer.dispatch5(Lexer.Job5_15{rest, after, Con{T.Token.Token{Lexer.ident_kind(SCon{head, text}), loc}, acc}})
    case Lexer.Job5_14{+c, +loc, +acc, +head, +tail}:
      match c:
        case 32: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), acc})
        case 9: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), acc})
        case 13: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), acc})
        case 10: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_line(loc), acc})
        case 98:
          +quote : Bool = String.starts_with(tail, "\"")
          Lexer.dispatch5(Lexer.Job5_0{quote, loc, acc, head, tail})
        case 45:
          +comment : Bool = String.starts_with(tail, "-")
          +arrow : Bool = String.starts_with(tail, ">")
          Lexer.dispatch5(Lexer.Job5_1{comment, arrow, loc, acc, tail})
        case 61:
          +arrow : Bool = String.starts_with(tail, ">")
          Lexer.dispatch5(Lexer.Job5_2{arrow, loc, acc, tail})
        case 58:
          +assign : Bool = String.starts_with(tail, "=")
          Lexer.dispatch5(Lexer.Job5_3{assign, loc, acc, tail})
        case 40:
          +unit : Bool = String.starts_with(tail, ")")
          Lexer.dispatch5(Lexer.Job5_4{unit, loc, acc, tail})
        case 41: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.RParen{}, loc}, acc}})
        case 42: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.Star{}, loc}, acc}})
        case 44: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.Comma{}, loc}, acc}})
        case 124: Lexer.dispatch5(Lexer.Job5_15{tail, T.Token.next_col(loc), Con{T.Token.Token{T.Token.Pipe{}, loc}, acc}})
        case 46:
          Lexer.dispatch5(Lexer.Job5_9{Lexer.dispatch2(Lexer.Job2_1{True{}, tail, T.Token.next_col(loc), ""}), loc, acc})
        case _:
          +digit : Bool = Lexer.is_digit(c)
          +ident : Bool = Lexer.is_ident_start(c)
          Lexer.dispatch5(Lexer.Job5_6{digit, ident, c, loc, acc, head, tail})
    case Lexer.Job5_15{+cs, +loc, +acc}:
      match cs:
        case SNil{}: Done{List.reverse(&2, T.Token.t, Con{T.Token.Token{T.Token.Eof{}, loc}, acc})}
        case SCon{+head, +tail}:
          +c : U32 = Char.to_u32(head)
          Lexer.dispatch5(Lexer.Job5_14{c, loc, acc, head, tail})


def Lexer.lex(+src: String) -> Result<&2, &2, F.Error.t, List<&2, T.Token.t>>:
  Lexer.dispatch5(Lexer.Job5_15{src, T.Token.start, Nil{}})
