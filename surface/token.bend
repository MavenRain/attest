import Base
import ../lib/foundation.bend as F

type Token.loc is Data:
  Token.Loc{line: Nat, col: Nat}

def Token.start() -> Token.loc:
  Token.Loc{1n, 1n}

def Token.advance(loc: Token.loc, n: Nat) -> Token.loc:
  Token.Loc{line, col} = loc
  Token.Loc{line, (col + n : Nat)}

def Token.next_col(loc: Token.loc) -> Token.loc:
  Token.advance(loc, 1n)

def Token.next_line(loc: Token.loc) -> Token.loc:
  Token.Loc{line, col} = loc
  Token.Loc{(line + 1n : Nat), 1n}

type Token.kind is Data:
  Token.LParen{}
  Token.RParen{}
  Token.Colon{}
  Token.ColonEq{}
  Token.Arrow{}
  Token.DArrow{}
  Token.Star{}
  Token.Comma{}
  Token.Dot{}
  Token.Dot1{}
  Token.Dot2{}
  Token.Pipe{}
  Token.Unit{}
  Token.KDef{}
  Token.KAxiom{}
  Token.KFun{}
  Token.KInj{}
  Token.KOf{}
  Token.KCase{}
  Token.KMatch{}
  Token.KAs{}
  Token.KReturn{}
  Token.KWith{}
  Token.KTuple{}
  Token.KSum{}
  Token.KProd{}
  Token.KAbsurd{}
  Token.KProp{}
  Token.KType{}
  Token.KLet{}
  Token.KIn{}
  Token.KAuto{}
  Token.KMu{}
  Token.KMutual{}
  Token.KEnd{}
  Token.KNu{}
  Token.KAnd{}
  Token.KRec{}
  Token.KNatAdd{}
  Token.KNatSub{}
  Token.KNatMul{}
  Token.KNatEq{}
  Token.KNatLt{}
  Token.Ident{value: String}
  Token.Nat{value: String}
  Token.Bytes{value: List<&2, U32>}
  Token.Eof{}

type Token.t is Data:
  Token.Token{kind: Token.kind, loc: Token.loc}

def Token.nat_value_of(+value: Maybe<&2, F.Bignum.t>) -> F.Bignum.t:
  match value:
    case None{}:
      F.Bignum.zero
    case Some{+value}:
      value

# A Nat token carries its checked decimal text.  The parser converts it
# only where it needs the value, so a bounded position rejects a long
# literal before the quadratic conversion runs.
def Token.nat_value(+digits: String) -> F.Bignum.t:
  Token.nat_value_of(F.Bignum.of_decimal(digits))

def Token.describe(k: Token.kind) -> String:
  match k:
    case Token.LParen{}: "'('"
    case Token.RParen{}: "')'"
    case Token.Colon{}: "':'"
    case Token.ColonEq{}: "':='"
    case Token.Arrow{}: "'->'"
    case Token.DArrow{}: "'=>'"
    case Token.Star{}: "'*'"
    case Token.Comma{}: "','"
    case Token.Dot{}: "'.'"
    case Token.Dot1{}: "'.1'"
    case Token.Dot2{}: "'.2'"
    case Token.Pipe{}: "'|'"
    case Token.Unit{}: "'()'"
    case Token.KDef{}: "'def'"
    case Token.KAxiom{}: "'axiom'"
    case Token.KFun{}: "'fun'"
    case Token.KInj{}: "'inj'"
    case Token.KOf{}: "'of'"
    case Token.KCase{}: "'case'"
    case Token.KMatch{}: "'match'"
    case Token.KAs{}: "'as'"
    case Token.KReturn{}: "'return'"
    case Token.KWith{}: "'with'"
    case Token.KTuple{}: "'tuple'"
    case Token.KSum{}: "'sum'"
    case Token.KProd{}: "'prod'"
    case Token.KAbsurd{}: "'absurd'"
    case Token.KProp{}: "'Prop'"
    case Token.KType{}: "'Type'"
    case Token.KLet{}: "'let'"
    case Token.KIn{}: "'in'"
    case Token.KAuto{}: "'auto'"
    case Token.KMu{}: "'mu'"
    case Token.KMutual{}: "'mutual'"
    case Token.KEnd{}: "'end'"
    case Token.KNu{}: "'nu'"
    case Token.KAnd{}: "'and'"
    case Token.KRec{}: "'rec'"
    case Token.KNatAdd{}: "'natAdd'"
    case Token.KNatSub{}: "'natSub'"
    case Token.KNatMul{}: "'natMul'"
    case Token.KNatEq{}: "'natEq'"
    case Token.KNatLt{}: "'natLt'"
    case Token.Ident{value}: "identifier " ++ value
    case Token.Nat{value}: "number " ++ F.Bignum.to_string(Token.nat_value(value))
    case Token.Bytes{value}: "byte literal"
    case Token.Eof{}: "end of input"
