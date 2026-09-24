import Base

import ../lib/foundation.bend as F

import token.bend as T

import syntax.bend as S

import lexer.bend as L

type Parser.output is Data:
  Parser.Term{term: S.Syntax.t, rest: List<&2, T.Token.t>}
  Parser.Binder{binder: S.Syntax.binder, rest: List<&2, T.Token.t>}
  Parser.Binders{binders: List<&2, S.Syntax.binder>, rest: List<&2, T.Token.t>}
  Parser.Fields{fields: List<&2, S.Syntax.field>, rest: List<&2, T.Token.t>}
  Parser.Branches{branches: List<&2, S.Syntax.branch>, rest: List<&2, T.Token.t>}
  Parser.Names{names: List<&2, String>, rest: List<&2, T.Token.t>}
  Parser.Index{ind: Maybe<&2, String>, names: List<&2, String>, rest: List<&2, T.Token.t>}
  Parser.Ctors{ctors: List<&2, S.Syntax.fam_ctor>, rest: List<&2, T.Token.t>}
  Parser.Fam{family: S.Syntax.fam, rest: List<&2, T.Token.t>}
  Parser.Fams{families: List<&2, S.Syntax.fam>, rest: List<&2, T.Token.t>}
  Parser.Rec{member: S.Syntax.rec_def, rest: List<&2, T.Token.t>}
  Parser.Recs{members: List<&2, S.Syntax.rec_def>, rest: List<&2, T.Token.t>}
  Parser.Decl{decl: S.Syntax.decl, rest: List<&2, T.Token.t>}
  Parser.Decls{decls: List<&2, S.Syntax.decl>}
  Parser.Marked{quantity: F.Quantity.t, rest: List<&2, T.Token.t>}
  Parser.Key{key: F.Bignum.t}

def Parser.result() -> Data:
  Result<&2, &2, F.Error.t, Parser.output>

type Parser.job1 is Data:
  Parser.Job1_0{r35: Parser.result, term: S.Syntax.t, rest: List<&2, T.Token.t>}
  Parser.Job1_1{ts: List<&2, T.Token.t>, term: S.Syntax.t}


type Parser.job2 is Data:
  Parser.Job2_0{ts: List<&2, T.Token.t>}
  Parser.Job2_1{head: S.Syntax.t, ts: List<&2, T.Token.t>}
  Parser.Job2_2{ts: List<&2, T.Token.t>}
  Parser.Job2_3{ts: List<&2, T.Token.t>}
  Parser.Job2_4{ts: List<&2, T.Token.t>}
  Parser.Job2_5{ts: List<&2, T.Token.t>}
  Parser.Job2_6{ts: List<&2, T.Token.t>}
  Parser.Job2_7{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.binder>}
  Parser.Job2_8{ts: List<&2, T.Token.t>, fibered: Bool, acc: List<&2, S.Syntax.branch>}
  Parser.Job2_9{fibered: Bool, ts: List<&2, T.Token.t>}
  Parser.Job2_10{r2: Parser.result, loc: T.Token.loc}
  Parser.Job2_11{r22: Parser.result, fibered: Bool, acc: List<&2, S.Syntax.branch>, name: String}
  Parser.Job2_12{attempt: Parser.result, ts: List<&2, T.Token.t>, loc: T.Token.loc, rest: List<&2, T.Token.t>}
  Parser.Job2_13{r27: Parser.result}
  Parser.Job2_14{r29: Parser.result}
  Parser.Job2_15{r32: Parser.result, n: String, nloc: T.Token.loc, rest: List<&2, T.Token.t>}
  Parser.Job2_16{starts: Bool, head: S.Syntax.t, ts: List<&2, T.Token.t>}
  Parser.Job2_17{r3: Parser.result, acc: List<&2, S.Syntax.binder>, rest: List<&2, T.Token.t>}
  Parser.Job2_18{r39: Parser.result}
  Parser.Job2_19{r40: Parser.result, word: String, acc: List<&2, S.Syntax.t>}
  Parser.Job2_20{r6: Parser.result}
  Parser.Job2_21{r5: Parser.result}
  Parser.Job2_22{r8: Parser.result, x: String, ty: S.Syntax.t, loc: T.Token.loc}
  Parser.Job2_23{r13: Parser.result, fibered: Bool, scrut: S.Syntax.t, x: String}
  Parser.Job2_24{r19: Parser.result, fibered: Bool, acc: List<&2, S.Syntax.branch>, loc: T.Token.loc, key: F.Bignum.t}
  Parser.Job2_25{r9: Parser.result, x: String}
  Parser.Job2_26{r21: Parser.result, fibered: Bool, acc: List<&2, S.Syntax.branch>, name: String, fs: List<&2, S.Syntax.field>}
  Parser.Job2_27{r31: Parser.result, rest: List<&2, T.Token.t>, key: F.Bignum.t}
  Parser.Job2_28{r33: Parser.result, head: S.Syntax.t}
  Parser.Job2_29{r12: Parser.result, fibered: Bool, scrut: S.Syntax.t, x: String, ind: Maybe<&2, String>, idx: List<&2, String>, loc: T.Token.loc}
  Parser.Job2_30{r18: Parser.result, fibered: Bool, acc: List<&2, S.Syntax.branch>, key: F.Bignum.t, bs: List<&2, S.Syntax.binder>}
  Parser.Job2_31{r15: Parser.result, fibered: Bool}
  Parser.Job2_32{r16: Parser.result, acc: List<&2, S.Syntax.field>, rest: List<&2, T.Token.t>}
  Parser.Job2_33{r17: Parser.result, ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.field>}
  Parser.Job2_34{r20: Parser.result, fibered: Bool, acc: List<&2, S.Syntax.branch>, loc: T.Token.loc, rest: List<&2, T.Token.t>}
  Parser.Job2_35{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.field>}
  Parser.Job2_36{ts: List<&2, T.Token.t>}
  Parser.Job2_37{ts: List<&2, T.Token.t>}
  Parser.Job2_38{ts: List<&2, T.Token.t>, word: String}
  Parser.Job2_39{ts: List<&2, T.Token.t>, word: String}
  Parser.Job2_40{word: String, ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.t>}
  Parser.Job2_41{ts: List<&2, T.Token.t>}
  Parser.Job2_42{ts: List<&2, T.Token.t>}
  Parser.Job2_43{ts: List<&2, T.Token.t>}
  Parser.Job2_44{result: Parser.result}


type Parser.frame2 is Data:
  Parser.Frame2_c13{}
  Parser.Frame2_14{}
  Parser.Frame2_12{ts: List<&2, T.Token.t>, loc: T.Token.loc, rest: List<&2, T.Token.t>}
  Parser.Frame2_13{}
  Parser.Frame2_c17{}
  Parser.Frame2_17{acc: List<&2, S.Syntax.binder>, rest: List<&2, T.Token.t>}
  Parser.Frame2_11{fibered: Bool, acc: List<&2, S.Syntax.branch>, name: String}
  Parser.Frame2_31{fibered: Bool}
  Parser.Frame2_c34{loc: T.Token.loc, q: F.Quantity.t, x: String}
  Parser.Frame2_26{fibered: Bool, acc: List<&2, S.Syntax.branch>, name: String, fs: List<&2, S.Syntax.field>}
  Parser.Frame2_c41{b: S.Syntax.binder}
  Parser.Frame2_c42{b: S.Syntax.binder}
  Parser.Frame2_c43{lhs: S.Syntax.t}
  Parser.Frame2_c44{lhs: S.Syntax.t}
  Parser.Frame2_28{head: S.Syntax.t}
  Parser.Frame2_c47{inner: S.Syntax.t, loc: T.Token.loc}
  Parser.Frame2_c48{inner: S.Syntax.t, loc: T.Token.loc}
  Parser.Frame2_21{}
  Parser.Frame2_c53{bs: List<&2, S.Syntax.binder>}
  Parser.Frame2_c54{x: String, ty: S.Syntax.t, val: S.Syntax.t}
  Parser.Frame2_29{fibered: Bool, scrut: S.Syntax.t, x: String, ind: Maybe<&2, String>, idx: List<&2, String>, loc: T.Token.loc}
  Parser.Frame2_30{fibered: Bool, acc: List<&2, S.Syntax.branch>, key: F.Bignum.t, bs: List<&2, S.Syntax.binder>}
  Parser.Frame2_22{x: String, ty: S.Syntax.t, loc: T.Token.loc}
  Parser.Frame2_c57{key: F.Bignum.t, arity: F.Bignum.t}
  Parser.Frame2_c60{fibered: Bool, scrut: S.Syntax.t, x: String, ind: Maybe<&2, String>, idx: List<&2, String>, body: S.Syntax.t}
  Parser.Frame2_c38{fibered: Bool, scrut: S.Syntax.t}
  Parser.Frame2_24{fibered: Bool, acc: List<&2, S.Syntax.branch>, loc: T.Token.loc, key: F.Bignum.t}
  Parser.Frame2_32{acc: List<&2, S.Syntax.field>, rest: List<&2, T.Token.t>}
  Parser.Frame2_20{}
  Parser.Frame2_19{word: String, acc: List<&2, S.Syntax.t>}
  Parser.Frame2_25{x: String}
  Parser.Frame2_18{}


type Parser.job3 is Data:
  Parser.Job3_0{r57: Parser.result, acc: List<&2, S.Syntax.fam_ctor>, name: String}
  Parser.Job3_1{r56: Parser.result, acc: List<&2, S.Syntax.fam_ctor>, name: String, bs: List<&2, S.Syntax.binder>}
  Parser.Job3_2{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.fam_ctor>}


type Parser.job4 is Data:
  Parser.Job4_0{r52: Parser.result, acc: List<&2, S.Syntax.fam>}
  Parser.Job4_1{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.fam>}


type Parser.job5 is Data:
  Parser.Job5_0{r50: Parser.result, acc: List<&2, S.Syntax.rec_def>}
  Parser.Job5_1{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.rec_def>}


type Parser.job6 is Data:
  Parser.Job6_0{r51: Parser.result, acc: List<&2, S.Syntax.fam>}
  Parser.Job6_1{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.fam>}


type Parser.job7 is Data:
  Parser.Job7_0{r41: Parser.result, acc: List<&2, S.Syntax.decl>}
  Parser.Job7_1{ts: List<&2, T.Token.t>, acc: List<&2, S.Syntax.decl>}



def Parser.internal() -> Parser.result:
  Fail{F.Error.Cannot_infer{"parser continuation result mismatch"}}

def Parser.error(+loc: T.Token.loc, +message: String) -> Parser.result:
  T.Token.Loc{+line,+col} = loc
  Fail{F.Error.Parse{message, line, col}}

def Parser.expected(+what: String, +ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{+kind,+loc},+rest}:
      Parser.error(loc, "expected " ++ what ++ ", found " ++ T.Token.describe(kind))
    case _:
      Parser.error(T.Token.start, "unexpected end of input")

def Parser.starts_atom(+ts: List<&2, T.Token.t>) -> Bool:
  match ts:
    case Con{T.Token.Token{T.Token.Ident{+name},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.Nat{+n},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.Bytes{+bytes},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.Unit{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KProp{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KType{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KAuto{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KTuple{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KSum{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KProd{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNatAdd{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNatSub{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNatMul{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNatEq{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNatLt{},+loc},+rest}:
      True{}
    case Con{T.Token.Token{T.Token.KNu{},+loc},+rest}:
      True{}
    case _:
      False{}

def Parser.bounded_check(+ok: Bool, +loc: T.Token.loc, +digits: String) -> Parser.result:
  match ok:
    case True{}:
      Done{Parser.Key{T.Token.nat_value(digits)}}
    case False{}:
      Parser.error(loc, "numeric literal too long")

def Parser.digit_weight(+zero: Bool) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      1n

# Counts the digits after the leading zeros.  The token text holds only
# digits, so a code point of at most 48 is a zero.
def Parser.significant(xs: String, +lead: Bool, +count: Nat) -> Nat:
  match xs:
    case SNil{}:
      count
    case SCon{Chr{+c}, tail}:
      Parser.significant(tail, Bool.and(lead, (c <= 48 : U32)), (count + Parser.digit_weight(Bool.and(lead, (c <= 48 : U32))) : Nat))

# HEAD bounds the decimal text at eighteen digits.  A literal is below
# 10^18 exactly when its text has at most eighteen digits after the
# leading zeros, so one linear count over the token text decides the
# bound, and a long literal is rejected before any conversion runs.
def Parser.bounded_nat(+loc: T.Token.loc, +digits: String) -> Parser.result:
  Parser.bounded_check(Nat.is_le(Parser.significant(digits, True{}, 0n), 18n), loc, digits)

def Parser.mark_compare(+zero: Bool, +one: Bool, +ts: List<&2, T.Token.t>, +rest: List<&2, T.Token.t>) -> Parser.result:
  match zero one:
    case True{} _:
      Done{Parser.Marked{F.Quantity.Zero{}, rest}}
    case _ True{}:
      Done{Parser.Marked{F.Quantity.One{}, rest}}
    case _ _:
      Done{Parser.Marked{F.Quantity.Many{}, ts}}

def Parser.mark(+ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.Nat{+n},+loc},+rest}:
      Parser.mark_compare(F.Bignum.equal(T.Token.nat_value(n), F.Bignum.zero), F.Bignum.equal(T.Token.nat_value(n), F.Bignum.one), ts, rest)
    case _:
      Done{Parser.Marked{F.Quantity.Many{}, ts}}

def Parser.bytes(+bytes: List<&2, U32>) -> S.Syntax.t:
  match bytes:
    case Nil{}:
      S.Syntax.SVar{"bytesNil"}
    case Con{+head,+tail}:
      S.Syntax.SApp{S.Syntax.SApp{S.Syntax.SVar{"bytesCons"}, S.Syntax.SNat{F.Bignum.from_u32(head)}}, Parser.bytes(tail)}

def Parser.fold_arrows(+bs: List<&2, S.Syntax.binder>, +body: S.Syntax.t) -> S.Syntax.t:
  match bs:
    case Nil{}:
      body
    case Con{+head,+tail}:
      S.Syntax.SArrow{head, Parser.fold_arrows(tail, body)}

def Parser.build_items_kind(+tuple: Bool, +sum: Bool, +xs: List<&2, S.Syntax.t>) -> S.Syntax.t:
  match tuple sum:
    case True{} _:
      S.Syntax.STuple{xs}
    case _ True{}:
      S.Syntax.SSum{xs}
    case _ _:
      S.Syntax.SProd{xs}

def Parser.build_items(+word: String, +xs: List<&2, S.Syntax.t>) -> S.Syntax.t:
  Parser.build_items_kind(String.eq(word, "tuple"), String.eq(word, "sum"), xs)

def Parser.elimination(+fibered: Bool, +scrut: S.Syntax.t, +motive: Maybe<&2, S.Syntax.motive>, +branches: List<&2, S.Syntax.branch>) -> S.Syntax.t:
  match fibered:
    case True{}:
      S.Syntax.SMatch{scrut, motive, branches}
    case False{}:
      S.Syntax.SCase{scrut, motive, branches}

def Parser.names(+ts: List<&2, T.Token.t>, +acc: List<&2, String>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.Ident{+x},+loc},+rest}:
      Parser.names(rest, Con{x, acc})
    case _:
      Done{Parser.Names{List.reverse(&2, String, acc), ts}}

def Parser.cont5(+r10: Parser.result, +name: String) -> Parser.result:
  match r10:
    case Fail{+error}: Fail{error}
    case Done{+v10}:
      match v10:
        case Parser.Names{+names,+r2}:
          Done{Parser.Index{Some{name}, names, r2}}
        case _: Parser.internal()

def Parser.index_clause(+ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.KIn{}, _}, Con{T.Token.Token{T.Token.Ident{+name}, _},+rest}}:
      +r10 : Parser.result = Parser.names(rest, Nil{})
      Parser.cont5(r10, name)
    case _:
      Done{Parser.Index{None{}, Nil{}, ts}}

def Parser.cont23(+r42: Parser.result) -> Parser.result:
  match r42:
    case Fail{+error}: Fail{error}
    case Done{+v42}:
      match v42:
        case Parser.Recs{+ms,+r2}:
          Done{Parser.Decl{S.Syntax.DRec{ms}, r2}}
        case _: Parser.internal()

def Parser.cont49(+r43: Parser.result, +name: String, +ty: S.Syntax.t) -> Parser.result:
  match r43:
    case Fail{+error}: Fail{error}
    case Done{+v43}:
      match v43:
        case Parser.Term{+body,+r4}:
          Done{Parser.Decl{S.Syntax.DDef{name, ty, body}, r4}}
        case _: Parser.internal()

def Parser.cont13(+r28: Parser.result) -> Parser.result:
  match r28:
    case Fail{+error}: Fail{error}
    case Done{+v28}:
      match v28:
        case Parser.Term{+term,+r2}:
          Done{Parser.Term{S.Syntax.SAbsurd{term}, r2}}
        case _: Parser.internal()

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch1(+job: Parser.job1) -> Parser.result:
  match job:
    case Parser.Job1_0{+r35, +term, +rest}:
      match r35:
        case Fail{+error}: Fail{error}
        case Done{+v35}:
          match v35:
            case Parser.Key{+key}:
              Parser.dispatch1(Parser.Job1_1{rest, S.Syntax.SProj{term, key}})
            case _: Parser.internal()
    case Parser.Job1_1{+ts, +term}:
      match ts:
        case Con{T.Token.Token{T.Token.Dot1{},+loc},+rest}:
          Parser.dispatch1(Parser.Job1_1{rest, S.Syntax.SProj{term, F.Bignum.one}})
        case Con{T.Token.Token{T.Token.Dot2{},+loc},+rest}:
          Parser.dispatch1(Parser.Job1_1{rest, S.Syntax.SProj{term, F.Bignum.from_nat(2n)}})
        case Con{T.Token.Token{T.Token.Dot{}, _}, Con{T.Token.Token{T.Token.Nat{+k},+loc},+rest}}:
          +r35 : Parser.result = Parser.bounded_nat(loc, k)
          Parser.dispatch1(Parser.Job1_0{r35, term, rest})
        case Con{T.Token.Token{T.Token.Dot{},+loc},+rest}:
          Parser.error(loc, "expected a leg number after '.'")
        case _:
          Done{Parser.Term{term, ts}}


def Parser.cont17(+r34: Parser.result) -> Parser.result:
  match r34:
    case Fail{+error}: Fail{error}
    case Done{+v34}:
      match v34:
        case Parser.Term{+term,+rest}:
          Parser.dispatch1(Parser.Job1_1{rest, term})
        case _: Parser.internal()

def Parser.cont19(+r36: Parser.result, +rest: List<&2, T.Token.t>) -> Parser.result:
  match r36:
    case Fail{+error}: Fail{error}
    case Done{+v36}:
      match v36:
        case Parser.Key{+level}:
          Done{Parser.Term{S.Syntax.SType{level}, rest}}
        case _: Parser.internal()

def Parser.cont34(+r1: Parser.result, +loc: T.Token.loc, +q: F.Quantity.t, +x: String) -> Parser.result:
  match r1:
    case Fail{+error}: Fail{error}
    case Done{+v1}:
      match v1:
        case Parser.Term{+ty,+r3}:
          match r3:
            case Con{T.Token.Token{T.Token.RParen{},+loc},+r4}:
              Done{Parser.Binder{S.Syntax.Binder{q, x, ty}, r4}}
            case _:
              Parser.expected("')'", r3)
        case _: Parser.internal()

def Parser.cont38(+r14: Parser.result, +fibered: Bool, +scrut: S.Syntax.t) -> Parser.result:
  match r14:
    case Fail{+error}: Fail{error}
    case Done{+v14}:
      match v14:
        case Parser.Branches{+brs,+r3}:
          Done{Parser.Term{Parser.elimination(fibered, scrut, None{}, brs), r3}}
        case _: Parser.internal()

def Parser.cont41(+r23: Parser.result, +b: S.Syntax.binder) -> Parser.result:
  match r23:
    case Fail{+error}: Fail{error}
    case Done{+v23}:
      match v23:
        case Parser.Term{+cod,+r2}:
          Done{Parser.Term{S.Syntax.SArrow{b, cod}, r2}}
        case _: Parser.internal()

def Parser.cont42(+r24: Parser.result, +b: S.Syntax.binder) -> Parser.result:
  match r24:
    case Fail{+error}: Fail{error}
    case Done{+v24}:
      match v24:
        case Parser.Term{+cod,+r2}:
          Done{Parser.Term{S.Syntax.SStar{b, cod}, r2}}
        case _: Parser.internal()

def Parser.cont43(+r25: Parser.result, +lhs: S.Syntax.t) -> Parser.result:
  match r25:
    case Fail{+error}: Fail{error}
    case Done{+v25}:
      match v25:
        case Parser.Term{+rhs,+r3}:
          Done{Parser.Term{S.Syntax.SArrow{S.Syntax.Binder{F.Quantity.Many{}, "_", lhs}, rhs}, r3}}
        case _: Parser.internal()

def Parser.cont44(+r26: Parser.result, +lhs: S.Syntax.t) -> Parser.result:
  match r26:
    case Fail{+error}: Fail{error}
    case Done{+v26}:
      match v26:
        case Parser.Term{+rhs,+r3}:
          Done{Parser.Term{S.Syntax.SStar{S.Syntax.Binder{F.Quantity.Many{}, "_", lhs}, rhs}, r3}}
        case _: Parser.internal()

def Parser.cont47(+r37: Parser.result, +inner: S.Syntax.t, +loc: T.Token.loc) -> Parser.result:
  match r37:
    case Fail{+error}: Fail{error}
    case Done{+v37}:
      match v37:
        case Parser.Term{+second,+r3}:
          match r3:
            case Con{T.Token.Token{T.Token.RParen{},+loc},+r4}:
              Done{Parser.Term{S.Syntax.SPair{inner, second}, r4}}
            case _:
              Parser.expected("')'", r3)
        case _: Parser.internal()

def Parser.cont48(+r38: Parser.result, +inner: S.Syntax.t, +loc: T.Token.loc) -> Parser.result:
  match r38:
    case Fail{+error}: Fail{error}
    case Done{+v38}:
      match v38:
        case Parser.Term{+second,+r3}:
          match r3:
            case Con{T.Token.Token{T.Token.RParen{},+loc},+r4}:
              Done{Parser.Term{S.Syntax.SAnn{inner, second}, r4}}
            case _:
              Parser.expected("')'", r3)
        case _: Parser.internal()

def Parser.cont53(+r4: Parser.result, +bs: List<&2, S.Syntax.binder>) -> Parser.result:
  match r4:
    case Fail{+error}: Fail{error}
    case Done{+v4}:
      match v4:
        case Parser.Term{+body,+r4}:
          Done{Parser.Term{S.Syntax.SFun{bs, body}, r4}}
        case _: Parser.internal()

def Parser.cont54(+r7: Parser.result, +x: String, +ty: S.Syntax.t, +val: S.Syntax.t) -> Parser.result:
  match r7:
    case Fail{+error}: Fail{error}
    case Done{+v7}:
      match v7:
        case Parser.Term{+body,+r6}:
          Done{Parser.Term{S.Syntax.SLet{x, ty, val, body}, r6}}
        case _: Parser.internal()

def Parser.cont57(+r30: Parser.result, +key: F.Bignum.t, +arity: F.Bignum.t) -> Parser.result:
  match r30:
    case Fail{+error}: Fail{error}
    case Done{+v30}:
      match v30:
        case Parser.Term{+term,+r2}:
          Done{Parser.Term{S.Syntax.SInj{key, arity, term}, r2}}
        case _: Parser.internal()

def Parser.cont60(+r11: Parser.result, +fibered: Bool, +scrut: S.Syntax.t, +x: String, +ind: Maybe<&2, String>, +idx: List<&2, String>, +body: S.Syntax.t) -> Parser.result:
  match r11:
    case Fail{+error}: Fail{error}
    case Done{+v11}:
      match v11:
        case Parser.Branches{+brs,+r7}:
          Done{Parser.Term{Parser.elimination(fibered, scrut, Some{S.Syntax.Motive{x, ind, idx, body}}, brs), r7}}
        case _: Parser.internal()

# Rebuild the pending continuation of one stacked frame from the result it waited for.
def Parser.resume2(+result: Parser.result, +frame: Parser.frame2) -> Parser.job2:
  match frame:
    case Parser.Frame2_c13{}:
      Parser.Job2_44{Parser.cont13(result)}
    case Parser.Frame2_14{}:
      Parser.Job2_14{result}
    case Parser.Frame2_12{+ts, +loc, +rest}:
      Parser.Job2_12{result, ts, loc, rest}
    case Parser.Frame2_13{}:
      Parser.Job2_13{result}
    case Parser.Frame2_c17{}:
      Parser.Job2_44{Parser.cont17(result)}
    case Parser.Frame2_17{+acc, +rest}:
      Parser.Job2_17{result, acc, rest}
    case Parser.Frame2_11{+fibered, +acc, +name}:
      Parser.Job2_11{result, fibered, acc, name}
    case Parser.Frame2_31{+fibered}:
      Parser.Job2_31{result, fibered}
    case Parser.Frame2_c34{+loc, +q, +x}:
      Parser.Job2_44{Parser.cont34(result, loc, q, x)}
    case Parser.Frame2_26{+fibered, +acc, +name, +fs}:
      Parser.Job2_26{result, fibered, acc, name, fs}
    case Parser.Frame2_c41{+b}:
      Parser.Job2_44{Parser.cont41(result, b)}
    case Parser.Frame2_c42{+b}:
      Parser.Job2_44{Parser.cont42(result, b)}
    case Parser.Frame2_c43{+lhs}:
      Parser.Job2_44{Parser.cont43(result, lhs)}
    case Parser.Frame2_c44{+lhs}:
      Parser.Job2_44{Parser.cont44(result, lhs)}
    case Parser.Frame2_28{+head}:
      Parser.Job2_28{result, head}
    case Parser.Frame2_c47{+inner, +loc}:
      Parser.Job2_44{Parser.cont47(result, inner, loc)}
    case Parser.Frame2_c48{+inner, +loc}:
      Parser.Job2_44{Parser.cont48(result, inner, loc)}
    case Parser.Frame2_21{}:
      Parser.Job2_21{result}
    case Parser.Frame2_c53{+bs}:
      Parser.Job2_44{Parser.cont53(result, bs)}
    case Parser.Frame2_c54{+x, +ty, +val}:
      Parser.Job2_44{Parser.cont54(result, x, ty, val)}
    case Parser.Frame2_29{+fibered, +scrut, +x, +ind, +idx, +loc}:
      Parser.Job2_29{result, fibered, scrut, x, ind, idx, loc}
    case Parser.Frame2_30{+fibered, +acc, +key, +bs}:
      Parser.Job2_30{result, fibered, acc, key, bs}
    case Parser.Frame2_22{+x, +ty, +loc}:
      Parser.Job2_22{result, x, ty, loc}
    case Parser.Frame2_c57{+key, +arity}:
      Parser.Job2_44{Parser.cont57(result, key, arity)}
    case Parser.Frame2_c60{+fibered, +scrut, +x, +ind, +idx, +body}:
      Parser.Job2_44{Parser.cont60(result, fibered, scrut, x, ind, idx, body)}
    case Parser.Frame2_c38{+fibered, +scrut}:
      Parser.Job2_44{Parser.cont38(result, fibered, scrut)}
    case Parser.Frame2_24{+fibered, +acc, +loc, +key}:
      Parser.Job2_24{result, fibered, acc, loc, key}
    case Parser.Frame2_32{+acc, +rest}:
      Parser.Job2_32{result, acc, rest}
    case Parser.Frame2_20{}:
      Parser.Job2_20{result}
    case Parser.Frame2_19{+word, +acc}:
      Parser.Job2_19{result, word, acc}
    case Parser.Frame2_25{+x}:
      Parser.Job2_25{result, x}
    case Parser.Frame2_18{}:
      Parser.Job2_18{result}


# The tagged dispatcher keeps each pending continuation on an explicit frame stack,
# so every call is a tail call and nesting depth uses heap, not the host stack.
@unsafe
def Parser.dispatch2(+job: Parser.job2, +stack: List<&2, Parser.frame2>) -> Parser.result:
  match job:
    case Parser.Job2_0{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.KInj{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_37{rest}, stack)
        case Con{T.Token.Token{T.Token.KAbsurd{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_0{rest}, Con{Parser.Frame2_c13{}, stack})
        case _:
          Parser.dispatch2(Parser.Job2_4{ts}, Con{Parser.Frame2_14{}, stack})
    case Parser.Job2_1{+head, +ts}:
      +starts : Bool = Parser.starts_atom(ts)
      Parser.dispatch2(Parser.Job2_16{starts, head, ts}, stack)
    case Parser.Job2_2{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_6{ts}, Con{Parser.Frame2_12{ts, loc, rest}, stack})
        case _:
          Parser.dispatch2(Parser.Job2_3{ts}, stack)
    case Parser.Job2_3{+ts}:
      Parser.dispatch2(Parser.Job2_0{ts}, Con{Parser.Frame2_13{}, stack})
    case Parser.Job2_4{+ts}:
      Parser.dispatch2(Parser.Job2_5{ts}, Con{Parser.Frame2_c17{}, stack})
    case Parser.Job2_5{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.Ident{+name},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SVar{name}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.Nat{+n},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SNat{T.Token.nat_value(n)}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.Bytes{+bytes},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{Parser.bytes(bytes), rest}}}, stack)
        case Con{T.Token.Token{T.Token.KProp{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SProp{}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KType{}, _}, Con{T.Token.Token{T.Token.Nat{+n},+loc},+rest}}:
          +r36 : Parser.result = Parser.bounded_nat(loc, n)
          Parser.dispatch2(Parser.Job2_44{Parser.cont19(r36, rest)}, stack)
        case Con{T.Token.Token{T.Token.KType{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SType{F.Bignum.zero}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KAuto{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SAuto{}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.Unit{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SUnit{}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KNatAdd{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SPrim{S.Syntax.PAdd{}}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KNatSub{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SPrim{S.Syntax.PSub{}}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KNatMul{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SPrim{S.Syntax.PMul{}}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KNatEq{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SPrim{S.Syntax.PEq{}}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KNatLt{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{S.Syntax.SPrim{S.Syntax.PLt{}}, rest}}}, stack)
        case Con{T.Token.Token{T.Token.KTuple{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_38{rest, "tuple"}, stack)
        case Con{T.Token.Token{T.Token.KSum{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_38{rest, "sum"}, stack)
        case Con{T.Token.Token{T.Token.KProd{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_38{rest, "prod"}, stack)
        case Con{T.Token.Token{T.Token.KMu{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "a mu group is a declaration and not a term")}, stack)
        case Con{T.Token.Token{T.Token.KAnd{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "'and' joins two members of a mu group and is not a term")}, stack)
        case Con{T.Token.Token{T.Token.KNu{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "nu arrives at M2")}, stack)
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_42{rest}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_44{Parser.expected("a term", ts)}, stack)
    case Parser.Job2_6{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          +r2 : Parser.result = Parser.mark(rest)
          Parser.dispatch2(Parser.Job2_10{r2, loc}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_44{Parser.expected("'('", ts)}, stack)
    case Parser.Job2_7{+ts, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_6{ts}, Con{Parser.Frame2_17{acc, rest}, stack})
        case _:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Binders{List.reverse(&2, S.Syntax.binder, acc), ts}}}, stack)
    case Parser.Job2_8{+ts, +fibered, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.Pipe{}, _}, Con{T.Token.Token{T.Token.Nat{+k},+loc},+rest}}:
          match fibered:
            case True{}:
              Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "a match branch keys a constructor, not a leg number")}, stack)
            case False{}:
              +r20 : Parser.result = Parser.bounded_nat(loc, k)
              Parser.dispatch2(Parser.Job2_34{r20, fibered, acc, loc, rest}, stack)
        case Con{T.Token.Token{T.Token.Pipe{}, _}, Con{T.Token.Token{T.Token.Ident{+name}, _},+rest}}:
          Parser.dispatch2(Parser.Job2_35{rest, Nil{}}, Con{Parser.Frame2_11{fibered, acc, name}, stack})
        case Con{T.Token.Token{T.Token.Pipe{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "expected a leg number or a constructor name after '|'")}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Branches{List.reverse(&2, S.Syntax.branch, acc), ts}}}, stack)
    case Parser.Job2_9{+fibered, +ts}:
      Parser.dispatch2(Parser.Job2_43{ts}, Con{Parser.Frame2_31{fibered}, stack})
    case Parser.Job2_10{+r2, +loc}:
      match r2:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v2}:
          match v2:
            case Parser.Marked{+q,+rq}:
              match rq:
                case Con{T.Token.Token{T.Token.Ident{+x}, _}, Con{T.Token.Token{T.Token.Colon{}, _},+r2}}:
                  Parser.dispatch2(Parser.Job2_43{r2}, Con{Parser.Frame2_c34{loc, q, x}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("a binder name and ':'", rq)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_11{+r22, +fibered, +acc, +name}:
      match r22:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v22}:
          match v22:
            case Parser.Fields{+fs,+r2}:
              match r2:
                case Con{T.Token.Token{T.Token.DArrow{},+loc},+r3}:
                  Parser.dispatch2(Parser.Job2_43{r3}, Con{Parser.Frame2_26{fibered, acc, name, fs}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'=>'", r2)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_12{+attempt, +ts, +loc, +rest}:
      match attempt:
        case Fail{+error}:
          Parser.dispatch2(Parser.Job2_3{ts}, stack)
        case Done{+value}:
          match value:
            case Parser.Binder{+b,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.Arrow{},+loc},+rest}:
                  Parser.dispatch2(Parser.Job2_43{rest}, Con{Parser.Frame2_c41{b}, stack})
                case Con{T.Token.Token{T.Token.Star{},+loc},+rest}:
                  Parser.dispatch2(Parser.Job2_43{rest}, Con{Parser.Frame2_c42{b}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_3{ts}, stack)
            case _:
              Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_13{+r27}:
      match r27:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v27}:
          match v27:
            case Parser.Term{+lhs,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.Arrow{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_43{r2}, Con{Parser.Frame2_c43{lhs}, stack})
                case Con{T.Token.Token{T.Token.Star{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_43{r2}, Con{Parser.Frame2_c44{lhs}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{lhs, rest}}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_14{+r29}:
      match r29:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v29}:
          match v29:
            case Parser.Term{+head,+rest}:
              Parser.dispatch2(Parser.Job2_1{head, rest}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_15{+r32, +n, +nloc, +rest}:
      match r32:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v32}:
          match v32:
            case Parser.Key{+key}:
              +r31 : Parser.result = Parser.bounded_nat(nloc, n)
              Parser.dispatch2(Parser.Job2_27{r31, rest, key}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_16{+starts, +head, +ts}:
      match starts:
        case True{}:
          Parser.dispatch2(Parser.Job2_4{ts}, Con{Parser.Frame2_28{head}, stack})
        case False{}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{head, ts}}}, stack)
    case Parser.Job2_17{+r3, +acc, +rest}:
      match r3:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v3}:
          match v3:
            case Parser.Binder{+b,+rest}:
              Parser.dispatch2(Parser.Job2_7{rest, Con{b, acc}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_18{+r39}:
      match r39:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v39}:
          match v39:
            case Parser.Term{+inner,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.RParen{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{inner, r2}}}, stack)
                case Con{T.Token.Token{T.Token.Comma{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_43{r2}, Con{Parser.Frame2_c47{inner, loc}, stack})
                case Con{T.Token.Token{T.Token.Colon{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_43{r2}, Con{Parser.Frame2_c48{inner, loc}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("')', ',' or ':'", rest)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_19{+r40, +word, +acc}:
      match r40:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v40}:
          match v40:
            case Parser.Term{+item,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.Comma{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_40{word, r2, Con{item, acc}}, stack)
                case Con{T.Token.Token{T.Token.RParen{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{Parser.build_items(word, List.reverse(&2, S.Syntax.t, Con{item, acc})), r2}}}, stack)
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("',' or ')'", rest)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_20{+r6}:
      match r6:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v6}:
          match v6:
            case Parser.Binder{+first,+rest}:
              Parser.dispatch2(Parser.Job2_7{rest, [first]}, Con{Parser.Frame2_21{}, stack})
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_21{+r5}:
      match r5:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v5}:
          match v5:
            case Parser.Binders{+bs,+r2}:
              match r2:
                case Con{T.Token.Token{T.Token.DArrow{},+loc},+r3}:
                  Parser.dispatch2(Parser.Job2_43{r3}, Con{Parser.Frame2_c53{bs}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'=>'", r2)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_22{+r8, +x, +ty, +loc}:
      match r8:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v8}:
          match v8:
            case Parser.Term{+val,+r4}:
              match r4:
                case Con{T.Token.Token{T.Token.KIn{},+loc},+r5}:
                  Parser.dispatch2(Parser.Job2_43{r5}, Con{Parser.Frame2_c54{x, ty, val}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'in'", r4)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_23{+r13, +fibered, +scrut, +x}:
      match r13:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v13}:
          match v13:
            case Parser.Index{+ind,+idx,+r3}:
              match r3:
                case Con{T.Token.Token{T.Token.KReturn{},+loc},+r4}:
                  Parser.dispatch2(Parser.Job2_43{r4}, Con{Parser.Frame2_29{fibered, scrut, x, ind, idx, loc}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'return'", r3)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_24{+r19, +fibered, +acc, +loc, +key}:
      match r19:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v19}:
          match v19:
            case Parser.Binders{+bs,+r2}:
              match r2:
                case Con{T.Token.Token{T.Token.DArrow{},+loc},+r3}:
                  Parser.dispatch2(Parser.Job2_43{r3}, Con{Parser.Frame2_30{fibered, acc, key, bs}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'=>'", r2)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_25{+r9, +x}:
      match r9:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v9}:
          match v9:
            case Parser.Term{+ty,+r2}:
              match r2:
                case Con{T.Token.Token{T.Token.ColonEq{},+loc},+r3}:
                  Parser.dispatch2(Parser.Job2_43{r3}, Con{Parser.Frame2_22{x, ty, loc}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("':='", r2)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_26{+r21, +fibered, +acc, +name, +fs}:
      match r21:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v21}:
          match v21:
            case Parser.Term{+body,+r4}:
              Parser.dispatch2(Parser.Job2_8{r4, fibered, Con{S.Syntax.BrCtor{name, fs, body}, acc}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_27{+r31, +rest, +key}:
      match r31:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v31}:
          match v31:
            case Parser.Key{+arity}:
              Parser.dispatch2(Parser.Job2_0{rest}, Con{Parser.Frame2_c57{key, arity}, stack})
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_28{+r33, +head}:
      match r33:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v33}:
          match v33:
            case Parser.Term{+arg,+rest}:
              Parser.dispatch2(Parser.Job2_1{S.Syntax.SApp{head, arg}, rest}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_29{+r12, +fibered, +scrut, +x, +ind, +idx, +loc}:
      match r12:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v12}:
          match v12:
            case Parser.Term{+body,+r5}:
              match r5:
                case Con{T.Token.Token{T.Token.KWith{},+loc},+r6}:
                  Parser.dispatch2(Parser.Job2_8{r6, fibered, Nil{}}, Con{Parser.Frame2_c60{fibered, scrut, x, ind, idx, body}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'with'", r5)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_30{+r18, +fibered, +acc, +key, +bs}:
      match r18:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v18}:
          match v18:
            case Parser.Term{+body,+r4}:
              Parser.dispatch2(Parser.Job2_8{r4, fibered, Con{S.Syntax.BrLeg{key, bs, body}, acc}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_31{+r15, +fibered}:
      match r15:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v15}:
          match v15:
            case Parser.Term{+scrut,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.KAs{}, _}, Con{T.Token.Token{T.Token.Ident{+x}, _},+r2}}:
                  +r13 : Parser.result = Parser.index_clause(r2)
                  Parser.dispatch2(Parser.Job2_23{r13, fibered, scrut, x}, stack)
                case Con{T.Token.Token{T.Token.KAs{},+loc},+rest}:
                  Parser.dispatch2(Parser.Job2_44{Parser.error(loc, "expected 'NAME [in FAMILY IDX..] return TYPE' after 'as'")}, stack)
                case Con{T.Token.Token{T.Token.KWith{},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_8{r2, fibered, Nil{}}, Con{Parser.Frame2_c38{fibered, scrut}, stack})
                case _:
                  Parser.dispatch2(Parser.Job2_44{Parser.expected("'as' or 'with'", rest)}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_32{+r16, +acc, +rest}:
      match r16:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v16}:
          match v16:
            case Parser.Binder{+b,+rest}:
              S.Syntax.Binder{+q,+name,+ty} = b
              Parser.dispatch2(Parser.Job2_35{rest, Con{S.Syntax.Field{q, name, Some{ty}}, acc}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_33{+r17, +ts, +acc}:
      match r17:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v17}:
          match v17:
            case Parser.Marked{+q,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.Ident{+x},+loc},+r2}:
                  Parser.dispatch2(Parser.Job2_35{r2, Con{S.Syntax.Field{q, x, None{}}, acc}}, stack)
                case _:
                  Parser.dispatch2(Parser.Job2_44{Done{Parser.Fields{List.reverse(&2, S.Syntax.field, acc), ts}}}, stack)
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_34{+r20, +fibered, +acc, +loc, +rest}:
      match r20:
        case Fail{+error}: Parser.dispatch2(Parser.Job2_44{Fail{error}}, stack)
        case Done{+v20}:
          match v20:
            case Parser.Key{+key}:
              Parser.dispatch2(Parser.Job2_7{rest, Nil{}}, Con{Parser.Frame2_24{fibered, acc, loc, key}, stack})
            case _: Parser.dispatch2(Parser.Job2_44{Parser.internal()}, stack)
    case Parser.Job2_35{+ts, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_6{ts}, Con{Parser.Frame2_32{acc, rest}, stack})
        case _:
          +r17 : Parser.result = Parser.mark(ts)
          Parser.dispatch2(Parser.Job2_33{r17, ts, acc}, stack)
    case Parser.Job2_36{+ts}:
      Parser.dispatch2(Parser.Job2_6{ts}, Con{Parser.Frame2_20{}, stack})
    case Parser.Job2_37{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.Nat{+k},+kloc}, Con{T.Token.Token{T.Token.KOf{}, _}, Con{T.Token.Token{T.Token.Nat{+n},+nloc},+rest}}}:
          +r32 : Parser.result = Parser.bounded_nat(kloc, k)
          Parser.dispatch2(Parser.Job2_15{r32, n, nloc, rest}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_44{Parser.expected("'K of N' after 'inj'", ts)}, stack)
    case Parser.Job2_38{+ts, +word}:
      match ts:
        case Con{T.Token.Token{T.Token.Unit{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{Parser.build_items(word, Nil{}), rest}}}, stack)
        case Con{T.Token.Token{T.Token.LParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_39{rest, word}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_44{Parser.expected("'(' after '" ++ word ++ "'", ts)}, stack)
    case Parser.Job2_39{+ts, +word}:
      match ts:
        case Con{T.Token.Token{T.Token.RParen{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_44{Done{Parser.Term{Parser.build_items(word, Nil{}), rest}}}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_40{word, ts, Nil{}}, stack)
    case Parser.Job2_40{+word, +ts, +acc}:
      Parser.dispatch2(Parser.Job2_43{ts}, Con{Parser.Frame2_19{word, acc}, stack})
    case Parser.Job2_41{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.Ident{+x}, _}, Con{T.Token.Token{T.Token.Colon{}, _},+rest}}:
          Parser.dispatch2(Parser.Job2_43{rest}, Con{Parser.Frame2_25{x}, stack})
        case _:
          Parser.dispatch2(Parser.Job2_44{Parser.expected("a name and ':' after 'let'", ts)}, stack)
    case Parser.Job2_42{+ts}:
      Parser.dispatch2(Parser.Job2_43{ts}, Con{Parser.Frame2_18{}, stack})
    case Parser.Job2_43{+ts}:
      match ts:
        case Con{T.Token.Token{T.Token.KFun{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_36{rest}, stack)
        case Con{T.Token.Token{T.Token.KLet{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_41{rest}, stack)
        case Con{T.Token.Token{T.Token.KCase{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_9{False{}, rest}, stack)
        case Con{T.Token.Token{T.Token.KMatch{},+loc},+rest}:
          Parser.dispatch2(Parser.Job2_9{True{}, rest}, stack)
        case _:
          Parser.dispatch2(Parser.Job2_2{ts}, stack)
    case Parser.Job2_44{+result}:
      match stack:
        case Nil{}:
          result
        case Con{+frame,+rest}:
          Parser.dispatch2(Parser.resume2(result, frame), rest)


def Parser.cont24(+r44: Parser.result, +name: String) -> Parser.result:
  match r44:
    case Fail{+error}: Fail{error}
    case Done{+v44}:
      match v44:
        case Parser.Term{+ty,+r2}:
          match r2:
            case Con{T.Token.Token{T.Token.ColonEq{},+loc},+r3}:
              +r43 : Parser.result = Parser.dispatch2(Parser.Job2_43{r3}, Nil{})
              Parser.cont49(r43, name, ty)
            case _:
              Parser.expected("':='", r2)
        case _: Parser.internal()

def Parser.cont25(+r45: Parser.result, +name: String) -> Parser.result:
  match r45:
    case Fail{+error}: Fail{error}
    case Done{+v45}:
      match v45:
        case Parser.Term{+ty,+r2}:
          Done{Parser.Decl{S.Syntax.DAxiom{name, ty}, r2}}
        case _: Parser.internal()

def Parser.cont26(+r46: Parser.result) -> Parser.result:
  match r46:
    case Fail{+error}: Fail{error}
    case Done{+v46}:
      match v46:
        case Parser.Fams{+fams,+r2}:
          Done{Parser.Decl{S.Syntax.DMu{fams}, r2}}
        case _: Parser.internal()

def Parser.cont27(+r47: Parser.result) -> Parser.result:
  match r47:
    case Fail{+error}: Fail{error}
    case Done{+v47}:
      match v47:
        case Parser.Fams{+fams,+r2}:
          Done{Parser.Decl{S.Syntax.DMu{fams}, r2}}
        case _: Parser.internal()

def Parser.cont58(+r53: Parser.result, +name: String, +params: List<&2, S.Syntax.binder>, +ty: S.Syntax.t) -> Parser.result:
  match r53:
    case Fail{+error}: Fail{error}
    case Done{+v53}:
      match v53:
        case Parser.Ctors{+ctors,+r6}:
          Done{Parser.Fam{S.Syntax.Fam{name, params, ty, ctors}, r6}}
        case _: Parser.internal()

def Parser.cont59(+r53: Parser.result, +name: String, +params: List<&2, S.Syntax.binder>, +ty: S.Syntax.t) -> Parser.result:
  match r53:
    case Fail{+error}: Fail{error}
    case Done{+v53}:
      match v53:
        case Parser.Ctors{+ctors,+r6}:
          Done{Parser.Fam{S.Syntax.Fam{name, params, ty, ctors}, r6}}
        case _: Parser.internal()

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch3(+job: Parser.job3) -> Parser.result:
  match job:
    case Parser.Job3_0{+r57, +acc, +name}:
      match r57:
        case Fail{+error}: Fail{error}
        case Done{+v57}:
          match v57:
            case Parser.Binders{+bs,+r2}:
              match r2:
                case Con{T.Token.Token{T.Token.Colon{},+loc},+r3}:
                  +r56 : Parser.result = Parser.dispatch2(Parser.Job2_43{r3}, Nil{})
                  Parser.dispatch3(Parser.Job3_1{r56, acc, name, bs})
                case _:
                  Parser.expected("':' after constructor binders", r2)
            case _: Parser.internal()
    case Parser.Job3_1{+r56, +acc, +name, +bs}:
      match r56:
        case Fail{+error}: Fail{error}
        case Done{+v56}:
          match v56:
            case Parser.Term{+result,+r4}:
              Parser.dispatch3(Parser.Job3_2{r4, Con{S.Syntax.FamCtor{name, Parser.fold_arrows(bs, result)}, acc}})
            case _: Parser.internal()
    case Parser.Job3_2{+ts, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.Pipe{}, _}, Con{T.Token.Token{T.Token.Ident{+name}, _},+rest}}:
          +r57 : Parser.result = Parser.dispatch2(Parser.Job2_7{rest, Nil{}}, Nil{})
          Parser.dispatch3(Parser.Job3_0{r57, acc, name})
        case Con{T.Token.Token{T.Token.Pipe{},+loc},+rest}:
          Parser.error(loc, "expected a constructor name and ':' after '|'")
        case _:
          Done{Parser.Ctors{List.reverse(&2, S.Syntax.fam_ctor, acc), ts}}


def Parser.cont51(+r54: Parser.result, +name: String, +loc: T.Token.loc, +params: List<&2, S.Syntax.binder>) -> Parser.result:
  match r54:
    case Fail{+error}: Fail{error}
    case Done{+v54}:
      match v54:
        case Parser.Term{+ty,+r4}:
          match r4:
            case Con{T.Token.Token{T.Token.KWith{},+loc},+r5}:
              +r53 : Parser.result = Parser.dispatch3(Parser.Job3_2{r5, Nil{}})
              Parser.cont58(r53, name, params, ty)
            case Con{T.Token.Token{T.Token.ColonEq{},+loc},+r5}:
              +r53 : Parser.result = Parser.dispatch3(Parser.Job3_2{r5, Nil{}})
              Parser.cont59(r53, name, params, ty)
            case _:
              Parser.expected("':=' or 'with'", r4)
        case _: Parser.internal()

def Parser.cont32(+r55: Parser.result, +name: String, +loc: T.Token.loc) -> Parser.result:
  match r55:
    case Fail{+error}: Fail{error}
    case Done{+v55}:
      match v55:
        case Parser.Binders{+params,+r2}:
          match r2:
            case Con{T.Token.Token{T.Token.Colon{},+loc},+r3}:
              +r54 : Parser.result = Parser.dispatch2(Parser.Job2_43{r3}, Nil{})
              Parser.cont51(r54, name, loc, params)
            case _:
              Parser.expected("':'", r2)
        case _: Parser.internal()

def Parser.fam(+ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.Ident{+name},+loc},+rest}:
      +r55 : Parser.result = Parser.dispatch2(Parser.Job2_7{rest, Nil{}}, Nil{})
      Parser.cont32(r55, name, loc)
    case _:
      Parser.expected("a family name", ts)

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch4(+job: Parser.job4) -> Parser.result:
  match job:
    case Parser.Job4_0{+r52, +acc}:
      match r52:
        case Fail{+error}: Fail{error}
        case Done{+v52}:
          match v52:
            case Parser.Fam{+fm,+r2}:
              Parser.dispatch4(Parser.Job4_1{r2, Con{fm, acc}})
            case _: Parser.internal()
    case Parser.Job4_1{+ts, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.KMu{},+loc},+rest}:
          +r52 : Parser.result = Parser.fam(rest)
          Parser.dispatch4(Parser.Job4_0{r52, acc})
        case Con{T.Token.Token{T.Token.KEnd{},+loc},+rest}:
          match acc:
            case Con{+first, Con{+second,+remaining}}:
              Done{Parser.Fams{List.reverse(&2, S.Syntax.fam, acc), rest}}
            case _:
              Parser.error(loc, "a mutual group needs at least two mu declarations")
        case _:
          Parser.expected("'mu' or 'end' in a mutual group", ts)


def Parser.cont50(+r48: Parser.result, +name: String, +ty: S.Syntax.t) -> Parser.result:
  match r48:
    case Fail{+error}: Fail{error}
    case Done{+v48}:
      match v48:
        case Parser.Term{+body,+r4}:
          Done{Parser.Rec{S.Syntax.RecDef{name, ty, body}, r4}}
        case _: Parser.internal()

def Parser.cont28(+r49: Parser.result, +name: String) -> Parser.result:
  match r49:
    case Fail{+error}: Fail{error}
    case Done{+v49}:
      match v49:
        case Parser.Term{+ty,+r2}:
          match r2:
            case Con{T.Token.Token{T.Token.ColonEq{},+loc},+r3}:
              +r48 : Parser.result = Parser.dispatch2(Parser.Job2_43{r3}, Nil{})
              Parser.cont50(r48, name, ty)
            case _:
              Parser.expected("':='", r2)
        case _: Parser.internal()

def Parser.rec_member(+ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.Ident{+name}, _}, Con{T.Token.Token{T.Token.Colon{}, _},+rest}}:
      +r49 : Parser.result = Parser.dispatch2(Parser.Job2_43{rest}, Nil{})
      Parser.cont28(r49, name)
    case _:
      Parser.expected("a definition name and ':'", ts)

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch5(+job: Parser.job5) -> Parser.result:
  match job:
    case Parser.Job5_0{+r50, +acc}:
      match r50:
        case Fail{+error}: Fail{error}
        case Done{+v50}:
          match v50:
            case Parser.Rec{+member,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.KAnd{},+loc},+r2}:
                  Parser.dispatch5(Parser.Job5_1{r2, Con{member, acc}})
                case _:
                  Done{Parser.Recs{List.reverse(&2, S.Syntax.rec_def, Con{member, acc}), rest}}
            case _: Parser.internal()
    case Parser.Job5_1{+ts, +acc}:
      +r50 : Parser.result = Parser.rec_member(ts)
      Parser.dispatch5(Parser.Job5_0{r50, acc})


# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch6(+job: Parser.job6) -> Parser.result:
  match job:
    case Parser.Job6_0{+r51, +acc}:
      match r51:
        case Fail{+error}: Fail{error}
        case Done{+v51}:
          match v51:
            case Parser.Fam{+member,+rest}:
              match rest:
                case Con{T.Token.Token{T.Token.KAnd{},+loc},+r2}:
                  Parser.dispatch6(Parser.Job6_1{r2, Con{member, acc}})
                case _:
                  Done{Parser.Fams{List.reverse(&2, S.Syntax.fam, Con{member, acc}), rest}}
            case _: Parser.internal()
    case Parser.Job6_1{+ts, +acc}:
      +r51 : Parser.result = Parser.fam(ts)
      Parser.dispatch6(Parser.Job6_0{r51, acc})


def Parser.decl(+ts: List<&2, T.Token.t>) -> Parser.result:
  match ts:
    case Con{T.Token.Token{T.Token.KDef{}, _}, Con{T.Token.Token{T.Token.KRec{}, _},+rest}}:
      +r42 : Parser.result = Parser.dispatch5(Parser.Job5_1{rest, Nil{}})
      Parser.cont23(r42)
    case Con{T.Token.Token{T.Token.KDef{}, _}, Con{T.Token.Token{T.Token.Ident{+name}, _}, Con{T.Token.Token{T.Token.Colon{}, _},+rest}}}:
      +r44 : Parser.result = Parser.dispatch2(Parser.Job2_43{rest}, Nil{})
      Parser.cont24(r44, name)
    case Con{T.Token.Token{T.Token.KAxiom{}, _}, Con{T.Token.Token{T.Token.Ident{+name}, _}, Con{T.Token.Token{T.Token.Colon{}, _},+rest}}}:
      +r45 : Parser.result = Parser.dispatch2(Parser.Job2_43{rest}, Nil{})
      Parser.cont25(r45, name)
    case Con{T.Token.Token{T.Token.KMu{},+loc},+rest}:
      +r46 : Parser.result = Parser.dispatch6(Parser.Job6_1{rest, Nil{}})
      Parser.cont26(r46)
    case Con{T.Token.Token{T.Token.KMutual{},+loc},+rest}:
      +r47 : Parser.result = Parser.dispatch4(Parser.Job4_1{rest, Nil{}})
      Parser.cont27(r47)
    case Con{T.Token.Token{T.Token.KNu{},+loc},+rest}:
      Parser.error(loc, "nu arrives at M2")
    case _:
      Parser.expected("'def NAME :', 'def rec NAME :', 'axiom NAME :', 'mu NAME' or 'mutual'", ts)

# The tagged dispatcher preserves suffix recursion across continuations.
@unsafe
def Parser.dispatch7(+job: Parser.job7) -> Parser.result:
  match job:
    case Parser.Job7_0{+r41, +acc}:
      match r41:
        case Fail{+error}: Fail{error}
        case Done{+v41}:
          match v41:
            case Parser.Decl{+decl,+rest}:
              Parser.dispatch7(Parser.Job7_1{rest, Con{decl, acc}})
            case _: Parser.internal()
    case Parser.Job7_1{+ts, +acc}:
      match ts:
        case Con{T.Token.Token{T.Token.Eof{},+loc},+rest}:
          Done{Parser.Decls{List.reverse(&2, S.Syntax.decl, acc)}}
        case _:
          +r41 : Parser.result = Parser.decl(ts)
          Parser.dispatch7(Parser.Job7_0{r41, acc})

def Parser.declarations(result: Parser.result) -> Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>:
  match result:
    case Fail{error}: Fail{error}
    case Done{value}:
      match value:
        case Parser.Decls{decls}: Done{decls}
        case _: Fail{F.Error.Cannot_infer{"parser continuation result mismatch"}}

def Parser.lexed(result: Result<&2, &2, F.Error.t, List<&2, T.Token.t>>) -> Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>:
  match result:
    case Fail{error}: Fail{error}
    case Done{tokens}: Parser.declarations(Parser.dispatch7(Parser.Job7_1{tokens, Nil{}}))

def Parser.parse(source: String) -> Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>:
  Parser.lexed(L.Lexer.lex(source))

def Parser.round_trip_equal(equal: Bool) -> Result<&2, &2, F.Error.t, Unit>:
  match equal:
    case True{}: Done{Unit{}}
    case False{}: Fail{F.Error.Cannot_infer{"printed tree changed"}}

def Parser.round_trip_second(first: List<&2, S.Syntax.decl>, second: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> Result<&2, &2, F.Error.t, Unit>:
  match second:
    case Fail{error}: Fail{error}
    case Done{tree}: Parser.round_trip_equal(S.Syntax.equal_declarations(first, tree))

def Parser.round_trip_first(first: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> Result<&2, &2, F.Error.t, Unit>:
  match first:
    case Fail{error}: Fail{error}
    case Done{+tree}: Parser.round_trip_second(tree, Parser.parse(S.Syntax.print(tree)))

def Parser.round_trip(source: String) -> Result<&2, &2, F.Error.t, Unit>:
  Parser.round_trip_first(Parser.parse(source))
