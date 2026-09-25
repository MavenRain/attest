import Base
import ./foundation.bend as F
import ./kernel_util.bend as U

def Rules.spar_word() -> String:
  F.Shape.parallel_word

def Rules.snu_word() -> String:
  F.Shape.coinductive_word

def Rules.auto_word() -> String:
  "instances arrive at M2"

def Rules.wrong_pack() -> String:
  "the rule pack does not match the shape of the term"

def Rules.stuck_msg() -> String:
  "an elimination met a value it cannot eliminate"

def Rules.leg_msg() -> String:
  "the leg address is outside the collection"

def Rules.diagram_msg() -> String:
  "the diagram is not a section of the declared width"

def Rules.as_vpi(-A: Data, shape: F.Shape.t<A>) -> Maybe<&2, F.Triple3<F.Quantity.t, String, A>>:
  F.Shape.point(A, shape)

def Rules.as_vcoll(-A: Data, shape: F.Shape.t<A>) -> Maybe<&2, Nat>:
  F.Shape.collection(A, shape)

def Rules.arrow(q: F.Quantity.t, x: String, dom: F.Term.t, cod: F.Term.t) -> F.Term.t:
  F.Term.Ran{F.Shape.make_point(F.Term.t, q, x, dom), cod}

def Rules.legs(ts: List<&2, F.Term.t>) -> List<&2, F.Term.leg>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{F.Term.Leg{Nil{}, x}, Rules.legs(rest)}

def Rules.leg_of(body: F.Term.t) -> F.Term.leg:
  F.Term.Leg{Nil{}, body}

def Rules.diagram_of(+legs: List<&2, F.Term.t>) -> F.Term.t:
  F.Term.Sec{F.Shape.make_collection(F.Term.t, List.length(&2, F.Term.t, legs)), Rules.legs(legs)}

def Rules.sum_ty(+legs: List<&2, F.Term.t>) -> F.Term.t:
  F.Term.Lan{F.Shape.make_collection(F.Term.t, List.length(&2, F.Term.t, legs)), Rules.diagram_of(legs)}

def Rules.prod_ty(+legs: List<&2, F.Term.t>) -> F.Term.t:
  F.Term.Ran{F.Shape.make_collection(F.Term.t, List.length(&2, F.Term.t, legs)), Rules.diagram_of(legs)}

def Rules.unit_ty(level: F.Level.t) -> F.Term.t:
  F.Term.Ann{Rules.prod_ty(Nil{}), F.Term.Univ{level}}

def Rules.unit_val() -> F.Term.t:
  F.Term.Sec{F.Shape.make_collection(F.Term.t, 0n), Nil{}}

def Rules.bool_ty() -> F.Term.t:
  Rules.sum_ty([Rules.unit_ty(F.Level.one), Rules.unit_ty(F.Level.one)])

def Rules.bool_value(b: Bool) -> F.Value.t:
  match b:
    case False{}:
      F.Value.VIn{F.Shape.make_collection(F.Value.t, 2n), F.Value.VALeg{0n}, [F.Value.VSec{F.Shape.make_collection(F.Value.t, 0n), Nil{}}]}
    case True{}:
      F.Value.VIn{F.Shape.make_collection(F.Value.t, 2n), F.Value.VALeg{1n}, [F.Value.VSec{F.Shape.make_collection(F.Value.t, 0n), Nil{}}]}

def Rules.imax_right(is_zero: Bool, a: F.Level.t, b: F.Level.t) -> F.Level.t:
  match is_zero:
    case True{}:
      F.Level.zero
    case False{}:
      F.Level.max(a, b)

def Rules.imax(a: F.Level.t, +b: F.Level.t) -> F.Level.t:
  Rules.imax_right(F.Level.equal(b, F.Level.zero), a, b)

def Rules.max_of(xs: List<&2, F.Level.t>) -> F.Level.t:
  match xs:
    case Nil{}:
      F.Level.zero
    case Con{x, rest}:
      F.Level.max(x, Rules.max_of(rest))

def Prim.name(p: F.Prim.t) -> String:
  match p:
    case F.Prim.Nat_add{}:
      "natAdd"
    case F.Prim.Nat_sub{}:
      "natSub"
    case F.Prim.Nat_mul{}:
      "natMul"
    case F.Prim.Nat_eq{}:
      "natEq"
    case F.Prim.Nat_lt{}:
      "natLt"

def Prim.catalog() -> List<&2, F.Prim.t>:
  [F.Prim.Nat_add{}, F.Prim.Nat_sub{}, F.Prim.Nat_mul{}, F.Prim.Nat_eq{}, F.Prim.Nat_lt{}]

def Prim.find_next(hit: Bool, p: F.Prim.t, rest: Maybe<&2, F.Prim.t>) -> Maybe<&2, F.Prim.t>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      rest

def Prim.find(xs: List<&2, F.Prim.t>, +name: String) -> Maybe<&2, F.Prim.t>:
  match xs:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      Prim.find_next(String.eq(Prim.name(p), name), p, Prim.find(rest, name))

def Prim.nat_name() -> String:
  "Nat"

def Prim.nat_ty() -> F.Term.t:
  F.Term.Global{Prim.nat_name}

def Prim.result_type(p: F.Prim.t) -> F.Term.t:
  match p:
    case F.Prim.Nat_add{}:
      Prim.nat_ty
    case F.Prim.Nat_sub{}:
      Prim.nat_ty
    case F.Prim.Nat_mul{}:
      Prim.nat_ty
    case F.Prim.Nat_eq{}:
      Rules.bool_ty
    case F.Prim.Nat_lt{}:
      Rules.bool_ty

def Prim.ty(p: F.Prim.t) -> F.Term.t:
  Rules.arrow(F.Quantity.Many{}, "a", Prim.nat_ty,
    Rules.arrow(F.Quantity.Many{}, "b", Prim.nat_ty, Prim.result_type(p)))

def Prim.nonnegative(sign: Cmp, n: F.Bignum.t) -> Maybe<&2, F.Bignum.t>:
  match sign:
    case LT{}:
      None{}
    case EQ{}:
      Some{n}
    case GT{}:
      Some{n}

def Prim.as_nat(literal: F.Literal.t) -> Maybe<&2, F.Bignum.t>:
  match literal:
    case F.Literal.LString{s}:
      None{}
    case F.Literal.LInt{+n}:
      Prim.nonnegative(F.Bignum.sign(n), n)

def Prim.nats_pair(pair: F.Pair2<F.Literal.t, F.Literal.t>) -> Maybe<&2, F.Pair2<F.Bignum.t, F.Bignum.t>>:
  F.Pair2{x, y} = pair
  do Maybe<&2, F.Pair2<F.Bignum.t, F.Bignum.t>>:
    a: F.Bignum.t <- Prim.as_nat(x)
    b: F.Bignum.t <- Prim.as_nat(y)
    return F.Pair2{a, b}

def Prim.two_nats(args: List<&2, F.Literal.t>) -> Maybe<&2, F.Pair2<F.Bignum.t, F.Bignum.t>>:
  Maybe.bind(&2, F.Pair2<F.Literal.t, F.Literal.t>, F.Pair2<F.Bignum.t, F.Bignum.t>,
    U.Kernel.two(F.Literal.t, args), Prim.nats_pair)

def Prim.less(order: Cmp) -> Bool:
  match order:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def Prim.calculate(p: F.Prim.t, a: F.Bignum.t, b: F.Bignum.t) -> F.Value.t:
  match p:
    case F.Prim.Nat_add{}:
      F.Value.VLit{F.Literal.LInt{F.Bignum.add(a, b)}}
    case F.Prim.Nat_sub{}:
      F.Value.VLit{F.Literal.LInt{F.Bignum.sub(a, b)}}
    case F.Prim.Nat_mul{}:
      F.Value.VLit{F.Literal.LInt{F.Bignum.mul(a, b)}}
    case F.Prim.Nat_eq{}:
      Rules.bool_value(F.Bignum.equal(a, b))
    case F.Prim.Nat_lt{}:
      Rules.bool_value(Prim.less(F.Bignum.compare(a, b)))

def Prim.apply_nats(pair: Maybe<&2, F.Pair2<F.Bignum.t, F.Bignum.t>>, p: F.Prim.t)
  -> Result<&2, &2, F.Error.t, Maybe<&2, F.Value.t>>:
  match pair:
    case None{}:
      Done{None{}}
    case Some{ab}:
      F.Pair2{a, b} = ab
      Done{Some{Prim.calculate(p, a, b)}}

def Prim.apply(p: F.Prim.t, args: List<&2, F.Literal.t>)
  -> Result<&2, &2, F.Error.t, Maybe<&2, F.Value.t>>:
  Prim.apply_nats(Prim.two_nats(args), p)

def Global.primitives(primitives: List<&2, F.Prim.t>, globals: F.Global.t) -> F.Global.t:
  match primitives:
    case Nil{}: globals
    case Con{+prim, rest}:
      Global.primitives(rest, F.Global.add(Prim.name(prim), F.Global.Prim{F.Global.PrimEntry{Prim.ty(prim), prim}}, globals))

def Global.initial() -> F.Global.t:
  Global.primitives(Prim.catalog,
    F.Global.add(Prim.nat_name, F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.one}}}, F.Global.empty))
