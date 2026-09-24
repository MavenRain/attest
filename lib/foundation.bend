import Base

# Shared data declarations. Positional variant fields preserve OCaml order.

type Pair2<-A: Data, -B: Data> is Data:
  Pair2{fst: A, snd: B}

type Triple3<-A: Data, -B: Data, -C: Data> is Data:
  Triple3{fst: A, snd: B, thd: C}

type Bignum.t is Data:
  Bignum.Int{negative: Bool, limbs: List<&2, U32>}

def Level.t() -> Data:
  Bignum.t

type Quantity.t is Data:
  Quantity.Zero{}
  Quantity.One{}
  Quantity.Many{}

def Quantity.interval() -> Data:
  Pair2<Quantity.t, Quantity.t>

type Quantity.usage is Data:
  Quantity.Usage{paths: Maybe<&2, List<&2, Pair2<Nat, Quantity.interval>>>, reads: List<&2, Pair2<Nat, Quantity.interval>>}

type Literal.t is Data:
  Literal.LString{x0: String}
  Literal.LInt{x0: Bignum.t}

type Error.t is Data:
  Error.Not_yet{x0: String}
  Error.Parse{x0: String, x1: Nat, x2: Nat}
  Error.Carry{x0: String}
  Error.Unbound{x0: String}
  Error.Mismatch{x0: String}
  Error.Universe{x0: String}
  Error.Quantity{x0: String}
  Error.Wrong_leg{x0: String}
  Error.Missing_branch{x0: String}
  Error.Overflow{x0: String}
  Error.Cannot_infer{x0: String}
  Error.Budget_exhausted{x0: String}
  Error.Index_not_zero{x0: String}
  Error.Index_above_universe{x0: String}
  Error.Termination{x0: String}

type Shape.t<-A: Data> is Data:
  Shape.SPi{x0: Quantity.t, x1: String, x2: A}
  Shape.SColl{x0: Nat}
  Shape.SPar{x0: A, x1: A}
  Shape.SMu{x0: String, x1: List<&2, A>}
  Shape.SNu{x0: String, x1: List<&2, A>}

type Term.AddrData<-Tm: Data> is Data:
  Term.APt{x0: Quantity.t, x1: Tm}
  Term.ALeg{x0: Nat}
  Term.ACtor{x0: String}

type Term.LegData<-Tm: Data> is Data:
  Term.Leg{l_binders: List<&2, Pair2<Quantity.t, String>>, l_body: Tm}

type Term.MotiveData<-Tm: Data> is Data:
  Term.Motive{m_ind: Maybe<&2, String>, m_idx: List<&2, String>, m_self: String, m_body: Tm}

type Term.ElimData<-Tm: Data> is Data:
  Term.Elimination{e_shape: Shape.t<Tm>, e_scrut: Tm, e_scrut_q: Quantity.t, e_motive: Maybe<&2, Term.MotiveData<Tm>>, e_branches: List<&2, Pair2<Term.AddrData<Tm>, Term.LegData<Tm>>>}

type Term.t is Data:
  Term.Var{x0: Nat}
  Term.Univ{x0: Level.t}
  Term.Lan{x0: Shape.t<Term.t>, x1: Term.t}
  Term.Ran{x0: Shape.t<Term.t>, x1: Term.t}
  Term.In{x0: Shape.t<Term.t>, x1: Term.AddrData<Term.t>, x2: List<&2, Term.t>}
  Term.Elim{x0: Term.ElimData<Term.t>}
  Term.Sec{x0: Shape.t<Term.t>, x1: List<&2, Term.LegData<Term.t>>}
  Term.Out{x0: Shape.t<Term.t>, x1: Term.AddrData<Term.t>, x2: Term.t}
  Term.Let{x0: String, x1: Term.t, x2: Term.t, x3: Term.t}
  Term.Ann{x0: Term.t, x1: Term.t}
  Term.Global{x0: String}
  Term.Lit{x0: Literal.t}
  Term.Auto{}

def Term.addr() -> Data:
  Term.AddrData<Term.t>

def Term.leg() -> Data:
  Term.LegData<Term.t>

def Term.elim() -> Data:
  Term.ElimData<Term.t>

def Term.motive() -> Data:
  Term.MotiveData<Term.t>

type Value.head is Data:
  Value.HLocal{x0: Nat}
  Value.HGlobal{x0: String}

type Value.ClosureData<-Tm: Data> is Data:
  Value.Closure{env: List<&2, Tm>, body: Term.t}

type Value.AddrData<-Tm: Data> is Data:
  Value.VAPt{x0: Quantity.t, x1: Tm}
  Value.VALeg{x0: Nat}
  Value.VACtor{x0: String}

type Value.StuckData<-Tm: Data> is Data:
  Value.StuckElim{s_shape: Shape.t<Tm>, s_scrut_q: Quantity.t, s_motive: Maybe<&2, Term.motive>, s_branches: List<&2, Pair2<Term.addr, Term.leg>>, s_env: List<&2, Tm>}

type Value.SpineData<-Tm: Data> is Data:
  Value.SOut{x0: Shape.t<Tm>, x1: Value.AddrData<Tm>}
  Value.SElim{x0: Value.StuckData<Tm>}

type Value.LegData<-Tm: Data> is Data:
  Value.Leg{vl_binders: List<&2, Pair2<Quantity.t, String>>, vl_clo: Value.ClosureData<Tm>}

type Value.t is Data:
  Value.VUniv{x0: Level.t}
  Value.VLan{x0: Shape.t<Value.t>, x1: Value.ClosureData<Value.t>, x2: Maybe<&2, Level.t>}
  Value.VRan{x0: Shape.t<Value.t>, x1: Value.ClosureData<Value.t>, x2: Maybe<&2, Level.t>}
  Value.VIn{x0: Shape.t<Value.t>, x1: Value.AddrData<Value.t>, x2: List<&2, Value.t>}
  Value.VSec{x0: Shape.t<Value.t>, x1: List<&2, Value.LegData<Value.t>>}
  Value.VLit{x0: Literal.t}
  Value.VNeutral{x0: Value.head, x1: List<&2, Value.SpineData<Value.t>>}

def Value.vaddr() -> Data:
  Value.AddrData<Value.t>

def Value.vleg() -> Data:
  Value.LegData<Value.t>

def Value.spine() -> Data:
  Value.SpineData<Value.t>

def Value.stuck_elim() -> Data:
  Value.StuckData<Value.t>

def Value.closure() -> Data:
  Value.ClosureData<Value.t>

def Positivity.telescope() -> Data:
  List<&2, Triple3<Quantity.t, String, Term.t>>

type Positivity.ctor_status is Data:
  Positivity.Provisional{}
  Positivity.Builtin{}
  Positivity.Complete{x0: List<&2, String>}

type Positivity.ctor is Data:
  Positivity.Ctor{c_name: String, c_args: Positivity.telescope, c_res_idx: List<&2, Term.t>, c_full_arity: Nat, c_self_rec: Bool}

type Positivity.family is Data:
  Positivity.Family{f_name: String, f_params: Positivity.telescope, f_indices: Positivity.telescope, f_level: Level.t, f_status: Positivity.ctor_status, f_ctors: List<&2, Positivity.ctor>, f_positive: Bool}

type Prim.t is Data:
  Prim.Nat_add{}
  Prim.Nat_sub{}
  Prim.Nat_mul{}
  Prim.Nat_eq{}
  Prim.Nat_lt{}

def Global.telescope() -> Data:
  List<&2, Triple3<Quantity.t, String, Term.t>>

type Global.def_entry is Data:
  Global.DefEntry{ty: Term.t, body: Term.t, reducible: Bool, rec_arg: Maybe<&2, Nat>, partial: Bool}

type Global.axiom_entry is Data:
  Global.AxiomEntry{ax_ty: Term.t}

type Global.prim_entry is Data:
  Global.PrimEntry{p_ty: Term.t, prim: Prim.t}

type Global.entry is Data:
  Global.Def{x0: Global.def_entry}
  Global.Axiom{x0: Global.axiom_entry}
  Global.Prim{x0: Global.prim_entry}

type Global.map<-A: Data> is Data:
  Global.Leaf{}
  Global.Node{height: Nat, key: String, value: A, left: Global.map<A>, right: Global.map<A>}

type Global.table<-A: Data> is Data:
  Global.Table{tree: Global.map<A>, original: Maybe<&2, List<&2, Pair2<String, A>>>}

type Global.t is Data:
  Global.Globals{entries: Global.table<Global.entry>, families: Global.table<Positivity.family>}

# Integer magnitudes use little-endian radix 32768 limbs.
# All limb arithmetic stays below U32 overflow.
def Bignum.trim_zero(h: U32, zero: Bool) -> List<&2, U32>:
  match zero:
    case True{}:
      []
    case False{}:
      [h]

def Bignum.trim_cons(+h: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match tail:
    case Nil{}:
      Bignum.trim_zero(h, U32.is_zero(h))
    case Con{x, xs}:
      Con{h, Con{x, xs}}

def Bignum.trim(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      Bignum.trim_cons(h, Bignum.trim(t))

def Bignum.make_norm(negative: Bool, limbs: List<&2, U32>) -> Bignum.t:
  match limbs:
    case Nil{}:
      Bignum.Int{False{}, []}
    case Con{h, t}:
      Bignum.Int{negative, Con{h, t}}

def Bignum.make(negative: Bool, limbs: List<&2, U32>) -> Bignum.t:
  Bignum.make_norm(negative, Bignum.trim(limbs))

def Bignum.zero() -> Bignum.t:
  Bignum.Int{False{}, []}

def Bignum.one() -> Bignum.t:
  Bignum.Int{False{}, [1]}

def Bignum.nat_limbs_step(+n: Nat, empty: Bool) -> List<&2, U32>:
  match empty:
    case True{}:
      []
    case False{}:
      [U32.from_nat(n)]

def Bignum.from_u32(+n: U32) -> Bignum.t:
  Bignum.make(False{}, [(n % 32768 : U32), ((n / 32768 : U32) % 32768 : U32), (n / 1073741824 : U32)])

@unsafe
def Bignum.nat_limbs(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{U32.from_nat(((1n+p) % 32768n : Nat)), Bignum.nat_limbs(((1n+p) / 32768n : Nat))}

def Bignum.from_nat(n: Nat) -> Bignum.t:
  Bignum.Int{False{}, Bignum.nat_limbs(n)}

def Bignum.of_int(n: Nat) -> Bignum.t:
  Bignum.from_nat(n)

def Bignum.of_nat(n: Nat) -> Bignum.t:
  Bignum.from_nat(n)

def Bignum.cmp_head(a: U32, b: U32, tails: Cmp) -> Cmp:
  match tails:
    case LT{}:
      LT{}
    case EQ{}:
      U32.cmp(a, b)
    case GT{}:
      GT{}

def Bignum.cmp_abs(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          EQ{}
        case Con{h, t}:
          LT{}
    case Con{h, t}:
      match ys:
        case Nil{}:
          GT{}
        case Con{k, u}:
          Bignum.cmp_head(h, k, Bignum.cmp_abs(t, u))

def Bignum.cmp_flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def Bignum.compare(a: Bignum.t, b: Bignum.t) -> Cmp:
  match a b:
    case Bignum.Int{False{}, al} Bignum.Int{False{}, bl}:
      Bignum.cmp_abs(al, bl)
    case Bignum.Int{True{}, al} Bignum.Int{True{}, bl}:
      Bignum.cmp_flip(Bignum.cmp_abs(al, bl))
    case Bignum.Int{True{}, al} Bignum.Int{False{}, bl}:
      LT{}
    case Bignum.Int{False{}, al} Bignum.Int{True{}, bl}:
      GT{}

def Bignum.is_equal(c: Cmp) -> Bool:
  match c:
    case EQ{}:
      True{}
    case LT{}:
      False{}
    case GT{}:
      False{}

def Bignum.equal(a: Bignum.t, b: Bignum.t) -> Bool:
  Bignum.is_equal(Bignum.compare(a, b))

def Bignum.sign(a: Bignum.t) -> Cmp:
  Bignum.compare(a, Bignum.zero)

def Bignum.negate(a: Bignum.t) -> Bignum.t:
  match a:
    case Bignum.Int{negative, limbs}:
      Bignum.make(Bool.not(negative), limbs)

def Bignum.carry_end(carry: U32, empty: Bool) -> List<&2, U32>:
  match empty:
    case True{}:
      []
    case False{}:
      [carry]

def Bignum.add_carry(xs: List<&2, U32>, +carry: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Bignum.carry_end(carry, U32.is_zero(carry))
    case Con{+h, t}:
      Con{((h + carry) % 32768 : U32), Bignum.add_carry(t, ((h + carry) / 32768 : U32))}

def Bignum.add_abs(xs: List<&2, U32>, ys: List<&2, U32>, +carry: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Bignum.add_carry(ys, carry)
    case Con{+h, t}:
      match ys:
        case Nil{}:
          Con{((h + carry) % 32768 : U32), Bignum.add_carry(t, ((h + carry) / 32768 : U32))}
        case Con{+k, u}:
          Con{((h + k + carry) % 32768 : U32), Bignum.add_abs(t, u, ((h + k + carry) / 32768 : U32))}

def Bignum.borrow(a: U32, b: U32, carry: U32) -> U32:
  Bool.to_u32((a < (b + carry) : U32))

def Bignum.sub_abs(xs: List<&2, U32>, ys: List<&2, U32>, +borrow: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+h, t}:
      match ys:
        case Nil{}:
          Con{((32768 + h - borrow) % 32768 : U32), Bignum.sub_abs(t, [], Bignum.borrow(h, 0, borrow))}
        case Con{+k, u}:
          Con{((32768 + h - k - borrow) % 32768 : U32), Bignum.sub_abs(t, u, Bignum.borrow(h, k, borrow))}

def Bignum.add_different(negative: Bool, al: List<&2, U32>, bl: List<&2, U32>, order: Cmp) -> Bignum.t:
  match order:
    case EQ{}:
      Bignum.zero
    case GT{}:
      Bignum.make(negative, Bignum.sub_abs(al, bl, 0))
    case LT{}:
      Bignum.make(Bool.not(negative), Bignum.sub_abs(bl, al, 0))

def Bignum.add(a: Bignum.t, b: Bignum.t) -> Bignum.t:
  match a b:
    case Bignum.Int{False{}, al} Bignum.Int{False{}, bl}:
      Bignum.make(False{}, Bignum.add_abs(al, bl, 0))
    case Bignum.Int{True{}, al} Bignum.Int{True{}, bl}:
      Bignum.make(True{}, Bignum.add_abs(al, bl, 0))
    case Bignum.Int{True{}, +al} Bignum.Int{False{}, +bl}:
      Bignum.add_different(True{}, al, bl, Bignum.cmp_abs(al, bl))
    case Bignum.Int{False{}, +al} Bignum.Int{True{}, +bl}:
      Bignum.add_different(False{}, al, bl, Bignum.cmp_abs(al, bl))

def Bignum.sub_order(a: Bignum.t, b: Bignum.t, order: Cmp) -> Bignum.t:
  match order:
    case GT{}:
      Bignum.add(a, Bignum.negate(b))
    case EQ{}:
      Bignum.zero
    case LT{}:
      Bignum.zero

def Bignum.sub(+a: Bignum.t, +b: Bignum.t) -> Bignum.t:
  Bignum.sub_order(a, b, Bignum.compare(a, b))

def Bignum.mul_limb(xs: List<&2, U32>, +factor: U32, +carry: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Bignum.carry_end(carry, U32.is_zero(carry))
    case Con{+h, t}:
      Con{((h * factor + carry) % 32768 : U32), Bignum.mul_limb(t, factor, ((h * factor + carry) / 32768 : U32))}

def Bignum.mul_abs(xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      Bignum.add_abs(Bignum.mul_limb(ys, h, 0), Con{0, Bignum.mul_abs(t, ys)}, 0)

def Bignum.mul(a: Bignum.t, b: Bignum.t) -> Bignum.t:
  match a b:
    case Bignum.Int{an, al} Bignum.Int{bn, bl}:
      Bignum.make(Bool.xor(an, bn), Bignum.mul_abs(al, bl))

# of_decimal reads five digits per pass: each pass multiplies the limbs by
# 10^5 and adds the chunk in one tail-recursive walk.  A limb is below
# 2^15, so limb * 10^5 + carry stays below 2^32 and every step is U32.
# The limbs never carry a high zero limb, so the result needs no trim.
def Bignum.carry_lo(zero: Bool, +lo: U32, out: List<&2, U32>) -> List<&2, U32>:
  match zero:
    case True{}:
      out
    case False{}:
      Con{lo, out}

def Bignum.carry_out(+carry: U32, out: List<&2, U32>) -> List<&2, U32>:
  Bignum.carry_lo(U32.is_zero((carry / 32768 : U32)), (carry / 32768 : U32), Bignum.carry_lo(U32.is_zero(carry), (carry % 32768 : U32), out))

def Bignum.limbs_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Bignum.limbs_onto(t, Con{h, acc})

def Bignum.muladd_go(xs: List<&2, U32>, +factor: U32, +carry: U32, out: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Bignum.carry_out(carry, out)
    case Con{+h, t}:
      Bignum.muladd_go(t, factor, ((h * factor + carry) / 32768 : U32), Con{((h * factor + carry) % 32768 : U32), out})

def Bignum.muladd(xs: List<&2, U32>, +factor: U32, +chunk: U32) -> List<&2, U32>:
  Bignum.limbs_onto(Bignum.muladd_go(xs, factor, chunk, []), [])

def Bignum.all_digits(xs: String, ok: Bool) -> Bool:
  match xs:
    case SNil{}:
      ok
    case SCon{Chr{+c}, tail}:
      Bignum.all_digits(tail, Bool.and(ok, Bool.and((c >= 48 : U32), (c <= 57 : U32))))

def Bignum.dec_limbs(full: Bool, limbs: List<&2, U32>, +factor: U32, +value: U32) -> List<&2, U32>:
  match full:
    case True{}:
      Bignum.muladd(limbs, factor, value)
    case False{}:
      limbs

def Bignum.dec_value(full: Bool, +value: U32) -> U32:
  match full:
    case True{}:
      0
    case False{}:
      value

def Bignum.dec_factor(full: Bool, +factor: U32) -> U32:
  match full:
    case True{}:
      1
    case False{}:
      factor

def Bignum.dec_count(full: Bool, +count: Nat) -> Nat:
  match full:
    case True{}:
      0n
    case False{}:
      count

# decimal_go runs on checked digits only, so c - 48 never wraps.  The
# fifth digit of a chunk flushes the chunk into the limbs.
def Bignum.decimal_go(xs: String, limbs: List<&2, U32>, +value: U32, +factor: U32, +count: Nat) -> Bignum.t:
  match xs:
    case SNil{}:
      Bignum.Int{False{}, Bignum.muladd(limbs, factor, value)}
    case SCon{Chr{+c}, tail}:
      Bignum.decimal_go(tail, Bignum.dec_limbs(Nat.is_eq(count, 4n), limbs, (factor * 10 : U32), (value * 10 + (c - 48) : U32)), Bignum.dec_value(Nat.is_eq(count, 4n), (value * 10 + (c - 48) : U32)), Bignum.dec_factor(Nat.is_eq(count, 4n), (factor * 10 : U32)), Bignum.dec_count(Nat.is_eq(count, 4n), (count + 1n : Nat)))

def Bignum.of_decimal_valid(valid: Bool, source: String) -> Maybe<&2, Bignum.t>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{Bignum.decimal_go(source, [], 0, 1, 0n)}

def Bignum.of_decimal(source: String) -> Maybe<&2, Bignum.t>:
  match source:
    case SNil{}:
      None{}
    case SCon{+h, +t}:
      Bignum.of_decimal_valid(Bignum.all_digits(SCon{h, t}, True{}), SCon{h, t})

def Bignum.div_ten(xs: List<&2, U32>, +carry: U32, acc: List<&2, U32>) -> Pair2<List<&2, U32>, U32>:
  match xs:
    case Nil{}:
      Pair2{Bignum.trim(acc), carry}
    case Con{+h, t}:
      Bignum.div_ten(t, ((carry * 32768 + h) % 10 : U32), Con{((carry * 32768 + h) / 10 : U32), acc})

def Bignum.show_digit(divided: Pair2<List<&2, U32>, U32>, text: String) -> Pair2<List<&2, U32>, String>:
  match divided:
    case Pair2{q, digit}:
      Pair2{q, SCon{Chr{(48 + digit : U32)}, text}}

@unsafe
def Bignum.show_loop(state: Pair2<List<&2, U32>, String>) -> String:
  match state:
    case Pair2{Nil{}, text}:
      text
    case Pair2{Con{h, t}, text}:
      Bignum.show_loop(Bignum.show_digit(Bignum.div_ten(List.reverse(&2, U32, Con{h, t}), 0, []), text))

def Bignum.to_string(value: Bignum.t) -> String:
  match value:
    case Bignum.Int{negative, Nil{}}:
      "0"
    case Bignum.Int{False{}, Con{h, t}}:
      Bignum.show_loop(Pair2{Con{h, t}, ""})
    case Bignum.Int{True{}, Con{h, t}}:
      String.append("-", Bignum.show_loop(Pair2{Con{h, t}, ""}))

def Bignum.narrow_ok(h: U32, n: Nat, valid: Bool) -> Maybe<&2, Nat>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{(n * 32768n + U32.to_nat(h) : Nat)}

def Bignum.narrow_step(h: U32, tail: Maybe<&2, Nat>, max: Nat) -> Maybe<&2, Nat>:
  match tail:
    case None{}:
      None{}
    case Some{+n}:
      Bignum.narrow_ok(h, n, (n <= max : Nat))

def Bignum.narrow(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      Some{0n}
    case Con{h, t}:
      Bignum.narrow_step(h, Bignum.narrow(t), (4294967295n * 2n + 1n : Nat))

def Bignum.to_nat(value: Bignum.t) -> Maybe<&2, Nat>:
  match value:
    case Bignum.Int{True{}, limbs}:
      None{}
    case Bignum.Int{False{}, limbs}:
      Bignum.narrow(limbs)

def Bignum.i31_check(value: Bignum.t, order: Cmp) -> Maybe<&2, Nat>:
  match order:
    case GT{}:
      None{}
    case EQ{}:
      Bignum.to_nat(value)
    case LT{}:
      Bignum.to_nat(value)

def Bignum.to_i31(+value: Bignum.t) -> Maybe<&2, Nat>:
  Bignum.i31_check(value, Bignum.compare(value, Bignum.from_nat(1073741823n)))

def Level.zero() -> Level.t:
  Bignum.zero

def Level.one() -> Level.t:
  Bignum.one

def Level.succ(value: Level.t) -> Level.t:
  Bignum.add(value, Bignum.one)

def Level.equal(a: Level.t, b: Level.t) -> Bool:
  Bignum.equal(a, b)

def Level.le_order(order: Cmp) -> Bool:
  match order:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Level.le(a: Level.t, b: Level.t) -> Bool:
  Level.le_order(Bignum.compare(a, b))

def Level.max_order(a: Level.t, b: Level.t, order: Cmp) -> Level.t:
  match order:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def Level.max(+a: Level.t, +b: Level.t) -> Level.t:
  Level.max_order(a, b, Bignum.compare(a, b))

def Level.of_int(n: Nat) -> Maybe<&2, Level.t>:
  Some{Bignum.from_nat(n)}

def Level.of_bignum_order(value: Bignum.t, sign: Cmp, bounded: Cmp) -> Maybe<&2, Level.t>:
  match sign:
    case LT{}:
      None{}
    case EQ{}:
      Some{value}
    case GT{}:
      match bounded:
        case GT{}:
          None{}
        case EQ{}:
          Some{value}
        case LT{}:
          Some{value}

def Level.of_bignum(+value: Bignum.t) -> Maybe<&2, Level.t>:
  Level.of_bignum_order(value, Bignum.sign(value), Bignum.compare(value, Bignum.Int{False{}, [32767, 32767, 32767, 32767, 3]}))

def Level.to_string(value: Level.t) -> String:
  Bignum.to_string(value)

def Literal.equal(a: Literal.t, b: Literal.t) -> Bool:
  match a b:
    case Literal.LString{x} Literal.LString{y}:
      String.eq(x, y)
    case Literal.LInt{x} Literal.LInt{y}:
      Bignum.equal(x, y)
    case Literal.LInt{x} Literal.LString{y}:
      False{}
    case Literal.LString{x} Literal.LInt{y}:
      False{}

# Shared views and usage operations
def Data.choose(-A: Data, condition: Bool, yes: A, no: A) -> A:
  match condition:
    case True{}:
      yes
    case False{}:
      no

def Text.nat(n: Nat) -> String:
  Bignum.to_string(Bignum.from_nat(n))

def Quantity.mul(a: Quantity.t, b: Quantity.t) -> Quantity.t:
  match a b:
    case Quantity.Zero{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.One{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.Many{}:
      Quantity.Zero{}
    case Quantity.One{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.One{} Quantity.One{}:
      Quantity.One{}
    case Quantity.One{} Quantity.Many{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Many{} Quantity.One{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Many{}:
      Quantity.Many{}

def Quantity.equal(a: Quantity.t, b: Quantity.t) -> Bool:
  match a b:
    case Quantity.Zero{} Quantity.Zero{}:
      True{}
    case Quantity.Zero{} Quantity.One{}:
      False{}
    case Quantity.Zero{} Quantity.Many{}:
      False{}
    case Quantity.One{} Quantity.Zero{}:
      False{}
    case Quantity.One{} Quantity.One{}:
      True{}
    case Quantity.One{} Quantity.Many{}:
      False{}
    case Quantity.Many{} Quantity.Zero{}:
      False{}
    case Quantity.Many{} Quantity.One{}:
      False{}
    case Quantity.Many{} Quantity.Many{}:
      True{}

def Quantity.add(a: Quantity.t, b: Quantity.t) -> Quantity.t:
  match a b:
    case Quantity.Zero{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.One{}:
      Quantity.One{}
    case Quantity.Zero{} Quantity.Many{}:
      Quantity.Many{}
    case Quantity.One{} Quantity.Zero{}:
      Quantity.One{}
    case Quantity.One{} Quantity.One{}:
      Quantity.Many{}
    case Quantity.One{} Quantity.Many{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Zero{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.One{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Many{}:
      Quantity.Many{}

def Quantity.minimum(a: Quantity.t, b: Quantity.t) -> Quantity.t:
  match a b:
    case Quantity.Zero{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.One{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.Many{}:
      Quantity.Zero{}
    case Quantity.One{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.One{} Quantity.One{}:
      Quantity.One{}
    case Quantity.One{} Quantity.Many{}:
      Quantity.One{}
    case Quantity.Many{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Many{} Quantity.One{}:
      Quantity.One{}
    case Quantity.Many{} Quantity.Many{}:
      Quantity.Many{}

def Quantity.maximum(a: Quantity.t, b: Quantity.t) -> Quantity.t:
  match a b:
    case Quantity.Zero{} Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.Zero{} Quantity.One{}:
      Quantity.One{}
    case Quantity.Zero{} Quantity.Many{}:
      Quantity.Many{}
    case Quantity.One{} Quantity.Zero{}:
      Quantity.One{}
    case Quantity.One{} Quantity.One{}:
      Quantity.One{}
    case Quantity.One{} Quantity.Many{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Zero{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.One{}:
      Quantity.Many{}
    case Quantity.Many{} Quantity.Many{}:
      Quantity.Many{}

def Quantity.to_string(v: Quantity.t) -> String:
  match v:
    case Quantity.Zero{}:
      "0"
    case Quantity.One{}:
      "1"
    case Quantity.Many{}:
      "w"

def Quantity.runtime(v: Quantity.t) -> Quantity.t:
  match v:
    case Quantity.Zero{}:
      Quantity.Zero{}
    case Quantity.One{}:
      Quantity.One{}
    case Quantity.Many{}:
      Quantity.One{}

def Quantity.rank(v: Quantity.t) -> Nat:
  match v:
    case Quantity.Zero{}:
      0n
    case Quantity.One{}:
      1n
    case Quantity.Many{}:
      2n

def Shape.payload(-A: Data, v: Shape.t<A>) -> List<&2, A>:
  match v:
    case Shape.SPi{x0, x1, x2}:
      [x2]
    case Shape.SColl{x0}:
      []
    case Shape.SPar{x0, x1}:
      [x0, x1]
    case Shape.SMu{x0, x1}:
      x1
    case Shape.SNu{x0, x1}:
      x1

def Shape.point_dom(-A: Data, v: Shape.t<A>) -> Maybe<&2, A>:
  match v:
    case Shape.SPi{x0, x1, x2}:
      Some{x2}
    case Shape.SColl{x0}:
      None{}
    case Shape.SPar{x0, x1}:
      None{}
    case Shape.SMu{x0, x1}:
      None{}
    case Shape.SNu{x0, x1}:
      None{}

def Shape.family(-A: Data, v: Shape.t<A>) -> Maybe<&2, String>:
  match v:
    case Shape.SPi{x0, x1, x2}:
      None{}
    case Shape.SColl{x0}:
      None{}
    case Shape.SPar{x0, x1}:
      None{}
    case Shape.SMu{x0, x1}:
      Some{x0}
    case Shape.SNu{x0, x1}:
      Some{x0}

def Term.as_apt(v: Term.addr) -> Maybe<&2, Pair2<Quantity.t, Term.t>>:
  match v:
    case Term.APt{x0, x1}:
      Some{Pair2{x0, x1}}
    case Term.ALeg{x0}:
      None{}
    case Term.ACtor{x0}:
      None{}

def Term.as_aleg(v: Term.addr) -> Maybe<&2, Nat>:
  match v:
    case Term.APt{x0, x1}:
      None{}
    case Term.ALeg{x0}:
      Some{x0}
    case Term.ACtor{x0}:
      None{}

def Term.as_actor(v: Term.addr) -> Maybe<&2, String>:
  match v:
    case Term.APt{x0, x1}:
      None{}
    case Term.ALeg{x0}:
      None{}
    case Term.ACtor{x0}:
      Some{x0}

def Value.as_univ(v: Value.t) -> Maybe<&2, Level.t>:
  match v:
    case Value.VUniv{x0}:
      Some{x0}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_lan(v: Value.t) -> Maybe<&2, Triple3<Shape.t<Value.t>, Value.closure, Maybe<&2, Level.t>>>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      Some{Triple3{x0, x1, x2}}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_ran(v: Value.t) -> Maybe<&2, Triple3<Shape.t<Value.t>, Value.closure, Maybe<&2, Level.t>>>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      Some{Triple3{x0, x1, x2}}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_in(v: Value.t) -> Maybe<&2, Triple3<Shape.t<Value.t>, Value.vaddr, List<&2, Value.t>>>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      Some{Triple3{x0, x1, x2}}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_sec(v: Value.t) -> Maybe<&2, Pair2<Shape.t<Value.t>, List<&2, Value.vleg>>>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      Some{Pair2{x0, x1}}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_lit(v: Value.t) -> Maybe<&2, Literal.t>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      Some{x0}
    case Value.VNeutral{x0, x1}:
      None{}

def Value.as_neutral(v: Value.t) -> Maybe<&2, Pair2<Value.head, List<&2, Value.spine>>>:
  match v:
    case Value.VUniv{x0}:
      None{}
    case Value.VLan{x0, x1, x2}:
      None{}
    case Value.VRan{x0, x1, x2}:
      None{}
    case Value.VIn{x0, x1, x2}:
      None{}
    case Value.VSec{x0, x1}:
      None{}
    case Value.VLit{x0}:
      None{}
    case Value.VNeutral{x0, x1}:
      Some{Pair2{x0, x1}}

def Value.as_pt(v: Value.vaddr) -> Maybe<&2, Pair2<Quantity.t, Value.t>>:
  match v:
    case Value.VAPt{x0, x1}:
      Some{Pair2{x0, x1}}
    case Value.VALeg{x0}:
      None{}
    case Value.VACtor{x0}:
      None{}

def Value.as_leg(v: Value.vaddr) -> Maybe<&2, Nat>:
  match v:
    case Value.VAPt{x0, x1}:
      None{}
    case Value.VALeg{x0}:
      Some{x0}
    case Value.VACtor{x0}:
      None{}

def Value.as_ctor(v: Value.vaddr) -> Maybe<&2, String>:
  match v:
    case Value.VAPt{x0, x1}:
      None{}
    case Value.VALeg{x0}:
      None{}
    case Value.VACtor{x0}:
      Some{x0}

def Value.var(level: Nat) -> Value.t:
  Value.VNeutral{Value.HLocal{level}, []}

def Value.close(env: List<&2, Value.t>, body: Term.t) -> Value.closure:
  Value.Closure{env, body}

def Value.head_equal(a: Value.head, b: Value.head) -> Bool:
  match a b:
    case Value.HLocal{i} Value.HLocal{j}:
      Nat.is_eq(i, j)
    case Value.HGlobal{m} Value.HGlobal{n}:
      String.eq(m, n)
    case Value.HLocal{i} Value.HGlobal{n}:
      False{}
    case Value.HGlobal{m} Value.HLocal{j}:
      False{}

def Term.formers() -> List<&2, String>:
  ["Lan", "Ran"]

def Term.schema() -> List<&2, String>:
  ["In", "Elim", "Sec", "Out"]

def Shape.declared() -> List<&2, String>:
  ["SPi", "SColl", "SPar", "SMu", "SNu"]

# The context is affine: only the selected callback receives it.
def Shape.fold(-A: Data, -Ctx: Type, -Out: Type, shape: Shape.t<A>, context: Ctx,
  point: Quantity.t -> String -> A -> Ctx -> Out,
  collection: Nat -> Ctx -> Out,
  parallel: A -> A -> Ctx -> Out,
  inductive: String -> List<&2, A> -> Ctx -> Out,
  coinductive: String -> List<&2, A> -> Ctx -> Out) -> Out:
  match shape:
    case Shape.SPi{q, name, domain}: point(q, name, domain, context)
    case Shape.SColl{width}: collection(width, context)
    case Shape.SPar{left, right}: parallel(left, right, context)
    case Shape.SMu{name, indices}: inductive(name, indices, context)
    case Shape.SNu{name, indices}: coinductive(name, indices, context)

def Shape.same_fold(-A: Data, -Ctx: Type, -Out: Type, a: Shape.t<A>, b: Shape.t<A>, context: Ctx,
  point: Quantity.t -> String -> A -> Quantity.t -> String -> A -> Ctx -> Out,
  collection: Nat -> Nat -> Ctx -> Out,
  parallel: A -> A -> A -> A -> Ctx -> Out,
  inductive: String -> List<&2, A> -> String -> List<&2, A> -> Ctx -> Out,
  coinductive: String -> List<&2, A> -> String -> List<&2, A> -> Ctx -> Out,
  different: Ctx -> Out) -> Out:
  match a b:
    case Shape.SPi{q1, n1, d1} Shape.SPi{q2, n2, d2}: point(q1, n1, d1, q2, n2, d2, context)
    case Shape.SColl{n1} Shape.SColl{n2}: collection(n1, n2, context)
    case Shape.SPar{a, b} Shape.SPar{c, d}: parallel(a, b, c, d, context)
    case Shape.SMu{n1, ix1} Shape.SMu{n2, ix2}: inductive(n1, ix1, n2, ix2, context)
    case Shape.SNu{n1, ix1} Shape.SNu{n2, ix2}: coinductive(n1, ix1, n2, ix2, context)
    case _ _: different(context)

def Shape.make_point(-A: Data, q: Quantity.t, name: String, domain: A) -> Shape.t<A>:
  Shape.SPi{q, name, domain}

def Shape.make_collection(-A: Data, width: Nat) -> Shape.t<A>:
  Shape.SColl{width}

def Shape.make_parallel(-A: Data, left: A, right: A) -> Shape.t<A>:
  Shape.SPar{left, right}

def Shape.make_inductive(-A: Data, name: String, indices: List<&2, A>) -> Shape.t<A>:
  Shape.SMu{name, indices}

def Shape.make_coinductive(-A: Data, name: String, indices: List<&2, A>) -> Shape.t<A>:
  Shape.SNu{name, indices}

def Shape.collection(-A: Data, shape: Shape.t<A>) -> Maybe<&2, Nat>:
  Shape.fold(A, Unit, Maybe<&2, Nat>, shape, Unit{},
    q => name => domain => unit => None{}, width => unit => Some{width},
    a => b => unit => None{}, name => indices => unit => None{}, name => indices => unit => None{})

def Shape.inductive(-A: Data, shape: Shape.t<A>) -> Maybe<&2, Pair2<String, List<&2, A>>>:
  Shape.fold(A, Unit, Maybe<&2, Pair2<String, List<&2, A>>>, shape, Unit{},
    q => name => domain => unit => None{}, width => unit => None{},
    a => b => unit => None{}, name => indices => unit => Some{Pair2{name, indices}}, name => indices => unit => None{})

def Shape.name(-A: Data, shape: Shape.t<A>) -> String:
  Shape.fold(A, Unit, String, shape, Unit{},
    q => name => domain => unit => "SPi", width => unit => "SColl",
    a => b => unit => "SPar", name => indices => unit => "SMu", name => indices => unit => "SNu")

def Shape.parallel_word() -> String:
  "SPar arrives at M1"

def Shape.inductive_word() -> String:
  "SMu arrives at M1"

def Shape.coinductive_word() -> String:
  "SNu arrives at M2"

def Error.termination_msg(name: String) -> String:
  String.concat(["recursive definition ", name, " failed the structural termination guard"])

def Error.message(v: Error.t) -> String:
  match v:
    case Error.Not_yet{x0}:
      x0
    case Error.Parse{x0, x1, x2}:
      x0
    case Error.Carry{x0}:
      x0
    case Error.Unbound{x0}:
      x0
    case Error.Mismatch{x0}:
      x0
    case Error.Universe{x0}:
      x0
    case Error.Quantity{x0}:
      x0
    case Error.Wrong_leg{x0}:
      x0
    case Error.Missing_branch{x0}:
      x0
    case Error.Overflow{x0}:
      x0
    case Error.Cannot_infer{x0}:
      x0
    case Error.Budget_exhausted{x0}:
      x0
    case Error.Index_not_zero{x0}:
      x0
    case Error.Index_above_universe{x0}:
      x0
    case Error.Termination{x0}:
      Error.termination_msg(x0)

def Error.to_string(v: Error.t) -> String:
  match v:
    case Error.Not_yet{x0}:
      String.append("not yet: ", x0)
    case Error.Parse{x0, x1, x2}:
      String.concat(["line ", Text.nat(x1), ", column ", Text.nat(x2), ": ", x0])
    case Error.Carry{x0}:
      String.append("carry: ", x0)
    case Error.Unbound{x0}:
      String.append("unbound: ", x0)
    case Error.Mismatch{x0}:
      String.append("mismatch: ", x0)
    case Error.Universe{x0}:
      String.append("universe: ", x0)
    case Error.Quantity{x0}:
      String.append("quantity: ", x0)
    case Error.Wrong_leg{x0}:
      String.append("wrong leg: ", x0)
    case Error.Missing_branch{x0}:
      String.append("missing branch: ", x0)
    case Error.Overflow{x0}:
      String.append("overflow: ", x0)
    case Error.Cannot_infer{x0}:
      String.append("cannot infer: ", x0)
    case Error.Budget_exhausted{x0}:
      String.append("budget: ", x0)
    case Error.Index_not_zero{x0}:
      String.append("index not zero: ", x0)
    case Error.Index_above_universe{x0}:
      String.append("index above universe: ", x0)
    case Error.Termination{x0}:
      String.append("termination: ", Error.termination_msg(x0))

# Usage interval operations
# Usage maps retain one entry per level; lookup is independent of order.
def Quantity.Map() -> Data:
  List<&2, Pair2<Nat, Quantity.interval>>

type Quantity.Join is Data:
  Quantity.Add{}
  Quantity.Min{}
  Quantity.Max{}
  Quantity.Left{}

def Quantity.join(kind: Quantity.Join, a: Quantity.t, b: Quantity.t) -> Quantity.t:
  match kind:
    case Quantity.Add{}:
      Quantity.add(a, b)
    case Quantity.Min{}:
      Quantity.minimum(a, b)
    case Quantity.Max{}:
      Quantity.maximum(a, b)
    case Quantity.Left{}:
      a

def Quantity.zero_interval() -> Quantity.interval:
  Pair2{Quantity.Zero{}, Quantity.Zero{}}

def Quantity.empty() -> Quantity.usage:
  Quantity.Usage{Some{[]}, []}

def Quantity.unreachable() -> Quantity.usage:
  Quantity.Usage{None{}, []}

def Quantity.get_interval(+level: Nat, uses: Quantity.Map) -> Quantity.interval:
  match uses:
    case Nil{}:
      Quantity.zero_interval
    case Con{Pair2{k, value}, rest}:
      Data.choose(Quantity.interval, Nat.is_eq(level, k), value, Quantity.get_interval(level, rest))

def Quantity.occurrence(+level: Nat, +q: Quantity.t) -> Quantity.usage:
  Quantity.Usage{Some{[Pair2{level, Pair2{q, q}}]}, [Pair2{level, Pair2{q, q}}]}

def Quantity.remove_cons(+k: Nat, value: Quantity.interval, +rest: Quantity.Map, level: Nat) -> Quantity.Map:
  Data.choose(Quantity.Map, Nat.is_eq(k, level), rest, Con{Pair2{k, value}, rest})

def Quantity.map_remove(+level: Nat, uses: Quantity.Map) -> Quantity.Map:
  match uses:
    case Nil{}:
      []
    case Con{Pair2{k, v}, rest}:
      Quantity.remove_cons(k, v, Quantity.map_remove(level, rest), level)

def Quantity.join_pair(lo: Quantity.Join, hi: Quantity.Join, a: Quantity.interval, b: Quantity.interval) -> Quantity.interval:
  match a b:
    case Pair2{x, y} Pair2{u, v}:
      Pair2{Quantity.join(lo, x, u), Quantity.join(hi, y, v)}

def Quantity.right_only(+lo: Quantity.Join, +hi: Quantity.Join, b: Quantity.Map) -> Quantity.Map:
  match b:
    case Nil{}:
      []
    case Con{Pair2{k, v}, rest}:
      Con{Pair2{k, Quantity.join_pair(lo, hi, Quantity.zero_interval, v)}, Quantity.right_only(lo, hi, rest)}

def Quantity.combine(+lo: Quantity.Join, +hi: Quantity.Join, a: Quantity.Map, +b: Quantity.Map) -> Quantity.Map:
  match a:
    case Nil{}:
      Quantity.right_only(lo, hi, b)
    case Con{Pair2{+k, value}, rest}:
      Con{Pair2{k, Quantity.join_pair(lo, hi, value, Quantity.get_interval(k, b))},
        Quantity.combine(lo, hi, rest, Quantity.map_remove(k, b))}

def Quantity.sequence_paths(a: Maybe<&2, Quantity.Map>, b: Maybe<&2, Quantity.Map>) -> Maybe<&2, Quantity.Map>:
  match a b:
    case Some{x} Some{y}:
      Some{Quantity.combine(Quantity.Add{}, Quantity.Add{}, x, y)}
    case None{} Some{y}:
      None{}
    case Some{x} None{}:
      None{}
    case None{} None{}:
      None{}

def Quantity.sequence(a: Quantity.usage, b: Quantity.usage) -> Quantity.usage:
  match a b:
    case Quantity.Usage{ap, ar} Quantity.Usage{bp, br}:
      Quantity.Usage{Quantity.sequence_paths(ap, bp), Quantity.combine(Quantity.Add{}, Quantity.Add{}, ar, br)}

def Quantity.alternative_paths(a: Maybe<&2, Quantity.Map>, b: Maybe<&2, Quantity.Map>) -> Maybe<&2, Quantity.Map>:
  match a b:
    case Some{x} Some{y}:
      Some{Quantity.combine(Quantity.Min{}, Quantity.Max{}, x, y)}
    case None{} Some{y}:
      Some{y}
    case Some{x} None{}:
      Some{x}
    case None{} None{}:
      None{}

def Quantity.alternative(a: Quantity.usage, b: Quantity.usage) -> Quantity.usage:
  match a b:
    case Quantity.Usage{ap, ar} Quantity.Usage{bp, br}:
      Quantity.Usage{Quantity.alternative_paths(ap, bp), Quantity.combine(Quantity.Max{}, Quantity.Max{}, ar, br)}

def Quantity.scale_pair(range: Quantity.interval, value: Quantity.interval) -> Quantity.interval:
  match range value:
    case Pair2{lo, hi} Pair2{a, b}:
      Pair2{Quantity.mul(lo, a), Quantity.mul(hi, b)}

def Quantity.scale_map(+range: Quantity.interval, uses: Quantity.Map) -> Quantity.Map:
  match uses:
    case Nil{}:
      []
    case Con{Pair2{k, v}, rest}:
      Con{Pair2{k, Quantity.scale_pair(range, v)}, Quantity.scale_map(range, rest)}

def Quantity.scale_paths(range: Quantity.interval, paths: Maybe<&2, Quantity.Map>) -> Maybe<&2, Quantity.Map>:
  match paths:
    case None{}:
      None{}
    case Some{values}:
      Some{Quantity.scale_map(range, values)}

def Quantity.scale_range(+range: Quantity.interval, uses: Quantity.usage) -> Quantity.usage:
  match uses:
    case Quantity.Usage{paths, reads}:
      Quantity.Usage{Quantity.scale_paths(range, paths), Quantity.scale_map(range, reads)}

def Quantity.scale(q: Quantity.t, uses: Quantity.usage) -> Quantity.usage:
  match q:
    case Quantity.Zero{}:
      Quantity.empty
    case Quantity.One{}:
      Quantity.scale_range(Pair2{Quantity.One{}, Quantity.One{}}, uses)
    case Quantity.Many{}:
      Quantity.scale_range(Pair2{Quantity.Many{}, Quantity.Many{}}, uses)

def Quantity.get_paths(level: Nat, paths: Maybe<&2, Quantity.Map>, reads: Quantity.interval) -> Quantity.interval:
  match paths:
    case Some{values}:
      Quantity.get_interval(level, values)
    case None{}:
      match reads:
        case Pair2{lo, hi}:
          Pair2{Quantity.One{}, Quantity.maximum(Quantity.One{}, hi)}

def Quantity.get(+level: Nat, uses: Quantity.usage) -> Quantity.interval:
  match uses:
    case Quantity.Usage{paths, reads}:
      Quantity.get_paths(level, paths, Quantity.get_interval(level, reads))

def Quantity.remove_paths(level: Nat, paths: Maybe<&2, Quantity.Map>) -> Maybe<&2, Quantity.Map>:
  match paths:
    case None{}:
      None{}
    case Some{values}:
      Some{Quantity.map_remove(level, values)}

def Quantity.remove(+level: Nat, uses: Quantity.usage) -> Quantity.usage:
  match uses:
    case Quantity.Usage{paths, reads}:
      Quantity.Usage{Quantity.remove_paths(level, paths), Quantity.map_remove(level, reads)}

def Quantity.once_pair(value: Quantity.interval) -> Bool:
  match value:
    case Pair2{lo, hi}:
      Bool.and(Quantity.equal(lo, Quantity.One{}), Quantity.equal(hi, Quantity.One{}))

def Quantity.exactly_once(level: Nat, uses: Quantity.usage) -> Bool:
  Quantity.once_pair(Quantity.get(level, uses))

def Quantity.used_pair(value: Quantity.interval) -> Bool:
  match value:
    case Pair2{lo, hi}:
      Bool.not(Quantity.equal(hi, Quantity.Zero{}))

def Quantity.used(level: Nat, uses: Quantity.usage) -> Bool:
  match uses:
    case Quantity.Usage{paths, reads}:
      Quantity.used_pair(Quantity.get_interval(level, reads))

def Quantity.at_most_pair(value: Quantity.interval) -> Bool:
  match value:
    case Pair2{lo, hi}:
      Bool.not(Quantity.equal(hi, Quantity.Many{}))

def Quantity.at_most_once(level: Nat, uses: Quantity.usage) -> Bool:
  Quantity.at_most_pair(Quantity.get(level, uses))

def Quantity.capture_paths(paths: Maybe<&2, Quantity.Map>, reads: Quantity.Map) -> Quantity.Map:
  match paths:
    case None{}:
      reads
    case Some{values}:
      Quantity.combine(Quantity.Left{}, Quantity.Max{}, values, reads)

def Quantity.captures(uses: Quantity.usage) -> Quantity.usage:
  match uses:
    case Quantity.Usage{paths, +reads}:
      Quantity.Usage{Some{Quantity.capture_paths(paths, reads)}, reads}

# Immutable global environment
def Global.lookup_if(-A: Data, equal: Bool, value: A, later: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:
  match equal:
    case True{}:
      Some{value}
    case False{}:
      later(Unit{})

def Global.lookup(-A: Data, +name: String, rows: List<&2, Pair2<String, A>>) -> Maybe<&2, A>:
  match rows:
    case Nil{}:
      None{}
    case Con{Pair2{key, value}, tail}:
      Global.lookup_if(A, String.eq(name, key), value, unused => Global.lookup(A, name, tail))

def Global.put_order(-A: Data, order: Cmp, name: String, value: A, key: String, old: A, tail: List<&2, Pair2<String, A>>, updated: Unit -> List<&2, Pair2<String, A>>) -> List<&2, Pair2<String, A>>:
  match order:
    case LT{}:
      Con{Pair2{name, value}, Con{Pair2{key, old}, tail}}
    case EQ{}:
      Con{Pair2{name, value}, tail}
    case GT{}:
      Con{Pair2{key, old}, updated(Unit{})}

def Global.put(-A: Data, +name: String, +value: A, rows: List<&2, Pair2<String, A>>) -> List<&2, Pair2<String, A>>:
  match rows:
    case Nil{}:
      [Pair2{name, value}]
    case Con{Pair2{+key, old}, +tail}:
      Global.put_order(A, String.order(name, key), name, value, key, old, tail, unused => Global.put(A, name, value, tail))

def Global.height(-A: Data, tree: Global.map<A>) -> Nat:
  match tree:
    case Global.Leaf{}: 0n
    case Global.Node{height, key, value, left, right}: height

def Global.node(-A: Data, key: String, value: A, +left: Global.map<A>, +right: Global.map<A>) -> Global.map<A>:
  Global.Node{(1n + Nat.max(Global.height(A, left), Global.height(A, right)) : Nat), key, value, left, right}

def Global.rotate_left(-A: Data, key: String, value: A, left: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match right:
    case Global.Leaf{}: Global.node(A, key, value, left, Global.Leaf{})
    case Global.Node{height, pivot, item, middle, last}:
      Global.node(A, pivot, item, Global.node(A, key, value, left, middle), last)

def Global.rotate_right(-A: Data, key: String, value: A, left: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match left:
    case Global.Leaf{}: Global.node(A, key, value, Global.Leaf{}, right)
    case Global.Node{height, pivot, item, first, middle}:
      Global.node(A, pivot, item, first, Global.node(A, key, value, middle, right))

def Global.balance_left_pick(-A: Data, single: Bool, key: String, value: A, pivot: String, item: A, first: Global.map<A>, middle: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match single:
    case True{}:
      Global.node(A, pivot, item, first, Global.node(A, key, value, middle, right))
    case False{}:
      Global.rotate_right(A, key, value, Global.rotate_left(A, pivot, item, first, middle), right)

def Global.balance_left(-A: Data, key: String, value: A, left: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match left:
    case Global.Leaf{}: Global.node(A, key, value, Global.Leaf{}, right)
    case Global.Node{height, pivot, item, +first, +middle}:
      Global.balance_left_pick(A, Nat.is_ge(Global.height(A, first), Global.height(A, middle)), key, value, pivot, item, first, middle, right)

def Global.balance_right_pick(-A: Data, single: Bool, key: String, value: A, pivot: String, item: A, left: Global.map<A>, middle: Global.map<A>, last: Global.map<A>) -> Global.map<A>:
  match single:
    case True{}:
      Global.node(A, pivot, item, Global.node(A, key, value, left, middle), last)
    case False{}:
      Global.rotate_left(A, key, value, left, Global.rotate_right(A, pivot, item, middle, last))

def Global.balance_right(-A: Data, key: String, value: A, left: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match right:
    case Global.Leaf{}: Global.node(A, key, value, left, Global.Leaf{})
    case Global.Node{height, pivot, item, +middle, +last}:
      Global.balance_right_pick(A, Nat.is_ge(Global.height(A, last), Global.height(A, middle)), key, value, pivot, item, left, middle, last)

def Global.balance_pick(-A: Data, heavy_left: Bool, heavy_right: Bool, key: String, value: A, left: Global.map<A>, right: Global.map<A>) -> Global.map<A>:
  match heavy_left heavy_right:
    case True{} other: Global.balance_left(A, key, value, left, right)
    case False{} True{}: Global.balance_right(A, key, value, left, right)
    case False{} False{}: Global.node(A, key, value, left, right)

def Global.balance(-A: Data, key: String, value: A, +left: Global.map<A>, +right: Global.map<A>) -> Global.map<A>:
  +lh = Global.height(A, left)
  +rh = Global.height(A, right)
  Global.balance_pick(A, Nat.is_gt(lh, (rh + 1n : Nat)), Nat.is_gt(rh, (lh + 1n : Nat)), key, value, left, right)

def Global.map_put_order(-A: Data, order: Cmp, name: String, value: A, key: String, old: A, left: Global.map<A>, right: Global.map<A>, put_left: Unit -> Global.map<A>, put_right: Unit -> Global.map<A>) -> Global.map<A>:
  match order:
    case LT{}: Global.balance(A, key, old, put_left(Unit{}), right)
    case EQ{}: Global.node(A, name, value, left, right)
    case GT{}: Global.balance(A, key, old, left, put_right(Unit{}))

def Global.map_put(-A: Data, +name: String, +value: A, tree: Global.map<A>) -> Global.map<A>:
  match tree:
    case Global.Leaf{}: Global.Node{1n, name, value, Global.Leaf{}, Global.Leaf{}}
    case Global.Node{height, +key, old, +left, +right}:
      Global.map_put_order(A, String.order(name, key), name, value, key, old, left, right,
        unused => Global.map_put(A, name, value, left), unused => Global.map_put(A, name, value, right))

def Global.map_lookup_order(-A: Data, order: Cmp, value: A, left: Unit -> Maybe<&2, A>, right: Unit -> Maybe<&2, A>) -> Maybe<&2, A>:
  match order:
    case LT{}: left(Unit{})
    case EQ{}: Some{value}
    case GT{}: right(Unit{})

def Global.map_lookup(-A: Data, +name: String, tree: Global.map<A>) -> Maybe<&2, A>:
  match tree:
    case Global.Leaf{}: None{}
    case Global.Node{height, key, value, left, right}:
      Global.map_lookup_order(A, String.order(name, key), value,
        unused => Global.map_lookup(A, name, left), unused => Global.map_lookup(A, name, right))

def Global.map_rows(-A: Data, tree: Global.map<A>, tail: List<&2, Pair2<String, A>>) -> List<&2, Pair2<String, A>>:
  match tree:
    case Global.Leaf{}: tail
    case Global.Node{height, key, value, left, right}:
      Global.map_rows(A, left, Con{Pair2{key, value}, Global.map_rows(A, right, tail)})

def Global.map_from_rows(-A: Data, rows: List<&2, Pair2<String, A>>) -> Global.map<A>:
  match rows:
    case Nil{}: Global.Leaf{}
    case Con{Pair2{name, value}, tail}:
      Global.map_put(A, name, value, Global.map_from_rows(A, tail))

def Global.table_from_rows(-A: Data, +rows: List<&2, Pair2<String, A>>) -> Global.table<A>:
  Global.Table{Global.map_from_rows(A, rows), Some{rows}}

def Global.table_put_original(-A: Data, original: Maybe<&2, List<&2, Pair2<String, A>>>, name: String, value: A, tree: Global.map<A>) -> Global.table<A>:
  match original:
    case None{}: Global.Table{Global.map_put(A, name, value, tree), None{}}
    case Some{rows}: Global.table_from_rows(A, Global.put(A, name, value, rows))

def Global.table_put(-A: Data, name: String, value: A, table: Global.table<A>) -> Global.table<A>:
  match table:
    case Global.Table{tree, original}: Global.table_put_original(A, original, name, value, tree)

def Global.table_lookup(-A: Data, name: String, table: Global.table<A>) -> Maybe<&2, A>:
  match table:
    case Global.Table{tree, original}: Global.map_lookup(A, name, tree)

def Global.table_rows_original(-A: Data, original: Maybe<&2, List<&2, Pair2<String, A>>>, tree: Global.map<A>) -> List<&2, Pair2<String, A>>:
  match original:
    case None{}: Global.map_rows(A, tree, Nil{})
    case Some{rows}: rows

def Global.table_rows(-A: Data, table: Global.table<A>) -> List<&2, Pair2<String, A>>:
  match table:
    case Global.Table{tree, original}: Global.table_rows_original(A, original, tree)

def Global.empty() -> Global.t:
  Global.Globals{Global.Table{Global.Leaf{}, None{}}, Global.Table{Global.Leaf{}, None{}}}

def Global.from_rows(entries: List<&2, Pair2<String, Global.entry>>, families: List<&2, Pair2<String, Positivity.family>>) -> Global.t:
  Global.Globals{Global.table_from_rows(Global.entry, entries), Global.table_from_rows(Positivity.family, families)}

def Global.with_entries(entries: List<&2, Pair2<String, Global.entry>>, globals: Global.t) -> Global.t:
  match globals:
    case Global.Globals{old, families}: Global.Globals{Global.table_from_rows(Global.entry, entries), families}

def Global.add(name: String, entry: Global.entry, globals: Global.t) -> Global.t:
  match globals:
    case Global.Globals{entries, families}:
      Global.Globals{Global.table_put(Global.entry, name, entry, entries), families}

def Global.find(name: String, globals: Global.t) -> Maybe<&2, Global.entry>:
  match globals:
    case Global.Globals{entries, families}:
      Global.table_lookup(Global.entry, name, entries)

def Global.entries(globals: Global.t) -> List<&2, Pair2<String, Global.entry>>:
  match globals:
    case Global.Globals{entries, families}:
      Global.table_rows(Global.entry, entries)

def Global.families(globals: Global.t) -> List<&2, Pair2<String, Positivity.family>>:
  match globals:
    case Global.Globals{entries, families}: Global.table_rows(Positivity.family, families)

def Global.add_family(name: String, family: Positivity.family, globals: Global.t) -> Global.t:
  match globals:
    case Global.Globals{entries, families}:
      Global.Globals{entries, Global.table_put(Positivity.family, name, family, families)}

def Global.find_family(name: String, globals: Global.t) -> Maybe<&2, Positivity.family>:
  match globals:
    case Global.Globals{entries, families}:
      Global.table_lookup(Positivity.family, name, families)

def Global.entry_ty(entry: Global.entry) -> Term.t:
  match entry:
    case Global.Def{Global.DefEntry{ty, body, reducible, rec_arg, partial}}:
      ty
    case Global.Axiom{Global.AxiomEntry{ty}}:
      ty
    case Global.Prim{Global.PrimEntry{ty, prim}}:
      ty

def Global.def_of(entry: Global.entry) -> Maybe<&2, Global.def_entry>:
  match entry:
    case Global.Def{value}:
      Some{value}
    case Global.Axiom{value}:
      None{}
    case Global.Prim{value}:
      None{}

def Global.axiom_of(entry: Global.entry) -> Maybe<&2, Global.axiom_entry>:
  match entry:
    case Global.Def{value}:
      None{}
    case Global.Axiom{value}:
      Some{value}
    case Global.Prim{value}:
      None{}

def Global.prim_of(entry: Global.entry) -> Maybe<&2, Global.prim_entry>:
  match entry:
    case Global.Def{value}:
      None{}
    case Global.Axiom{value}:
      None{}
    case Global.Prim{value}:
      Some{value}

def Global.maybe_def(entry: Maybe<&2, Global.entry>) -> Maybe<&2, Global.def_entry>:
  match entry:
    case None{}:
      None{}
    case Some{value}:
      Global.def_of(value)

def Global.maybe_axiom(entry: Maybe<&2, Global.entry>) -> Maybe<&2, Global.axiom_entry>:
  match entry:
    case None{}:
      None{}
    case Some{value}:
      Global.axiom_of(value)

def Global.maybe_prim(entry: Maybe<&2, Global.entry>) -> Maybe<&2, Global.prim_entry>:
  match entry:
    case None{}:
      None{}
    case Some{value}:
      Global.prim_of(value)

def Global.find_def(name: String, globals: Global.t) -> Maybe<&2, Global.def_entry>:
  Global.maybe_def(Global.find(name, globals))

def Global.find_axiom(name: String, globals: Global.t) -> Maybe<&2, Global.axiom_entry>:
  Global.maybe_axiom(Global.find(name, globals))

def Global.find_prim(name: String, globals: Global.t) -> Maybe<&2, Global.prim_entry>:
  Global.maybe_prim(Global.find(name, globals))

def Shape.point(-A: Data, s: Shape.t<A>) -> Maybe<&2, Triple3<Quantity.t, String, A>>:
  match s:
    case Shape.SPi{q, name, dom}:
      Some{Triple3{q, name, dom}}
    case Shape.SColl{k}:
      None{}
    case Shape.SPar{a, b}:
      None{}
    case Shape.SMu{name, args}:
      None{}
    case Shape.SNu{name, args}:
      None{}

def Shape.replaced(-B: Data, shape: Shape.t<B>, valid: Bool) -> Result<&2, &2, Error.t, Shape.t<B>>:
  match valid:
    case True{}:
      Done{shape}
    case False{}:
      Fail{Error.Carry{"shape payload arity mismatch"}}

def Shape.replace_point(-B: Data, q: Quantity.t, name: String, items: List<&2, B>) -> Result<&2, &2, Error.t, Shape.t<B>>:
  match items:
    case Nil{}:
      Fail{Error.Carry{"shape payload arity mismatch"}}
    case Con{x, Nil{}}:
      Done{Shape.SPi{q, name, x}}
    case Con{x, Con{y, rest}}:
      Fail{Error.Carry{"shape payload arity mismatch"}}

def Shape.replace_pair(-B: Data, items: List<&2, B>) -> Result<&2, &2, Error.t, Shape.t<B>>:
  match items:
    case Nil{}:
      Fail{Error.Carry{"shape payload arity mismatch"}}
    case Con{x, Nil{}}:
      Fail{Error.Carry{"shape payload arity mismatch"}}
    case Con{x, Con{y, Nil{}}}:
      Done{Shape.SPar{x, y}}
    case Con{x, Con{y, Con{z, rest}}}:
      Fail{Error.Carry{"shape payload arity mismatch"}}

def Shape.with_payload(-A: Data, -B: Data, shape: Shape.t<A>, +items: List<&2, B>) -> Result<&2, &2, Error.t, Shape.t<B>>:
  match shape:
    case Shape.SPi{q, name, dom}:
      Shape.replace_point(B, q, name, items)
    case Shape.SColl{k}:
      Shape.replaced(B, Shape.SColl{k}, List.is_empty(&2, B, items))
    case Shape.SPar{a, b}:
      Shape.replace_pair(B, items)
    case Shape.SMu{name, args}:
      Shape.replaced(B, Shape.SMu{name, items}, Nat.is_eq(List.length(&2, A, args), List.length(&2, B, items)))
    case Shape.SNu{name, args}:
      Shape.replaced(B, Shape.SNu{name, items}, Nat.is_eq(List.length(&2, A, args), List.length(&2, B, items)))
