import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import syntax.bend as S
import elab_requests.bend as R
import elab_common.bend as H

type Elab.declaration is Data:
  Elab.Declaration{name: String, postulate: Bool, ty: F.Term.t, body: Maybe<&2, F.Term.t>}

type Elab.family_header is Data:
  Elab.FamilyHeader{name: String, params: F.Positivity.telescope, indices: F.Positivity.telescope, level: F.Level.t}

type Elab.constructor_header is Data:
  Elab.ConstructorHeader{name: String, args: F.Positivity.telescope, params: List<&2, F.Term.t>, indices: List<&2, F.Term.t>}

type Elab.telescope_result is Data:
  Elab.Telescope{telescope: F.Positivity.telescope, ctx: C.Check.ctx}

type Elab.chain_result is Data:
  Elab.Chain{telescope: F.Positivity.telescope, result: S.Syntax.t, ctx: C.Check.ctx}

@unsafe
def Elab.telescope(binders: List<&2, S.Syntax.binder>, +ctx: C.Check.ctx, acc: F.Positivity.telescope) -> R.Elab.Program<Elab.telescope_result>:
  match binders:
    case Nil{}: R.Elab.Done{Elab.Telescope{acc, ctx}}
    case Con{S.Syntax.Binder{+q, +name, ty}, tail}:
      do R.Elab.Program<Elab.telescope_result>:
        +term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        value : F.Value.t <- H.Elab.eval(ctx, term)
        Elab.telescope(tail, C.Check.bind(name, q, value, ctx), List.append(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, acc, [F.Triple3{q, name, term}]))

@unsafe
def Elab.chain(term: S.Syntax.t, +ctx: C.Check.ctx, acc: F.Positivity.telescope) -> R.Elab.Program<Elab.chain_result>:
  match term:
    case S.Syntax.SArrow{S.Syntax.Binder{+q, +name, ty}, cod}:
      do R.Elab.Program<Elab.chain_result>:
        +ty_term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        ty_value : F.Value.t <- H.Elab.eval(ctx, ty_term)
        Elab.chain(cod, C.Check.bind(name, q, ty_value, ctx), List.append(&2, F.Triple3<F.Quantity.t, String, F.Term.t>, acc, [F.Triple3{q, name, ty_term}]))
    case _: R.Elab.Done{Elab.Chain{acc, term, ctx}}

def Elab.universe_term(term: F.Term.t) -> R.Elab.Program<F.Level.t>:
  match term:
    case F.Term.Univ{level}: R.Elab.Done{level}
    case _: R.Elab.Fail{F.Error.Universe{"the header of a family ends in a universe"}}

def Elab.family_indices(chain: Elab.chain_result, name: String, params: F.Positivity.telescope) -> R.Elab.Program<Elab.family_header>:
  Elab.Chain{indices, result, ctx} = chain
  do R.Elab.Program<Elab.family_header>:
    term : F.Term.t <- R.Elab.term(ctx, None{}, result)
    level : F.Level.t <- Elab.universe_term(term)
    return Elab.FamilyHeader{name, params, indices, level}

def Elab.family_parameters(telescope: Elab.telescope_result, name: String, ty: S.Syntax.t) -> R.Elab.Program<Elab.family_header>:
  Elab.Telescope{params, ctx} = telescope
  do R.Elab.Program<Elab.family_header>:
    indices : Elab.chain_result <- Elab.chain(ty, ctx, Nil{})
    Elab.family_indices(indices, name, params)

def Elab.family(family: S.Syntax.fam, ctx: C.Check.ctx) -> R.Elab.Program<Elab.family_header>:
  S.Syntax.Fam{name, params, ty, ctors} = family
  do R.Elab.Program<Elab.family_header>:
    parameters : Elab.telescope_result <- Elab.telescope(params, ctx, Nil{})
    Elab.family_parameters(parameters, name, ty)

def Elab.leg_bodies(legs: List<&2, F.Term.leg>) -> List<&2, F.Term.t>:
  match legs:
    case Nil{}: Nil{}
    case Con{F.Term.Leg{binders, body}, rest}: Con{body, Elab.leg_bodies(rest)}

def Elab.mu_params(diagram: F.Term.t) -> R.Elab.Program<List<&2, F.Term.t>>:
  match diagram:
    case F.Term.Sec{shape, legs}: R.Elab.Done{Elab.leg_bodies(legs)}
    case _: R.Elab.Fail{F.Error.Mismatch{"the diagram is not a section of the declared width"}}

def Elab.result_matches(equal: Bool, name: String, indices: List<&2, F.Term.t>, diagram: F.Term.t) -> R.Elab.Program<F.Pair2<List<&2, F.Term.t>, List<&2, F.Term.t>>>:
  match equal:
    case False{}: R.Elab.Fail{F.Error.Mismatch{"a constructor of " ++ name ++ " ends at another type"}}
    case True{}:
      do R.Elab.Program<F.Pair2<List<&2, F.Term.t>, List<&2, F.Term.t>>>:
        params : List<&2, F.Term.t> <- Elab.mu_params(diagram)
        return F.Pair2{params, indices}

def Elab.mu_result(term: F.Term.t, +name: String) -> R.Elab.Program<F.Pair2<List<&2, F.Term.t>, List<&2, F.Term.t>>>:
  match term:
    case F.Term.Lan{F.Shape.SMu{member, indices}, diagram}: Elab.result_matches(String.eq(name, member), name, indices, diagram)
    case _: R.Elab.Fail{F.Error.Mismatch{"a constructor of " ++ name ++ " ends at another type"}}

def Elab.constructor_result(result: F.Pair2<List<&2, F.Term.t>, List<&2, F.Term.t>>, name: String, args: F.Positivity.telescope) -> Elab.constructor_header:
  F.Pair2{params, indices} = result
  Elab.ConstructorHeader{name, args, params, indices}

def Elab.constructor_chain(chain: Elab.chain_result, family: String, name: String) -> R.Elab.Program<Elab.constructor_header>:
  Elab.Chain{args, result, ctx} = chain
  do R.Elab.Program<Elab.constructor_header>:
    term : F.Term.t <- R.Elab.term(ctx, None{}, result)
    result : F.Pair2<List<&2, F.Term.t>, List<&2, F.Term.t>> <- Elab.mu_result(term, family)
    return Elab.constructor_result(result, name, args)

def Elab.constructor(ctor: S.Syntax.fam_ctor, family: String, ctx: C.Check.ctx) -> R.Elab.Program<Elab.constructor_header>:
  S.Syntax.FamCtor{name, ty} = ctor
  do R.Elab.Program<Elab.constructor_header>:
    chain : Elab.chain_result <- Elab.chain(ty, ctx, Nil{})
    Elab.constructor_chain(chain, family, name)

@unsafe
def Elab.constructors(ctors: List<&2, S.Syntax.fam_ctor>, +family: String, +ctx: C.Check.ctx) -> R.Elab.Program<List<&2, Elab.constructor_header>>:
  match ctors:
    case Nil{}: R.Elab.Done{Nil{}}
    case Con{head, tail}:
      do R.Elab.Program<List<&2, Elab.constructor_header>>:
        ctor : Elab.constructor_header <- Elab.constructor(head, family, ctx)
        rest : List<&2, Elab.constructor_header> <- Elab.constructors(tail, family, ctx)
        return Con{ctor, rest}

def Elab.elab_decl(decl: S.Syntax.decl, +ctx: C.Check.ctx) -> R.Elab.Program<Elab.declaration>:
  match decl:
    case S.Syntax.DDef{name, ty, body}:
      do R.Elab.Program<Elab.declaration>:
        +ty_term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        ty_value : F.Value.t <- H.Elab.eval(ctx, ty_term)
        body_term : F.Term.t <- R.Elab.term(ctx, Some{ty_value}, body)
        return Elab.Declaration{name, False{}, ty_term, Some{body_term}}
    case S.Syntax.DAxiom{name, ty}:
      do R.Elab.Program<Elab.declaration>:
        term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
        return Elab.Declaration{name, True{}, term, None{}}
    case S.Syntax.DMu{families}: R.Elab.Fail{F.Error.Mismatch{"a mu group declares no entry of its own"}}
    case S.Syntax.DRec{members}: R.Elab.Fail{F.Error.Mismatch{"a recursive group is elaborated as a group"}}
