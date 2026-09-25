import Base
import ./foundation.bend as F

# Preserve source universes and annotations when specializing field types.
# Parameters are in reverse telescope order, under the outer scope.
type Source.mapping is Data:
  Source.Shift{amount: Nat}
  Source.Parameters{arguments: List<&2, F.Term.t>}

def Source.result() -> Type:
  Result<&2,&2,F.Error.t,F.Term.t>

def Source.argument(arguments: List<&2, F.Term.t>, index: Nat) -> Source.result:
  match arguments index:
    case Nil{} index: Fail{F.Error.Mismatch{"parameter outside its telescope"}}
    case first <> rest 0n: Done{first}
    case first <> rest 1n+n: Source.argument(rest, n)

def Source.point_depth(point: Maybe<&2, F.Term.t>, depth: Nat) -> Nat:
  match point:
    case None{}: depth
    case Some{domain}: (depth + 1n : Nat)

def Source.shape_done(result: Result<&2,&2,F.Error.t,F.Shape.t<F.Term.t>>, done: F.Shape.t<F.Term.t> -> Source.result) -> Source.result:
  match result:
    case Fail{error}: Fail{error}
    case Done{shape}: done(shape)

type Source.Task is Type:
  Source.Node{mapping: Source.mapping, depth: Nat, term: F.Term.t, done: F.Term.t -> Source.result}
  Source.Variable{bound: Bool, mapping: Source.mapping, depth: Nat, index: Nat, done: F.Term.t -> Source.result}
  Source.Argument{argument: Source.result, depth: Nat, done: F.Term.t -> Source.result}
  Source.Terms{mapping: Source.mapping, depth: Nat, terms: List<&2, F.Term.t>, done: List<&2, F.Term.t> -> Source.result}
  Source.Shape{mapping: Source.mapping, depth: Nat, shape: F.Shape.t<F.Term.t>, done: F.Shape.t<F.Term.t> -> Source.result}
  Source.Address{mapping: Source.mapping, depth: Nat, address: F.Term.addr, done: F.Term.addr -> Source.result}
  Source.Leg{mapping: Source.mapping, depth: Nat, leg: F.Term.leg, done: F.Term.leg -> Source.result}
  Source.Legs{mapping: Source.mapping, depth: Nat, legs: List<&2, F.Term.leg>, done: List<&2, F.Term.leg> -> Source.result}
  Source.Motive{mapping: Source.mapping, depth: Nat, motive: Maybe<&2, F.Term.motive>, done: Maybe<&2, F.Term.motive> -> Source.result}
  Source.Branches{mapping: Source.mapping, depth: Nat, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, done: List<&2, F.Pair2<F.Term.addr, F.Term.leg>> -> Source.result}

# The task dispatcher walks finite source trees. A substituted argument is
# traversed only in Shift mode, so substitution cannot expand itself.
@unsafe
def Source.run(task: Source.Task) -> Source.result:
  match task:
    case Source.Variable{bound, mapping, +depth, index, done}:
      match bound:
        case True{}: done(F.Term.Var{index})
        case False{}:
          match mapping:
            case Source.Shift{amount}: done(F.Term.Var{(index + amount : Nat)})
            case Source.Parameters{arguments}:
              Source.run(Source.Argument{Source.argument(arguments, (index - depth : Nat)), depth, done})
    case Source.Argument{argument, depth, done}:
      match argument:
        case Fail{error}: Fail{error}
        case Done{term}: Source.run(Source.Node{Source.Shift{depth}, 0n, term, done})
    case Source.Terms{+mapping, +depth, terms, done}:
      match terms:
        case Nil{}: done(Nil{})
        case first <> rest:
          Source.run(Source.Node{mapping, depth, first, term =>
            Source.run(Source.Terms{mapping, depth, rest, more => done(term <> more)})})
    case Source.Shape{mapping, depth, +shape, done}:
      Source.run(Source.Terms{mapping, depth, F.Shape.payload(F.Term.t, shape), payload =>
        Source.shape_done(F.Shape.with_payload(F.Term.t, F.Term.t, shape, payload), done)})
    case Source.Address{mapping, depth, address, done}:
      match address:
        case F.Term.APt{q, term}: Source.run(Source.Node{mapping, depth, term, body => done(F.Term.APt{q, body})})
        case other: done(other)
    case Source.Leg{mapping, depth, F.Term.Leg{+binders, body}, done}:
      Source.run(Source.Node{mapping, (depth + List.length(&2, F.Pair2<F.Quantity.t, String>, binders) : Nat), body, term => done(F.Term.Leg{binders, term})})
    case Source.Legs{+mapping, +depth, legs, done}:
      match legs:
        case Nil{}: done(Nil{})
        case first <> rest:
          Source.run(Source.Leg{mapping, depth, first, leg =>
            Source.run(Source.Legs{mapping, depth, rest, more => done(leg <> more)})})
    case Source.Motive{mapping, depth, motive, done}:
      match motive:
        case None{}: done(None{})
        case Some{F.Term.Motive{ind, +indices, self, body}}:
          Source.run(Source.Node{mapping, (depth + 1n + List.length(&2, String, indices) : Nat), body, term => done(Some{F.Term.Motive{ind, indices, self, term}})})
    case Source.Branches{+mapping, +depth, branches, done}:
      match branches:
        case Nil{}: done(Nil{})
        case F.Pair2{address, leg} <> rest:
          Source.run(Source.Address{mapping, depth, address, a =>
            Source.run(Source.Leg{mapping, depth, leg, l =>
              Source.run(Source.Branches{mapping, depth, rest, more => done(F.Pair2{a, l} <> more)})})})
    case Source.Node{+mapping, +depth, term, done}:
      match term:
        case F.Term.Var{+index}: Source.run(Source.Variable{Nat.is_lt(index, depth), mapping, depth, index, done})
        case F.Term.Lan{+shape, diagram}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Node{mapping, Source.point_depth(F.Shape.point_dom(F.Term.t, shape), depth), diagram, d => done(F.Term.Lan{s, d})})})
        case F.Term.Ran{+shape, diagram}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Node{mapping, Source.point_depth(F.Shape.point_dom(F.Term.t, shape), depth), diagram, d => done(F.Term.Ran{s, d})})})
        case F.Term.In{shape, address, arguments}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Address{mapping, depth, address, a =>
              Source.run(Source.Terms{mapping, depth, arguments, xs => done(F.Term.In{s, a, xs})})})})
        case F.Term.Out{shape, address, head}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Address{mapping, depth, address, a =>
              Source.run(Source.Node{mapping, depth, head, h => done(F.Term.Out{s, a, h})})})})
        case F.Term.Sec{shape, legs}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Legs{mapping, depth, legs, ls => done(F.Term.Sec{s, ls})})})
        case F.Term.Elim{F.Term.Elimination{shape, scrut, quantity, motive, branches}}:
          Source.run(Source.Shape{mapping, depth, shape, s =>
            Source.run(Source.Node{mapping, depth, scrut, sc =>
              Source.run(Source.Motive{mapping, depth, motive, mo =>
                Source.run(Source.Branches{mapping, depth, branches, bs => done(F.Term.Elim{F.Term.Elimination{s, sc, quantity, mo, bs}})})})})})
        case F.Term.Let{name, ty, value, body}:
          Source.run(Source.Node{mapping, depth, ty, t =>
            Source.run(Source.Node{mapping, depth, value, v =>
              Source.run(Source.Node{mapping, (depth + 1n : Nat), body, b => done(F.Term.Let{name, t, v, b})})})})
        case F.Term.Ann{value, ty}:
          Source.run(Source.Node{mapping, depth, value, v =>
            Source.run(Source.Node{mapping, depth, ty, t => done(F.Term.Ann{v, t})})})
        case other: done(other)

def Source.term(mapping: Source.mapping, depth: Nat, term: F.Term.t) -> Source.result:
  Source.run(Source.Node{mapping, depth, term, result => Done{result}})
