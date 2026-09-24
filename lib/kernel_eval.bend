import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_primitives.bend as P

type Eval.Job is Data:
  Eval.Evaluate{env: List<&2, F.Value.t>, term: F.Term.t}
  Eval.Weak{value: F.Value.t}
  Eval.Project{shape: F.Shape.t<F.Value.t>, addr: F.Value.vaddr, value: F.Value.t}
  Eval.Eliminate{shape: F.Shape.t<F.Value.t>, quantity: F.Quantity.t,
    motive: Maybe<&2, F.Term.motive>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>,
    env: List<&2, F.Value.t>, value: F.Value.t}
  Eval.Replay{frames: List<&2, F.Value.spine>, value: F.Value.t}
  Eval.Return{value: F.Value.t}
  Eval.Annotate{env: List<&2, F.Value.t>, value: F.Value.t, ty: F.Term.t}
  Eval.UnfoldReplay{body: F.Term.t, frames: List<&2, F.Value.spine>}


type Eval.Task is Type:
  Eval.ValueTask{job: Eval.Job, done: F.Value.t -> Result<&2, &2, F.Error.t, F.Value.t>}
  Eval.ShapeTask{shape: F.Shape.t<F.Term.t>, env: List<&2, F.Value.t>,
    done: F.Shape.t<F.Value.t> -> Result<&2, &2, F.Error.t, F.Value.t>}
  Eval.AddrTask{addr: F.Term.addr, env: List<&2, F.Value.t>,
    done: F.Value.vaddr -> Result<&2, &2, F.Error.t, F.Value.t>}
  Eval.ListTask{terms: List<&2, F.Term.t>, env: List<&2, F.Value.t>,
    done: List<&2, F.Value.t> -> Result<&2, &2, F.Error.t, F.Value.t>}


type Eval.QuoteTask is Type:
  Eval.QuoteValue{value: F.Value.t, size: Nat, done: F.Term.t -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteShape{shape: F.Shape.t<F.Value.t>, size: Nat, done: F.Shape.t<F.Term.t> -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteAddr{addr: F.Value.vaddr, size: Nat, done: F.Term.addr -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteValues{values: List<&2, F.Value.t>, size: Nat, done: List<&2, F.Term.t> -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteLegs{legs: List<&2, F.Value.vleg>, size: Nat, done: List<&2, F.Term.leg> -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteFormer{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, level: Maybe<&2, F.Level.t>, left: Bool,
    size: Nat, done: F.Term.t -> Result<&2, &2, F.Error.t, F.Term.t>}
  Eval.QuoteFrames{frames: List<&2, F.Value.spine>, head: F.Term.t, size: Nat, done: F.Term.t -> Result<&2, &2, F.Error.t, F.Term.t>}

# Quotation can evaluate a closure before recursively quoting its result, so
# the termination relation is semantic rather than Bend's syntactic subterms.

def Eval.context() -> Data:
  F.Pair2<F.Global.t, List<&2, F.Value.t>>


def Eval.close_legs(legs: List<&2, F.Term.leg>, +env: List<&2, F.Value.t>)
  -> List<&2, F.Value.vleg>:
  match legs:
    case Nil{}:
      Nil{}
    case Con{leg, rest}:
      F.Term.Leg{binders, body} = leg
      Con{F.Value.Leg{binders, F.Value.Closure{env, body}}, Eval.close_legs(rest, env)}


def Eval.filled(old: Maybe<&2, F.Level.t>, new: Maybe<&2, F.Level.t>) -> Maybe<&2, F.Level.t>:
  match old:
    case None{}:
      new
    case Some{level}:
      Some{level}


def Eval.annotation_level(result: Result<&2, &2, F.Error.t, F.Value.t>) -> Maybe<&2, F.Level.t>:
  match result:
    case Fail{error}:
      None{}
    case Done{value}:
      F.Value.as_univ(value)


def Eval.spine_literals(frames: List<&2, F.Value.spine>, acc: List<&2, F.Literal.t>)
  -> Maybe<&2, List<&2, F.Literal.t>>:
  match frames:
    case Nil{}:
      Some{acc}
    case Con{frame, rest}:
      match frame:
        case F.Value.SElim{elimination}:
          None{}
        case F.Value.SOut{s, addr}:
          match addr:
            case F.Value.VALeg{k}:
              None{}
            case F.Value.VACtor{name}:
              None{}
            case F.Value.VAPt{q, value}:
              do Maybe<&2, List<&2, F.Literal.t>>:
                literal: F.Literal.t <- F.Value.as_lit(value)
                Eval.spine_literals(rest, Con{literal, acc})


def Eval.primitive_entry(entry: F.Global.prim_entry) -> F.Prim.t:
  F.Global.PrimEntry{ty, prim} = entry
  prim


def Eval.head_prim(head: F.Value.head, globals: F.Global.t) -> Maybe<&2, F.Prim.t>:
  match head:
    case F.Value.HLocal{level}:
      None{}
    case F.Value.HGlobal{name}:
      do Maybe<&2, F.Prim.t>:
        entry: F.Global.prim_entry <- F.Global.find_prim(name, globals)
        return Eval.primitive_entry(entry)


def Eval.prim_candidate(value: F.Value.t, +globals: F.Global.t) -> Maybe<&2, F.Value.t>:
  match value:
    case F.Value.VNeutral{head, spine}:
      do Maybe<&2, F.Value.t>:
        prim: F.Prim.t <- Eval.head_prim(head, globals)
        literals: List<&2, F.Literal.t> <- Eval.spine_literals(spine, Nil{})
        result: Maybe<&2, F.Value.t> <- U.Kernel.result_option(Maybe<&2, F.Value.t>, P.Prim.apply(prim, literals))
        result
    case F.Value.VUniv{level}:
      None{}
    case F.Value.VLan{s, d, level}:
      None{}
    case F.Value.VRan{s, d, level}:
      None{}
    case F.Value.VIn{s, addr, args}:
      None{}
    case F.Value.VSec{s, legs}:
      None{}
    case F.Value.VLit{literal}:
      None{}


def Eval.prim_step(globals: F.Global.t, +value: F.Value.t) -> F.Value.t:
  Maybe.default(&2, F.Value.t, Eval.prim_candidate(value, globals), value)


def Eval.constructor(value: F.Value.t) -> Bool:
  match value:
    case F.Value.VIn{s, addr, args}:
      Maybe.is_some(&2, String, F.Value.as_ctor(addr))
    case F.Value.VUniv{level}:
      False{}
    case F.Value.VLan{s, d, level}:
      False{}
    case F.Value.VRan{s, d, level}:
      False{}
    case F.Value.VSec{s, legs}:
      False{}
    case F.Value.VLit{literal}:
      False{}
    case F.Value.VNeutral{head, spine}:
      False{}


def Eval.guarded_frame(frames: List<&2, F.Value.spine>, k: Nat) -> Bool:
  match frames:
    case Nil{}:
      False{}
    case Con{frame, rest}:
      match frame:
        case F.Value.SElim{elimination}:
          False{}
        case F.Value.SOut{s, addr}:
          match addr:
            case F.Value.VALeg{i}:
              False{}
            case F.Value.VACtor{name}:
              False{}
            case F.Value.VAPt{q, value}:
              match k:
                case Zero{}:
                  Eval.constructor(value)
                case Succ{pred}:
                  Eval.guarded_frame(rest, pred)


def Eval.rec_definition(reducible: Bool, recursive: Maybe<&2, Nat>, body: F.Term.t,
  spine: List<&2, F.Value.spine>) -> Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
  match reducible:
    case False{}:
      None{}
    case True{}:
      do Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
        k: Nat <- recursive
        return F.Triple3{body, k, List.reverse(&2, F.Value.spine, spine)}


def Eval.rec_def(definition: F.Global.def_entry, spine: List<&2, F.Value.spine>)
  -> Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
  F.Global.DefEntry{ty, body, reducible, recursive, partial} = definition
  Eval.rec_definition(reducible, recursive, body, spine)


def Eval.rec_head(head: F.Value.head, spine: List<&2, F.Value.spine>, globals: F.Global.t)
  -> Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
  match head:
    case F.Value.HLocal{level}:
      None{}
    case F.Value.HGlobal{name}:
      do Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
        entry: F.Global.entry <- F.Global.find(name, globals)
        definition: F.Global.def_entry <- F.Global.def_of(entry)
        Eval.rec_def(definition, spine)


def Eval.rec_pair(pair: F.Pair2<F.Value.head, List<&2, F.Value.spine>>, globals: F.Global.t)
  -> Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
  F.Pair2{head, spine} = pair
  Eval.rec_head(head, spine, globals)


def Eval.rec_candidate(value: F.Value.t, globals: F.Global.t)
  -> Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
  do Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>:
    pair: F.Pair2<F.Value.head, List<&2, F.Value.spine>> <- F.Value.as_neutral(value)
    Eval.rec_pair(pair, globals)


def Eval.open_job(closure: F.Value.closure, args: List<&2, F.Value.t>) -> Eval.Job:
  F.Value.Closure{env, body} = closure
  Eval.Evaluate{U.Kernel.rev_append(F.Value.t, args, env), body}


def Eval.leg_job(leg: F.Value.vleg, args: List<&2, F.Value.t>) -> Eval.Job:
  F.Value.Leg{binders, closure} = leg
  Eval.open_job(closure, args)


def Eval.out_pi_section(section: F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>>, arg: F.Value.t)
  -> Maybe<&2, Eval.Job>:
  F.Pair2{shape, legs} = section
  do Maybe<&2, Eval.Job>:
    leg: F.Value.vleg <- U.Kernel.one(F.Value.vleg, legs)
    return Eval.leg_job(leg, [arg])


def Eval.out_pi(addr: F.Value.vaddr, value: F.Value.t) -> Maybe<&2, Eval.Job>:
  match addr:
    case F.Value.VAPt{q, arg}:
      do Maybe<&2, Eval.Job>:
        section: F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>> <- F.Value.as_sec(value)
        Eval.out_pi_section(section, arg)
    case F.Value.VALeg{k}:
      None{}
    case F.Value.VACtor{name}:
      None{}


def Eval.out_coll_section(section: F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>>, k: Nat)
  -> Maybe<&2, Eval.Job>:
  F.Pair2{shape, legs} = section
  do Maybe<&2, Eval.Job>:
    leg: F.Value.vleg <- List.get(&2, F.Value.vleg, legs, k)
    return Eval.leg_job(leg, Nil{})


def Eval.out_coll(addr: F.Value.vaddr, value: F.Value.t) -> Maybe<&2, Eval.Job>:
  match addr:
    case F.Value.VALeg{k}:
      do Maybe<&2, Eval.Job>:
        section: F.Pair2<F.Shape.t<F.Value.t>, List<&2, F.Value.vleg>> <- F.Value.as_sec(value)
        Eval.out_coll_section(section, k)
    case F.Value.VAPt{q, arg}:
      None{}
    case F.Value.VACtor{name}:
      None{}


def Eval.out_candidate(+shape: F.Shape.t<F.Value.t>, +addr: F.Value.vaddr, +value: F.Value.t)
  -> Result<&2, &2, F.Error.t, Maybe<&2, Eval.Job>>:
  F.Shape.fold(F.Value.t, Unit, Result<&2, &2, F.Error.t, Maybe<&2, Eval.Job>>, shape, Unit{},
    q => name => domain => unit => (
      Done{Eval.out_pi(addr, value)}
    ),
    width => unit => (
      Done{Eval.out_coll(addr, value)}
    ),
    a => b => unit => (
      Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      Fail{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}
    ),
    name => indices => unit => (
      Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Eval.addr_key_equal(key: F.Term.addr, addr: F.Value.vaddr) -> Bool:
  match key:
    case F.Term.APt{q, arg}:
      False{}
    case F.Term.ALeg{k}:
      match addr:
        case F.Value.VALeg{j}:
          Nat.is_eq(k, j)
        case F.Value.VAPt{q, arg}:
          False{}
        case F.Value.VACtor{name}:
          False{}
    case F.Term.ACtor{name}:
      match addr:
        case F.Value.VACtor{other}:
          String.eq(name, other)
        case F.Value.VAPt{q, arg}:
          False{}
        case F.Value.VALeg{k}:
          False{}


def Eval.branch_choose(hit: Bool, leg: F.Term.leg, other: Maybe<&2, F.Term.leg>) -> Maybe<&2, F.Term.leg>:
  match hit:
    case True{}:
      Some{leg}
    case False{}:
      other


def Eval.branch(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +addr: F.Value.vaddr)
  -> Maybe<&2, F.Term.leg>:
  match branches:
    case Nil{}:
      None{}
    case Con{branch, rest}:
      F.Pair2{key, leg} = branch
      Eval.branch_choose(Eval.addr_key_equal(key, addr), leg, Eval.branch(rest, addr))


def Eval.branch_job(leg: F.Term.leg, env: List<&2, F.Value.t>) -> Eval.Job:
  F.Term.Leg{binders, body} = leg
  Eval.Evaluate{env, body}


def Eval.pi_branch(branch: F.Pair2<F.Term.addr, F.Term.leg>, env: List<&2, F.Value.t>,
  arg: F.Value.t, fibre: F.Value.t) -> Eval.Job:
  F.Pair2{key, leg} = branch
  Eval.branch_job(leg, Con{fibre, Con{arg, env}})


def Eval.elim_pi_addr(addr: F.Value.vaddr, args: List<&2, F.Value.t>,
  branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, env: List<&2, F.Value.t>) -> Maybe<&2, Eval.Job>:
  match addr:
    case F.Value.VAPt{q, arg}:
      do Maybe<&2, Eval.Job>:
        fibre: F.Value.t <- U.Kernel.one(F.Value.t, args)
        branch: F.Pair2<F.Term.addr, F.Term.leg> <- U.Kernel.one(F.Pair2<F.Term.addr, F.Term.leg>, branches)
        return Eval.pi_branch(branch, env, arg, fibre)
    case F.Value.VALeg{k}:
      None{}
    case F.Value.VACtor{name}:
      None{}


def Eval.elim_pi_in(injection: F.Triple3<F.Shape.t<F.Value.t>, F.Value.vaddr, List<&2, F.Value.t>>,
  branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, env: List<&2, F.Value.t>) -> Maybe<&2, Eval.Job>:
  F.Triple3{shape, addr, args} = injection
  Eval.elim_pi_addr(addr, args, branches, env)


def Eval.elim_coll_addr(+addr: F.Value.vaddr, args: List<&2, F.Value.t>,
  branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, env: List<&2, F.Value.t>, ctor: Bool) -> Maybe<&2, Eval.Job>:
  match addr:
    case F.Value.VAPt{q, arg}:
      None{}
    case F.Value.VALeg{k}:
      match ctor:
        case True{}:
          None{}
        case False{}:
          do Maybe<&2, Eval.Job>:
            leg: F.Term.leg <- Eval.branch(branches, addr)
            return Eval.branch_job(leg, U.Kernel.rev_append(F.Value.t, args, env))
    case F.Value.VACtor{name}:
      match ctor:
        case False{}:
          None{}
        case True{}:
          do Maybe<&2, Eval.Job>:
            leg: F.Term.leg <- Eval.branch(branches, addr)
            return Eval.branch_job(leg, U.Kernel.rev_append(F.Value.t, args, env))


def Eval.elim_coll_in(injection: F.Triple3<F.Shape.t<F.Value.t>, F.Value.vaddr, List<&2, F.Value.t>>,
  branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, env: List<&2, F.Value.t>, ctor: Bool) -> Maybe<&2, Eval.Job>:
  F.Triple3{shape, addr, args} = injection
  Eval.elim_coll_addr(addr, args, branches, env, ctor)


def Eval.elim_candidate(+shape: F.Shape.t<F.Value.t>, +value: F.Value.t,
  +branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +env: List<&2, F.Value.t>)
  -> Result<&2, &2, F.Error.t, Maybe<&2, Eval.Job>>:
  F.Shape.fold(F.Value.t, Unit, Result<&2, &2, F.Error.t, Maybe<&2, Eval.Job>>, shape, Unit{},
    q => name => domain => unit => (
      Done{Maybe.bind(&2, F.Triple3<F.Shape.t<F.Value.t>, F.Value.vaddr, List<&2, F.Value.t>>, Eval.Job,
        F.Value.as_in(value), injection => Eval.elim_pi_in(injection, branches, env))}
    ),
    width => unit => (
      Done{Maybe.bind(&2, F.Triple3<F.Shape.t<F.Value.t>, F.Value.vaddr, List<&2, F.Value.t>>, Eval.Job,
        F.Value.as_in(value), injection => Eval.elim_coll_in(injection, branches, env, False{}))}
    ),
    a => b => unit => (
      Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      Done{Maybe.bind(&2, F.Triple3<F.Shape.t<F.Value.t>, F.Value.vaddr, List<&2, F.Value.t>>, Eval.Job,
        F.Value.as_in(value), injection => Eval.elim_coll_in(injection, branches, env, True{}))}
    ),
    name => indices => unit => (
      Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Eval.stuck(value: F.Value.t, frame: F.Value.spine) -> Result<&2, &2, F.Error.t, F.Value.t>:
  match value:
    case F.Value.VNeutral{head, spine}:
      Done{F.Value.VNeutral{head, Con{frame, spine}}}
    case F.Value.VUniv{level}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}
    case F.Value.VLan{s, d, level}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}
    case F.Value.VRan{s, d, level}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}
    case F.Value.VIn{s, addr, args}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}
    case F.Value.VSec{s, legs}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}
    case F.Value.VLit{literal}:
      Fail{F.Error.Mismatch{P.Rules.stuck_msg}}


def Eval.apply_done(result: Result<&2, &2, F.Error.t, F.Value.t>, done: F.Value.t -> Result<&2, &2, F.Error.t, F.Value.t>)
  -> Result<&2, &2, F.Error.t, F.Value.t>:
  Result.bind(&2, &2, F.Error.t, F.Value.t, F.Value.t, result, done)

# Only this evaluator dispatcher bypasses Bend's termination check. Closure
# evaluation and guarded global unfolding preserve the source's unbounded
# behavior. Continuations carry exact result types without partial projections.

def Eval.unfold_job(reducible: Bool, recursive: Maybe<&2, Nat>, body: F.Term.t, opaque: F.Value.t) -> Eval.Job:
  match reducible:
    case False{}:
      Eval.Return{opaque}
    case True{}:
      match recursive:
        case None{}:
          Eval.Evaluate{Nil{}, body}
        case Some{k}:
          Eval.Return{opaque}


def Eval.global_job(entry: F.Global.entry, opaque: F.Value.t) -> Eval.Job:
  match entry:
    case F.Global.Axiom{axiom}:
      Eval.Return{opaque}
    case F.Global.Prim{primitive}:
      Eval.Return{opaque}
    case F.Global.Def{definition}:
      F.Global.DefEntry{ty, body, reducible, recursive, partial} = definition
      Eval.unfold_job(reducible, recursive, body, opaque)


def Eval.guard_job(guarded: Bool, body: F.Term.t, frames: List<&2, F.Value.spine>, value: F.Value.t) -> Eval.Job:
  match guarded:
    case False{}:
      Eval.Return{value}
    case True{}:
      Eval.UnfoldReplay{body, frames}


def Eval.weak_job(candidate: Maybe<&2, F.Triple3<F.Term.t, Nat, List<&2, F.Value.spine>>>, value: F.Value.t) -> Eval.Job:
  match candidate:
    case None{}:
      Eval.Return{value}
    case Some{triple}:
      F.Triple3{body, k, +frames} = triple
      Eval.guard_job(Eval.guarded_frame(frames, k), body, frames, value)


def Eval.beta_job(candidate: Maybe<&2, Eval.Job>, value: F.Value.t, frame: F.Value.spine)
  -> Result<&2, &2, F.Error.t, Eval.Job>:
  match candidate:
    case None{}:
      do Result<&2, &2, F.Error.t, Eval.Job>:
        stuck: F.Value.t <- Eval.stuck(value, frame)
        return Eval.Return{stuck}
    case Some{job}:
      Done{job}


# Evaluation is intentionally unbounded, as in the source kernel. This marker
# skips only termination checking; types and affine usage remain checked.
@unsafe def Eval.task(task: Eval.Task, +globals: F.Global.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  match task:
    case Eval.ListTask{terms, +env, done}:
      match terms:
        case Nil{}:
          done(Nil{})
        case Con{term, rest}:
          Eval.task(Eval.ValueTask{Eval.Evaluate{env, term}, value =>
            Eval.task(Eval.ListTask{rest, env, values => done(Con{value, values})}, globals)}, globals)
    case Eval.AddrTask{addr, env, done}:
      match addr:
        case F.Term.APt{q, arg}:
          Eval.task(Eval.ValueTask{Eval.Evaluate{env, arg}, value => done(F.Value.VAPt{q, value})}, globals)
        case F.Term.ALeg{k}:
          done(F.Value.VALeg{k})
        case F.Term.ACtor{name}:
          done(F.Value.VACtor{name})
    case Eval.ShapeTask{shape, +env, done}:
      F.Shape.fold(F.Term.t, F.Shape.t<F.Value.t> -> Result<&2, &2, F.Error.t, F.Value.t>, Result<&2, &2, F.Error.t, F.Value.t>, shape, done,
        q => name => domain => resume => (
          Eval.task(Eval.ValueTask{Eval.Evaluate{env, domain}, value => resume(F.Shape.make_point(F.Value.t, q, name, value))}, globals)
        ),
        width => resume => (
          resume(F.Shape.make_collection(F.Value.t, width))
        ),
        a => b => resume => (
          Fail{F.Error.Not_yet{P.Rules.spar_word}}
        ),
        name => indices => resume => (
          Eval.task(Eval.ListTask{indices, env, values => resume(F.Shape.make_inductive(F.Value.t, name, values))}, globals)
        ),
        name => indices => resume => (
          Fail{F.Error.Not_yet{P.Rules.snu_word}}
        ))
    case Eval.ValueTask{job, done}:
      match job:
        case Eval.Return{value}:
          done(value)
        case Eval.Evaluate{+env, term}:
          match term:
            case F.Term.Var{+index}:
              Eval.apply_done(U.Kernel.from_maybe(F.Value.t, List.get(&2, F.Value.t, env, index),
                F.Error.Unbound{"de Bruijn index " ++ Nat.show(index) ++ " is outside the environment"}), done)
            case F.Term.Univ{level}:
              done(F.Value.VUniv{level})
            case F.Term.Lit{literal}:
              done(F.Value.VLit{literal})
            case F.Term.Lan{shape, diagram}:
              Eval.task(Eval.ShapeTask{shape, env, vs => done(F.Value.VLan{vs, F.Value.Closure{env, diagram}, None{}})}, globals)
            case F.Term.Ran{shape, diagram}:
              Eval.task(Eval.ShapeTask{shape, env, vs => done(F.Value.VRan{vs, F.Value.Closure{env, diagram}, None{}})}, globals)
            case F.Term.In{shape, addr, args}:
              Eval.task(Eval.ShapeTask{shape, env, vs =>
                Eval.task(Eval.AddrTask{addr, env, va =>
                  Eval.task(Eval.ListTask{args, env, values => done(F.Value.VIn{vs, va, values})}, globals)}, globals)}, globals)
            case F.Term.Sec{shape, legs}:
              Eval.task(Eval.ShapeTask{shape, env, vs => done(F.Value.VSec{vs, Eval.close_legs(legs, env)})}, globals)
            case F.Term.Out{shape, addr, scrutinee}:
              Eval.task(Eval.ShapeTask{shape, env, vs =>
                Eval.task(Eval.AddrTask{addr, env, va =>
                  Eval.task(Eval.ValueTask{Eval.Evaluate{env, scrutinee}, value =>
                    Eval.task(Eval.ValueTask{Eval.Project{vs, va, value}, applied =>
                      Eval.task(Eval.ValueTask{Eval.Weak{applied}, done}, globals)}, globals)}, globals)}, globals)}, globals)
            case F.Term.Elim{elimination}:
              F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
              Eval.task(Eval.ShapeTask{shape, env, vs =>
                Eval.task(Eval.ValueTask{Eval.Evaluate{env, scrutinee}, value =>
                  Eval.task(Eval.ValueTask{Eval.Eliminate{vs, q, motive, branches, env, value}, done}, globals)}, globals)}, globals)
            case F.Term.Let{name, ty, body, rest}:
              Eval.task(Eval.ValueTask{Eval.Evaluate{env, body}, value =>
                Eval.task(Eval.ValueTask{Eval.Evaluate{Con{value, env}, rest}, done}, globals)}, globals)
            case F.Term.Ann{term, ty}:
              Eval.task(Eval.ValueTask{Eval.Evaluate{env, term}, value =>
                Eval.task(Eval.ValueTask{Eval.Annotate{env, value, ty}, done}, globals)}, globals)
            case F.Term.Global{+name}:
              do Result<&2, &2, F.Error.t, F.Value.t>:
                entry: F.Global.entry <- U.Kernel.from_maybe(F.Global.entry,
                  F.Global.find(name, globals), F.Error.Unbound{name})
                Eval.task(Eval.ValueTask{Eval.global_job(entry, F.Value.VNeutral{F.Value.HGlobal{name}, Nil{}}), done}, globals)
            case F.Term.Auto{}:
              Fail{F.Error.Not_yet{P.Rules.auto_word}}
        case Eval.Annotate{env, value, ty}:
          match value:
            case F.Value.VLan{s, diagram, old}:
              level = Eval.annotation_level(Eval.task(Eval.ValueTask{Eval.Evaluate{env, ty}, v => Done{v}}, globals))
              done(F.Value.VLan{s, diagram, Eval.filled(old, level)})
            case F.Value.VRan{s, diagram, old}:
              level = Eval.annotation_level(Eval.task(Eval.ValueTask{Eval.Evaluate{env, ty}, v => Done{v}}, globals))
              done(F.Value.VRan{s, diagram, Eval.filled(old, level)})
            case F.Value.VUniv{l}:
              done(F.Value.VUniv{l})
            case F.Value.VIn{s, a, args}:
              done(F.Value.VIn{s, a, args})
            case F.Value.VSec{s, legs}:
              done(F.Value.VSec{s, legs})
            case F.Value.VLit{literal}:
              done(F.Value.VLit{literal})
            case F.Value.VNeutral{head, spine}:
              done(F.Value.VNeutral{head, spine})
        case Eval.Weak{value}:
          +stepped = Eval.prim_step(globals, value)
          Eval.task(Eval.ValueTask{Eval.weak_job(Eval.rec_candidate(stepped, globals), stepped), done}, globals)
        case Eval.Project{+shape, +addr, +value}:
          do Result<&2, &2, F.Error.t, F.Value.t>:
            candidate: Maybe<&2, Eval.Job> <- Eval.out_candidate(shape, addr, value)
            next: Eval.Job <- Eval.beta_job(candidate, value, F.Value.SOut{shape, addr})
            Eval.task(Eval.ValueTask{next, done}, globals)
        case Eval.Eliminate{+shape, q, motive, +branches, +env, +value}:
          do Result<&2, &2, F.Error.t, F.Value.t>:
            candidate: Maybe<&2, Eval.Job> <- Eval.elim_candidate(shape, value, branches, env)
            next: Eval.Job <- Eval.beta_job(candidate, value, F.Value.SElim{F.Value.StuckElim{shape, q, motive, branches, env}})
            Eval.task(Eval.ValueTask{next, done}, globals)
        case Eval.UnfoldReplay{body, frames}:
          Eval.task(Eval.ValueTask{Eval.Evaluate{Nil{}, body}, head =>
            Eval.task(Eval.ValueTask{Eval.Replay{frames, head}, done}, globals)}, globals)
        case Eval.Replay{frames, value}:
          match frames:
            case Nil{}:
              done(value)
            case Con{frame, rest}:
              match frame:
                case F.Value.SOut{shape, addr}:
                  Eval.task(Eval.ValueTask{Eval.Project{shape, addr, value}, applied =>
                    Eval.task(Eval.ValueTask{Eval.Weak{applied}, weak =>
                      Eval.task(Eval.ValueTask{Eval.Replay{rest, weak}, done}, globals)}, globals)}, globals)
                case F.Value.SElim{elimination}:
                  F.Value.StuckElim{shape, q, motive, branches, env} = elimination
                  Eval.task(Eval.ValueTask{Eval.Eliminate{shape, q, motive, branches, env, value}, applied =>
                    Eval.task(Eval.ValueTask{Eval.Replay{rest, applied}, done}, globals)}, globals)


def Eval.run(globals: F.Global.t, job: Eval.Job) -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.task(Eval.ValueTask{job, value => Done{value}}, globals)


def Eval.eval(globals: F.Global.t, env: List<&2, F.Value.t>, term: F.Term.t)
  -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.run(globals, Eval.Evaluate{env, term})


def Eval.whnf(globals: F.Global.t, value: F.Value.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.run(globals, Eval.Weak{value})


def Eval.open_closure(globals: F.Global.t, closure: F.Value.closure, args: List<&2, F.Value.t>)
  -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.run(globals, Eval.open_job(closure, args))


def Rules.out_value(globals: F.Global.t, shape: F.Shape.t<F.Value.t>, addr: F.Value.vaddr, value: F.Value.t)
  -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.run(globals, Eval.Project{shape, addr, value})


def Rules.elim_value(globals: F.Global.t, shape: F.Shape.t<F.Value.t>, q: F.Quantity.t,
  motive: Maybe<&2, F.Term.motive>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>,
  env: List<&2, F.Value.t>, value: F.Value.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  Eval.run(globals, Eval.Eliminate{shape, q, motive, branches, env, value})


def Eval.variables(count: Nat, +size: Nat) -> List<&2, F.Value.t>:
  match count:
    case Zero{}: Nil{}
    case Succ{pred}: Con{F.Value.var(size), Eval.variables(pred, (size + 1n : Nat))}


def Eval.diagram_arity(shape: F.Shape.t<F.Value.t>) -> Result<&2, &2, F.Error.t, Nat>:
  F.Shape.fold(F.Value.t, Unit, Result<&2, &2, F.Error.t, Nat>, shape, Unit{},
    q => name => domain => unit => (
      Done{1n}
    ),
    width => unit => (
      Done{0n}
    ),
    a => b => unit => (
      Fail{F.Error.Not_yet{P.Rules.spar_word}}
    ),
    name => indices => unit => (
      Done{0n}
    ),
    name => indices => unit => (
      Fail{F.Error.Not_yet{P.Rules.snu_word}}
    ))

def Eval.annotate_term(level: Maybe<&2, F.Level.t>, term: F.Term.t) -> F.Term.t:
  match level:
    case None{}: term
    case Some{l}: F.Term.Ann{term, F.Term.Univ{l}}


def Eval.former(left: Bool, shape: F.Shape.t<F.Term.t>, diagram: F.Term.t) -> F.Term.t:
  match left:
    case True{}: F.Term.Lan{shape, diagram}
    case False{}: F.Term.Ran{shape, diagram}


def Eval.quote_local(valid: Bool, size: Nat, level: Nat) -> Result<&2, &2, F.Error.t, F.Term.t>:
  match valid:
    case True{}: Done{F.Term.Var{((size - level : Nat) - 1n : Nat)}}
    case False{}: Fail{F.Error.Unbound{"de Bruijn level " ++ Nat.show(level) ++ " is outside the quotation context"}}


def Eval.quote_head(head: F.Value.head, +size: Nat) -> Result<&2, &2, F.Error.t, F.Term.t>:
  match head:
    case F.Value.HLocal{+level}: Eval.quote_local(Nat.is_lt(level, size), size, level)
    case F.Value.HGlobal{name}: Done{F.Term.Global{name}}


# Closure opening constructs new tasks, outside the syntactic subterm test.
# Only termination is unchecked, without a fuel limit or proof axiom.
@unsafe def Eval.quote_task(task: Eval.QuoteTask, +globals: F.Global.t) -> Result<&2, &2, F.Error.t, F.Term.t>:
  match task:
    case Eval.QuoteValues{values, +size, done}:
      match values:
        case Nil{}: done(Nil{})
        case Con{value, rest}:
          Eval.quote_task(Eval.QuoteValue{value, size, term =>
            Eval.quote_task(Eval.QuoteValues{rest, size, terms => done(Con{term, terms})}, globals)}, globals)
    case Eval.QuoteLegs{legs, +size, done}:
      match legs:
        case Nil{}: done(Nil{})
        case Con{leg, rest}:
          F.Value.Leg{+binders, closure} = leg
          +arity = List.length(&2, F.Pair2<F.Quantity.t, String>, binders)
          do Result<&2, &2, F.Error.t, F.Term.t>:
            body: F.Value.t <- Eval.open_closure(globals, closure, Eval.variables(arity, size))
            Eval.quote_task(Eval.QuoteValue{body, (size + arity : Nat), term =>
              Eval.quote_task(Eval.QuoteLegs{rest, size, terms => done(Con{F.Term.Leg{binders, term}, terms})}, globals)}, globals)
    case Eval.QuoteShape{shape, +size, done}:
      F.Shape.fold(F.Value.t, F.Shape.t<F.Term.t> -> Result<&2, &2, F.Error.t, F.Term.t>, Result<&2, &2, F.Error.t, F.Term.t>, shape, done,
        q => name => domain => resume => (
          Eval.quote_task(Eval.QuoteValue{domain, size, term => resume(F.Shape.make_point(F.Term.t, q, name, term))}, globals)
        ),
        width => resume => (
          resume(F.Shape.make_collection(F.Term.t, width))
        ),
        a => b => resume => (
          Fail{F.Error.Not_yet{P.Rules.spar_word}}
        ),
        name => indices => resume => (
          Eval.quote_task(Eval.QuoteValues{indices, size, terms => resume(F.Shape.make_inductive(F.Term.t, name, terms))}, globals)
        ),
        name => indices => resume => (
          Fail{F.Error.Not_yet{P.Rules.snu_word}}
        ))
    case Eval.QuoteAddr{addr, size, done}:
      match addr:
        case F.Value.VAPt{q, value}:
          Eval.quote_task(Eval.QuoteValue{value, size, term => done(F.Term.APt{q, term})}, globals)
        case F.Value.VALeg{k}: done(F.Term.ALeg{k})
        case F.Value.VACtor{name}: done(F.Term.ACtor{name})
    case Eval.QuoteFormer{+shape, diagram, level, left, +size, done}:
      Eval.quote_task(Eval.QuoteShape{shape, size, s => (
        do Result<&2, &2, F.Error.t, F.Term.t>:
          +arity: Nat <- Eval.diagram_arity(shape)
          body: F.Value.t <- Eval.open_closure(globals, diagram, Eval.variables(arity, size))
          Eval.quote_task(Eval.QuoteValue{body, (size + arity : Nat), d =>
            done(Eval.annotate_term(level, Eval.former(left, s, d)))}, globals)
      )}, globals)
    case Eval.QuoteFrames{frames, head, +size, done}:
      match frames:
        case Nil{}: done(head)
        case Con{frame, rest}:
          match frame:
            case F.Value.SOut{shape, addr}:
              Eval.quote_task(Eval.QuoteShape{shape, size, s =>
                Eval.quote_task(Eval.QuoteAddr{addr, size, a =>
                  Eval.quote_task(Eval.QuoteFrames{rest, F.Term.Out{s, a, head}, size, done}, globals)}, globals)}, globals)
            case F.Value.SElim{elimination}:
              F.Value.StuckElim{shape, q, motive, branches, env} = elimination
              Eval.quote_task(Eval.QuoteShape{shape, size, s =>
                Eval.quote_task(Eval.QuoteFrames{rest, F.Term.Elim{F.Term.Elimination{s, head, q, motive, branches}}, size, done}, globals)}, globals)
    case Eval.QuoteValue{value, +size, done}:
      match value:
        case F.Value.VUniv{level}: done(F.Term.Univ{level})
        case F.Value.VLit{literal}: done(F.Term.Lit{literal})
        case F.Value.VLan{shape, diagram, level}:
          Eval.quote_task(Eval.QuoteFormer{shape, diagram, level, True{}, size, done}, globals)
        case F.Value.VRan{shape, diagram, level}:
          Eval.quote_task(Eval.QuoteFormer{shape, diagram, level, False{}, size, done}, globals)
        case F.Value.VIn{shape, addr, args}:
          Eval.quote_task(Eval.QuoteShape{shape, size, s =>
            Eval.quote_task(Eval.QuoteAddr{addr, size, a =>
              Eval.quote_task(Eval.QuoteValues{args, size, terms => done(F.Term.In{s, a, terms})}, globals)}, globals)}, globals)
        case F.Value.VSec{shape, legs}:
          Eval.quote_task(Eval.QuoteShape{shape, size, s =>
            Eval.quote_task(Eval.QuoteLegs{legs, size, terms => done(F.Term.Sec{s, terms})}, globals)}, globals)
        case F.Value.VNeutral{head, spine}:
          do Result<&2, &2, F.Error.t, F.Term.t>:
            term: F.Term.t <- Eval.quote_head(head, size)
            Eval.quote_task(Eval.QuoteFrames{List.reverse(&2, F.Value.spine, spine), term, size, done}, globals)


def Eval.quote(globals: F.Global.t, size: Nat, value: F.Value.t) -> Result<&2, &2, F.Error.t, F.Term.t>:
  Eval.quote_task(Eval.QuoteValue{value, size, term => Done{term}}, globals)
