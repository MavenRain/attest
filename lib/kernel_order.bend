import Base
import ./foundation.bend as F
import ./kernel_util.bend as U
import ./kernel_context.bend as C

# Term traversal is shared by positivity, structural order, and budget accounting.
def Term.addr_children(addr: F.Term.addr) -> List<&2, F.Term.t>:
  match addr:
    case F.Term.APt{q, arg}:
      [arg]
    case F.Term.ALeg{k}:
      []
    case F.Term.ACtor{name}:
      []

def Term.leg_children(legs: List<&2, F.Term.leg>) -> List<&2, F.Term.t>:
  match legs:
    case Nil{}:
      []
    case Con{leg, rest}:
      F.Term.Leg{binders, body} = leg
      Con{body, Term.leg_children(rest)}

def Term.motive_children(motive: Maybe<&2, F.Term.motive>) -> List<&2, F.Term.t>:
  match motive:
    case None{}:
      []
    case Some{m}:
      F.Term.Motive{ind, indices, self, body} = m
      [body]

def Term.branch_children(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> List<&2, F.Term.t>:
  match branches:
    case Nil{}:
      []
    case Con{branch, rest}:
      F.Pair2{addr, leg} = branch
      F.Term.Leg{binders, body} = leg
      List.append(&2, F.Term.t, Term.addr_children(addr), Con{body, Term.branch_children(rest)})

def Term.children(term: F.Term.t) -> List<&2, F.Term.t>:
  match term:
    case F.Term.Var{index}:
      []
    case F.Term.Univ{level}:
      []
    case F.Term.Lan{shape, diagram}:
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), [diagram])
    case F.Term.Ran{shape, diagram}:
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), [diagram])
    case F.Term.In{shape, addr, args}:
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), List.append(&2, F.Term.t, Term.addr_children(addr), args))
    case F.Term.Out{shape, addr, head}:
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), List.append(&2, F.Term.t, Term.addr_children(addr), [head]))
    case F.Term.Sec{shape, legs}:
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), Term.leg_children(legs))
    case F.Term.Elim{elimination}:
      F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
      List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), Con{scrutinee, List.append(&2, F.Term.t, Term.motive_children(motive), Term.branch_children(branches))})
    case F.Term.Let{name, ty, value, body}:
      [ty, value, body]
    case F.Term.Ann{body, ty}:
      [body, ty]
    case F.Term.Global{name}:
      []
    case F.Term.Lit{literal}:
      []
    case F.Term.Auto{}:
      []

def Term.family(term: F.Term.t) -> Maybe<&2, String>:
  match term:
    case F.Term.Lan{shape, diagram}:
      F.Shape.family(F.Term.t, shape)
    case F.Term.Ran{shape, diagram}:
      F.Shape.family(F.Term.t, shape)
    case F.Term.In{shape, addr, args}:
      F.Shape.family(F.Term.t, shape)
    case F.Term.Out{shape, addr, head}:
      F.Shape.family(F.Term.t, shape)
    case F.Term.Sec{shape, legs}:
      F.Shape.family(F.Term.t, shape)
    case F.Term.Elim{elimination}:
      F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
      F.Shape.family(F.Term.t, shape)
    case F.Term.Var{index}:
      None{}
    case F.Term.Univ{level}:
      None{}
    case F.Term.Let{name, ty, value, body}:
      None{}
    case F.Term.Ann{body, ty}:
      None{}
    case F.Term.Global{name}:
      None{}
    case F.Term.Lit{literal}:
      None{}
    case F.Term.Auto{}:
      None{}

def Term.named(names: List<&2, String>, term: F.Term.t) -> Bool:
  match term:
    case F.Term.Global{name}:
      U.Kernel.member(names, name)
    case F.Term.Var{index}:
      False{}
    case F.Term.Univ{level}:
      False{}
    case F.Term.Lan{shape, diagram}:
      False{}
    case F.Term.Ran{shape, diagram}:
      False{}
    case F.Term.In{shape, addr, args}:
      False{}
    case F.Term.Out{shape, addr, head}:
      False{}
    case F.Term.Sec{shape, legs}:
      False{}
    case F.Term.Elim{elimination}:
      False{}
    case F.Term.Let{name, ty, value, body}:
      False{}
    case F.Term.Ann{body, ty}:
      False{}
    case F.Term.Lit{literal}:
      False{}
    case F.Term.Auto{}:
      False{}

def Positivity.is_member(names: List<&2, String>, name: Maybe<&2, String>) -> Bool:
  match name:
    case None{}:
      False{}
    case Some{value}:
      U.Kernel.member(names, value)

type Term.Search is Data:
  Term.SearchNodes{work: List<&2, F.Term.t>}
  Term.SearchFound{found: Bool, term: F.Term.t, rest: List<&2, F.Term.t>}

# The worklist grows when a node is expanded; semantic termination follows the finite tree.
@unsafe def Term.search(+include_families: Bool, +names: List<&2, String>, job: Term.Search) -> Bool:
  match job:
    case Term.SearchNodes{work}:
      match work:
        case Nil{}:
          False{}
        case Con{+term, rest}:
          Term.search(include_families, names, Term.SearchFound{Bool.or(Term.named(names, term), Bool.and(include_families, Positivity.is_member(names, Term.family(term)))), term, rest})
    case Term.SearchFound{found, term, rest}:
      match found:
        case True{}:
          True{}
        case False{}:
          Term.search(include_families, names, Term.SearchNodes{List.append(&2, F.Term.t, Term.children(term), rest)})

def Term.exists_all(include_families: Bool, names: List<&2, String>, work: List<&2, F.Term.t>) -> Bool:
  Term.search(include_families, names, Term.SearchNodes{work})

def Term.exists_name(include_families: Bool, names: List<&2, String>, term: F.Term.t) -> Bool:
  Term.exists_all(include_families, names, [term])

def Positivity.nonpositive_word() -> String:
  "a family that is not strictly positive arrives at M2"

def Positivity.occurs(names: List<&2, String>, term: F.Term.t) -> Bool:
  Term.exists_name(True{}, names, term)

def Positivity.absent_list(names: List<&2, String>, terms: List<&2, F.Term.t>) -> Result<&2, &2, F.Error.t, Unit>:
  U.Kernel.guard(Bool.not(Term.exists_all(True{}, names, terms)), F.Error.Not_yet{Positivity.nonpositive_word})

def Positivity.absent(names: List<&2, String>, term: F.Term.t) -> Result<&2, &2, F.Error.t, Unit>:
  Positivity.absent_list(names, [term])

type Positivity.Job is Data:
  Positivity.Positive{term: F.Term.t}
  Positivity.Absent{terms: List<&2, F.Term.t>}
  Positivity.Decide{valid: Bool, terms: List<&2, F.Term.t>}
  Positivity.Arrow{domain: Maybe<&2, F.Term.t>, term: F.Term.t, codomain: F.Term.t}
  Positivity.Project{domain: Maybe<&2, F.Term.t>, argument: Maybe<&2, F.Pair2<F.Quantity.t, F.Term.t>>, term: F.Term.t, head: F.Term.t}

# Positive positions recurse through codomains and projection heads, without a fuel cutoff.
@unsafe def Positivity.run(+names: List<&2, String>, jobs: List<&2, Positivity.Job>) -> Result<&2, &2, F.Error.t, Unit>:
  match jobs:
    case Nil{}:
      Done{Unit{}}
    case Con{job, rest}:
      match job:
        case Positivity.Absent{terms}:
          do Result<&2, &2, F.Error.t, Unit>:
            unit: Unit <- Positivity.absent_list(names, terms)
            Positivity.run(names, rest)
        case Positivity.Decide{valid, terms}:
          match valid:
            case True{}:
              Positivity.run(names, Con{Positivity.Absent{terms}, rest})
            case False{}:
              Fail{F.Error.Not_yet{Positivity.nonpositive_word}}
        case Positivity.Arrow{domain, term, codomain}:
          match domain:
            case None{}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case Some{dom}:
              Positivity.run(names, Con{Positivity.Absent{[dom]}, Con{Positivity.Positive{codomain}, rest}})
        case Positivity.Project{domain, argument, term, head}:
          match domain:
            case None{}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case Some{dom}:
              match argument:
                case None{}:
                  Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
                case Some{pair}:
                  F.Pair2{q, arg} = pair
                  Positivity.run(names, Con{Positivity.Absent{[arg]}, Con{Positivity.Positive{head}, rest}})
        case Positivity.Positive{+term}:
          match term:
            case F.Term.Lan{+shape, diagram}:
              Positivity.run(names, Con{Positivity.Decide{Bool.or(Positivity.is_member(names, F.Shape.family(F.Term.t, shape)), Bool.not(Positivity.occurs(names, term))), List.append(&2, F.Term.t, F.Shape.payload(F.Term.t, shape), [diagram])}, rest})
            case F.Term.Ran{shape, codomain}:
              Positivity.run(names, Con{Positivity.Arrow{F.Shape.point_dom(F.Term.t, shape), term, codomain}, rest})
            case F.Term.Out{shape, addr, head}:
              Positivity.run(names, Con{Positivity.Project{F.Shape.point_dom(F.Term.t, shape), F.Term.as_apt(addr), term, head}, rest})
            case F.Term.Global{name}:
              Positivity.run(names, rest)
            case F.Term.Var{index}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Univ{level}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.In{shape, addr, args}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Elim{elimination}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Sec{shape, legs}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Let{name, ty, value, body}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Ann{body, ty}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Lit{literal}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})
            case F.Term.Auto{}:
              Positivity.run(names, Con{Positivity.Absent{[term]}, rest})

def Positivity.positive(names: List<&2, String>, term: F.Term.t) -> Result<&2, &2, F.Error.t, Unit>:
  Positivity.run(names, [Positivity.Positive{term}])

def Positivity.fields(args: F.Positivity.telescope) -> List<&2, F.Term.t>:
  match args:
    case Nil{}:
      []
    case Con{arg, rest}:
      F.Triple3{q, name, ty} = arg
      Con{ty, Positivity.fields(rest)}

def Positivity.field_jobs(args: F.Positivity.telescope) -> List<&2, Positivity.Job>:
  match args:
    case Nil{}:
      []
    case Con{arg, rest}:
      F.Triple3{q, name, ty} = arg
      Con{Positivity.Positive{ty}, Positivity.field_jobs(rest)}

def Positivity.ctor_fields(names: List<&2, String>, args: F.Positivity.telescope) -> Result<&2, &2, F.Error.t, Unit>:
  Positivity.run(names, Positivity.field_jobs(args))

def Positivity.self_rec(names: List<&2, String>, args: F.Positivity.telescope) -> Bool:
  Term.exists_all(True{}, names, Positivity.fields(args))

def Positivity.find_ctor(+name: String, ctors: List<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:
  match ctors:
    case Nil{}:
      None{}
    case Con{+ctor, rest}:
      F.Positivity.Ctor{ctor_name, args, indices, arity, recursive} = ctor
      F.Data.choose(Maybe<&2, F.Positivity.ctor>, String.eq(name, ctor_name), Some{ctor}, Positivity.find_ctor(name, rest))

def Positivity.ctor_of(name: String, family: F.Positivity.family) -> Maybe<&2, F.Positivity.ctor>:
  F.Positivity.Family{family_name, params, indices, level, status, ctors, positive} = family
  Positivity.find_ctor(name, ctors)

def Totality.budget_msg() -> String:
  "the totality budget is exhausted"

type Totality.Job is Data:
  Totality.Spend{terms: List<&2, F.Term.t>, budget: C.Budget.t}
  Totality.Polled{poll: F.Pair2<Bool, C.Budget.t>, term: F.Term.t, rest: List<&2, F.Term.t>}

# Poll exactly once per original term node, in the original child order.
@unsafe def Totality.spend_loop(job: Totality.Job) -> F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>:
  match job:
    case Totality.Spend{terms, budget}:
      match terms:
        case Nil{}:
          F.Pair2{Done{Unit{}}, budget}
        case Con{term, rest}:
          Totality.spend_loop(Totality.Polled{C.Budget.poll(budget), term, rest})
    case Totality.Polled{poll, term, rest}:
      F.Pair2{exhausted, budget} = poll
      match exhausted:
        case True{}:
          F.Pair2{Fail{F.Error.Budget_exhausted{Totality.budget_msg}}, budget}
        case False{}:
          Totality.spend_loop(Totality.Spend{List.append(&2, F.Term.t, Term.children(term), rest), budget})

def Totality.spend_all(budget: C.Budget.t, terms: List<&2, F.Term.t>) -> F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>:
  Totality.spend_loop(Totality.Spend{terms, budget})

def Totality.spend(budget: C.Budget.t, term: F.Term.t) -> F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>:
  Totality.spend_all(budget, [term])

type Order.rule is Data:
  Order.Structural{}

type Order.status is Data:
  Order.Principal{}
  Order.Smaller{}
  Order.Other{}

type Order.step is Data:
  Order.Step{st_scrut: Nat, st_ctor: Maybe<&2, String>}

type Order.call is Data:
  Order.Call{cl_callee: String, cl_chain: List<&2, Order.step>}

type Order.row is Data:
  Order.Row{rw_member: String, rw_calls: List<&2, Order.call>}

type Order.t is Data:
  Order.Certificate{o_group: List<&2, String>, o_arg: Nat, o_rows: List<&2, Order.row>}

def Order.wrapper() -> Data:
  F.Pair2<F.Shape.t<F.Term.t>, F.Term.leg>

def Order.lam_binder(shape: F.Shape.t<F.Term.t>, leg: F.Term.leg, binder: Maybe<&2, F.Pair2<F.Quantity.t, String>>) -> Maybe<&2, Order.wrapper>:
  match binder:
    case None{}:
      None{}
    case Some{value}:
      Some{F.Pair2{shape, leg}}

def Order.lam_leg(shape: F.Shape.t<F.Term.t>, leg: Maybe<&2, F.Term.leg>) -> Maybe<&2, Order.wrapper>:
  match leg:
    case None{}:
      None{}
    case Some{+value}:
      F.Term.Leg{binders, body} = value
      Order.lam_binder(shape, value, U.Kernel.one(F.Pair2<F.Quantity.t, String>, binders))

def Order.lam_shape(shape: F.Shape.t<F.Term.t>, legs: List<&2, F.Term.leg>, point: Maybe<&2, F.Term.t>) -> Maybe<&2, Order.wrapper>:
  match point:
    case None{}:
      None{}
    case Some{domain}:
      Order.lam_leg(shape, U.Kernel.one(F.Term.leg, legs))

def Order.as_lam(term: F.Term.t) -> Maybe<&2, Order.wrapper>:
  match term:
    case F.Term.Sec{+shape, legs}:
      Order.lam_shape(shape, legs, F.Shape.point_dom(F.Term.t, shape))
    case F.Term.Var{index}:
      None{}
    case F.Term.Univ{level}:
      None{}
    case F.Term.Lan{shape, diagram}:
      None{}
    case F.Term.Ran{shape, diagram}:
      None{}
    case F.Term.In{shape, addr, args}:
      None{}
    case F.Term.Out{shape, addr, head}:
      None{}
    case F.Term.Elim{elimination}:
      None{}
    case F.Term.Let{name, ty, value, body}:
      None{}
    case F.Term.Ann{body, ty}:
      None{}
    case F.Term.Global{name}:
      None{}
    case F.Term.Lit{literal}:
      None{}
    case F.Term.Auto{}:
      None{}

def Order.as_var(term: F.Term.t) -> Maybe<&2, Nat>:
  match term:
    case F.Term.Var{index}:
      Some{index}
    case F.Term.Univ{level}:
      None{}
    case F.Term.Lan{shape, diagram}:
      None{}
    case F.Term.Ran{shape, diagram}:
      None{}
    case F.Term.In{shape, addr, args}:
      None{}
    case F.Term.Sec{shape, legs}:
      None{}
    case F.Term.Out{shape, addr, head}:
      None{}
    case F.Term.Elim{elimination}:
      None{}
    case F.Term.Let{name, ty, value, body}:
      None{}
    case F.Term.Ann{body, ty}:
      None{}
    case F.Term.Global{name}:
      None{}
    case F.Term.Lit{literal}:
      None{}
    case F.Term.Auto{}:
      None{}

type Order.Peel is Data:
  Order.Peeling{term: F.Term.t}
  Order.PeelNext{term: F.Term.t, wrapper: Maybe<&2, Order.wrapper>}

@unsafe def Order.unwrap_loop(job: Order.Peel, acc: List<&2, Order.wrapper>) -> F.Pair2<List<&2, Order.wrapper>, F.Term.t>:
  match job:
    case Order.Peeling{+term}:
      Order.unwrap_loop(Order.PeelNext{term, Order.as_lam(term)}, acc)
    case Order.PeelNext{term, wrapper}:
      match wrapper:
        case None{}:
          F.Pair2{List.reverse(&2, Order.wrapper, acc), term}
        case Some{+value}:
          F.Pair2{shape, leg} = value
          F.Term.Leg{binders, body} = leg
          Order.unwrap_loop(Order.Peeling{body}, Con{value, acc})

def Order.unwrap(term: F.Term.t) -> F.Pair2<List<&2, Order.wrapper>, F.Term.t>:
  Order.unwrap_loop(Order.Peeling{term}, [])

def Order.spine(+term: F.Term.t, args: List<&2, F.Term.t>, shapes: List<&2, F.Shape.t<F.Term.t>>) -> F.Triple3<F.Term.t, List<&2, F.Term.t>, List<&2, F.Shape.t<F.Term.t>>>:
  match term:
    case F.Term.Out{shape, addr, head}:
      match addr:
        case F.Term.APt{q, arg}:
          Order.spine(head, Con{arg, args}, Con{shape, shapes})
        case F.Term.ALeg{k}:
          F.Triple3{term, args, shapes}
        case F.Term.ACtor{name}:
          F.Triple3{term, args, shapes}
    case F.Term.Var{index}:
      F.Triple3{term, args, shapes}
    case F.Term.Univ{level}:
      F.Triple3{term, args, shapes}
    case F.Term.Lan{shape, diagram}:
      F.Triple3{term, args, shapes}
    case F.Term.Ran{shape, diagram}:
      F.Triple3{term, args, shapes}
    case F.Term.In{shape, addr, fields}:
      F.Triple3{term, args, shapes}
    case F.Term.Sec{shape, legs}:
      F.Triple3{term, args, shapes}
    case F.Term.Elim{elimination}:
      F.Triple3{term, args, shapes}
    case F.Term.Let{name, ty, value, body}:
      F.Triple3{term, args, shapes}
    case F.Term.Ann{body, ty}:
      F.Triple3{term, args, shapes}
    case F.Term.Global{name}:
      F.Triple3{term, args, shapes}
    case F.Term.Lit{literal}:
      F.Triple3{term, args, shapes}
    case F.Term.Auto{}:
      F.Triple3{term, args, shapes}

def Order.mentions(group: List<&2, String>, term: F.Term.t) -> Bool:
  Term.exists_name(False{}, group, term)

def Order.under(+status: Order.status, binders: List<&2, F.Pair2<F.Quantity.t, String>>, statuses: List<&2, Order.status>) -> List<&2, Order.status>:
  match binders:
    case Nil{}:
      statuses
    case Con{binder, rest}:
      Order.under(status, rest, Con{status, statuses})

def Order.under_indices(indices: List<&2, String>, statuses: List<&2, Order.status>) -> List<&2, Order.status>:
  match indices:
    case Nil{}:
      statuses
    case Con{name, rest}:
      Order.under_indices(rest, Con{Order.Other{}, statuses})

def Order.under_point(domain: Maybe<&2, F.Term.t>, statuses: List<&2, Order.status>) -> List<&2, Order.status>:
  match domain:
    case None{}:
      statuses
    case Some{dom}:
      Con{Order.Other{}, statuses}

def Order.is_smaller(status: Maybe<&2, Order.status>) -> Bool:
  match status:
    case None{}:
      False{}
    case Some{value}:
      match value:
        case Order.Smaller{}:
          True{}
        case Order.Principal{}:
          False{}
        case Order.Other{}:
          False{}

def Order.is_special(status: Maybe<&2, Order.status>) -> Bool:
  match status:
    case None{}:
      False{}
    case Some{value}:
      match value:
        case Order.Smaller{}:
          True{}
        case Order.Principal{}:
          True{}
        case Order.Other{}:
          False{}

def Order.guarded_var(statuses: List<&2, Order.status>, variable: Maybe<&2, Nat>) -> Bool:
  match variable:
    case None{}:
      False{}
    case Some{index}:
      Order.is_smaller(List.get(&2, Order.status, statuses, index))

def Order.guarded_arg(statuses: List<&2, Order.status>, argument: Maybe<&2, F.Term.t>) -> Bool:
  match argument:
    case None{}:
      False{}
    case Some{term}:
      Order.guarded_var(statuses, Order.as_var(term))

def Order.special_var(statuses: List<&2, Order.status>, variable: Maybe<&2, Nat>) -> Bool:
  match variable:
    case None{}:
      False{}
    case Some{index}:
      Order.is_special(List.get(&2, Order.status, statuses, index))

def Order.chain_at(special: Bool, variable: Maybe<&2, Nat>, addr: F.Term.addr, chain: List<&2, Order.step>) -> List<&2, Order.step>:
  match special:
    case False{}:
      chain
    case True{}:
      match variable:
        case None{}:
          chain
        case Some{index}:
          Con{Order.Step{index, F.Term.as_actor(addr)}, chain}

type Order.Job is Data:
  Order.Scan{statuses: List<&2, Order.status>, chain: List<&2, Order.step>, term: F.Term.t}
  Order.Spine{statuses: List<&2, Order.status>, chain: List<&2, Order.step>, spine: F.Triple3<F.Term.t, List<&2, F.Term.t>, List<&2, F.Shape.t<F.Term.t>>>}
  Order.SpineHead{statuses: List<&2, Order.status>, chain: List<&2, Order.step>, head: F.Term.t, args: List<&2, F.Term.t>}
  Order.Admit{valid: Bool}
  Order.CallCheck{member: Bool, guarded: Bool, name: String, chain: List<&2, Order.step>}

def Order.scan_list(terms: List<&2, F.Term.t>, +statuses: List<&2, Order.status>, +chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  match terms:
    case Nil{}:
      []
    case Con{term, rest}:
      Con{Order.Scan{statuses, chain, term}, Order.scan_list(rest, statuses, chain)}

def Order.scan_shape(shape: F.Shape.t<F.Term.t>, statuses: List<&2, Order.status>, chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  Order.scan_list(F.Shape.payload(F.Term.t, shape), statuses, chain)

def Order.scan_shapes(shapes: List<&2, F.Shape.t<F.Term.t>>, +statuses: List<&2, Order.status>, +chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  match shapes:
    case Nil{}:
      []
    case Con{shape, rest}:
      List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain), Order.scan_shapes(rest, statuses, chain))

def Order.scan_addr(addr: F.Term.addr, statuses: List<&2, Order.status>, chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  Order.scan_list(Term.addr_children(addr), statuses, chain)

def Order.scan_legs(legs: List<&2, F.Term.leg>, +statuses: List<&2, Order.status>, +chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  match legs:
    case Nil{}:
      []
    case Con{leg, rest}:
      F.Term.Leg{binders, body} = leg
      Con{Order.Scan{Order.under(Order.Other{}, binders, statuses), chain, body}, Order.scan_legs(rest, statuses, chain)}

def Order.scan_motive(motive: Maybe<&2, F.Term.motive>, statuses: List<&2, Order.status>, chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  match motive:
    case None{}:
      []
    case Some{value}:
      F.Term.Motive{ind, indices, self, body} = value
      [Order.Scan{Order.under_indices(indices, Con{Order.Other{}, statuses}), chain, body}]

def Order.scan_branches(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +statuses: List<&2, Order.status>, +chain: List<&2, Order.step>, +special: Bool, +variable: Maybe<&2, Nat>) -> List<&2, Order.Job>:
  match branches:
    case Nil{}:
      []
    case Con{branch, rest}:
      F.Pair2{+addr, leg} = branch
      F.Term.Leg{binders, body} = leg
      List.append(&2, Order.Job, Order.scan_addr(addr, statuses, chain),
        Con{Order.Scan{Order.under(F.Data.choose(Order.status, special, Order.Smaller{}, Order.Other{}), binders, statuses), Order.chain_at(special, variable, addr, chain), body}, Order.scan_branches(rest, statuses, chain, special, variable)})

def Order.scan_elim(elimination: F.Term.elim, +statuses: List<&2, Order.status>, +chain: List<&2, Order.step>) -> List<&2, Order.Job>:
  F.Term.Elimination{shape, +scrutinee, q, motive, branches} = elimination
  Con{Order.Scan{statuses, chain, scrutinee},
    List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
      List.append(&2, Order.Job, Order.scan_motive(motive, statuses, chain),
        Order.scan_branches(branches, statuses, chain, Order.special_var(statuses, Order.as_var(scrutinee)), Order.as_var(scrutinee))))}

# The driver preserves depth-first traversal, call order, and the constructor chain.
@unsafe def Order.run(+group: List<&2, String>, +argument: Nat, jobs: List<&2, Order.Job>, calls: List<&2, Order.call>) -> Maybe<&2, List<&2, Order.call>>:
  match jobs:
    case Nil{}:
      Some{List.reverse(&2, Order.call, calls)}
    case Con{job, rest}:
      match job:
        case Order.Admit{valid}:
          match valid:
            case False{}:
              None{}
            case True{}:
              Order.run(group, argument, rest, calls)
        case Order.CallCheck{member, guarded, name, chain}:
          match member:
            case False{}:
              Order.run(group, argument, rest, calls)
            case True{}:
              match guarded:
                case False{}:
                  None{}
                case True{}:
                  Order.run(group, argument, rest, Con{Order.Call{name, chain}, calls})
        case Order.Scan{+statuses, +chain, +term}:
          match term:
            case F.Term.Var{index}:
              Order.run(group, argument, rest, calls)
            case F.Term.Univ{level}:
              Order.run(group, argument, rest, calls)
            case F.Term.Global{name}:
              Order.run(group, argument, Con{Order.Admit{Bool.not(U.Kernel.member(group, name))}, rest}, calls)
            case F.Term.Lit{literal}:
              Order.run(group, argument, rest, calls)
            case F.Term.Auto{}:
              Order.run(group, argument, rest, calls)
            case F.Term.Lan{+shape, diagram}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
                Con{Order.Scan{Order.under_point(F.Shape.point_dom(F.Term.t, shape), statuses), chain, diagram}, rest}), calls)
            case F.Term.Ran{+shape, diagram}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
                Con{Order.Scan{Order.under_point(F.Shape.point_dom(F.Term.t, shape), statuses), chain, diagram}, rest}), calls)
            case F.Term.In{shape, addr, args}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
                List.append(&2, Order.Job, Order.scan_addr(addr, statuses, chain), List.append(&2, Order.Job, Order.scan_list(args, statuses, chain), rest))), calls)
            case F.Term.Sec{shape, legs}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
                List.append(&2, Order.Job, Order.scan_legs(legs, statuses, chain), rest)), calls)
            case F.Term.Out{shape, addr, head}:
              Order.run(group, argument, Con{Order.Spine{statuses, chain, Order.spine(term, [], [])}, rest}, calls)
            case F.Term.Elim{elimination}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_elim(elimination, statuses, chain), rest), calls)
            case F.Term.Let{name, ty, value, body}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, ty}, Con{Order.Scan{statuses, chain, value}, Con{Order.Scan{Con{Order.Other{}, statuses}, chain, body}, rest}}}, calls)
            case F.Term.Ann{body, ty}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, body}, Con{Order.Scan{statuses, chain, ty}, rest}}, calls)
        case Order.Spine{+statuses, +chain, spine}:
          F.Triple3{head, +args, shapes} = spine
          Order.run(group, argument, Con{Order.SpineHead{statuses, chain, head, args}, List.append(&2, Order.Job, Order.scan_shapes(shapes, statuses, chain), List.append(&2, Order.Job, Order.scan_list(args, statuses, chain), rest))}, calls)
        case Order.SpineHead{+statuses, +chain, +head, args}:
          match head:
            case F.Term.Global{+name}:
              Order.run(group, argument, Con{Order.CallCheck{U.Kernel.member(group, name), Order.guarded_arg(statuses, List.get(&2, F.Term.t, args, argument)), name, chain}, rest}, calls)
            case F.Term.Out{shape, addr, scrutinee}:
              Order.run(group, argument, List.append(&2, Order.Job, Order.scan_shape(shape, statuses, chain),
                List.append(&2, Order.Job, Order.scan_addr(addr, statuses, chain), Con{Order.Scan{statuses, chain, scrutinee}, rest})), calls)
            case F.Term.Var{index}:
              Order.run(group, argument, rest, calls)
            case F.Term.Univ{level}:
              Order.run(group, argument, rest, calls)
            case F.Term.Lit{literal}:
              Order.run(group, argument, rest, calls)
            case F.Term.Auto{}:
              Order.run(group, argument, rest, calls)
            case F.Term.Lan{shape, diagram}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.Ran{shape, diagram}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.In{shape, addr, fields}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.Sec{shape, legs}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.Elim{elimination}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.Let{name, ty, value, body}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)
            case F.Term.Ann{body, ty}:
              Order.run(group, argument, Con{Order.Scan{statuses, chain, head}, rest}, calls)

def Order.seed(formals: Nat, +argument: Nat) -> List<&2, Order.status>:
  match formals:
    case Zero{}:
      []
    case Succ{+rest}:
      Con{F.Data.choose(Order.status, Nat.is_eq(rest, argument), Order.Principal{}, Order.Other{}), Order.seed(rest, argument)}

def Order.passes(group: List<&2, String>, +argument: Nat, formals: Nat, body: F.Term.t) -> Maybe<&2, List<&2, Order.call>>:
  Order.run(group, argument, [Order.Scan{Order.seed(formals, argument), [], body}], [])

def Order.peeled_member(name: String, peeled: F.Pair2<List<&2, Order.wrapper>, F.Term.t>) -> F.Triple3<String, Nat, F.Term.t>:
  F.Pair2{wrappers, inner} = peeled
  F.Triple3{name, List.length(&2, Order.wrapper, wrappers), inner}

def Order.peeled(members: List<&2, F.Pair2<String, F.Term.t>>) -> List<&2, F.Triple3<String, Nat, F.Term.t>>:
  match members:
    case Nil{}:
      []
    case Con{member, rest}:
      F.Pair2{name, body} = member
      Con{Order.peeled_member(name, Order.unwrap(body)), Order.peeled(rest)}

def Order.group(members: List<&2, F.Pair2<String, F.Term.t>>) -> List<&2, String>:
  match members:
    case Nil{}:
      []
    case Con{member, rest}:
      F.Pair2{name, body} = member
      Con{name, Order.group(rest)}

def Order.bodies(members: List<&2, F.Pair2<String, F.Term.t>>) -> List<&2, F.Term.t>:
  match members:
    case Nil{}:
      []
    case Con{member, rest}:
      F.Pair2{name, body} = member
      Con{body, Order.bodies(rest)}

def Order.refusal(members: List<&2, F.Pair2<String, F.Term.t>>) -> F.Error.t:
  match members:
    case Nil{}:
      F.Error.Termination{""}
    case Con{member, rest}:
      F.Pair2{name, body} = member
      F.Error.Termination{name}

def Order.bound_update(mentions: Bool, formals: Nat, bound: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match mentions:
    case False{}:
      bound
    case True{}:
      match bound:
        case None{}:
          Some{formals}
        case Some{current}:
          Some{Nat.min(current, formals)}

def Order.bound_value(bound: Maybe<&2, Nat>) -> Nat:
  match bound:
    case None{}:
      0n
    case Some{value}:
      value

def Order.bound(+group: List<&2, String>, members: List<&2, F.Triple3<String, Nat, F.Term.t>>, acc: Maybe<&2, Nat>) -> Nat:
  match members:
    case Nil{}:
      Order.bound_value(acc)
    case Con{member, rest}:
      F.Triple3{name, formals, inner} = member
      Order.bound(group, rest, Order.bound_update(Order.mentions(group, inner), formals, acc))

def Order.row_cons(name: String, calls: Maybe<&2, List<&2, Order.call>>, rows: Maybe<&2, List<&2, Order.row>>) -> Maybe<&2, List<&2, Order.row>>:
  match calls:
    case None{}:
      None{}
    case Some{items}:
      match rows:
        case None{}:
          None{}
        case Some{tail}:
          Some{Con{Order.Row{name, items}, tail}}

def Order.rows_at(+group: List<&2, String>, +argument: Nat, members: List<&2, F.Triple3<String, Nat, F.Term.t>>) -> Maybe<&2, List<&2, Order.row>>:
  match members:
    case Nil{}:
      Some{[]}
    case Con{member, rest}:
      F.Triple3{name, formals, inner} = member
      Order.row_cons(name, Order.passes(group, argument, formals, inner), Order.rows_at(group, argument, rest))

type Order.Fit is Data:
  Order.TryPosition{position: Nat, remaining: Nat}
  Order.PositionRows{position: Nat, remaining: Nat, rows: Maybe<&2, List<&2, Order.row>>}

# The candidate count decreases after each refused position.
@unsafe def Order.first_fit(+group: List<&2, String>, +members: List<&2, F.Triple3<String, Nat, F.Term.t>>, error: F.Error.t, job: Order.Fit) -> Result<&2, &2, F.Error.t, Order.t>:
  match job:
    case Order.TryPosition{+position, remaining}:
      match remaining:
        case Zero{}:
          Fail{error}
        case Succ{more}:
          Order.first_fit(group, members, error, Order.PositionRows{position, more, Order.rows_at(group, position, members)})
    case Order.PositionRows{position, remaining, rows}:
      match rows:
        case None{}:
          Order.first_fit(group, members, error, Order.TryPosition{Succ{position}, remaining})
        case Some{items}:
          Done{Order.Certificate{group, position, items}}

def Order.certify_needed(needed: Bool, +group: List<&2, String>, +members: List<&2, F.Triple3<String, Nat, F.Term.t>>, error: F.Error.t) -> Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>:
  match needed:
    case False{}:
      Done{None{}}
    case True{}:
      do Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>:
        cert: Order.t <- Order.first_fit(group, members, error, Order.TryPosition{0n, Order.bound(group, members, None{})})
        return Some{cert}

def Order.certify(+members: List<&2, F.Pair2<String, F.Term.t>>) -> Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>:
  Order.certify_needed(Term.exists_all(False{}, Order.group(members), Order.bodies(members)), Order.group(members), Order.peeled(members), Order.refusal(members))

def Order.one_elim_msg() -> String:
  "a structurally recursive definition eliminates its recursive argument at the head of its body"

def Order.motive_msg() -> String:
  "the elimination of a structurally recursive definition carries its motive"

def Order.ctor_key_msg() -> String:
  "every branch of the elimination of a structurally recursive definition keys a constructor"

def Order.translate_index(+argument: Nat, +formals: Nat, variable: Maybe<&2, Nat>) -> Result<&2, &2, F.Error.t, Unit>:
  match variable:
    case None{}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case Some{index}:
      U.Kernel.guard(Bool.and(Nat.is_lt(argument, formals), Nat.is_eq(index, Nat.sub(Nat.sub(formals, 1n), argument))), F.Error.Mismatch{Order.one_elim_msg})

def Order.translate_branch(addr: F.Term.addr) -> Result<&2, &2, F.Error.t, Unit>:
  do Result<&2, &2, F.Error.t, Unit>:
    name: String <- U.Kernel.from_maybe(String, F.Term.as_actor(addr), F.Error.Wrong_leg{Order.ctor_key_msg})
    return Unit{}

def Order.translate_branches(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>) -> Result<&2, &2, F.Error.t, Unit>:
  match branches:
    case Nil{}:
      Done{Unit{}}
    case Con{branch, rest}:
      F.Pair2{addr, leg} = branch
      do Result<&2, &2, F.Error.t, Unit>:
        unit: Unit <- Order.translate_branch(addr)
        Order.translate_branches(rest)

def Order.translate_chain(name: String, chain: List<&2, Order.step>) -> Result<&2, &2, F.Error.t, Unit>:
  match chain:
    case Nil{}:
      Fail{F.Error.Termination{name}}
    case Con{step, rest}:
      Order.Step{scrutinee, ctor} = step
      do Result<&2, &2, F.Error.t, Unit>:
        value: String <- U.Kernel.from_maybe(String, ctor, F.Error.Termination{name})
        return Unit{}

def Order.translate_calls(+name: String, calls: List<&2, Order.call>) -> Result<&2, &2, F.Error.t, Unit>:
  match calls:
    case Nil{}:
      Done{Unit{}}
    case Con{call, rest}:
      Order.Call{callee, chain} = call
      do Result<&2, &2, F.Error.t, Unit>:
        unit: Unit <- Order.translate_chain(name, chain)
        Order.translate_calls(name, rest)

def Order.translate_rows(rows: List<&2, Order.row>) -> Result<&2, &2, F.Error.t, Unit>:
  match rows:
    case Nil{}:
      Done{Unit{}}
    case Con{row, rest}:
      Order.Row{name, calls} = row
      do Result<&2, &2, F.Error.t, Unit>:
        unit: Unit <- Order.translate_calls(name, calls)
        Order.translate_rows(rest)

def Order.translate_elim(argument: Nat, rows: List<&2, Order.row>, formals: Nat, elimination: F.Term.elim) -> Result<&2, &2, F.Error.t, Unit>:
  F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
  do Result<&2, &2, F.Error.t, Unit>:
    index: Unit <- Order.translate_index(argument, formals, Order.as_var(scrutinee))
    mot: F.Term.motive <- U.Kernel.from_maybe(F.Term.motive, motive, F.Error.Missing_branch{Order.motive_msg})
    branch: Unit <- Order.translate_branches(branches)
    Order.translate_rows(rows)

def Order.translate_inner(argument: Nat, rows: List<&2, Order.row>, formals: Nat, inner: F.Term.t) -> Result<&2, &2, F.Error.t, Unit>:
  match inner:
    case F.Term.Elim{elimination}:
      Order.translate_elim(argument, rows, formals, elimination)
    case F.Term.Var{index}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Univ{level}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Lan{shape, diagram}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Ran{shape, diagram}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.In{shape, addr, args}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Sec{shape, legs}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Out{shape, addr, head}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Let{name, ty, value, body}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Ann{body, ty}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Global{name}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Lit{literal}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}
    case F.Term.Auto{}:
      Fail{F.Error.Mismatch{Order.one_elim_msg}}

def Order.translate_peeled(argument: Nat, rows: List<&2, Order.row>, peeled: F.Pair2<List<&2, Order.wrapper>, F.Term.t>) -> Result<&2, &2, F.Error.t, Unit>:
  F.Pair2{wrappers, inner} = peeled
  Order.translate_inner(argument, rows, List.length(&2, Order.wrapper, wrappers), inner)

def Order.translate_needed(needed: Bool, cert: Order.t, +body: F.Term.t) -> Result<&2, &2, F.Error.t, F.Term.t>:
  match needed:
    case False{}:
      Done{body}
    case True{}:
      Order.Certificate{group, argument, rows} = cert
      do Result<&2, &2, F.Error.t, F.Term.t>:
        unit: Unit <- Order.translate_peeled(argument, rows, Order.unwrap(body))
        return body

def Order.translate(+cert: Order.t, +body: F.Term.t) -> Result<&2, &2, F.Error.t, F.Term.t>:
  Order.Certificate{group, argument, rows} = cert
  Order.translate_needed(Order.mentions(group, body), cert, body)

def Totality.certified(spent: F.Pair2<Result<&2, &2, F.Error.t, Unit>, C.Budget.t>, members: List<&2, F.Pair2<String, F.Term.t>>) -> F.Pair2<Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>, C.Budget.t>:
  F.Pair2{result, budget} = spent
  match result:
    case Fail{error}:
      F.Pair2{Fail{error}, budget}
    case Done{unit}:
      F.Pair2{Order.certify(members), budget}

def Totality.guard_group_stateful(budget: C.Budget.t, globals: F.Global.t, +members: List<&2, F.Pair2<String, F.Term.t>>) -> F.Pair2<Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>, C.Budget.t>:
  Totality.certified(Totality.spend_all(budget, Order.bodies(members)), members)

def Totality.guard_group(globals: F.Global.t, members: List<&2, F.Pair2<String, F.Term.t>>) -> Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>, C.Budget.t, Totality.guard_group_stateful(C.Budget.Unlimited{}, globals, members))

def Totality.argument(cert: Maybe<&2, Order.t>) -> Maybe<&2, Nat>:
  match cert:
    case None{}:
      None{}
    case Some{value}:
      Order.Certificate{group, argument, rows} = value
      Some{argument}

def Totality.guarded(result: F.Pair2<Result<&2, &2, F.Error.t, Maybe<&2, Order.t>>, C.Budget.t>) -> F.Pair2<Result<&2, &2, F.Error.t, Maybe<&2, Nat>>, C.Budget.t>:
  F.Pair2{answer, budget} = result
  F.Pair2{do Result<&2, &2, F.Error.t, Maybe<&2, Nat>>:
    cert: Maybe<&2, Order.t> <- answer
    return Totality.argument(cert), budget}

def Totality.guard_stateful(budget: C.Budget.t, globals: F.Global.t, name: String, ty: F.Term.t, body: F.Term.t) -> F.Pair2<Result<&2, &2, F.Error.t, Maybe<&2, Nat>>, C.Budget.t>:
  Totality.guarded(Totality.guard_group_stateful(budget, globals, [F.Pair2{name, body}]))

def Totality.guard(globals: F.Global.t, name: String, ty: F.Term.t, body: F.Term.t) -> Result<&2, &2, F.Error.t, Maybe<&2, Nat>>:
  U.Kernel.fst(Result<&2, &2, F.Error.t, Maybe<&2, Nat>>, C.Budget.t, Totality.guard_stateful(C.Budget.Unlimited{}, globals, name, ty, body))
