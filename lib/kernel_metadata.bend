import Base
import ./foundation.bend as F
import ./kernel_util.bend as U

# Each admitted shape carries its right and left eta capabilities.
def Rules.capability(+shape: F.Shape.t<F.Term.t>) -> Maybe<&2, F.Triple3<String, Bool, Bool>>:
  F.Shape.fold(F.Term.t, String, Maybe<&2, F.Triple3<String, Bool, Bool>>, shape, F.Shape.name(F.Term.t, shape),
    q => name => domain => label => Some{F.Triple3{label, True{}, True{}}},
    count => label => Some{F.Triple3{label, True{}, False{}}},
    left => right => label => None{},
    name => indices => label => Some{F.Triple3{label, False{}, False{}}},
    name => indices => label => None{})

def Rules.samples() -> List<&2, F.Shape.t<F.Term.t>>:
  [F.Shape.make_point(F.Term.t, F.Quantity.Many{}, "x", F.Term.Univ{F.Level.zero}), F.Shape.make_collection(F.Term.t, 0n),
   F.Shape.make_parallel(F.Term.t, F.Term.Univ{F.Level.zero}, F.Term.Univ{F.Level.zero}),
   F.Shape.make_inductive(F.Term.t, "x", Nil{}), F.Shape.make_coinductive(F.Term.t, "x", Nil{})]

def Rules.prepend(info: Maybe<&2, F.Triple3<String, Bool, Bool>>, rest: List<&2, F.Triple3<String, Bool, Bool>>)
  -> List<&2, F.Triple3<String, Bool, Bool>>:
  match info:
    case None{}: rest
    case Some{row}: Con{row, rest}

def Rules.packs_of(shapes: List<&2, F.Shape.t<F.Term.t>>) -> List<&2, F.Triple3<String, Bool, Bool>>:
  match shapes:
    case Nil{}: Nil{}
    case Con{shape, rest}: Rules.prepend(Rules.capability(shape), Rules.packs_of(rest))

def Rules.packs() -> List<&2, F.Triple3<String, Bool, Bool>>:
  Rules.packs_of(Rules.samples)

def Rules.names(rows: List<&2, F.Triple3<String, Bool, Bool>>) -> List<&2, String>:
  match rows:
    case Nil{}: Nil{}
    case Con{F.Triple3{name, right, left}, rest}: Con{name, Rules.names(rest)}

def Rules.admitted() -> List<&2, String>:
  Rules.names(Rules.packs)

def Rules.named_declared() -> List<&2, String>:
  ["proof-irrelevance", "subsingleton-large-elimination", "literal-fast-path"]

def Rules.named_present() -> List<&2, String>:
  Rules.named_declared

def SpecCount.at(items: List<&2, String>, n: Nat) -> String:
  match items:
    case Nil{}: "?"
    case Con{item, rest}:
      match n:
        case Zero{}: item
        case Succ{pred}: SpecCount.at(rest, pred)

def SpecCount.pick(n: Nat) -> String:
  SpecCount.at(F.Term.formers, n)

def SpecCount.choose(keep: Bool, row: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}: Con{row, rest}
    case False{}: rest

def SpecCount.same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}: b
    case False{}: Bool.not(b)

def SpecCount.eta_of(rows: List<&2, F.Triple3<String, Bool, Bool>>, +keep: Bool) -> List<&2, String>:
  match rows:
    case Nil{}: Nil{}
    case Con{F.Triple3{+name, right, left}, rest}:
      SpecCount.choose(SpecCount.same(right, keep), SpecCount.pick(1n) ++ "-" ++ name,
        SpecCount.choose(SpecCount.same(left, keep), SpecCount.pick(0n) ++ "-" ++ name, SpecCount.eta_of(rest, keep)))

def SpecCount.eta_rows() -> List<&2, String>:
  SpecCount.eta_of(Rules.packs, True{})

def SpecCount.no_eta() -> List<&2, String>:
  SpecCount.eta_of(Rules.packs, False{})

def SpecCount.row(label: String, +items: List<&2, String>) -> String:
  label ++ " " ++ F.Text.nat(List.length(&2, String, items)) ++ ": " ++ U.Kernel.join(items, " ") ++ "\n"

def SpecCount.print() -> String:
  String.concat([SpecCount.row("formers", F.Term.formers), SpecCount.row("schema constructors", F.Term.schema),
    SpecCount.row("shapes declared", F.Shape.declared), SpecCount.row("shapes admitted", Rules.admitted),
    SpecCount.row("named rules declared", Rules.named_declared), SpecCount.row("named rules present", Rules.named_present),
    SpecCount.row("eta rows", SpecCount.eta_rows), SpecCount.row("no eta", SpecCount.no_eta)])

def SpecCount.valid() -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, F.Term.formers), 2n), Nat.is_eq(List.length(&2, String, F.Shape.declared), 5n))
