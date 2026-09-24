import Base
import ../../lib/foundation.bend as F
import ../../lib/kernel_context.bend as C
import ../../lib/kernel_eval.bend as E
import ../inline.bend as I
import ../../lib/erasure.bend as R

# A bounded semantic fixture for the sealing pass. Unsupported fixture types
# fail explicitly; full source elaboration is exercised by integration tests.
def univ_name(proof: Bool, name: String) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match proof:
    case True{}: Done{F.Level.zero}
    case False{}: Fail{F.Error.Unbound{name}}

def univ(checker: C.Check.ctx, ty: F.Term.t) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match ty:
    case F.Term.Global{+name}: univ_name(String.eq(name, "P"), name)
    case F.Term.Univ{level}: Done{F.Level.succ(level)}
    case F.Term.Ran{shape, body}: Done{F.Level.succ(F.Level.zero)}
    case other: Fail{F.Error.Cannot_infer{"outside sealing fixture"}}

def infer(+checker: C.Check.ctx, quantity: F.Quantity.t, term: F.Term.t) -> Result<&2, &2, F.Error.t, F.Value.t>:
  match term:
    case F.Term.Ann{value, ty}: E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), ty)
    case other: Fail{F.Error.Cannot_infer{"outside sealing fixture"}}

def semantics() -> I.Inline.Semantics:
  R.Erase.Semantics{+checker => term => F.Pair2{univ(checker,term),C.Check.budget(checker)}, +checker => quantity => term => F.Pair2{infer(checker,quantity,term),C.Check.budget(checker)}, E.Eval.quote}

def globals() -> F.Global.t:
  F.Global.add("P", F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.zero}}}, F.Global.empty)

def root(+g: F.Global.t) -> I.Inline.context:
  I.Inline.Context{C.Check.make(g, C.Budget.unlimited), Nil{}}

def sealed_type(found: Maybe<&2, F.Global.entry>, expected: F.Term.t) -> Bool:
  match found:
    case Some{F.Global.Axiom{F.Global.AxiomEntry{ty}}}: I.Inline.term_equal(ty, expected)
    case other: False{}

def sealed_result(result: I.Inline.walk_result, expected: F.Term.t, ty: F.Term.t, count: Nat) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{F.Pair2{term, I.Inline.State{g, next}}}:
      Bool.and(I.Inline.term_equal(term, expected), Bool.and(Nat.is_eq(next, count), sealed_type(F.Global.find("__attest_inline_proof_0", g), ty)))

def no_seal(result: I.Inline.walk_result, expected: F.Term.t) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{F.Pair2{term, I.Inline.State{g, next}}}: Bool.and(I.Inline.term_equal(term, expected), Nat.is_eq(next, 0n))

def mismatch(result: Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>) -> Bool:
  match result:
    case Fail{F.Error.Mismatch{message}}: String.eq(message, "erasure row differs from its environment: wrong")
    case other: False{}

def redeclared(result: Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>) -> Bool:
  match result:
    case Done{F.Pair2{globals, F.Pair2{name, a} <> F.Pair2{name2, b} <> Nil{}}}: I.Inline.entry_equal(a, b)
    case other: False{}

def main() -> List<&2, Bool>:
  +g = globals()
  +p : F.Term.t = F.Term.Global{"P"}
  +annotated : F.Term.t = F.Term.Ann{F.Term.Global{"missing_body"}, p}
  +shape : F.Shape.t<F.Term.t> = F.Shape.SPi{F.Quantity.Many{}, "h", p}
  +lambda : F.Term.t = F.Term.Sec{shape, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "h"}], F.Term.Var{0n}}]}
  +expected : F.Term.t = F.Term.Ran{shape, p}
  +postulate_shape : F.Shape.t<F.Term.t> = F.Shape.SPi{F.Quantity.Zero{}, "h", p}
  +replacement : F.Term.t = F.Term.Sec{shape, [F.Term.Leg{[F.Pair2{F.Quantity.Many{}, "h"}], F.Term.Out{postulate_shape, F.Term.APt{F.Quantity.Zero{}, F.Term.Var{0n}}, F.Term.Global{"__attest_inline_proof_0"}}}]}
  +old : F.Global.entry = F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.zero}}}
  +new : F.Global.entry = F.Global.Axiom{F.Global.AxiomEntry{F.Term.Univ{F.Level.succ(F.Level.zero)}}}
  +redefined = F.Global.add("value", new, g)
  [sealed_result(I.Inline.term(~semantics, root(g), I.Inline.State{g, 0n}, None{}, annotated), F.Term.Global{"__attest_inline_proof_0"}, p, 1n),
   sealed_result(I.Inline.term(~semantics, root(g), I.Inline.State{g, 0n}, Some{expected}, lambda), replacement, F.Term.Ran{postulate_shape, p}, 1n),
   no_seal(I.Inline.term(~semantics, root(g), I.Inline.State{g, 0n}, Some{p}, F.Term.Var{0n}), F.Term.Var{0n}),
   mismatch(I.Inline.prepare(~semantics, C.Check.make(g, C.Budget.unlimited), g, [F.Pair2{"wrong", old}])),
   redeclared(I.Inline.prepare(~semantics, C.Check.make(redefined, C.Budget.unlimited), redefined, [F.Pair2{"value", old}, F.Pair2{"value", new}]))]
