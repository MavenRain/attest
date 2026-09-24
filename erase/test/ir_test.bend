import Base
import ../../lib/foundation.bend as F
import ../../lib/erasure.bend as E

def check_term(t: E.Eterm.ktm, want: String) -> Bool:
  String.eq(E.Eterm.print_ktm(t), want)

def check_lookup(found: E.Erase.found, want: Nat) -> Bool:
  match found:
    case E.Erase.LKeep{i}: Nat.is_eq(i, want)
    case other: False{}

def check_dropped(found: E.Erase.found) -> Bool:
  match found:
    case E.Erase.LDrop{}: True{}
    case other: False{}

def check_out(found: E.Erase.found) -> Bool:
  match found:
    case E.Erase.LOut{}: True{}
    case other: False{}

def check_pruned(p: F.Triple3<List<&2, E.Eterm.repr>, List<&2, E.Eterm.ktm>, E.Eterm.ktm>) -> Bool:
  F.Triple3{ps, args, body} = p
  Bool.and(String.eq(String.join(E.Eterm.repr_texts(ps), ","), "i31,union last"),
    Bool.and(String.eq(E.Eterm.print_task(E.Eterm.PrintTerms{args}), "KVar 7; KVar 9"),
      check_term(body, "KLet x (KVar 2) (KApp (KVar 0) [KVar 2; KVar 1; KVar 3])")))

def main() -> List<&2, Bool>:
  +slots : List<&2, E.Erase.slot> = [E.Erase.SExtra{}, E.Erase.SDrop{}, E.Erase.SKeep{}, E.Erase.SExtra{}, E.Erase.SKeep{}]
  +branch : E.Eterm.ktm = E.Eterm.KCase{E.Eterm.Tid{"sum"}, E.Eterm.KVar{2n}, [E.Eterm.Branch{1n, 2n, E.Eterm.KApp{E.Eterm.KVar{0n}, [E.Eterm.KVar{1n}, E.Eterm.KVar{2n}, E.Eterm.KVar{4n}]}}]}
  +captured : E.Eterm.ktm = E.Eterm.KLet{"x", E.Eterm.KVar{4n}, E.Eterm.KApp{E.Eterm.KVar{0n}, [E.Eterm.KVar{2n}, E.Eterm.KVar{1n}, E.Eterm.KVar{5n}]}}
  [check_term(E.Eterm.KVar{12n}, "KVar 12"),
   check_term(E.Eterm.KLit{F.Literal.LString{"a\n\t\r\u{8}\"\\"}}, "KLit \"a\\n\\t\\r\\b\\\"\\\\\""),
   check_term(E.Eterm.KLit{F.Literal.LInt{F.Bignum.of_int(123n)}}, "KLit 123"),
   check_term(E.Eterm.KErased{}, "KErased"),
   check_term(E.Eterm.KGlobal{"value"}, "KGlobal value"),
   check_term(E.Eterm.KLet{"x", E.Eterm.KVar{1n}, E.Eterm.KVar{0n}}, "KLet x (KVar 1) (KVar 0)"),
   check_term(E.Eterm.KClos{E.Eterm.Fid{"f"}, 2n, [E.Eterm.KVar{0n}]}, "KClos f 2 [KVar 0]"),
   check_term(E.Eterm.KApp{E.Eterm.KGlobal{"f"}, [E.Eterm.KErased{}, E.Eterm.KVar{0n}]}, "KApp (KGlobal f) [KErased; KVar 0]"),
   check_term(E.Eterm.KTail{E.Eterm.KGlobal{"f"}, Nil{}}, "KTail (KGlobal f) []"),
   check_term(E.Eterm.KStruct{E.Eterm.Tid{"pair"}, Nil{}}, "KStruct pair []"),
   check_term(E.Eterm.KProj{E.Eterm.Tid{"pair"}, 1n, E.Eterm.KVar{0n}}, "KProj pair 1 (KVar 0)"),
   check_term(E.Eterm.KTag{E.Eterm.Tid{"sum"}, 2n, [E.Eterm.KVar{1n}]}, "KTag sum 2 [KVar 1]"),
   check_term(E.Eterm.KCase{E.Eterm.Tid{"sum"}, E.Eterm.KVar{0n}, [E.Eterm.Branch{1n, 2n, E.Eterm.KVar{1n}}]}, "KCase sum (KVar 0) [{1 2 (KVar 1)}]"),
   check_term(E.Eterm.KDelay{E.Eterm.Fid{"d"}, [E.Eterm.KVar{0n}]}, "KDelay d [KVar 0]"),
   check_term(E.Eterm.KForce{E.Eterm.KVar{0n}}, "KForce (KVar 0)"),
   check_lookup(E.Erase.lookup(slots, 1n, 0n), 1n),
   check_lookup(E.Erase.lookup(slots, 2n, 0n), 3n),
   check_dropped(E.Erase.lookup(slots, 0n, 0n)),
   check_out(E.Erase.lookup(slots, 3n, 0n)),
   check_term(E.Erase.shift_runtime(3n, 0n, branch), "KCase sum (KVar 5) [{1 2 (KApp (KVar 0) [KVar 1; KVar 5; KVar 7])}]"),
   check_pruned(E.Erase.prune_captures([E.Eterm.RI31{}, E.Eterm.RUnion{E.Eterm.Tid{"dead"}}, E.Eterm.RUnion{E.Eterm.Tid{"dead2"}}, E.Eterm.RUnion{E.Eterm.Tid{"last"}}], [E.Eterm.KVar{7n}, E.Eterm.KVar{6n}, E.Eterm.KVar{8n}, E.Eterm.KVar{9n}], 1n, captured)),
   String.eq(E.Erase.print([F.Pair2{"P", E.Erase.Dropped{}}, F.Pair2{"a", E.Erase.Postulate{E.Eterm.RUnion{E.Eterm.Tid{"any"}}}}, F.Pair2{"f", E.Erase.Code{[E.Eterm.KRec{[E.Eterm.Tid{"T"}]}, E.Eterm.KFun{E.Eterm.Fid{"f"}, [E.Eterm.RI31{}], E.Eterm.RI31{}, E.Eterm.KVar{0n}}]}}]), "erased P\naxiom a : union any\nrec [T]\nfun f (i31) : i31 := KVar 0\n"),
   String.eq(String.join(E.Eterm.tid_texts(E.Erase.dedup_tids([E.Eterm.Tid{"B"}, E.Eterm.Tid{"A"}, E.Eterm.Tid{"B"}, E.Eterm.Tid{"C"}])), ","), "B,A,C")]
