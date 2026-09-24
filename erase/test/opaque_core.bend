import Base
import ../../lib/foundation.bend as F
import ../opaque.bend as O

def classify_name(proof: Bool, name: String) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match proof:
    case True{}: Done{F.Level.zero}
    case False{}: Fail{F.Error.Unbound{name}}

def classify(globals: F.Global.t, ty: F.Term.t) -> Result<&2, &2, F.Error.t, F.Level.t>:
  match ty:
    case F.Term.Global{+name}: classify_name(String.eq(name, "P"), name)
    case F.Term.Univ{level}: Done{F.Level.succ(level)}
    case other: Fail{F.Error.Cannot_infer{"test classification"}}

def sealed(entry: F.Global.entry) -> Bool:
  match entry:
    case F.Global.Axiom{F.Global.AxiomEntry{F.Term.Global{name}}}: String.eq(name, "P")
    case other: False{}

def retained(entry: F.Global.entry) -> Bool:
  match entry:
    case F.Global.Def{F.Global.DefEntry{ty, F.Term.Global{name}, reducible, recursive, partial}}: String.eq(name, "runtime")
    case other: False{}

def rows_check(rows: List<&2, F.Pair2<String, F.Global.entry>>) -> Bool:
  match rows:
    case F.Pair2{name1, p} <> F.Pair2{name2, d} <> Nil{}:
      Bool.and(String.eq(name1, "proof"), Bool.and(String.eq(name2, "data"), Bool.and(sealed(p), retained(d))))
    case other: False{}

def result_check(result: Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>) -> Bool:
  match result:
    case Fail{error}: False{}
    case Done{F.Pair2{globals, rows}}:
      Bool.and(rows_check(F.Global.entries(globals)), rows_check(rows))

def failed(result: Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>) -> Bool:
  match result:
    case Fail{F.Error.Unbound{name}}: String.eq(name, "missing_type")
    case other: False{}

def inherited_rows(rows: List<&2, F.Pair2<String, F.Global.entry>>) -> Bool:
  match rows:
    case F.Pair2{name, entry} <> Nil{}: sealed(entry)
    case other: False{}

def inherited(result: Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>) -> Bool:
  match result:
    case Done{F.Pair2{globals, Nil{}}}: inherited_rows(F.Global.entries(globals))
    case other: False{}

def main() -> List<&2, Bool>:
  +proof : F.Global.entry = F.Global.Def{F.Global.DefEntry{F.Term.Global{"P"}, F.Term.Global{"missing_body"}, True{}, None{}, False{}}}
  +data : F.Global.entry = F.Global.Def{F.Global.DefEntry{F.Term.Univ{F.Level.zero}, F.Term.Global{"runtime"}, True{}, None{}, False{}}}
  +rows : List<&2, F.Pair2<String, F.Global.entry>> = [F.Pair2{"proof", proof}, F.Pair2{"data", data}]
  +bad : F.Global.entry = F.Global.Def{F.Global.DefEntry{F.Term.Global{"missing_type"}, F.Term.Global{"missing_body"}, True{}, None{}, False{}}}
  [result_check(O.Opaque.seal_checked(~classify, F.Global.from_rows(rows, Nil{}), rows)),
   failed(O.Opaque.seal_checked(~classify, F.Global.from_rows([F.Pair2{"proof", bad}], Nil{}), Nil{})),
   inherited(O.Opaque.seal_checked(~classify, F.Global.from_rows([F.Pair2{"proof", proof}], Nil{}), Nil{})),
   sealed(O.Opaque.seal(proof, ["proof"], "proof")),
   retained(O.Opaque.seal(data, ["proof"], "data"))]
