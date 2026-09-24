import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ./inline.bend as I
import ../lib/erasure.bend as R

def Opaque.contains(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}: False{}
    case h <> t: Bool.or(String.eq(h, name), Opaque.contains(t, name))

def Opaque.proof_name(proof: Bool, name: String, names: List<&2, String>) -> List<&2, String>:
  match proof:
    case True{}: name <> names
    case False{}: names

def Opaque.classify_entry(~infer_univ: F.Global.t -> F.Term.t -> Result<&2, &2, F.Error.t, F.Level.t>, entry: F.Global.entry, globals: F.Global.t, name: String, names: List<&2, String>) -> Result<&2, &2, F.Error.t, List<&2, String>>:
  match entry:
    case F.Global.Axiom{axiom}: Done{names}
    case F.Global.Prim{primitive}: Done{names}
    case F.Global.Def{F.Global.DefEntry{ty, body, reducible, recursive, partial}}:
      Result.bind(&2, &2, F.Error.t, F.Level.t, List<&2, String>, infer_univ(globals, ty), level =>
        Done{Opaque.proof_name(F.Level.equal(level, F.Level.zero), name, names)})

# Classification reads only declared types in the original checked globals.
# The definition body is deliberately not evaluated or traversed here.
def Opaque.proof_names(~infer_univ: F.Global.t -> F.Term.t -> Result<&2, &2, F.Error.t, F.Level.t>, entries: List<&2, F.Pair2<String, F.Global.entry>>, +globals: F.Global.t, names: List<&2, String>) -> Result<&2, &2, F.Error.t, List<&2, String>>:
  match entries:
    case Nil{}: Done{names}
    case F.Pair2{name, entry} <> rest:
      Result.bind(&2, &2, F.Error.t, List<&2, String>, List<&2, String>, Opaque.classify_entry(~infer_univ, entry, globals, name, names), next =>
        Opaque.proof_names(~infer_univ, rest, globals, next))

def Opaque.seal_definition(proof: Bool, definition: F.Global.def_entry) -> F.Global.entry:
  match proof:
    case True{}:
      F.Global.DefEntry{ty, body, reducible, recursive, partial} = definition
      F.Global.Axiom{F.Global.AxiomEntry{ty}}
    case False{}: F.Global.Def{definition}

def Opaque.seal(entry: F.Global.entry, names: List<&2, String>, name: String) -> F.Global.entry:
  match entry:
    case F.Global.Axiom{axiom}: F.Global.Axiom{axiom}
    case F.Global.Prim{primitive}: F.Global.Prim{primitive}
    case F.Global.Def{definition}: Opaque.seal_definition(Opaque.contains(names, name), definition)

def Opaque.seal_rows(rows: List<&2, F.Pair2<String, F.Global.entry>>, +names: List<&2, String>) -> List<&2, F.Pair2<String, F.Global.entry>>:
  match rows:
    case Nil{}: Nil{}
    case F.Pair2{+name, entry} <> rest:
      F.Pair2{name, Opaque.seal(entry, names, name)} <> Opaque.seal_rows(rest, names)

def Opaque.seal_checked(~infer_univ: F.Global.t -> F.Term.t -> Result<&2, &2, F.Error.t, F.Level.t>, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  +entries = F.Global.entries(globals)
  Result.bind(&2, &2, F.Error.t, List<&2, String>, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Opaque.proof_names(~infer_univ, entries, globals, Nil{}), +names =>
    Done{F.Pair2{F.Global.with_entries(Opaque.seal_rows(entries, names), globals), Opaque.seal_rows(rows, names)}})

def Opaque.checked_entry_state(~ops: I.Inline.Semantics, entry: F.Global.entry, checker: C.Check.ctx, name: String, names: List<&2, String>) -> R.Erase.State<List<&2, String>>:
  match entry:
    case F.Global.Axiom{axiom}: R.Erase.Return{names}
    case F.Global.Prim{primitive}: R.Erase.Return{names}
    case F.Global.Def{F.Global.DefEntry{ty, body, reducible, recursive, partial}}:
      I.Inline.bind_state(F.Level.t, List<&2, String>, I.Inline.call_univ_state(ops, checker, ty), level =>
        R.Erase.Return{Opaque.proof_name(F.Level.equal(level, F.Level.zero), name, names)})

def Opaque.checked_names_state(~ops: I.Inline.Semantics, entries: List<&2, F.Pair2<String, F.Global.entry>>, +checker: C.Check.ctx, names: List<&2, String>) -> R.Erase.State<List<&2, String>>:
  match entries:
    case Nil{}: R.Erase.Return{names}
    case F.Pair2{name, entry} <> rest:
      I.Inline.bind_state(List<&2, String>, List<&2, String>, Opaque.checked_entry_state(~ops, entry, checker, name, names), next =>
        Opaque.checked_names_state(~ops, rest, checker, next))

def Opaque.prepare_names_state(~ops: I.Inline.Semantics, +names: List<&2, String>, checker: C.Check.ctx, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> R.Erase.State<F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  entries = F.Global.entries(globals)
  I.Inline.prepare_state(~ops, checker, F.Global.with_entries(Opaque.seal_rows(entries, names), globals), Opaque.seal_rows(rows, names))

def Opaque.prepare_state(~ops: I.Inline.Semantics, budget: C.Budget.t, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> R.Erase.State<F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  +checker = C.Check.make(globals, budget)
  I.Inline.bind_state(List<&2, String>, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Opaque.checked_names_state(~ops, F.Global.entries(globals), checker, Nil{}), names =>
    Opaque.prepare_names_state(~ops, names, checker, globals, rows))

def Opaque.erase_prepared_state(~ops: I.Inline.Semantics, budget: C.Budget.t, prepared: F.Pair2<F.Global.t,List<&2,F.Pair2<String,F.Global.entry>>>) -> R.Erase.State<List<&2,F.Pair2<String,R.Erase.entry>>>:
  F.Pair2{globals,rows} = prepared
  R.Erase.program_state(~ops,budget,globals,rows)

def Opaque.program_state(~ops: I.Inline.Semantics, +budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> R.Erase.State<List<&2,F.Pair2<String,R.Erase.entry>>>:
  I.Inline.bind_state(F.Pair2<F.Global.t,List<&2,F.Pair2<String,F.Global.entry>>>,List<&2,F.Pair2<String,R.Erase.entry>>,Opaque.prepare_state(~ops,budget,globals,rows),prepared => Opaque.erase_prepared_state(~ops,budget,prepared))

def Opaque.prepare(~ops: I.Inline.Semantics, +budget: C.Budget.t, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>:
  R.Erase.State.finish(F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Opaque.prepare_state(~ops, budget, globals, rows), budget)

def Opaque.prepare_stateful(~ops: I.Inline.Semantics, +budget: C.Budget.t, +globals: F.Global.t, rows: List<&2, F.Pair2<String, F.Global.entry>>) -> F.Pair2<Result<&2, &2, F.Error.t, F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>>,C.Budget.t>:
  R.Erase.State.execute(F.Pair2<F.Global.t, List<&2, F.Pair2<String, F.Global.entry>>>, Opaque.prepare_state(~ops, budget, globals, rows), budget)

def Opaque.program(~ops: I.Inline.Semantics, +budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,R.Erase.entry>>>:
  R.Erase.State.finish(List<&2,F.Pair2<String,R.Erase.entry>>, Opaque.program_state(~ops, budget, globals, rows), budget)

def Opaque.program_stateful(~ops: I.Inline.Semantics, +budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> F.Pair2<Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,R.Erase.entry>>>,C.Budget.t>:
  R.Erase.State.execute(List<&2,F.Pair2<String,R.Erase.entry>>, Opaque.program_state(~ops, budget, globals, rows), budget)
