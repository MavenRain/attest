import Base
import ./foundation.bend as F
import ./kernel_context.bend as C
import ./kernel_eval.bend as E
import ./kernel_primitives.bend as P

# Pure state threads one shared checking budget through every classifier.
# Return/Raise keep pure computations cheap; Pending defers checked queries.
type Erase.State<-A: Data> is Type:
  Erase.Return{value:A}
  Erase.Raise{error:F.Error.t}
  Erase.Pending{run:C.Budget.t -> F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>}

def Erase.State.execute(-A:Data,state:Erase.State<A>,budget:C.Budget.t) -> F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>:
  match state:
    case Erase.Return{value}: F.Pair2{Done{value},budget}
    case Erase.Raise{error}: F.Pair2{Fail{error},budget}
    case Erase.Pending{run}: run(budget)

def Erase.State.bound(-A:Data,-B:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>,next:A -> Erase.State<B>) -> F.Pair2<Result<&2,&2,F.Error.t,B>,C.Budget.t>:
  match result:
    case F.Pair2{Fail{error},budget}: F.Pair2{Fail{error},budget}
    case F.Pair2{Done{value},budget}: Erase.State.execute(B,next(value),budget)

def Erase.State.bind(-A:Data,-B:Data,state:Erase.State<A>,next:A -> Erase.State<B>) -> Erase.State<B>:
  match state:
    case Erase.Return{value}: next(value)
    case Erase.Raise{error}: Erase.Raise{error}
    case Erase.Pending{run}: Erase.Pending{budget => Erase.State.bound(A,B,run(budget),next)}

def Erase.State.pure(-A:Data,value:A) -> Erase.State<A>:
  Erase.Return{value}

def Erase.State.lift(-A:Data,result:Result<&2,&2,F.Error.t,A>) -> Erase.State<A>:
  match result:
    case Done{value}: Erase.Return{value}
    case Fail{error}: Erase.Raise{error}

def Erase.State.attempted(-A:Data,-B:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>,next:Result<&2,&2,F.Error.t,A> -> Erase.State<B>) -> F.Pair2<Result<&2,&2,F.Error.t,B>,C.Budget.t>:
  F.Pair2{value,budget} = result
  Erase.State.execute(B,next(value),budget)

def Erase.State.attempt(-A:Data,-B:Data,state:Erase.State<A>,next:Result<&2,&2,F.Error.t,A> -> Erase.State<B>) -> Erase.State<B>:
  Erase.Pending{budget => Erase.State.attempted(A,B,Erase.State.execute(A,state,budget),next)}

def Erase.State.result(-A:Data,result:F.Pair2<Result<&2,&2,F.Error.t,A>,C.Budget.t>) -> Result<&2,&2,F.Error.t,A>:
  F.Pair2{value,budget} = result
  value

def Erase.State.finish(-A:Data,state:Erase.State<A>,budget:C.Budget.t) -> Result<&2,&2,F.Error.t,A>:
  Erase.State.result(A,Erase.State.execute(A,state,budget))

# Closed template adapters connect the erasure passes to the checked kernel.
# The record contains real operations, with no default or fallback checker.
type Erase.Semantics is Type:
  Erase.Semantics{
    infer_univ: C.Check.ctx -> F.Term.t -> F.Pair2<Result<&2,&2,F.Error.t,F.Level.t>,C.Budget.t>,
    infer: C.Check.ctx -> F.Quantity.t -> F.Term.t -> F.Pair2<Result<&2,&2,F.Error.t,F.Value.t>,C.Budget.t>,
    quote: F.Global.t -> Nat -> F.Value.t -> Result<&2,&2,F.Error.t,F.Term.t>}

def Erase.with_budget(ctx:C.Check.ctx,budget:C.Budget.t) -> C.Check.ctx:
  C.Check.Ctx{globals,env,locals,size,old} = ctx
  C.Check.Ctx{globals,env,locals,size,budget}

def Erase.semantic_univ_state(ops:Erase.Semantics,checker:C.Check.ctx,term:F.Term.t) -> Erase.State<F.Level.t>:
  Erase.Semantics{universe,infer,quote} = ops
  Erase.Pending{budget => universe(Erase.with_budget(checker,budget),term)}

def Erase.semantic_infer_state(ops:Erase.Semantics,checker:C.Check.ctx,quantity:F.Quantity.t,term:F.Term.t) -> Erase.State<F.Value.t>:
  Erase.Semantics{universe,infer,quote} = ops
  Erase.Pending{budget => infer(Erase.with_budget(checker,budget),quantity,term)}

def Erase.semantic_quote_state(ops:Erase.Semantics,globals:F.Global.t,size:Nat,value:F.Value.t) -> Erase.State<F.Term.t>:
  Erase.Semantics{universe,infer,quote} = ops
  Erase.State.lift(F.Term.t,quote(globals,size,value))

type Eterm.tid is Data:
  Eterm.Tid{text: String}

type Eterm.fid is Data:
  Eterm.Fid{text: String}

type Eterm.repr is Data:
  Eterm.RI31{}
  Eterm.RStruct{tid: Eterm.tid}
  Eterm.RUnion{tid: Eterm.tid}
  Eterm.RFunc{tid: Eterm.tid}
  Eterm.RThunk{tid: Eterm.tid}

type Eterm.branch<-T: Data> is Data:
  Eterm.Branch{tag: Nat, arity: Nat, body: T}

type Eterm.ktm is Data:
  Eterm.KVar{index: Nat}
  Eterm.KLit{literal: F.Literal.t}
  Eterm.KGlobal{name: String}
  Eterm.KErased{}
  Eterm.KLet{name: String, value: Eterm.ktm, body: Eterm.ktm}
  Eterm.KClos{fid: Eterm.fid, arity: Nat, captures: List<&2, Eterm.ktm>}
  Eterm.KApp{head: Eterm.ktm, args: List<&2, Eterm.ktm>}
  Eterm.KTail{head: Eterm.ktm, args: List<&2, Eterm.ktm>}
  Eterm.KStruct{tid: Eterm.tid, fields: List<&2, Eterm.ktm>}
  Eterm.KProj{tid: Eterm.tid, index: Nat, value: Eterm.ktm}
  Eterm.KTag{tid: Eterm.tid, tag: Nat, fields: List<&2, Eterm.ktm>}
  Eterm.KCase{tid: Eterm.tid, scrutinee: Eterm.ktm, branches: List<&2, Eterm.branch<Eterm.ktm>>}
  Eterm.KDelay{fid: Eterm.fid, captures: List<&2, Eterm.ktm>}
  Eterm.KForce{value: Eterm.ktm}

type Eterm.kdecl is Data:
  Eterm.KFun{fid: Eterm.fid, params: List<&2, Eterm.repr>, result: Eterm.repr, body: Eterm.ktm}
  Eterm.KRec{tids: List<&2, Eterm.tid>}

def Eterm.tid_text(t: Eterm.tid) -> String:
  Eterm.Tid{text} = t
  text

def Eterm.fid_text(f: Eterm.fid) -> String:
  Eterm.Fid{text} = f
  text

def Eterm.choose(test: Bool, yes: String, no: String) -> String:
  match test:
    case True{}: yes
    case False{}: no

def Eterm.escape_char(+c: Char) -> String:
  +n = Char.to_u32(c)
  decimal = "\\" ++ U32.show((n / 100 : U32)) ++ U32.show(((n / 10 : U32) % 10 : U32)) ++ U32.show((n % 10 : U32))
  printable = Eterm.choose(Bool.and(U32.is_ge(n, 32), U32.is_lt(n, 127)), SCon{c, SNil{}}, decimal)
  backspace = Eterm.choose(U32.is_eq(n, 8), "\\b", printable)
  carriage = Eterm.choose(U32.is_eq(n, 13), "\\r", backspace)
  tab = Eterm.choose(U32.is_eq(n, 9), "\\t", carriage)
  newline = Eterm.choose(U32.is_eq(n, 10), "\\n", tab)
  slash = Eterm.choose(U32.is_eq(n, 92), "\\\\", newline)
  Eterm.choose(U32.is_eq(n, 34), "\\\"", slash)

def Eterm.escape(s: String) -> String:
  match s:
    case SNil{}: ""
    case SCon{h, t}: Eterm.escape_char(h) ++ Eterm.escape(t)

def Eterm.literal_text(l: F.Literal.t) -> String:
  match l:
    case F.Literal.LString{s}: "\"" ++ Eterm.escape(s) ++ "\""
    case F.Literal.LInt{n}: F.Bignum.to_string(n)

def Eterm.print_repr(r: Eterm.repr) -> String:
  match r:
    case Eterm.RI31{}: "i31"
    case Eterm.RStruct{t}: "struct " ++ Eterm.tid_text(t)
    case Eterm.RUnion{t}: "union " ++ Eterm.tid_text(t)
    case Eterm.RFunc{t}: "func " ++ Eterm.tid_text(t)
    case Eterm.RThunk{t}: "thunk " ++ Eterm.tid_text(t)

type Eterm.PrintTask is Data:
  Eterm.PrintTerm{term: Eterm.ktm}
  Eterm.PrintTerms{terms: List<&2, Eterm.ktm>}
  Eterm.PrintBranches{branches: List<&2, Eterm.branch<Eterm.ktm>>}

def Eterm.separator(-T: Data, xs: List<&2, T>) -> String:
  match xs:
    case Nil{}: ""
    case h <> t: "; "

# Each recursive call consumes a strict syntax child or list tail. The task
# union exposes OCaml's mutually recursive printer as one unbounded traversal.
@unsafe
def Eterm.print_task(task: Eterm.PrintTask) -> String:
  match task:
    case Eterm.PrintTerms{terms}:
      match terms:
        case Nil{}: ""
        case h <> +t:
          Eterm.print_task(Eterm.PrintTerm{h}) ++ Eterm.separator(Eterm.ktm, t) ++ Eterm.print_task(Eterm.PrintTerms{t})
    case Eterm.PrintBranches{branches}:
      match branches:
        case Nil{}: ""
        case Eterm.Branch{tag, arity, body} <> +t:
          "{" ++ Nat.show(tag) ++ " " ++ Nat.show(arity) ++ " (" ++ Eterm.print_task(Eterm.PrintTerm{body}) ++ ")}" ++ Eterm.separator(Eterm.branch<Eterm.ktm>, t) ++ Eterm.print_task(Eterm.PrintBranches{t})
    case Eterm.PrintTerm{term}:
      match term:
        case Eterm.KVar{i}: "KVar " ++ Nat.show(i)
        case Eterm.KLit{l}: "KLit " ++ Eterm.literal_text(l)
        case Eterm.KGlobal{n}: "KGlobal " ++ n
        case Eterm.KErased{}: "KErased"
        case Eterm.KLet{x, v, b}: "KLet " ++ x ++ " (" ++ Eterm.print_task(Eterm.PrintTerm{v}) ++ ") (" ++ Eterm.print_task(Eterm.PrintTerm{b}) ++ ")"
        case Eterm.KClos{f, n, cs}: "KClos " ++ Eterm.fid_text(f) ++ " " ++ Nat.show(n) ++ " [" ++ Eterm.print_task(Eterm.PrintTerms{cs}) ++ "]"
        case Eterm.KApp{h, args}: "KApp (" ++ Eterm.print_task(Eterm.PrintTerm{h}) ++ ") [" ++ Eterm.print_task(Eterm.PrintTerms{args}) ++ "]"
        case Eterm.KTail{h, args}: "KTail (" ++ Eterm.print_task(Eterm.PrintTerm{h}) ++ ") [" ++ Eterm.print_task(Eterm.PrintTerms{args}) ++ "]"
        case Eterm.KStruct{t, fs}: "KStruct " ++ Eterm.tid_text(t) ++ " [" ++ Eterm.print_task(Eterm.PrintTerms{fs}) ++ "]"
        case Eterm.KProj{t, k, x}: "KProj " ++ Eterm.tid_text(t) ++ " " ++ Nat.show(k) ++ " (" ++ Eterm.print_task(Eterm.PrintTerm{x}) ++ ")"
        case Eterm.KTag{t, k, ps}: "KTag " ++ Eterm.tid_text(t) ++ " " ++ Nat.show(k) ++ " [" ++ Eterm.print_task(Eterm.PrintTerms{ps}) ++ "]"
        case Eterm.KCase{t, s, bs}: "KCase " ++ Eterm.tid_text(t) ++ " (" ++ Eterm.print_task(Eterm.PrintTerm{s}) ++ ") [" ++ Eterm.print_task(Eterm.PrintBranches{bs}) ++ "]"
        case Eterm.KDelay{f, cs}: "KDelay " ++ Eterm.fid_text(f) ++ " [" ++ Eterm.print_task(Eterm.PrintTerms{cs}) ++ "]"
        case Eterm.KForce{x}: "KForce (" ++ Eterm.print_task(Eterm.PrintTerm{x}) ++ ")"

def Eterm.print_ktm(t: Eterm.ktm) -> String:
  Eterm.print_task(Eterm.PrintTerm{t})

def Eterm.repr_texts(rs: List<&2, Eterm.repr>) -> List<&2, String>:
  match rs:
    case Nil{}: Nil{}
    case r <> rest: Eterm.print_repr(r) <> Eterm.repr_texts(rest)

def Eterm.tid_texts(ts: List<&2, Eterm.tid>) -> List<&2, String>:
  match ts:
    case Nil{}: Nil{}
    case t <> rest: Eterm.tid_text(t) <> Eterm.tid_texts(rest)

def Eterm.print_decl(d: Eterm.kdecl) -> String:
  match d:
    case Eterm.KFun{f, params, result, body}:
      "fun " ++ Eterm.fid_text(f) ++ " (" ++ String.join(Eterm.repr_texts(params), ", ") ++ ") : " ++ Eterm.print_repr(result) ++ " := " ++ Eterm.print_ktm(body)
    case Eterm.KRec{ts}: "rec [" ++ String.join(Eterm.tid_texts(ts), "; ") ++ "]"

type Erase.entry is Data:
  Erase.Dropped{}
  Erase.Postulate{repr: Eterm.repr}
  Erase.Code{decls: List<&2, Eterm.kdecl>}

type Erase.slot is Data:
  Erase.SDrop{}
  Erase.SKeep{}
  Erase.SExtra{}

type Erase.found is Data:
  Erase.LKeep{index: Nat}
  Erase.LDrop{}
  Erase.LOut{}

def Erase.lookup(slots: List<&2, Erase.slot>, ix: Nat, seen: Nat) -> Erase.found:
  match slots:
    case Nil{}: Erase.LOut{}
    case s <> rest:
      match s:
        case Erase.SExtra{}: Erase.lookup(rest, ix, (seen + 1n : Nat))
        case Erase.SKeep{}:
          match ix:
            case 0n: Erase.LKeep{seen}
            case 1n+p: Erase.lookup(rest, p, (seen + 1n : Nat))
        case Erase.SDrop{}:
          match ix:
            case 0n: Erase.LDrop{}
            case 1n+p: Erase.lookup(rest, p, seen)

def Erase.print_code(ds: List<&2, Eterm.kdecl>) -> String:
  match ds:
    case Nil{}: ""
    case d <> rest: Eterm.print_decl(d) ++ "\n" ++ Erase.print_code(rest)

def Erase.print_entry(name: String, e: Erase.entry) -> String:
  match e:
    case Erase.Dropped{}: "erased " ++ name ++ "\n"
    case Erase.Postulate{r}: "axiom " ++ name ++ " : " ++ Eterm.print_repr(r) ++ "\n"
    case Erase.Code{ds}: Erase.print_code(ds)

def Erase.print(rows: List<&2, F.Pair2<String, Erase.entry>>) -> String:
  match rows:
    case Nil{}: ""
    case F.Pair2{name, e} <> rest: Erase.print_entry(name, e) ++ Erase.print(rest)

def Erase.append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}: ys
    case h <> t: h <> Erase.append(A, t, ys)

def Erase.length(-A: Data, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}: 0n
    case h <> t: 1n+Erase.length(A, t)

def Erase.var_at(test: Bool, ix: Nat, depth: Nat) -> List<&2, Nat>:
  match test:
    case True{}: [(ix - depth : Nat)]
    case False{}: Nil{}

def Erase.runtime_children(xs: List<&2, Eterm.ktm>, +depth: Nat) -> List<&2, F.Pair2<Nat, Eterm.ktm>>:
  match xs:
    case Nil{}: Nil{}
    case h <> t: F.Pair2{depth, h} <> Erase.runtime_children(t, depth)

def Erase.runtime_branches(xs: List<&2, Eterm.branch<Eterm.ktm>>, +depth: Nat) -> List<&2, F.Pair2<Nat, Eterm.ktm>>:
  match xs:
    case Nil{}: Nil{}
    case Eterm.Branch{tag, arity, body} <> t:
      F.Pair2{(depth + arity : Nat), body} <> Erase.runtime_branches(t, depth)

def Erase.ktm_children(t: Eterm.ktm, +depth: Nat) -> List<&2, F.Pair2<Nat, Eterm.ktm>>:
  match t:
    case Eterm.KVar{i}: Nil{}
    case Eterm.KLit{l}: Nil{}
    case Eterm.KGlobal{n}: Nil{}
    case Eterm.KErased{}: Nil{}
    case Eterm.KLet{x, v, b}: [F.Pair2{depth, v}, F.Pair2{1n+depth, b}]
    case Eterm.KClos{f, n, cs}: Erase.runtime_children(cs, depth)
    case Eterm.KApp{h, args}: F.Pair2{depth, h} <> Erase.runtime_children(args, depth)
    case Eterm.KTail{h, args}: F.Pair2{depth, h} <> Erase.runtime_children(args, depth)
    case Eterm.KStruct{t, fs}: Erase.runtime_children(fs, depth)
    case Eterm.KProj{t, k, x}: [F.Pair2{depth, x}]
    case Eterm.KTag{t, k, ps}: Erase.runtime_children(ps, depth)
    case Eterm.KCase{t, s, bs}: F.Pair2{depth, s} <> Erase.runtime_branches(bs, depth)
    case Eterm.KDelay{f, cs}: Erase.runtime_children(cs, depth)
    case Eterm.KForce{x}: [F.Pair2{depth, x}]

@unsafe
def Erase.runtime_vars_tasks(tasks: List<&2, F.Pair2<Nat, Eterm.ktm>>) -> List<&2, Nat>:
  match tasks:
    case Nil{}: Nil{}
    case F.Pair2{+depth, term} <> rest:
      match term:
        case Eterm.KVar{+ix}:
          Erase.append(Nat, Erase.var_at(Nat.is_ge(ix, depth), ix, depth), Erase.runtime_vars_tasks(rest))
        case other:
          Erase.runtime_vars_tasks(Erase.append(F.Pair2<Nat, Eterm.ktm>, Erase.ktm_children(other, depth), rest))

def Erase.runtime_vars(depth: Nat, term: Eterm.ktm) -> List<&2, Nat>:
  Erase.runtime_vars_tasks([F.Pair2{depth, term}])

def Erase.bool_nat(b: Bool) -> Nat:
  match b:
    case True{}: 1n
    case False{}: 0n

def Erase.count_below(xs: List<&2, Nat>, +bound: Nat) -> Nat:
  match xs:
    case Nil{}: 0n
    case h <> t:
      (Erase.bool_nat(Nat.is_lt(h, bound)) + Erase.count_below(t, bound) : Nat)

type Erase.IndexMap is Data:
  Erase.Shift{by: Nat}
  Erase.Prune{params: Nat, live: List<&2, Nat>}

def Erase.prune_index(local: Bool, i: Nat, +params: Nat, live: List<&2, Nat>) -> Nat:
  match local:
    case True{}: i
    case False{}: (params + Erase.count_below(live, (i - params : Nat)) : Nat)

def Erase.map_index(mapping: Erase.IndexMap, +i: Nat) -> Nat:
  match mapping:
    case Erase.Shift{by}: (i + by : Nat)
    case Erase.Prune{+params, live}: Erase.prune_index(Nat.is_lt(i, params), i, params, live)

def Erase.reindex_var(outside: Bool, mapping: Erase.IndexMap, +depth: Nat, i: Nat) -> Eterm.ktm:
  match outside:
    case True{}: Eterm.KVar{(depth + Erase.map_index(mapping, (i - depth : Nat)) : Nat)}
    case False{}: Eterm.KVar{i}

type Erase.ReindexTask is Type:
  Erase.ReindexTerm{term: Eterm.ktm, depth: Nat, done: Eterm.ktm -> Eterm.ktm}
  Erase.ReindexTerms{terms: List<&2, Eterm.ktm>, depth: Nat, done: List<&2, Eterm.ktm> -> Eterm.ktm}
  Erase.ReindexBranches{branches: List<&2, Eterm.branch<Eterm.ktm>>, depth: Nat, done: List<&2, Eterm.branch<Eterm.ktm>> -> Eterm.ktm}

# Continuations retain the type of each result, so no partial list projection
# or synthetic fallback is needed when replacing mutually recursive maps.
@unsafe
def Erase.reindex_task(task: Erase.ReindexTask, +mapping: Erase.IndexMap) -> Eterm.ktm:
  match task:
    case Erase.ReindexTerms{terms, +depth, done}:
      match terms:
        case Nil{}: done(Nil{})
        case h <> t:
          Erase.reindex_task(Erase.ReindexTerm{h, depth, x =>
            Erase.reindex_task(Erase.ReindexTerms{t, depth, xs => done(x <> xs)}, mapping)}, mapping)
    case Erase.ReindexBranches{branches, +depth, done}:
      match branches:
        case Nil{}: done(Nil{})
        case Eterm.Branch{tag, +arity, body} <> t:
          Erase.reindex_task(Erase.ReindexTerm{body, (depth + arity : Nat), x =>
            Erase.reindex_task(Erase.ReindexBranches{t, depth, xs => done(Eterm.Branch{tag, arity, x} <> xs)}, mapping)}, mapping)
    case Erase.ReindexTerm{term, +depth, done}:
      match term:
        case Eterm.KVar{+i}: done(Erase.reindex_var(Nat.is_ge(i, depth), mapping, depth, i))
        case Eterm.KLit{l}: done(Eterm.KLit{l})
        case Eterm.KGlobal{n}: done(Eterm.KGlobal{n})
        case Eterm.KErased{}: done(Eterm.KErased{})
        case Eterm.KLet{x, v, b}:
          Erase.reindex_task(Erase.ReindexTerm{v, depth, value =>
            Erase.reindex_task(Erase.ReindexTerm{b, 1n+depth, body => done(Eterm.KLet{x, value, body})}, mapping)}, mapping)
        case Eterm.KClos{f, n, cs}:
          Erase.reindex_task(Erase.ReindexTerms{cs, depth, xs => done(Eterm.KClos{f, n, xs})}, mapping)
        case Eterm.KApp{h, args}:
          Erase.reindex_task(Erase.ReindexTerm{h, depth, head =>
            Erase.reindex_task(Erase.ReindexTerms{args, depth, xs => done(Eterm.KApp{head, xs})}, mapping)}, mapping)
        case Eterm.KTail{h, args}:
          Erase.reindex_task(Erase.ReindexTerm{h, depth, head =>
            Erase.reindex_task(Erase.ReindexTerms{args, depth, xs => done(Eterm.KTail{head, xs})}, mapping)}, mapping)
        case Eterm.KStruct{t, fs}:
          Erase.reindex_task(Erase.ReindexTerms{fs, depth, xs => done(Eterm.KStruct{t, xs})}, mapping)
        case Eterm.KProj{t, k, x}:
          Erase.reindex_task(Erase.ReindexTerm{x, depth, value => done(Eterm.KProj{t, k, value})}, mapping)
        case Eterm.KTag{t, k, ps}:
          Erase.reindex_task(Erase.ReindexTerms{ps, depth, xs => done(Eterm.KTag{t, k, xs})}, mapping)
        case Eterm.KCase{t, s, bs}:
          Erase.reindex_task(Erase.ReindexTerm{s, depth, scrut =>
            Erase.reindex_task(Erase.ReindexBranches{bs, depth, branches => done(Eterm.KCase{t, scrut, branches})}, mapping)}, mapping)
        case Eterm.KDelay{f, cs}:
          Erase.reindex_task(Erase.ReindexTerms{cs, depth, xs => done(Eterm.KDelay{f, xs})}, mapping)
        case Eterm.KForce{x}:
          Erase.reindex_task(Erase.ReindexTerm{x, depth, value => done(Eterm.KForce{value})}, mapping)

def Erase.reindex_runtime(t: Eterm.ktm, depth: Nat, mapping: Erase.IndexMap) -> Eterm.ktm:
  Erase.reindex_task(Erase.ReindexTerm{t, depth, x => x}, mapping)

def Erase.shift_runtime(by: Nat, depth: Nat, t: Eterm.ktm) -> Eterm.ktm:
  Erase.reindex_runtime(t, depth, Erase.Shift{by})

def Erase.member_nat(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}: False{}
    case h <> t: Bool.or(Nat.is_eq(h, x), Erase.member_nat(t, x))

def Erase.insert_order(order: Cmp, n: Nat, h: Nat, t: List<&2, Nat>, later: List<&2, Nat>) -> List<&2, Nat>:
  match order:
    case LT{}: n <> h <> t
    case EQ{}: h <> t
    case GT{}: h <> later

def Erase.insert_nat(xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}: [n]
    case +h <> +t: Erase.insert_order(Nat.cmp(n, h), n, h, t, Erase.insert_nat(t, n))

def Erase.sort_unique(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case h <> t: Erase.insert_nat(Erase.sort_unique(t), h)

def Erase.live_index(keep: Bool, i: Nat, params: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}: (i - params : Nat) <> rest
    case False{}: rest

def Erase.live_captures(xs: List<&2, Nat>, +params: Nat, +count: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case +i <> t:
      Erase.live_index(Bool.and(Nat.is_ge(i, params), Nat.is_lt(i, (params + count : Nat))), i, params, Erase.live_captures(t, params, count))

def Erase.keep_item(-A: Data, keep: Bool, x: A, rest: List<&2, A>) -> List<&2, A>:
  match keep:
    case True{}: x <> rest
    case False{}: rest

def Erase.filter_capture(-A: Data, xs: List<&2, A>, i: Nat, +count: Nat, +live: List<&2, Nat>) -> List<&2, A>:
  match xs:
    case Nil{}: Nil{}
    case x <> rest:
      +next : Nat = 1n+i
      Erase.keep_item(A, Bool.and(Nat.is_le(next, count), Erase.member_nat(live, (count - next : Nat))), x, Erase.filter_capture(A, rest, next, count, live))

def Erase.prune_captures(+ps: List<&2, Eterm.repr>, args: List<&2, Eterm.ktm>, +params: Nat, +body: Eterm.ktm) -> F.Triple3<List<&2, Eterm.repr>, List<&2, Eterm.ktm>, Eterm.ktm>:
  +count = Erase.length(Eterm.repr, ps)
  +live = Erase.sort_unique(Erase.live_captures(Erase.runtime_vars(0n, body), params, count))
  F.Triple3{Erase.filter_capture(Eterm.repr, ps, 0n, count, live), Erase.filter_capture(Eterm.ktm, args, 0n, count, live), Erase.reindex_runtime(body, 0n, Erase.Prune{params, live})}

def Erase.free_children(xs: List<&2, F.Term.t>, +depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match xs:
    case Nil{}: Nil{}
    case h <> t: F.Pair2{depth, h} <> Erase.free_children(t, depth)

def Erase.free_address(a: F.Term.addr, depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match a:
    case F.Term.APt{q, arg}: [F.Pair2{depth, arg}]
    case F.Term.ALeg{k}: Nil{}
    case F.Term.ACtor{n}: Nil{}

def Erase.free_legs(xs: List<&2, F.Term.leg>, +depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match xs:
    case Nil{}: Nil{}
    case F.Term.Leg{binders, body} <> rest:
      F.Pair2{(depth + Erase.length(F.Pair2<F.Quantity.t, String>, binders) : Nat), body} <> Erase.free_legs(rest, depth)

def Erase.free_branches(xs: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match xs:
    case Nil{}: Nil{}
    case F.Pair2{address, F.Term.Leg{binders, body}} <> rest:
      F.Pair2{(depth + Erase.length(F.Pair2<F.Quantity.t, String>, binders) : Nat), body} <> Erase.free_branches(rest, depth)

def Erase.term_children(t: F.Term.t, +depth: Nat) -> List<&2, F.Pair2<Nat, F.Term.t>>:
  match t:
    case F.Term.Var{i}: Nil{}
    case F.Term.Global{n}: Nil{}
    case F.Term.Univ{l}: Nil{}
    case F.Term.Lit{l}: Nil{}
    case F.Term.Auto{}: Nil{}
    case F.Term.Lan{s, d}: Nil{}
    case F.Term.Ran{s, d}: Nil{}
    case F.Term.In{s, a, args}: Erase.append(F.Pair2<Nat, F.Term.t>, Erase.free_address(a, depth), Erase.free_children(args, depth))
    case F.Term.Out{s, a, head}: Erase.append(F.Pair2<Nat, F.Term.t>, Erase.free_address(a, depth), [F.Pair2{depth, head}])
    case F.Term.Sec{s, legs}: Erase.free_legs(legs, depth)
    case F.Term.Elim{F.Term.Elimination{shape, scrut, quantity, motive, branches}}:
      F.Pair2{depth, scrut} <> Erase.free_branches(branches, depth)
    case F.Term.Let{name, ty, value, body}: [F.Pair2{depth, value}, F.Pair2{1n+depth, body}]
    case F.Term.Ann{value, ty}: [F.Pair2{depth, value}]

@unsafe
def Erase.free_vars_tasks(tasks: List<&2, F.Pair2<Nat, F.Term.t>>) -> List<&2, Nat>:
  match tasks:
    case Nil{}: Nil{}
    case F.Pair2{+depth, term} <> rest:
      match term:
        case F.Term.Var{+ix}:
          Erase.append(Nat, Erase.var_at(Nat.is_ge(ix, depth), ix, depth), Erase.free_vars_tasks(rest))
        case other:
          Erase.free_vars_tasks(Erase.append(F.Pair2<Nat, F.Term.t>, Erase.term_children(other, depth), rest))

def Erase.free_vars(depth: Nat, t: F.Term.t) -> List<&2, Nat>:
  Erase.free_vars_tasks([F.Pair2{depth, t}])

def Erase.capture_found(found: Erase.found, ix: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match found:
    case Erase.LKeep{i}: ix <> rest
    case Erase.LDrop{}: rest
    case Erase.LOut{}: rest

def Erase.capture_filter(xs: List<&2, Nat>, +slots: List<&2, Erase.slot>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case +i <> rest:
      Erase.capture_found(Erase.lookup(slots, i, 0n), i, Erase.capture_filter(rest, slots))

def Erase.captures_of(slots: List<&2, Erase.slot>, t: F.Term.t) -> List<&2, Nat>:
  Erase.sort_unique(Erase.capture_filter(Erase.free_vars(0n, t), slots))

def Erase.tids_here(t: Eterm.ktm) -> List<&2, Eterm.tid>:
  match t:
    case Eterm.KStruct{tid, fields}: [tid]
    case Eterm.KProj{tid, index, value}: [tid]
    case Eterm.KTag{tid, tag, fields}: [tid]
    case Eterm.KCase{tid, scrutinee, branches}: [tid]
    case other: Nil{}

@unsafe
def Erase.tids_tasks(tasks: List<&2, F.Pair2<Nat, Eterm.ktm>>) -> List<&2, Eterm.tid>:
  match tasks:
    case Nil{}: Nil{}
    case F.Pair2{depth, +term} <> rest:
      Erase.append(Eterm.tid, Erase.tids_here(term), Erase.tids_tasks(Erase.append(F.Pair2<Nat, Eterm.ktm>, Erase.ktm_children(term, 0n), rest)))

def Erase.tids_ktm(t: Eterm.ktm) -> List<&2, Eterm.tid>:
  Erase.tids_tasks([F.Pair2{0n, t}])

def Erase.tids_repr(r: Eterm.repr) -> List<&2, Eterm.tid>:
  match r:
    case Eterm.RI31{}: Nil{}
    case Eterm.RStruct{t}: [t]
    case Eterm.RUnion{t}: [t]
    case Eterm.RFunc{t}: [t]
    case Eterm.RThunk{t}: [t]

def Erase.tids_reprs(rs: List<&2, Eterm.repr>) -> List<&2, Eterm.tid>:
  match rs:
    case Nil{}: Nil{}
    case h <> t: Erase.append(Eterm.tid, Erase.tids_repr(h), Erase.tids_reprs(t))

def Erase.tids_decl(d: Eterm.kdecl) -> List<&2, Eterm.tid>:
  match d:
    case Eterm.KFun{fid, ps, ret, body}: Erase.append(Eterm.tid, Erase.tids_reprs(ps), Erase.append(Eterm.tid, Erase.tids_repr(ret), Erase.tids_ktm(body)))
    case Eterm.KRec{ts}: ts

def Erase.has_tid(xs: List<&2, Eterm.tid>, +name: String) -> Bool:
  match xs:
    case Nil{}: False{}
    case Eterm.Tid{s} <> rest: Bool.or(String.eq(s, name), Erase.has_tid(rest, name))

def Erase.dedup_step(exists: Bool, out: List<&2, Eterm.tid>, t: Eterm.tid) -> List<&2, Eterm.tid>:
  match exists:
    case True{}: out
    case False{}: Erase.append(Eterm.tid, out, [t])

def Erase.dedup_loop(xs: List<&2, Eterm.tid>, +out: List<&2, Eterm.tid>) -> List<&2, Eterm.tid>:
  match xs:
    case Nil{}: out
    case +t <> rest: Erase.dedup_loop(rest, Erase.dedup_step(Erase.has_tid(out, Eterm.tid_text(t)), out, t))

def Erase.dedup_tids(xs: List<&2, Eterm.tid>) -> List<&2, Eterm.tid>:
  Erase.dedup_loop(xs, Nil{})

# Structural metadata comparison is separate from comparison of payload terms.
def Erase.shape_shell_equal(-A: Data, -B: Data, a: F.Shape.t<A>, b: F.Shape.t<B>) -> Bool:
  match a:
    case F.Shape.SPi{q, name, domain}:
      match b:
        case F.Shape.SPi{q2, name2, domain2}: Bool.and(F.Quantity.equal(q, q2), String.eq(name, name2))
        case other: False{}
    case F.Shape.SColl{n}:
      match b:
        case F.Shape.SColl{m}: Nat.is_eq(n, m)
        case other: False{}
    case F.Shape.SPar{x, y}:
      match b:
        case F.Shape.SPar{u, v}: True{}
        case other: False{}
    case F.Shape.SMu{name, args}:
      match b:
        case F.Shape.SMu{name2, args2}: Bool.and(String.eq(name, name2), Nat.is_eq(Erase.length(A, args), Erase.length(B, args2)))
        case other: False{}
    case F.Shape.SNu{name, args}:
      match b:
        case F.Shape.SNu{name2, args2}: Bool.and(String.eq(name, name2), Nat.is_eq(Erase.length(A, args), Erase.length(B, args2)))
        case other: False{}

type Erase.ectx is Data:
  Erase.Context{c: C.Check.ctx, slots: List<&2, Erase.slot>, self: String}

type Erase.acc is Data:
  Erase.Acc{next: Nat, lifted: List<&2, Eterm.kdecl>, groups: List<&2, Eterm.tid>}

def Erase.checker(ec: Erase.ectx) -> C.Check.ctx:
  Erase.Context{c, slots, self} = ec
  c

def Erase.globals_of(ec: Erase.ectx) -> F.Global.t:
  C.Check.global(Erase.checker(ec))

def Erase.size_of(ec: Erase.ectx) -> Nat:
  C.Check.size(Erase.checker(ec))

def Erase.env_of(ec: Erase.ectx) -> List<&2, F.Value.t>:
  C.Check.environment(Erase.checker(ec))

def Erase.bind_state(-A: Data, -B: Data, result: Erase.State<A>, next: A -> Erase.State<B>) -> Erase.State<B>:
  Erase.State.bind(A, B, result, next)

def Erase.require_state(-A: Data, value: Maybe<&2, A>, reason: F.Error.t) -> Erase.State<A>:
  match value:
    case None{}: Erase.Raise{reason}
    case Some{x}: Erase.Return{x}

def Erase.at(-A: Data, xs: List<&2, A>, n: Nat) -> Maybe<&2, A>:
  match xs:
    case Nil{}: None{}
    case h <> t:
      match n:
        case 0n: Some{h}
        case 1n+p: Erase.at(A, t, p)

def Erase.one(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case h <> Nil{}: Some{h}
    case other: None{}

def Erase.slot_of(keep: Bool) -> Erase.slot:
  match keep:
    case True{}: Erase.SKeep{}
    case False{}: Erase.SDrop{}

def Erase.bind_context(ec: Erase.ectx, name: String, quantity: F.Quantity.t, domain: F.Value.t, keep: Bool) -> Erase.ectx:
  Erase.Context{c, slots, self} = ec
  Erase.Context{C.Check.bind(name, quantity, domain, c), Erase.slot_of(keep) <> slots, self}

def Erase.quantity_runtime(q: F.Quantity.t) -> Bool:
  Bool.not(F.Quantity.equal(q, F.Quantity.Zero{}))

def Erase.width_zero(w: F.Value.t) -> Bool:
  match w:
    case F.Value.VLan{shape, diagram, universe}:
      match shape:
        case F.Shape.SColl{n}: Nat.is_eq(n, 0n)
        case other: False{}
    case F.Value.VRan{shape, diagram, universe}:
      match shape:
        case F.Shape.SColl{n}: Nat.is_eq(n, 0n)
        case other: False{}
    case other: False{}

def Erase.proof_free_state(~ops: Erase.Semantics, +ec: Erase.ectx, w: F.Value.t) -> Erase.State<Bool>:
  do Erase.State<Bool>:
    syntax: F.Term.t <- Erase.semantic_quote_state(ops, Erase.globals_of(ec), Erase.size_of(ec), w)
    level: F.Level.t <- Erase.semantic_univ_state(ops, Erase.checker(ec), syntax)
    Erase.Return{Bool.not(F.Level.equal(level, F.Level.zero))}

def Erase.runtime_width_state(~ops: Erase.Semantics, zero: Bool, ec: Erase.ectx, w: F.Value.t) -> Erase.State<Bool>:
  match zero:
    case True{}: Erase.Return{False{}}
    case False{}: Erase.proof_free_state(~ops, ec, w)

def Erase.runtime_normal_state(~ops: Erase.Semantics, w: F.Value.t, ec: Erase.ectx) -> Erase.State<Bool>:
  match w:
    case F.Value.VUniv{level}: Erase.Return{False{}}
    case +other: Erase.runtime_width_state(~ops, Erase.width_zero(other), ec, other)

def Erase.runtime_ty_state(~ops: Erase.Semantics, +ec: Erase.ectx, ty: F.Value.t) -> Erase.State<Bool>:
  Erase.bind_state(F.Value.t, Bool, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty)), w => Erase.runtime_normal_state(~ops, w, ec))

def Erase.point_keep_state(~ops: Erase.Semantics, keep: Bool, ec: Erase.ectx, domain: F.Value.t) -> Erase.State<Bool>:
  match keep:
    case False{}: Erase.Return{False{}}
    case True{}: Erase.runtime_ty_state(~ops, ec, domain)

def Erase.point_runtime_state(~ops: Erase.Semantics, ec: Erase.ectx, quantity: F.Quantity.t, domain: F.Value.t) -> Erase.State<Bool>:
  Erase.point_keep_state(~ops, Erase.quantity_runtime(quantity), ec, domain)

def Erase.any_repr() -> Eterm.repr:
  Eterm.RUnion{Eterm.Tid{"any"}}

def Erase.mu_tid(name: String) -> Eterm.tid:
  Eterm.Tid{"mu<" ++ name ++ ">"}

def Erase.mu_leg_parts(rs: List<&2, Eterm.repr>) -> String:
  match rs:
    case Nil{}: ""
    case r <> rest: "," ++ Eterm.print_repr(r) ++ Erase.mu_leg_parts(rest)

def Erase.mu_leg_tid(name: String, tag: Nat, rs: List<&2, Eterm.repr>) -> Eterm.tid:
  Eterm.Tid{"leg<" ++ Eterm.tid_text(Erase.mu_tid(name)) ++ "," ++ Nat.show(tag) ++ Erase.mu_leg_parts(rs) ++ ">"}

def Erase.coll_section_state(value: F.Value.t) -> Erase.State<List<&2, F.Value.vleg>>:
  match value:
    case F.Value.VSec{shape, legs}: Erase.Return{legs}
    case other: Erase.Raise{F.Error.Mismatch{P.Rules.diagram_msg}}

def Erase.coll_legs_of_state(+ec: Erase.ectx, diagram: F.Value.closure) -> Erase.State<List<&2, F.Value.vleg>>:
  Erase.bind_state(F.Value.t, List<&2, F.Value.vleg>, Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, Nil{})), Erase.coll_section_state)

def Erase.open_leg_state(leg: F.Value.vleg, ec: Erase.ectx) -> Erase.State<F.Value.t>:
  F.Value.Leg{binders, closure} = leg
  Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), closure, Nil{}))

def Erase.leg_types_loop_state(n: Nat, +legs: List<&2, F.Value.vleg>, +ec: Erase.ectx, +index: Nat) -> Erase.State<List<&2, F.Value.t>>:
  match n:
    case 0n: Erase.Return{Nil{}}
    case 1n+p:
      do Erase.State<List<&2, F.Value.t>>:
        leg: F.Value.vleg <- Erase.require_state(F.Value.vleg, Erase.at(F.Value.vleg, legs, index), F.Error.Wrong_leg{P.Rules.leg_msg})
        ty: F.Value.t <- Erase.open_leg_state(leg, ec)
        rest: List<&2, F.Value.t> <- Erase.leg_types_loop_state(p, legs, ec, 1n+index)
        Erase.Return{ty <> rest}

def Erase.leg_types_state(+ec: Erase.ectx, n: Nat, diagram: F.Value.closure) -> Erase.State<List<&2, F.Value.t>>:
  Erase.bind_state(List<&2, F.Value.vleg>, List<&2, F.Value.t>, Erase.coll_legs_of_state(ec, diagram), legs => Erase.leg_types_loop_state(n, legs, ec, 0n))

@unsafe
def Erase.arity_normal_state(~ops: Erase.Semantics, value: F.Value.t, +ec: Erase.ectx, n: Nat) -> Erase.State<Nat>:
  match value:
    case F.Value.VRan{shape, diagram, universe}:
      match shape:
        case F.Shape.SPi{+q, name, +domain}:
          do Erase.State<Nat>:
            keep: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
            cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, [F.Value.var(Erase.size_of(ec))]))
            normal: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), cod))
            Erase.arity_normal_state(~ops, normal, Erase.bind_context(ec, name, q, domain, False{}), (n + Erase.bool_nat(keep) : Nat))
        case other: Erase.Return{n}
    case other: Erase.Return{n}

def Erase.arity_of_state(~ops: Erase.Semantics, ec: Erase.ectx, n: Nat, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure) -> Erase.State<Nat>:
  Erase.arity_normal_state(~ops, F.Value.VRan{shape, diagram, None{}}, ec, n)

type Erase.ReprTask is Type:
  Erase.ReprValue{ec: Erase.ectx, value: F.Value.t, done: Eterm.repr -> Erase.State<Eterm.repr>}
  Erase.ReprNormal{ec: Erase.ectx, value: F.Value.t, done: Eterm.repr -> Erase.State<Eterm.repr>}
  Erase.ReprText{ec: Erase.ectx, keep: Bool, value: F.Value.t, done: List<&2, String> -> Erase.State<Eterm.repr>}
  Erase.ReprTexts{ec: Erase.ectx, types: List<&2, F.Value.t>, sum: Bool, done: List<&2, String> -> Erase.State<Eterm.repr>}
  Erase.ReprTextsKeep{ec: Erase.ectx, keep: Bool, value: F.Value.t, types: List<&2, F.Value.t>, sum: Bool, done: List<&2, String> -> Erase.State<Eterm.repr>}

def Erase.unit_text(sum: Bool) -> List<&2, String>:
  match sum:
    case True{}: ["unit"]
    case False{}: Nil{}

def Erase.coll_repr(sum: Bool, texts: List<&2, String>) -> Eterm.repr:
  match sum:
    case True{}: Eterm.RUnion{Eterm.Tid{"sum<" ++ String.join(texts, "|") ++ ">"}}
    case False{}: Eterm.RStruct{Eterm.Tid{"tuple<" ++ String.join(texts, ",") ++ ">"}}

def Erase.neutral_repr(head: F.Value.head, spine: List<&2, F.Value.spine>) -> Eterm.repr:
  match head:
    case F.Value.HGlobal{name}:
      match spine:
        case Nil{}: Bool.pick(Eterm.repr, String.eq(name, "Nat"), Eterm.RUnion{Eterm.Tid{"nat"}}, Erase.any_repr)
        case other: Erase.any_repr
    case other: Erase.any_repr

@unsafe
def Erase.repr_task_state(~ops: Erase.Semantics, task: Erase.ReprTask) -> Erase.State<Eterm.repr>:
  match task:
    case Erase.ReprValue{+ec, value, done}:
      Erase.bind_state(F.Value.t, Eterm.repr, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), value)), normal => Erase.repr_task_state(~ops, Erase.ReprNormal{ec, normal, done}))
    case Erase.ReprText{ec, keep, value, done}:
      match keep:
        case False{}: done(Nil{})
        case True{}: Erase.repr_task_state(~ops, Erase.ReprValue{ec, value, repr => done([Eterm.print_repr(repr)])})
    case Erase.ReprTexts{+ec, types, sum, done}:
      match types:
        case Nil{}: done(Nil{})
        case +h <> t:
          Erase.bind_state(Bool, Eterm.repr, Erase.runtime_ty_state(~ops, ec, h), keep => Erase.repr_task_state(~ops, Erase.ReprTextsKeep{ec, keep, h, t, sum, done}))
    case Erase.ReprTextsKeep{+ec, keep, value, types, +sum, done}:
      match keep:
        case False{}: Erase.repr_task_state(~ops, Erase.ReprTexts{ec, types, sum, rest => done(Erase.append(String, Erase.unit_text(sum), rest))})
        case True{}: Erase.repr_task_state(~ops, Erase.ReprValue{ec, value, repr =>
          Erase.repr_task_state(~ops, Erase.ReprTexts{ec, types, sum, rest => done(Eterm.print_repr(repr) <> rest)})})
    case Erase.ReprNormal{+ec, value, done}:
      match value:
        case F.Value.VRan{shape, diagram, universe}:
          match shape:
            case F.Shape.SPi{q, name, domain}:
              Erase.bind_state(Nat, Eterm.repr, Erase.arity_of_state(~ops, ec, 0n, F.Shape.SPi{q, name, domain}, diagram), arity => done(Eterm.RFunc{Eterm.Tid{"fn<" ++ Nat.show(arity) ++ ">"}}))
            case F.Shape.SColl{n}:
              match n:
                case 0n: done(Erase.any_repr)
                case 1n+p:
                  Erase.bind_state(List<&2, F.Value.t>, Eterm.repr, Erase.leg_types_state(ec, 1n+p, diagram), tys => Erase.repr_task_state(~ops, Erase.ReprTexts{ec, tys, False{}, texts => done(Erase.coll_repr(False{}, texts))}))
            case other: done(Erase.any_repr)
        case F.Value.VLan{shape, +diagram, universe}:
          match shape:
            case F.Shape.SMu{name, indices}: done(Eterm.RUnion{Erase.mu_tid(name)})
            case F.Shape.SPi{+q, name, +domain}:
              do Erase.State<Eterm.repr>:
                keep1: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
                +cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, [F.Value.var(Erase.size_of(ec))]))
                (+next = Erase.bind_context(ec, name, q, domain, False{})
                 Erase.bind_state(Bool, Eterm.repr, Erase.runtime_ty_state(~ops, next, cod), keep2 =>
                   Erase.repr_task_state(~ops, Erase.ReprText{ec, keep1, domain, first =>
                     Erase.repr_task_state(~ops, Erase.ReprText{next, keep2, cod, second => done(Eterm.RStruct{Eterm.Tid{"pair<" ++ String.join(Erase.append(String, first, second), ",") ++ ">"}})})})))
            case F.Shape.SColl{n}:
              match n:
                case 0n: done(Erase.any_repr)
                case 1n+p:
                  Erase.bind_state(List<&2, F.Value.t>, Eterm.repr, Erase.leg_types_state(ec, 1n+p, diagram), tys => Erase.repr_task_state(~ops, Erase.ReprTexts{ec, tys, True{}, texts => done(Erase.coll_repr(True{}, texts))}))
            case other: done(Erase.any_repr)
        case F.Value.VNeutral{head, spine}: done(Erase.neutral_repr(head, spine))
        case other: done(Erase.any_repr)

def Erase.repr_of_state(~ops: Erase.Semantics, ec: Erase.ectx, value: F.Value.t) -> Erase.State<Eterm.repr>:
  Erase.repr_task_state(~ops, Erase.ReprValue{ec, value, repr => Erase.Return{repr}})

def Erase.repr_tid_state(repr: Eterm.repr) -> Erase.State<Eterm.tid>:
  match repr:
    case Eterm.RI31{}: Erase.Raise{F.Error.Mismatch{"a structured value stands at a type whose repr is i31"}}
    case Eterm.RStruct{t}: Erase.Return{t}
    case Eterm.RUnion{t}: Erase.Return{t}
    case Eterm.RFunc{t}: Erase.Return{t}
    case Eterm.RThunk{t}: Erase.Return{t}

def Erase.tid_of_state(~ops: Erase.Semantics, ec: Erase.ectx, ty: F.Value.t) -> Erase.State<Eterm.tid>:
  Erase.bind_state(Eterm.repr, Eterm.tid, Erase.repr_of_state(~ops, ec, ty), Erase.repr_tid_state)

def Erase.reverse(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}: acc
    case h <> t: Erase.reverse(A, t, h <> acc)

def Erase.present(-A: Data, value: Maybe<&2, A>) -> Bool:
  match value:
    case None{}: False{}
    case Some{x}: True{}

def Erase.position_choice(equal: Bool, index: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match equal:
    case True{}: Some{index}
    case False{}: rest

def Erase.position_loop(xs: List<&2, String>, +name: String, +index: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}: None{}
    case h <> t: Erase.position_choice(String.eq(name, h), index, Erase.position_loop(t, name, 1n+index))

def Erase.position(name: String, xs: List<&2, String>) -> Maybe<&2, Nat>:
  Erase.position_loop(xs, name, 0n)

def Erase.mu_names_status_state(status: F.Positivity.ctor_status, name: String) -> Erase.State<List<&2, String>>:
  match status:
    case F.Positivity.Complete{names}: Erase.Return{names}
    case F.Positivity.Provisional{}: Erase.Raise{F.Error.Unbound{"the family " ++ name ++ " is still under declaration"}}
    case F.Positivity.Builtin{}: Erase.Raise{F.Error.Mismatch{"the family " ++ name ++ " is a kernel family and has no branches"}}

def Erase.mu_ctor_names_state(name: String, family: F.Positivity.family) -> Erase.State<List<&2, String>>:
  F.Positivity.Family{family_name, params, indices, level, status, ctors, positive} = family
  Erase.mu_names_status_state(status, name)

def Erase.mu_positive_state(positive: Bool, family: F.Positivity.family) -> Erase.State<F.Positivity.family>:
  match positive:
    case True{}: Erase.Return{family}
    case False{}: Erase.Raise{F.Error.Not_yet{"a family that is not strictly positive arrives at M2"}}

def Erase.mu_family_status_state(status: F.Positivity.ctor_status, positive: Bool, family: F.Positivity.family) -> Erase.State<F.Positivity.family>:
  match status:
    case F.Positivity.Complete{names}: Erase.mu_positive_state(positive, family)
    case other: Erase.Return{family}

def Erase.mu_family_found_state(+family: F.Positivity.family) -> Erase.State<F.Positivity.family>:
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  Erase.mu_family_status_state(status, positive, family)

def Erase.mu_family_state(ec: Erase.ectx, +name: String) -> Erase.State<F.Positivity.family>:
  Erase.bind_state(F.Positivity.family, F.Positivity.family, Erase.require_state(F.Positivity.family, F.Global.find_family(name, Erase.globals_of(ec)), F.Error.Unbound{"the family " ++ name ++ " is not declared"}), family => Erase.mu_family_found_state(family))

def Erase.ctor_choice(equal: Bool, ctor: F.Positivity.ctor, rest: Maybe<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:
  match equal:
    case True{}: Some{ctor}
    case False{}: rest

def Erase.ctor_search(ctors: List<&2, F.Positivity.ctor>, +name: String) -> Maybe<&2, F.Positivity.ctor>:
  match ctors:
    case Nil{}: None{}
    case F.Positivity.Ctor{+ctor_name, args, indices, arity, self_rec} <> rest:
      Erase.ctor_choice(String.eq(ctor_name, name), F.Positivity.Ctor{ctor_name, args, indices, arity, self_rec}, Erase.ctor_search(rest, name))

def Erase.ctor_of(name: String, family: F.Positivity.family) -> Maybe<&2, F.Positivity.ctor>:
  F.Positivity.Family{family_name, params, indices, level, status, ctors, positive} = family
  Erase.ctor_search(ctors, name)

def Erase.mu_parameters_state(tele: F.Positivity.telescope, +ec: Erase.ectx) -> Erase.State<Erase.ectx>:
  match tele:
    case Nil{}: Erase.Return{ec}
    case F.Triple3{q, name, ty} <> rest:
      Erase.bind_state(F.Value.t, Erase.ectx, Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), Erase.env_of(ec), ty)), domain =>
        Erase.mu_parameters_state(rest, Erase.bind_context(ec, name, q, domain, False{})))

def Erase.optional_repr_state(~ops: Erase.Semantics, keep: Bool, ec: Erase.ectx, domain: F.Value.t) -> Erase.State<Maybe<&2, Eterm.repr>>:
  match keep:
    case False{}: Erase.Return{None{}}
    case True{}: Erase.bind_state(Eterm.repr, Maybe<&2, Eterm.repr>, Erase.repr_of_state(~ops, ec, domain), repr => Erase.Return{Some{repr}})

def Erase.mu_leg_reprs_state(~ops: Erase.Semantics, tele: F.Positivity.telescope, +ec: Erase.ectx, +env: List<&2, F.Value.t>) -> Erase.State<List<&2, Maybe<&2, Eterm.repr>>>:
  match tele:
    case Nil{}: Erase.Return{Nil{}}
    case F.Triple3{+q, name, ty} <> rest:
      do Erase.State<List<&2, Maybe<&2, Eterm.repr>>>:
        +domain: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), env, ty))
        keep: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
        here: Maybe<&2, Eterm.repr> <- Erase.optional_repr_state(~ops, keep, ec, domain)
        more: List<&2, Maybe<&2, Eterm.repr>> <- Erase.mu_leg_reprs_state(~ops, rest, Erase.bind_context(ec, name, q, domain, False{}), F.Value.var(Erase.size_of(ec)) <> env)
        Erase.Return{here <> more}

def Erase.mu_layout_state(~ops: Erase.Semantics, ec: Erase.ectx, family: F.Positivity.family, ctor: F.Positivity.ctor) -> Erase.State<List<&2, Maybe<&2, Eterm.repr>>>:
  Erase.Context{+checker, slots, self} = ec
  F.Positivity.Family{name, params, indices, level, status, ctors, positive} = family
  F.Positivity.Ctor{ctor_name, args, result_indices, arity, self_rec} = ctor
  fresh : Erase.ectx = Erase.Context{C.Check.make(C.Check.global(checker), C.Check.budget(checker)), Nil{}, self}
  Erase.bind_state(Erase.ectx, List<&2, Maybe<&2, Eterm.repr>>, Erase.mu_parameters_state(params, fresh), prepared =>
    (+next : Erase.ectx = prepared
     Erase.mu_leg_reprs_state(~ops, args, next, Erase.env_of(next))))

def Erase.some_reprs(rs: List<&2, Maybe<&2, Eterm.repr>>) -> List<&2, Eterm.repr>:
  match rs:
    case Nil{}: Nil{}
    case h <> t:
      match h:
        case None{}: Erase.some_reprs(t)
        case Some{r}: r <> Erase.some_reprs(t)

def Erase.mu_groups_loop_state(~ops: Erase.Semantics, names: List<&2, String>, +index: Nat, +ec: Erase.ectx, +name: String, +family: F.Positivity.family) -> Erase.State<List<&2, Eterm.tid>>:
  match names:
    case Nil{}: Erase.Return{Nil{}}
    case +ctor_name <> rest:
      do Erase.State<List<&2, Eterm.tid>>:
        ctor: F.Positivity.ctor <- Erase.require_state(F.Positivity.ctor, Erase.ctor_of(ctor_name, family), F.Error.Unbound{ctor_name ++ " is not a constructor of " ++ name})
        layout: List<&2, Maybe<&2, Eterm.repr>> <- Erase.mu_layout_state(~ops, ec, family, ctor)
        more: List<&2, Eterm.tid> <- Erase.mu_groups_loop_state(~ops, rest, 1n+index, ec, name, family)
        Erase.Return{Erase.mu_leg_tid(name, index, Erase.some_reprs(layout)) <> more}

def Erase.mu_group_tids_state(~ops: Erase.Semantics, ec: Erase.ectx, +name: String, +family: F.Positivity.family) -> Erase.State<List<&2, Eterm.tid>>:
  Erase.bind_state(List<&2, String>, List<&2, Eterm.tid>, Erase.mu_ctor_names_state(name, family), names => Erase.mu_groups_loop_state(~ops, names, 0n, ec, name, family))

def Erase.open_legs_state(legs: List<&2, F.Value.vleg>, +ec: Erase.ectx) -> Erase.State<List<&2, F.Value.t>>:
  match legs:
    case Nil{}: Erase.Return{Nil{}}
    case h <> t:
      do Erase.State<List<&2, F.Value.t>>:
        first: F.Value.t <- Erase.open_leg_state(h, ec)
        rest: List<&2, F.Value.t> <- Erase.open_legs_state(t, ec)
        Erase.Return{first <> rest}

def Erase.mu_param_env_state(+ec: Erase.ectx, diagram: F.Value.closure) -> Erase.State<List<&2, F.Value.t>>:
  do Erase.State<List<&2, F.Value.t>>:
    legs: List<&2, F.Value.vleg> <- Erase.coll_legs_of_state(ec, diagram)
    values: List<&2, F.Value.t> <- Erase.open_legs_state(legs, ec)
    Erase.Return{Erase.reverse(F.Value.t, values, Nil{})}

def Erase.eval_terms_state(terms: List<&2, F.Term.t>, +ec: Erase.ectx, +env: List<&2, F.Value.t>) -> Erase.State<List<&2, F.Value.t>>:
  match terms:
    case Nil{}: Erase.Return{Nil{}}
    case h <> t:
      do Erase.State<List<&2, F.Value.t>>:
        value: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), env, h))
        rest: List<&2, F.Value.t> <- Erase.eval_terms_state(t, ec, env)
        Erase.Return{value <> rest}

def Erase.eval_shape_state(+ec: Erase.ectx, +shape: F.Shape.t<F.Term.t>) -> Erase.State<F.Shape.t<F.Value.t>>:
  Erase.bind_state(List<&2, F.Value.t>, F.Shape.t<F.Value.t>, Erase.eval_terms_state(F.Shape.payload(F.Term.t, shape), ec, Erase.env_of(ec)), payload =>
    Erase.State.lift(F.Shape.t<F.Value.t>, F.Shape.with_payload(F.Term.t, F.Value.t, shape, payload)))

def Erase.elim_result_state(motive: Maybe<&2, F.Term.motive>, +ec: Erase.ectx, expected: F.Value.t, self: F.Value.t) -> Erase.State<F.Value.t>:
  match motive:
    case None{}: Erase.Return{expected}
    case Some{F.Term.Motive{ind, indices, name, body}}:
      Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), self <> Erase.env_of(ec), body))

def Erase.mu_result_state(motive: F.Term.motive, +ec: Erase.ectx, indices: List<&2, F.Value.t>, self: F.Value.t) -> Erase.State<F.Value.t>:
  F.Term.Motive{ind, names, name, body} = motive
  Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), self <> Erase.reverse(F.Value.t, indices, Erase.env_of(ec)), body))

def Erase.var_found_state(found: Erase.found, index: Nat) -> Erase.State<Eterm.ktm>:
  match found:
    case Erase.LKeep{i}: Erase.Return{Eterm.KVar{i}}
    case Erase.LDrop{}: Erase.Return{Eterm.KErased{}}
    case Erase.LOut{}: Erase.Raise{F.Error.Unbound{"the erasure context has no binder at index " ++ Nat.show(index)}}

def Erase.var_arm_state(ec: Erase.ectx, +index: Nat) -> Erase.State<Eterm.ktm>:
  Erase.Context{checker, slots, self} = ec
  Erase.var_found_state(Erase.lookup(slots, index, 0n), index)

def Erase.frame_loop(slots: List<&2, Erase.slot>, +captures: List<&2, Nat>, +index: Nat) -> List<&2, Erase.slot>:
  match slots:
    case Nil{}: Nil{}
    case slot <> rest:
      match slot:
        case Erase.SExtra{}: Erase.frame_loop(rest, captures, index)
        case Erase.SDrop{}: Erase.SDrop{} <> Erase.frame_loop(rest, captures, 1n+index)
        case Erase.SKeep{}: Erase.slot_of(Erase.member_nat(captures, index)) <> Erase.frame_loop(rest, captures, 1n+index)

def Erase.frame(slots: List<&2, Erase.slot>, captures: List<&2, Nat>) -> List<&2, Erase.slot>:
  Erase.frame_loop(slots, captures, 0n)

def Erase.repr_params_state(~ops: Erase.Semantics, keep: Bool, ec: Erase.ectx, domain: F.Value.t) -> Erase.State<List<&2, Eterm.repr>>:
  match keep:
    case False{}: Erase.Return{Nil{}}
    case True{}: Erase.bind_state(Eterm.repr, List<&2, Eterm.repr>, Erase.repr_of_state(~ops, ec, domain), r => Erase.Return{[r]})

def Erase.signature_prepend(here: List<&2, Eterm.repr>, rest: F.Pair2<List<&2, Eterm.repr>, Eterm.repr>) -> F.Pair2<List<&2, Eterm.repr>, Eterm.repr>:
  F.Pair2{params, ret} = rest
  F.Pair2{Erase.append(Eterm.repr, here, params), ret}

@unsafe
def Erase.signature_normal_state(~ops: Erase.Semantics, normal: F.Value.t, +ec: Erase.ectx, fallback: F.Value.t) -> Erase.State<F.Pair2<List<&2, Eterm.repr>, Eterm.repr>>:
  match normal:
    case F.Value.VRan{shape, diagram, universe}:
      match shape:
        case F.Shape.SPi{+q, name, +domain}:
          do Erase.State<F.Pair2<List<&2, Eterm.repr>, Eterm.repr>>:
            keep: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
            here: List<&2, Eterm.repr> <- Erase.repr_params_state(~ops, keep, ec, domain)
            +cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, [F.Value.var(Erase.size_of(ec))]))
            w: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), cod))
            rest: F.Pair2<List<&2, Eterm.repr>, Eterm.repr> <- Erase.signature_normal_state(~ops, w, Erase.bind_context(ec, name, q, domain, False{}), cod)
            Erase.Return{Erase.signature_prepend(here, rest)}
        case other:
          Erase.bind_state(Eterm.repr, F.Pair2<List<&2, Eterm.repr>, Eterm.repr>, Erase.repr_of_state(~ops, ec, fallback), r => Erase.Return{F.Pair2{Nil{}, r}})
    case other:
      Erase.bind_state(Eterm.repr, F.Pair2<List<&2, Eterm.repr>, Eterm.repr>, Erase.repr_of_state(~ops, ec, fallback), r => Erase.Return{F.Pair2{Nil{}, r}})

def Erase.remaining_signature_state(~ops: Erase.Semantics, ec: Erase.ectx, shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure) -> Erase.State<F.Pair2<List<&2, Eterm.repr>, Eterm.repr>>:
  +ty : F.Value.t = F.Value.VRan{shape, diagram, None{}}
  Erase.signature_normal_state(~ops, ty, ec, ty)

def Erase.capture_types_state(~ops: Erase.Semantics, captures: List<&2, Nat>, +ec: Erase.ectx) -> Erase.State<List<&2, F.Value.t>>:
  match captures:
    case Nil{}: Erase.Return{Nil{}}
    case ix <> rest:
      do Erase.State<List<&2, F.Value.t>>:
        ty: F.Value.t <- Erase.semantic_infer_state(ops, Erase.checker(ec), F.Quantity.Many{}, F.Term.Var{ix})
        more: List<&2, F.Value.t> <- Erase.capture_types_state(~ops, rest, ec)
        Erase.Return{ty <> more}

def Erase.capture_type_reprs_state(~ops: Erase.Semantics, types: List<&2, F.Value.t>, +ec: Erase.ectx) -> Erase.State<List<&2, Eterm.repr>>:
  match types:
    case Nil{}: Erase.Return{Nil{}}
    case ty <> rest:
      do Erase.State<List<&2, Eterm.repr>>:
        repr: Eterm.repr <- Erase.repr_of_state(~ops, ec, ty)
        more: List<&2, Eterm.repr> <- Erase.capture_type_reprs_state(~ops, rest, ec)
        Erase.Return{repr <> more}

def Erase.capture_reprs_state(~ops: Erase.Semantics, captures: List<&2, Nat>, +ec: Erase.ectx) -> Erase.State<List<&2, Eterm.repr>>:
  Erase.bind_state(List<&2,F.Value.t>,List<&2,Eterm.repr>,Erase.capture_types_state(~ops,captures,ec),types => Erase.capture_type_reprs_state(~ops,types,ec))

def Erase.capture_args_state(captures: List<&2, Nat>, +ec: Erase.ectx) -> Erase.State<List<&2, Eterm.ktm>>:
  match captures:
    case Nil{}: Erase.Return{Nil{}}
    case ix <> rest:
      do Erase.State<List<&2, Eterm.ktm>>:
        arg: Eterm.ktm <- Erase.var_arm_state(ec, ix)
        more: List<&2, Eterm.ktm> <- Erase.capture_args_state(rest, ec)
        Erase.Return{arg <> more}

def Erase.as_lam(term: F.Term.t) -> Maybe<&2, F.Term.leg>:
  match term:
    case F.Term.Sec{shape, legs}:
      match shape:
        case F.Shape.SPi{q, name, domain}: Erase.one(F.Term.leg, legs)
        case other: None{}
    case other: None{}

@unsafe
def Erase.spine(term: F.Term.t, args: List<&2, F.Triple3<F.Quantity.t, F.Term.t, F.Term.t>>) -> F.Pair2<F.Term.t, List<&2, F.Triple3<F.Quantity.t, F.Term.t, F.Term.t>>>:
  match term:
    case F.Term.Out{shape, address, head}:
      match shape:
        case F.Shape.SPi{q, name, domain}:
          match address:
            case F.Term.APt{qa, arg}: Erase.spine(head, F.Triple3{qa, domain, arg} <> args)
            case other: F.Pair2{F.Term.Out{F.Shape.SPi{q, name, domain}, other, head}, args}
        case other: F.Pair2{F.Term.Out{other, address, head}, args}
    case other: F.Pair2{other, args}

def Erase.function_parts_state(value: F.Value.t) -> Erase.State<F.Triple3<F.Quantity.t, F.Value.t, F.Value.closure>>:
  match value:
    case F.Value.VRan{shape, diagram, universe}:
      match shape:
        case F.Shape.SPi{q, name, domain}: Erase.Return{F.Triple3{q, domain, diagram}}
        case other: Erase.Raise{F.Error.Mismatch{"an application needs a point function type"}}
    case other: Erase.Raise{F.Error.Mismatch{"an application needs a point function type"}}

def Erase.job(keep: Bool, ty: F.Value.t, arg: F.Term.t) -> List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>:
  match keep:
    case False{}: Nil{}
    case True{}: [F.Pair2{Some{ty}, arg}]

def Erase.app_step_state(~ops: Erase.Semantics, parts: F.Triple3<F.Quantity.t, F.Value.t, F.Value.closure>, +ec: Erase.ectx, +arg: F.Term.t, jobs: List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>) -> Erase.State<F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>>:
  F.Triple3{q, +domain, diagram} = parts
  do Erase.State<F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>>:
    keep: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
    av: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), Erase.env_of(ec), arg))
    result: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, [av]))
    Erase.Return{F.Pair2{Erase.append(F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>, jobs, Erase.job(keep, domain, arg)), result}}

def Erase.app_jobs_state(~ops: Erase.Semantics, args: List<&2, F.Triple3<F.Quantity.t, F.Term.t, F.Term.t>>, +ec: Erase.ectx, state: F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>) -> Erase.State<F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>>:
  match args:
    case Nil{}: Erase.Return{state}
    case F.Triple3{qa, domain, arg} <> rest:
      F.Pair2{jobs, ty} = state
      do Erase.State<F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>>:
        normal: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty))
        parts: F.Triple3<F.Quantity.t, F.Value.t, F.Value.closure> <- Erase.function_parts_state(normal)
        next: F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t> <- Erase.app_step_state(~ops, parts, ec, arg, jobs)
        Erase.app_jobs_state(~ops, rest, ec, next)

def Erase.function_normal(value: F.Value.t) -> Bool:
  match value:
    case F.Value.VRan{shape, diagram, universe}: Erase.present(F.Triple3<F.Quantity.t, String, F.Value.t>, P.Rules.as_vpi(F.Value.t, shape))
    case other: False{}

def Erase.function_result_state(ec: Erase.ectx, ty: F.Value.t) -> Erase.State<Bool>:
  Erase.bind_state(F.Value.t, Bool, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty)), normal => Erase.Return{Erase.function_normal(normal)})

def Erase.apply_result(bare: Bool, tail: Bool, head: Eterm.ktm, args: List<&2, Eterm.ktm>) -> Eterm.ktm:
  match bare:
    case True{}: head
    case False{}:
      match tail:
        case True{}: Eterm.KTail{head, args}
        case False{}: Eterm.KApp{head, args}

def Erase.bare_application_state(args: List<&2, Eterm.ktm>, ec: Erase.ectx, ty: F.Value.t) -> Erase.State<Bool>:
  match args:
    case Nil{}: Erase.function_result_state(ec, ty)
    case other: Erase.Return{False{}}

def Erase.leg_flags_state(~ops: Erase.Semantics, tys: List<&2, F.Value.t>, +ec: Erase.ectx) -> Erase.State<List<&2, Bool>>:
  match tys:
    case Nil{}: Erase.Return{Nil{}}
    case ty <> rest:
      do Erase.State<List<&2, Bool>>:
        keep: Bool <- Erase.runtime_ty_state(~ops, ec, ty)
        more: List<&2, Bool> <- Erase.leg_flags_state(~ops, rest, ec)
        Erase.Return{keep <> more}

def Erase.tuple_jobs(legs: List<&2, F.Term.leg>, tys: List<&2, F.Value.t>, flags: List<&2, Bool>) -> List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>:
  match legs:
    case Nil{}: Nil{}
    case F.Term.Leg{binders, body} <> rest:
      match tys:
        case Nil{}: Nil{}
        case ty <> more:
          match flags:
            case Nil{}: Nil{}
            case keep <> others:
              Erase.append(F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>, Erase.job(keep, ty, body), Erase.tuple_jobs(rest, more, others))

def Erase.count_kept(flags: List<&2, Bool>, n: Nat) -> Nat:
  match flags:
    case Nil{}: 0n
    case keep <> rest:
      match n:
        case 0n: 0n
        case 1n+p: (Erase.bool_nat(keep) + Erase.count_kept(rest, p) : Nat)

def Erase.eta_args(+n: Nat) -> List<&2, Eterm.ktm>:
  match n:
    case 0n: Nil{}
    case 1n+p: Eterm.KVar{p} <> Erase.eta_args(p)

def Erase.ensure_state(valid: Bool, error: F.Error.t) -> Erase.State<Unit>:
  match valid:
    case True{}: Erase.Return{Unit{}}
    case False{}: Erase.Raise{error}

def Erase.mu_motive_check_state(+motive: F.Term.motive, +name: String, +want: Nat, +applied: Nat) -> Erase.State<F.Term.motive>:
  F.Term.Motive{ind, indices, self, body} = motive
  +got = Erase.length(String, indices)
  do Erase.State<F.Term.motive>:
    +named: String <- Erase.require_state(String, ind, F.Error.Mismatch{"the motive of an elimination at " ++ name ++ " names no family"})
    same: Unit <- Erase.ensure_state(String.eq(named, name), F.Error.Mismatch{"the motive is built for " ++ named ++ " and the scrutinee is at " ++ name})
    arity: Unit <- Erase.ensure_state(Nat.is_eq(got, want), F.Error.Mismatch{"the motive of " ++ name ++ " binds " ++ Nat.show(got) ++ " indices and the family has " ++ Nat.show(want)})
    index_arity: Unit <- Erase.ensure_state(Nat.is_eq(applied, want), F.Error.Mismatch{name ++ " is applied to " ++ Nat.show(applied) ++ " indices and the family has " ++ Nat.show(want)})
    Erase.Return{motive}

def Erase.mu_motive_of_state(name: String, family: F.Positivity.family, indices: List<&2, F.Value.t>, elim: F.Term.elim) -> Erase.State<F.Term.motive>:
  F.Positivity.Family{family_name, params, expected, level, status, ctors, positive} = family
  F.Term.Elimination{shape, scrut, q, motive, branches} = elim
  Erase.bind_state(F.Term.motive, F.Term.motive, Erase.require_state(F.Term.motive, motive, F.Error.Cannot_infer{"an elimination at a mu shape needs a motive"}), mo =>
    Erase.mu_motive_check_state(mo, name, Erase.length(F.Triple3<F.Quantity.t, String, F.Term.t>, expected), Erase.length(F.Value.t, indices)))

def Erase.branch_arity_word() -> String:
  "a branch binds a different number of fields than its constructor takes"

type Erase.MuScope is Data:
  Erase.MuScope{ec: Erase.ectx, env: List<&2, F.Value.t>, values: List<&2, F.Value.t>, arity: Nat}

def Erase.mu_binders_state(tele: F.Positivity.telescope, binders: List<&2, F.Pair2<F.Quantity.t, String>>, layout: List<&2, Maybe<&2, Eterm.repr>>, state: Erase.MuScope) -> Erase.State<Erase.MuScope>:
  match tele:
    case Nil{}:
      match binders:
        case Nil{}:
          match layout:
            case Nil{}: Erase.Return{state}
            case other: Erase.Raise{F.Error.Missing_branch{Erase.branch_arity_word}}
        case other: Erase.Raise{F.Error.Missing_branch{Erase.branch_arity_word}}
    case F.Triple3{q, name, ty} <> rest:
      match binders:
        case Nil{}: Erase.Raise{F.Error.Missing_branch{Erase.branch_arity_word}}
        case F.Pair2{bq, bx} <> more:
          match layout:
            case Nil{}: Erase.Raise{F.Error.Missing_branch{Erase.branch_arity_word}}
            case field <> fields:
              Erase.MuScope{+ec, +env, values, arity} = state
              +keep = Erase.present(Eterm.repr, field)
              +value = F.Value.var(Erase.size_of(ec))
              Erase.bind_state(F.Value.t, Erase.MuScope, Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec), env, ty)), domain =>
                Erase.mu_binders_state(rest, more, fields, Erase.MuScope{Erase.bind_context(ec, bx, q, domain, keep), value <> env, value <> values, (arity + Erase.bool_nat(keep) : Nat)}))

def Erase.address_equal(a: F.Term.addr, b: F.Term.addr) -> Bool:
  match a:
    case F.Term.ALeg{k}:
      match b:
        case F.Term.ALeg{j}: Nat.is_eq(k, j)
        case other: False{}
    case F.Term.ACtor{name}:
      match b:
        case F.Term.ACtor{name2}: String.eq(name, name2)
        case other: False{}
    case F.Term.APt{q, term}: False{}

def Erase.branch_choice(hit: Bool, leg: F.Term.leg, other: Maybe<&2, F.Term.leg>) -> Maybe<&2, F.Term.leg>:
  match hit:
    case True{}: Some{leg}
    case False{}: other

def Erase.find_branch(branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +key: F.Term.addr) -> Maybe<&2, F.Term.leg>:
  match branches:
    case Nil{}: None{}
    case F.Pair2{address, leg} <> rest:
      Erase.branch_choice(Erase.address_equal(address, key), leg, Erase.find_branch(rest, key))

type Erase.BranchPlan is Data:
  Erase.BranchPlan{ec: Erase.ectx, target: F.Value.t, body: F.Term.t, tag: Nat, arity: Nat}

def Erase.mu_branch_scope_state(scope: Erase.MuScope, +ec: Erase.ectx, motive: F.Term.motive, +name: String, +ctor_name: String, result_indices: List<&2, F.Term.t>, body: F.Term.t, tag: Nat) -> Erase.State<Erase.BranchPlan>:
  Erase.MuScope{next_context, env, values, arity} = scope
  do Erase.State<Erase.BranchPlan>:
    +indices: List<&2, F.Value.t> <- Erase.eval_terms_state(result_indices, ec, env)
    target: F.Value.t <- Erase.mu_result_state(motive, ec, indices, F.Value.VIn{F.Shape.SMu{name, indices}, F.Value.VACtor{ctor_name}, Erase.reverse(F.Value.t, values, Nil{})})
    Erase.Return{Erase.BranchPlan{next_context, target, body, tag, arity}}

def Erase.mu_branch_leg_state(~ops: Erase.Semantics, leg: F.Term.leg, +ctor: F.Positivity.ctor, +ec: Erase.ectx, family: F.Positivity.family, motive: F.Term.motive, penv: List<&2, F.Value.t>, name: String, ctor_name: String, tag: Nat) -> Erase.State<Erase.BranchPlan>:
  F.Term.Leg{binders, body} = leg
  F.Positivity.Ctor{ignored, args, indices, full_arity, recursive} = ctor
  do Erase.State<Erase.BranchPlan>:
    layout: List<&2, Maybe<&2, Eterm.repr>> <- Erase.mu_layout_state(~ops, ec, family, ctor)
    scope: Erase.MuScope <- Erase.mu_binders_state(args, binders, layout, Erase.MuScope{ec, penv, Nil{}, 0n})
    Erase.mu_branch_scope_state(scope, ec, motive, name, ctor_name, indices, body, tag)

def Erase.mu_branch_plan_state(~ops: Erase.Semantics, ec: Erase.ectx, +family: F.Positivity.family, motive: F.Term.motive, penv: List<&2, F.Value.t>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, +name: String, +ctor_name: String, tag: Nat) -> Erase.State<Erase.BranchPlan>:
  do Erase.State<Erase.BranchPlan>:
    ctor: F.Positivity.ctor <- Erase.require_state(F.Positivity.ctor, Erase.ctor_of(ctor_name, family), F.Error.Unbound{ctor_name ++ " is not a constructor of " ++ name})
    leg: F.Term.leg <- Erase.require_state(F.Term.leg, Erase.find_branch(branches, F.Term.ACtor{ctor_name}), F.Error.Missing_branch{"the elimination of " ++ name ++ " has no branch at " ++ ctor_name})
    Erase.mu_branch_leg_state(~ops, leg, ctor, ec, family, motive, penv, name, ctor_name, tag)

def Erase.case_binder_state(~ops: Erase.Semantics, binder: F.Pair2<F.Quantity.t, String>, +ec: Erase.ectx, +lty: F.Value.t, ty: F.Value.t, motive: Maybe<&2, F.Term.motive>, body: F.Term.t, width: Nat, +tag: Nat) -> Erase.State<Erase.BranchPlan>:
  F.Pair2{+q, name} = binder
  do Erase.State<Erase.BranchPlan>:
    +keep: Bool <- Erase.point_runtime_state(~ops, ec, q, lty)
    target: F.Value.t <- Erase.elim_result_state(motive, ec, ty, F.Value.VIn{F.Shape.SColl{width}, F.Value.VALeg{tag}, [F.Value.var(Erase.size_of(ec))]})
    Erase.Return{Erase.BranchPlan{Erase.bind_context(ec, name, q, lty, keep), target, body, tag, Erase.bool_nat(keep)}}

def Erase.case_leg_state(~ops: Erase.Semantics, leg: F.Term.leg, ec: Erase.ectx, lty: F.Value.t, ty: F.Value.t, motive: Maybe<&2, F.Term.motive>, width: Nat, tag: Nat) -> Erase.State<Erase.BranchPlan>:
  F.Term.Leg{binders, body} = leg
  Erase.bind_state(F.Pair2<F.Quantity.t, String>, Erase.BranchPlan, Erase.require_state(F.Pair2<F.Quantity.t, String>, Erase.one(F.Pair2<F.Quantity.t, String>, binders), F.Error.Mismatch{"a case branch takes one binder"}), binder =>
    Erase.case_binder_state(~ops, binder, ec, lty, ty, motive, body, width, tag))

def Erase.case_branch_plan_state(~ops: Erase.Semantics, ec: Erase.ectx, ty: F.Value.t, +tys: List<&2, F.Value.t>, elim: F.Term.elim, +tag: Nat) -> Erase.State<Erase.BranchPlan>:
  F.Term.Elimination{shape, scrut, q, motive, branches} = elim
  do Erase.State<Erase.BranchPlan>:
    lty: F.Value.t <- Erase.require_state(F.Value.t, Erase.at(F.Value.t, tys, tag), F.Error.Mismatch{"a leg number is outside the collection"})
    leg: F.Term.leg <- Erase.require_state(F.Term.leg, Erase.find_branch(branches, F.Term.ALeg{tag}), F.Error.Mismatch{"a case is missing a branch"})
    Erase.case_leg_state(~ops, leg, ec, lty, ty, motive, Erase.length(F.Value.t, tys), tag)

def Erase.refusal(shape: F.Shape.t<F.Term.t>) -> F.Error.t:
  match shape:
    case F.Shape.SPar{a, b}: F.Error.Not_yet{P.Rules.spar_word}
    case F.Shape.SNu{name, indices}: F.Error.Not_yet{P.Rules.snu_word}
    case other: F.Error.Not_yet{"an erasure at a shape past M0"}

def Erase.extra_context(ec: Erase.ectx) -> Erase.ectx:
  Erase.Context{checker, slots, self} = ec
  Erase.Context{checker, Erase.SExtra{} <> slots, self}

type Erase.PairScope is Data:
  Erase.PairScope{ec: Erase.ectx, body: F.Term.t, first: String, second: String, keep_first: Bool, keep_second: Bool}

def Erase.pair_binders_state(~ops: Erase.Semantics, binders: List<&2, F.Pair2<F.Quantity.t, String>>, body: F.Term.t, +ec: Erase.ectx, +q: F.Quantity.t, +name: String, +domain: F.Value.t, diagram: F.Value.closure) -> Erase.State<Erase.PairScope>:
  match binders:
    case first <> F.Pair2{second_q, +second_name} <> Nil{}:
      do Erase.State<Erase.PairScope>:
        +keep1: Bool <- Erase.point_runtime_state(~ops, ec, q, domain)
        +cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec), diagram, [F.Value.var(Erase.size_of(ec))]))
        (+ec1 = Erase.bind_context(Erase.extra_context(ec), name, q, domain, keep1)
         Erase.bind_state(Bool, Erase.PairScope, Erase.runtime_ty_state(~ops, ec1, cod), second_keep =>
           (+keep2 : Bool = second_keep
            Erase.Return{Erase.PairScope{Erase.bind_context(ec1, second_name, F.Quantity.Many{}, cod, keep2), body, name, second_name, keep1, keep2}})))
    case other: Erase.Raise{F.Error.Mismatch{"a pair branch takes two binders"}}

def Erase.pair_leg_state(~ops: Erase.Semantics, branch: F.Pair2<F.Term.addr, F.Term.leg>, ec: Erase.ectx, q: F.Quantity.t, name: String, domain: F.Value.t, diagram: F.Value.closure) -> Erase.State<Erase.PairScope>:
  F.Pair2{address, F.Term.Leg{binders, body}} = branch
  Erase.pair_binders_state(~ops, binders, body, ec, q, name, domain, diagram)

def Erase.pair_scope_state(~ops: Erase.Semantics, elim: F.Term.elim, ec: Erase.ectx, q: F.Quantity.t, name: String, domain: F.Value.t, diagram: F.Value.closure) -> Erase.State<Erase.PairScope>:
  F.Term.Elimination{shape, scrut, quantity, motive, branches} = elim
  Erase.bind_state(F.Pair2<F.Term.addr, F.Term.leg>, Erase.PairScope, Erase.require_state(F.Pair2<F.Term.addr, F.Term.leg>, Erase.one(F.Pair2<F.Term.addr, F.Term.leg>, branches), F.Error.Mismatch{"a pair elimination takes one branch"}), branch =>
    Erase.pair_leg_state(~ops, branch, ec, q, name, domain, diagram))

def Erase.pair_target_state(+ec: Erase.ectx, elim: F.Term.elim, ty: F.Value.t, q: F.Quantity.t) -> Erase.State<F.Value.t>:
  F.Term.Elimination{shape, scrut, quantity, motive, branches} = elim
  Erase.bind_state(F.Shape.t<F.Value.t>, F.Value.t, Erase.eval_shape_state(ec, shape), sv =>
    Erase.elim_result_state(motive, ec, ty, F.Value.VIn{sv, F.Value.VAPt{q, F.Value.var(Erase.size_of(ec))}, [F.Value.var(1n+Erase.size_of(ec))]}))

def Erase.pair_inner(keep: Bool, name: String, tid: Eterm.tid, index: Nat, body: Eterm.ktm) -> Eterm.ktm:
  match keep:
    case False{}: body
    case True{}:
      +i : Nat = index
      Eterm.KLet{name, Eterm.KProj{tid, i, Eterm.KVar{i}}, body}

def Erase.pair_finish(scope: Erase.PairScope, +tid: Eterm.tid, scrut: Eterm.ktm, body: Eterm.ktm) -> Eterm.ktm:
  Erase.PairScope{context, original_body, first, second, +keep1, keep2} = scope
  inner = Erase.pair_inner(keep2, second, tid, Erase.bool_nat(keep1), body)
  Eterm.KLet{"scrut", scrut, Erase.pair_inner(keep1, first, tid, 0n, inner)}

def Erase.define_context(ec: Erase.ectx, name: String, ty: F.Value.t, value: F.Value.t, keep: Bool) -> Erase.ectx:
  Erase.Context{checker, slots, self} = ec
  Erase.Context{C.Check.define(name, F.Quantity.Many{}, ty, value, checker), Erase.slot_of(keep) <> slots, self}

def Erase.point_arg_state(address: F.Term.addr) -> Erase.State<F.Term.t>:
  match address:
    case F.Term.APt{q, arg}: Erase.Return{arg}
    case other: Erase.Raise{F.Error.Mismatch{"a pair takes a point address"}}

def Erase.leg_address_state(address: F.Term.addr, message: String) -> Erase.State<Nat>:
  match address:
    case F.Term.ALeg{k}: Erase.Return{k}
    case other: Erase.Raise{F.Error.Mismatch{message}}

def Erase.ctor_address_state(address: F.Term.addr) -> Erase.State<String>:
  match address:
    case F.Term.ACtor{name}: Erase.Return{name}
    case other: Erase.Raise{F.Error.Mismatch{"a constructor takes a constructor address"}}

def Erase.mu_shape_state(shape: F.Shape.t<F.Value.t>, message: String) -> Erase.State<F.Pair2<String, List<&2, F.Value.t>>>:
  match shape:
    case F.Shape.SMu{name, indices}: Erase.Return{F.Pair2{name, indices}}
    case other: Erase.Raise{F.Error.Mismatch{message}}

type Erase.ChainResult is Data:
  Erase.ChainResult{params: List<&2, Eterm.repr>, ret: Eterm.repr, body: Eterm.ktm, acc: Erase.acc}

type Erase.Task<-A: Data> is Type:
  Erase.Term{ec: Erase.ectx, acc: Erase.acc, tail: Bool, expected: Maybe<&2, F.Value.t>, term: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Runtime{ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, term: F.Term.t, keep: Bool, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Node{ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, term: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Fold{ec: Erase.ectx, acc: Erase.acc, jobs: List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, done: List<&2, Eterm.ktm> -> Erase.acc -> Erase.State<A>}
  Erase.Struct{ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, fields: List<&2, Eterm.ktm>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Chain{ec: Erase.ectx, acc: Erase.acc, params: List<&2, Eterm.repr>, ty: F.Value.t, term: F.Term.t, done: Erase.ChainResult -> Erase.State<A>}
  Erase.ChainNormal{ec: Erase.ectx, acc: Erase.acc, params: List<&2, Eterm.repr>, ty: F.Value.t, term: F.Term.t, normal: F.Value.t, done: Erase.ChainResult -> Erase.State<A>}
  Erase.ChainStop{ec: Erase.ectx, acc: Erase.acc, params: List<&2, Eterm.repr>, ty: F.Value.t, term: F.Term.t, done: Erase.ChainResult -> Erase.State<A>}
  Erase.ChainPoint{ec: Erase.ectx, acc: Erase.acc, params: List<&2, Eterm.repr>, ty: F.Value.t, term: F.Term.t, lam: Maybe<&2, F.Term.leg>, quantity: F.Quantity.t, name: String, domain: F.Value.t, diagram: F.Value.closure, done: Erase.ChainResult -> Erase.State<A>}
  Erase.Eta{signature: F.Pair2<List<&2, Eterm.repr>, Eterm.repr>, params: List<&2, Eterm.repr>, head: Eterm.ktm, acc: Erase.acc, done: Erase.ChainResult -> Erase.State<A>}
  Erase.Lift{ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, term: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.LiftChain{result: Erase.ChainResult, fid: Eterm.fid, cap_reprs: List<&2, Eterm.repr>, cap_args: List<&2, Eterm.ktm>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.LiftPruned{pruned: F.Triple3<List<&2, Eterm.repr>, List<&2, Eterm.ktm>, Eterm.ktm>, fid: Eterm.fid, params: List<&2, Eterm.repr>, ret: Eterm.repr, acc: Erase.acc, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Tuple{normal: F.Value.t, ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, width: Nat, legs: List<&2, F.Term.leg>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Intro{normal: F.Value.t, ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, address: F.Term.addr, args: List<&2, F.Term.t>, nominal: Bool, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.IntroLeft{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, address: F.Term.addr, args: List<&2, F.Term.t>, nominal: Bool, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.IntroLeftNominal{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, address: F.Term.addr, args: List<&2, F.Term.t>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.IntroLeftTyped{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, ty: F.Value.t, address: F.Term.addr, args: List<&2, F.Term.t>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.MuIntro{name: String, indices: List<&2, F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, address: F.Term.addr, args: List<&2, F.Term.t>, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.MuFields{tele: F.Positivity.telescope, args: List<&2, F.Term.t>, layout: List<&2, Maybe<&2, Eterm.repr>>, ec: Erase.ectx, acc: Erase.acc, env: List<&2, F.Value.t>, done: List<&2, Eterm.ktm> -> Erase.acc -> Erase.State<A>}
  Erase.MuField{keep: Bool, ty: F.Value.t, arg: F.Term.t, tele: F.Positivity.telescope, args: List<&2, F.Term.t>, layout: List<&2, Maybe<&2, Eterm.repr>>, ec: Erase.ectx, acc: Erase.acc, env: List<&2, F.Value.t>, done: List<&2, Eterm.ktm> -> Erase.acc -> Erase.State<A>}
  Erase.Application{spine: F.Pair2<F.Term.t, List<&2, F.Triple3<F.Quantity.t, F.Term.t, F.Term.t>>>, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.ApplicationJobs{jobs: F.Pair2<List<&2, F.Pair2<Maybe<&2, F.Value.t>, F.Term.t>>, F.Value.t>, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, head_ty: F.Value.t, head: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Projection{normal: F.Value.t, ec: Erase.ectx, acc: Erase.acc, scrut_ty: F.Value.t, width: Nat, index: Nat, head: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Eliminate{normal: F.Value.t, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, scrut_ty: F.Value.t, elim: F.Term.elim, nominal: Bool, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.EliminateLeft{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, scrut_ty: F.Value.t, elim: F.Term.elim, nominal: Bool, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.EliminateLeftNominal{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, scrut_ty: F.Value.t, elim: F.Term.elim, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.EliminateLeftTyped{shape: F.Shape.t<F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, scrut_ty: F.Value.t, elim: F.Term.elim, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.PairElim{scope: Erase.PairScope, quantity: F.Quantity.t, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, scrut_ty: F.Value.t, elim: F.Term.elim, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.Cases{remaining: Nat, index: Nat, ec: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, types: List<&2, F.Value.t>, elim: F.Term.elim, done: List<&2, Eterm.branch<Eterm.ktm>> -> Erase.acc -> Erase.State<A>}
  Erase.Branch{plan: Erase.BranchPlan, acc: Erase.acc, tail: Bool, done: Eterm.branch<Eterm.ktm> -> Erase.acc -> Erase.State<A>}
  Erase.MuElim{name: String, indices: List<&2, F.Value.t>, diagram: F.Value.closure, ec: Erase.ectx, acc: Erase.acc, tail: Bool, scrut_ty: F.Value.t, elim: F.Term.elim, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}
  Erase.MuCases{names: List<&2, String>, index: Nat, family: F.Positivity.family, motive: F.Term.motive, penv: List<&2, F.Value.t>, branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, name: String, ec: Erase.ectx, acc: Erase.acc, tail: Bool, done: List<&2, Eterm.branch<Eterm.ktm>> -> Erase.acc -> Erase.State<A>}
  Erase.Let{keep: Bool, ec: Erase.ectx, next_context: Erase.ectx, acc: Erase.acc, tail: Bool, ty: F.Value.t, name: String, local_ty: F.Value.t, value: F.Term.t, body: F.Term.t, done: Eterm.ktm -> Erase.acc -> Erase.State<A>}

def Erase.position_ty_state(~ops: Erase.Semantics, expected: Maybe<&2, F.Value.t>, ec: Erase.ectx, term: F.Term.t) -> Erase.State<F.Value.t>:
  match expected:
    case Some{ty}: Erase.Return{ty}
    case None{}: Erase.semantic_infer_state(ops, Erase.checker(ec), F.Quantity.Many{}, term)

def Erase.acc_next(acc: Erase.acc) -> Erase.acc:
  Erase.Acc{next, lifted, groups} = acc
  Erase.Acc{1n+next, lifted, groups}

def Erase.acc_lift(acc: Erase.acc, decl: Eterm.kdecl) -> Erase.acc:
  Erase.Acc{next, lifted, groups} = acc
  Erase.Acc{next, Erase.append(Eterm.kdecl, lifted, [decl]), groups}

def Erase.acc_group(acc: Erase.acc, group: List<&2, Eterm.tid>) -> Erase.acc:
  Erase.Acc{next, lifted, groups} = acc
  Erase.Acc{next, lifted, Erase.append(Eterm.tid, groups, group)}

def Erase.lift_name(ec: Erase.ectx, acc: Erase.acc) -> Eterm.fid:
  Erase.Context{checker, slots, name} = ec
  Erase.Acc{next, lifted, groups} = acc
  Eterm.Fid{name ++ "$" ++ F.Text.nat(next)}

def Erase.context_slots(ec: Erase.ectx) -> List<&2, Erase.slot>:
  Erase.Context{checker, slots, name} = ec
  slots

def Erase.frame_context(ec: Erase.ectx, captures: List<&2, Nat>) -> Erase.ectx:
  Erase.Context{checker, slots, name} = ec
  Erase.Context{checker, Erase.frame(slots, captures), name}

def Erase.ctor_args(ctor: F.Positivity.ctor) -> F.Positivity.telescope:
  F.Positivity.Ctor{name,args,indices,arity,recursive} = ctor
  args

def Erase.elim_scrut(elim: F.Term.elim) -> F.Term.t:
  F.Term.Elimination{shape,scrut,q,motive,branches} = elim
  scrut

def Erase.elim_branches(elim: F.Term.elim) -> List<&2,F.Pair2<F.Term.addr,F.Term.leg>>:
  F.Term.Elimination{shape,scrut,q,motive,branches} = elim
  branches

def Erase.pair_context(scope: Erase.PairScope) -> Erase.ectx:
  Erase.PairScope{ec,body,first,second,keep1,keep2} = scope
  ec

def Erase.pair_body(scope: Erase.PairScope) -> F.Term.t:
  Erase.PairScope{ec,body,first,second,keep1,keep2} = scope
  body

# The dispatcher follows finite source syntax and semantic function telescopes.
# CPS continuations obscure structural descent from Bend's termination checker.
@unsafe
def Erase.run_state(~ops: Erase.Semantics, -A: Data, task: Erase.Task<A>) -> Erase.State<A>:
  match task:
    case Erase.Term{+ec, acc, tail, expected, +term, done}:
      do Erase.State<A>:
        +ty: F.Value.t <- Erase.position_ty_state(~ops, expected, ec, term)
        keep: Bool <- Erase.runtime_ty_state(~ops, ec, ty)
        Erase.run_state(~ops, A, Erase.Runtime{ec, acc, tail, ty, term, keep, done})
    case Erase.Runtime{ec, acc, tail, ty, term, keep, done}:
      match keep:
        case False{}: done(Eterm.KErased{}, acc)
        case True{}: Erase.run_state(~ops, A, Erase.Node{ec, acc, tail, ty, term, done})
    case Erase.Node{+ec, +acc, tail, +ty, term, done}:
      match term:
        case F.Term.Var{ix}: Erase.bind_state(Eterm.ktm, A, Erase.var_arm_state(ec, ix), value => done(value, acc))
        case F.Term.Univ{level}: done(Eterm.KErased{}, acc)
        case F.Term.Lan{shape, diagram}: done(Eterm.KErased{}, acc)
        case F.Term.Ran{shape, diagram}: done(Eterm.KErased{}, acc)
        case F.Term.Global{name}: done(Eterm.KGlobal{name}, acc)
        case F.Term.Lit{literal}: done(Eterm.KLit{literal}, acc)
        case F.Term.Auto{}: Erase.Raise{F.Error.Not_yet{P.Rules.auto_word}}
        case F.Term.Ann{body, annotation}: Erase.run_state(~ops, A, Erase.Term{ec, acc, tail, Some{ty}, body, done})
        case F.Term.Sec{shape, legs}:
          match shape:
            case F.Shape.SPi{q, name, domain}: Erase.run_state(~ops, A, Erase.Lift{ec, acc, ty, F.Term.Sec{F.Shape.SPi{q,name,domain},legs}, done})
            case F.Shape.SColl{width}:
              Erase.bind_state(F.Value.t, A, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty)), normal => Erase.run_state(~ops, A, Erase.Tuple{normal,ec,acc,ty,width,legs,done}))
            case F.Shape.SMu{name, indices}: Erase.Raise{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}
            case other: Erase.Raise{Erase.refusal(other)}
        case F.Term.In{shape, address, args}:
          match shape:
            case F.Shape.SPar{a,b}: Erase.Raise{F.Error.Not_yet{P.Rules.spar_word}}
            case F.Shape.SNu{name, indices}: Erase.Raise{F.Error.Not_yet{P.Rules.snu_word}}
            case F.Shape.SMu{name, indices}:
              Erase.bind_state(F.Value.t, A, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty)), normal => Erase.run_state(~ops,A,Erase.Intro{normal,ec,acc,ty,address,args,True{},done}))
            case other:
              Erase.bind_state(F.Value.t, A, Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec), ty)), normal => Erase.run_state(~ops,A,Erase.Intro{normal,ec,acc,ty,address,args,False{},done}))
        case F.Term.Out{shape, address, +head}:
          match shape:
            case F.Shape.SPi{q,name,domain}: Erase.run_state(~ops,A,Erase.Application{Erase.spine(F.Term.Out{F.Shape.SPi{q,name,domain},address,head},Nil{}),ec,acc,tail,ty,done})
            case F.Shape.SColl{width}:
              do Erase.State<A>:
                index: Nat <- Erase.leg_address_state(address,"a projection takes a leg address")
                +sty: F.Value.t <- Erase.semantic_infer_state(ops,Erase.checker(ec),F.Quantity.Many{},head)
                normal: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec),sty))
                Erase.run_state(~ops,A,Erase.Projection{normal,ec,acc,sty,width,index,head,done})
            case F.Shape.SMu{name, indices}: Erase.Raise{F.Error.Not_yet{"a right former at a mu shape arrives at M2"}}
            case other: Erase.Raise{Erase.refusal(other)}
        case F.Term.Elim{elim}:
          F.Term.Elimination{+shape,+scrut,+q,+motive,+branches} = elim
          match shape:
            case F.Shape.SPar{a,b}: Erase.Raise{F.Error.Not_yet{P.Rules.spar_word}}
            case F.Shape.SNu{name,indices}: Erase.Raise{F.Error.Not_yet{P.Rules.snu_word}}
            case F.Shape.SMu{name,indices}:
              do Erase.State<A>:
                +sty: F.Value.t <- Erase.semantic_infer_state(ops,Erase.checker(ec),F.Quantity.Many{},scrut)
                normal: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec),sty))
                Erase.run_state(~ops,A,Erase.Eliminate{normal,ec,acc,tail,ty,sty,F.Term.Elimination{F.Shape.SMu{name,indices},scrut,q,motive,branches},True{},done})
            case other:
              do Erase.State<A>:
                +sty: F.Value.t <- Erase.semantic_infer_state(ops,Erase.checker(ec),F.Quantity.Many{},scrut)
                normal: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec),sty))
                Erase.run_state(~ops,A,Erase.Eliminate{normal,ec,acc,tail,ty,sty,F.Term.Elimination{other,scrut,q,motive,branches},False{},done})
        case F.Term.Let{+name,lty,+value,body}:
          do Erase.State<A>:
            +local_ty: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),Erase.env_of(ec),lty))
            +keep: Bool <- Erase.runtime_ty_state(~ops,ec,local_ty)
            vv: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),Erase.env_of(ec),value))
            Erase.run_state(~ops,A,Erase.Let{keep,ec,Erase.define_context(ec,name,local_ty,vv,keep),acc,tail,ty,name,local_ty,value,body,done})
    case Erase.Fold{+ec,acc,jobs,done}:
      match jobs:
        case Nil{}: done(Nil{},acc)
        case F.Pair2{expected,term} <> rest:
          Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},expected,term,first => next => Erase.run_state(~ops,A,Erase.Fold{ec,next,rest,more => last => done(first <> more,last)})})
    case Erase.Struct{ec,acc,ty,fields,done}:
      match fields:
        case Nil{}: done(Eterm.KErased{},acc)
        case first <> rest: Erase.bind_state(Eterm.tid,A,Erase.tid_of_state(~ops,ec,ty),tid => done(Eterm.KStruct{tid,first <> rest},acc))
    case Erase.Chain{+ec,acc,params,+ty,term,done}:
      Erase.bind_state(F.Value.t,A,Erase.State.lift(F.Value.t, E.Eval.whnf(Erase.globals_of(ec),ty)),normal => Erase.run_state(~ops,A,Erase.ChainNormal{ec,acc,params,ty,term,normal,done}))
    case Erase.ChainNormal{ec,acc,params,ty,+term,normal,done}:
      match normal:
        case F.Value.VRan{shape,diagram,universe}:
          match shape:
            case F.Shape.SPi{q,name,domain}: Erase.run_state(~ops,A,Erase.ChainPoint{ec,acc,params,ty,term,Erase.as_lam(term),q,name,domain,diagram,done})
            case other: Erase.run_state(~ops,A,Erase.ChainStop{ec,acc,params,ty,term,done})
        case other: Erase.run_state(~ops,A,Erase.ChainStop{ec,acc,params,ty,term,done})
    case Erase.ChainStop{+ec,acc,params,+ty,term,done}:
      Erase.bind_state(Eterm.repr,A,Erase.repr_of_state(~ops,ec,ty),ret => Erase.run_state(~ops,A,Erase.Term{ec,acc,True{},Some{ty},term,body => next => done(Erase.ChainResult{params,ret,body,next})}))
    case Erase.ChainPoint{+ec,acc,params,ty,term,lam,+quantity,+name,+domain,+diagram,done}:
      match lam:
        case Some{F.Term.Leg{binders,body}}:
          do Erase.State<A>:
            +keep: Bool <- Erase.point_runtime_state(~ops,ec,quantity,domain)
            here: List<&2,Eterm.repr> <- Erase.repr_params_state(~ops,keep,ec,domain)
            cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec),diagram,[F.Value.var(Erase.size_of(ec))]))
            Erase.run_state(~ops,A,Erase.Chain{Erase.bind_context(ec,name,quantity,domain,keep),acc,Erase.append(Eterm.repr,params,here),cod,body,done})
        case None{}:
          Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{ty},term,head => next =>
            Erase.bind_state(F.Pair2<List<&2,Eterm.repr>,Eterm.repr>,A,Erase.remaining_signature_state(~ops,ec,F.Shape.SPi{quantity,name,domain},diagram),signature => Erase.run_state(~ops,A,Erase.Eta{signature,params,head,next,done}))})
    case Erase.Eta{F.Pair2{+extra,ret},params,head,acc,done}:
      +n : Nat = Erase.length(Eterm.repr,extra)
      done(Erase.ChainResult{Erase.append(Eterm.repr,params,extra),ret,Eterm.KTail{Erase.shift_runtime(n,0n,head),Erase.eta_args(n)},acc})
    case Erase.Lift{+ec,+acc,ty,+term,done}:
      +caps : List<&2,Nat> = Erase.captures_of(Erase.context_slots(ec),term)
      +outer : List<&2,Nat> = Erase.reverse(Nat,caps,Nil{})
      do Erase.State<A>:
        cap_reprs: List<&2,Eterm.repr> <- Erase.capture_reprs_state(~ops,outer,ec)
        cap_args: List<&2,Eterm.ktm> <- Erase.capture_args_state(outer,ec)
        Erase.run_state(~ops,A,Erase.Chain{Erase.frame_context(ec,caps),Erase.acc_next(acc),Nil{},ty,term,result => Erase.run_state(~ops,A,Erase.LiftChain{result,Erase.lift_name(ec,acc),cap_reprs,cap_args,done})})
    case Erase.LiftChain{Erase.ChainResult{+params,ret,body,acc},fid,cap_reprs,cap_args,done}:
      Erase.run_state(~ops,A,Erase.LiftPruned{Erase.prune_captures(cap_reprs,cap_args,Erase.length(Eterm.repr,params),body),fid,params,ret,acc,done})
    case Erase.LiftPruned{F.Triple3{cap_reprs,cap_args,body},+fid,+params,ret,acc,done}:
      done(Eterm.KClos{fid,Erase.length(Eterm.repr,params),cap_args},Erase.acc_lift(acc,Eterm.KFun{fid,Erase.append(Eterm.repr,cap_reprs,params),ret,body}))
    case Erase.Tuple{normal,+ec,acc,ty,width,legs,done}:
      match normal:
        case F.Value.VRan{shape,diagram,universe}:
          do Erase.State<A>:
            +types: List<&2,F.Value.t> <- Erase.leg_types_state(ec,width,diagram)
            flags: List<&2,Bool> <- Erase.leg_flags_state(~ops,types,ec)
            Erase.run_state(~ops,A,Erase.Fold{ec,acc,Erase.tuple_jobs(legs,types,flags),fields => next => Erase.run_state(~ops,A,Erase.Struct{ec,next,ty,fields,done})})
        case other: Erase.Raise{F.Error.Mismatch{"a tuple stands at a type that is not a right former"}}
    case Erase.Intro{normal,ec,acc,ty,address,args,nominal,done}:
      match normal:
        case F.Value.VLan{shape,diagram,universe}: Erase.run_state(~ops,A,Erase.IntroLeft{shape,diagram,ec,acc,ty,address,args,nominal,done})
        case other: Erase.Raise{F.Error.Mismatch{"an introduction stands at a type that is not a left former"}}
    case Erase.IntroLeft{shape,diagram,ec,acc,ty,address,args,nominal,done}:
      match nominal:
        case True{}: Erase.run_state(~ops,A,Erase.IntroLeftNominal{shape,diagram,ec,acc,ty,address,args,done})
        case False{}: Erase.run_state(~ops,A,Erase.IntroLeftTyped{shape,diagram,ec,acc,ty,address,args,done})
    case Erase.IntroLeftNominal{shape,+diagram,+ec,acc,+ty,address,args,done}:
      match shape:
        case F.Shape.SMu{name,indices}: Erase.run_state(~ops,A,Erase.MuIntro{name,indices,diagram,ec,acc,address,args,done})
        case other: Erase.Raise{F.Error.Mismatch{"an introduction at a shape past M0"}}
    case Erase.IntroLeftTyped{shape,+diagram,+ec,acc,+ty,address,args,done}:
      match shape:
        case F.Shape.SPi{+q,name,+domain}:
          do Erase.State<A>:
            +point: F.Term.t <- Erase.point_arg_state(address)
            fibre: F.Term.t <- Erase.require_state(F.Term.t,Erase.one(F.Term.t,args),F.Error.Mismatch{"a pair takes one fibre"})
            keep1: Bool <- Erase.point_runtime_state(~ops,ec,q,domain)
            cod: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec),diagram,[F.Value.var(Erase.size_of(ec))]))
            keep2: Bool <- Erase.runtime_ty_state(~ops,Erase.bind_context(ec,name,q,domain,False{}),cod)
            pv: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),Erase.env_of(ec),point))
            fty: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.open_closure(Erase.globals_of(ec),diagram,[pv]))
            Erase.run_state(~ops,A,Erase.Fold{ec,acc,Erase.append(F.Pair2<Maybe<&2,F.Value.t>,F.Term.t>,Erase.job(keep1,domain,point),Erase.job(keep2,fty,fibre)),fields => next => Erase.run_state(~ops,A,Erase.Struct{ec,next,ty,fields,done})})
        case F.Shape.SColl{width}:
          do Erase.State<A>:
            +tag: Nat <- Erase.leg_address_state(address,"an injection takes a leg address")
            types: List<&2,F.Value.t> <- Erase.leg_types_state(ec,width,diagram)
            +lty: F.Value.t <- Erase.require_state(F.Value.t,Erase.at(F.Value.t,types,tag),F.Error.Mismatch{"the leg address is outside the collection"})
            keep: Bool <- Erase.runtime_ty_state(~ops,ec,lty)
            payload: F.Term.t <- Erase.require_state(F.Term.t,Erase.one(F.Term.t,args),F.Error.Mismatch{"an injection takes one payload"})
            Erase.run_state(~ops,A,Erase.Fold{ec,acc,Erase.job(keep,lty,payload),fields => next => Erase.bind_state(Eterm.tid,A,Erase.tid_of_state(~ops,ec,ty),tid => done(Eterm.KTag{tid,tag,fields},next))})
        case other: Erase.Raise{F.Error.Mismatch{"an introduction at a shape past M0"}}
    case Erase.MuIntro{+name,indices,diagram,+ec,acc,address,args,done}:
      do Erase.State<A>:
        +ctor_name: String <- Erase.ctor_address_state(address)
        +family: F.Positivity.family <- Erase.mu_family_state(ec,name)
        names: List<&2,String> <- Erase.mu_ctor_names_state(name,family)
        tag: Nat <- Erase.require_state(Nat,Erase.position(ctor_name,names),F.Error.Unbound{ctor_name ++ " is not a constructor of " ++ name})
        +ctor: F.Positivity.ctor <- Erase.require_state(F.Positivity.ctor,Erase.ctor_of(ctor_name,family),F.Error.Unbound{ctor_name ++ " is not a constructor of " ++ name})
        penv: List<&2,F.Value.t> <- Erase.mu_param_env_state(ec,diagram)
        layout: List<&2,Maybe<&2,Eterm.repr>> <- Erase.mu_layout_state(~ops,ec,family,ctor)
        Erase.run_state(~ops,A,Erase.MuFields{Erase.ctor_args(ctor),args,layout,ec,acc,penv,fields => next => Erase.bind_state(List<&2,Eterm.tid>,A,Erase.mu_group_tids_state(~ops,ec,name,family),group => done(Eterm.KTag{Erase.mu_tid(name),tag,fields},Erase.acc_group(next,group)))})
    case Erase.MuFields{tele,args,layout,+ec,acc,+env,done}:
      match tele:
        case Nil{}:
          match args:
            case Nil{}:
              match layout:
                case Nil{}: done(Nil{},acc)
                case other: Erase.Raise{F.Error.Mismatch{Erase.branch_arity_word}}
            case other: Erase.Raise{F.Error.Mismatch{Erase.branch_arity_word}}
        case F.Triple3{q,name,ty} <> rest:
          match args:
            case Nil{}: Erase.Raise{F.Error.Mismatch{Erase.branch_arity_word}}
            case arg <> more:
              match layout:
                case Nil{}: Erase.Raise{F.Error.Mismatch{Erase.branch_arity_word}}
                case field <> fields:
                  Erase.bind_state(F.Value.t,A,Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),env,ty)),tyv => Erase.run_state(~ops,A,Erase.MuField{Erase.present(Eterm.repr,field),tyv,arg,rest,more,fields,ec,acc,env,done}))
    case Erase.MuField{keep,ty,+arg,tele,args,layout,+ec,acc,env,done}:
      match keep:
        case True{}:
          Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{ty},arg,here => next => Erase.bind_state(F.Value.t,A,Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),Erase.env_of(ec),arg)),av => Erase.run_state(~ops,A,Erase.MuFields{tele,args,layout,ec,next,av <> env,rest => last => done(here <> rest,last)}))})
        case False{}:
          Erase.bind_state(F.Value.t,A,Erase.State.lift(F.Value.t, E.Eval.eval(Erase.globals_of(ec),Erase.env_of(ec),arg)),av => Erase.run_state(~ops,A,Erase.MuFields{tele,args,layout,ec,acc,av <> env,done}))
    case Erase.Application{F.Pair2{+head,args},+ec,acc,tail,ty,done}:
      match args:
        case Nil{}: Erase.Raise{F.Error.Mismatch{"an application at a point shape with no point address"}}
        case first <> rest:
          do Erase.State<A>:
            +hty: F.Value.t <- Erase.semantic_infer_state(ops,Erase.checker(ec),F.Quantity.Many{},head)
            jobs: F.Pair2<List<&2,F.Pair2<Maybe<&2,F.Value.t>,F.Term.t>>,F.Value.t> <- Erase.app_jobs_state(~ops,first <> rest,ec,F.Pair2{Nil{},hty})
            Erase.run_state(~ops,A,Erase.ApplicationJobs{jobs,ec,acc,tail,ty,hty,head,done})
    case Erase.ApplicationJobs{F.Pair2{jobs,result_ty},+ec,acc,tail,ty,head_ty,head,done}:
      Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{head_ty},head,kh => next => Erase.run_state(~ops,A,Erase.Fold{ec,next,jobs,args => last => (+ka : List<&2,Eterm.ktm> = args
        Erase.bind_state(Bool,A,Erase.bare_application_state(ka,ec,ty),bare => done(Erase.apply_result(bare,tail,kh,ka),last)))})})
    case Erase.Projection{normal,+ec,acc,+scrut_ty,width,index,head,done}:
      match normal:
        case F.Value.VRan{shape,diagram,universe}:
          do Erase.State<A>:
            types: List<&2,F.Value.t> <- Erase.leg_types_state(ec,width,diagram)
            flags: List<&2,Bool> <- Erase.leg_flags_state(~ops,types,ec)
            Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{scrut_ty},head,kh => next => Erase.bind_state(Eterm.tid,A,Erase.tid_of_state(~ops,ec,scrut_ty),tid => done(Eterm.KProj{tid,Erase.count_kept(flags,index),kh},next))})
        case other: Erase.Raise{F.Error.Mismatch{"a projection stands on a value that is not a right former"}}
    case Erase.Eliminate{normal,ec,acc,tail,ty,scrut_ty,elim,nominal,done}:
      match normal:
        case F.Value.VLan{shape,diagram,universe}: Erase.run_state(~ops,A,Erase.EliminateLeft{shape,diagram,ec,acc,tail,ty,scrut_ty,elim,nominal,done})
        case other: Erase.Raise{F.Error.Mismatch{"an elimination stands on a value that is not a left former"}}
    case Erase.EliminateLeft{shape,diagram,ec,acc,tail,ty,scrut_ty,elim,nominal,done}:
      match nominal:
        case True{}: Erase.run_state(~ops,A,Erase.EliminateLeftNominal{shape,diagram,ec,acc,tail,ty,scrut_ty,elim,done})
        case False{}: Erase.run_state(~ops,A,Erase.EliminateLeftTyped{shape,diagram,ec,acc,tail,ty,scrut_ty,elim,done})
    case Erase.EliminateLeftNominal{shape,diagram,+ec,acc,tail,ty,+scrut_ty,+elim,done}:
      match shape:
        case F.Shape.SMu{name,indices}: Erase.run_state(~ops,A,Erase.MuElim{name,indices,diagram,ec,acc,tail,scrut_ty,elim,done})
        case other: Erase.Raise{F.Error.Mismatch{"an elimination at a shape past M0"}}
    case Erase.EliminateLeftTyped{shape,diagram,+ec,acc,tail,ty,+scrut_ty,+elim,done}:
      match shape:
        case F.Shape.SPi{+q,name,domain}:
          Erase.bind_state(Erase.PairScope,A,Erase.pair_scope_state(~ops,elim,ec,q,name,domain,diagram),scope => Erase.run_state(~ops,A,Erase.PairElim{scope,q,ec,acc,tail,ty,scrut_ty,elim,done}))
        case F.Shape.SColl{+width}:
          Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{scrut_ty},Erase.elim_scrut(elim),ks => next =>
            Erase.bind_state(List<&2,F.Value.t>,A,Erase.leg_types_state(ec,width,diagram),types => Erase.run_state(~ops,A,Erase.Cases{width,0n,ec,next,tail,ty,types,elim,branches => last => Erase.bind_state(Eterm.tid,A,Erase.tid_of_state(~ops,ec,scrut_ty),tid => done(Eterm.KCase{tid,ks,branches},last))}))})
        case other: Erase.Raise{F.Error.Mismatch{"an elimination at a shape past M0"}}
    case Erase.PairElim{+scope,quantity,+ec,acc,tail,ty,+scrut_ty,+elim,done}:
      Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{scrut_ty},Erase.elim_scrut(elim),ks => next =>
        Erase.bind_state(F.Value.t,A,Erase.pair_target_state(ec,elim,ty,quantity),target => Erase.run_state(~ops,A,Erase.Term{Erase.pair_context(scope),next,tail,Some{target},Erase.pair_body(scope),body => last => Erase.bind_state(Eterm.tid,A,Erase.tid_of_state(~ops,ec,scrut_ty),tid => done(Erase.pair_finish(scope,tid,ks,body),last))}))})
    case Erase.Cases{remaining,+index,+ec,acc,+tail,+ty,+types,+elim,done}:
      match remaining:
        case 0n: done(Nil{},acc)
        case 1n+rest:
          Erase.bind_state(Erase.BranchPlan,A,Erase.case_branch_plan_state(~ops,ec,ty,types,elim,index),plan => Erase.run_state(~ops,A,Erase.Branch{plan,acc,tail,branch => next => Erase.run_state(~ops,A,Erase.Cases{rest,1n+index,ec,next,tail,ty,types,elim,more => last => done(branch <> more,last)})}))
    case Erase.Branch{Erase.BranchPlan{ec,target,body,tag,arity},acc,tail,done}:
      Erase.run_state(~ops,A,Erase.Term{ec,acc,tail,Some{target},body,result => next => done(Eterm.Branch{tag,arity,result},next)})
    case Erase.MuElim{+name,indices,diagram,+ec,acc,+tail,scrut_ty,+elim,done}:
      do Erase.State<A>:
        +family: F.Positivity.family <- Erase.mu_family_state(ec,name)
        motive: F.Term.motive <- Erase.mu_motive_of_state(name,family,indices,elim)
        names: List<&2,String> <- Erase.mu_ctor_names_state(name,family)
        penv: List<&2,F.Value.t> <- Erase.mu_param_env_state(ec,diagram)
        Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{scrut_ty},Erase.elim_scrut(elim),ks => next => Erase.run_state(~ops,A,Erase.MuCases{names,0n,family,motive,penv,Erase.elim_branches(elim),name,ec,next,tail,branches => last => Erase.bind_state(List<&2,Eterm.tid>,A,Erase.mu_group_tids_state(~ops,ec,name,family),group => done(Eterm.KCase{Erase.mu_tid(name),ks,branches},Erase.acc_group(last,group)))})})
    case Erase.MuCases{names,+index,+family,+motive,+penv,+branches,+name,+ec,acc,+tail,done}:
      match names:
        case Nil{}: done(Nil{},acc)
        case ctor_name <> rest:
          Erase.bind_state(Erase.BranchPlan,A,Erase.mu_branch_plan_state(~ops,ec,family,motive,penv,branches,name,ctor_name,index),plan => Erase.run_state(~ops,A,Erase.Branch{plan,acc,tail,branch => next => Erase.run_state(~ops,A,Erase.MuCases{rest,1n+index,family,motive,penv,branches,name,ec,next,tail,more => last => done(branch <> more,last)})}))
    case Erase.Let{keep,ec,next_context,acc,tail,ty,name,local_ty,value,body,done}:
      match keep:
        case False{}: Erase.run_state(~ops,A,Erase.Term{next_context,acc,tail,Some{ty},body,done})
        case True{}: Erase.run_state(~ops,A,Erase.Term{ec,acc,False{},Some{local_ty},value,kv => next => Erase.run_state(~ops,A,Erase.Term{next_context,next,tail,Some{ty},body,kb => last => done(Eterm.KLet{name,kv,kb},last)})})

def Erase.term_state(~ops: Erase.Semantics, ec: Erase.ectx, acc: Erase.acc, tail: Bool, expected: Maybe<&2,F.Value.t>, term: F.Term.t) -> Erase.State<F.Pair2<Eterm.ktm,Erase.acc>>:
  Erase.run_state(~ops,F.Pair2<Eterm.ktm,Erase.acc>,Erase.Term{ec,acc,tail,expected,term,body => next => Erase.Return{F.Pair2{body,next}}})

def Erase.chain_state(~ops: Erase.Semantics, ec: Erase.ectx, acc: Erase.acc, params: List<&2,Eterm.repr>, ty: F.Value.t, term: F.Term.t) -> Erase.State<Erase.ChainResult>:
  Erase.run_state(~ops,Erase.ChainResult,Erase.Chain{ec,acc,params,ty,term,result => Erase.Return{result}})

def Erase.decl_tids(decls: List<&2,Eterm.kdecl>) -> List<&2,Eterm.tid>:
  match decls:
    case Nil{}: Nil{}
    case decl <> rest: Erase.append(Eterm.tid,Erase.tids_decl(decl),Erase.decl_tids(rest))

def Erase.definition_result(name: String, result: Erase.ChainResult) -> Erase.entry:
  Erase.ChainResult{params,ret,body,Erase.Acc{next,lifted,groups}} = result
  +decls : List<&2,Eterm.kdecl> = Erase.append(Eterm.kdecl,lifted,[Eterm.KFun{Eterm.Fid{name},params,ret,body}])
  Erase.Code{Eterm.KRec{Erase.dedup_tids(Erase.append(Eterm.tid,Erase.decl_tids(decls),groups))} <> decls}

def Erase.definition_state(~ops: Erase.Semantics, keep: Bool, ec: Erase.ectx, name: String, ty: F.Value.t, body: F.Term.t) -> Erase.State<Erase.entry>:
  match keep:
    case False{}: Erase.Return{Erase.Dropped{}}
    case True{}: Erase.bind_state(Erase.ChainResult,Erase.entry,Erase.chain_state(~ops,ec,Erase.Acc{0n,Nil{},Nil{}},Nil{},ty,body),result => Erase.Return{Erase.definition_result(name,result)})

def Erase.postulate_state(~ops: Erase.Semantics, keep: Bool, ec: Erase.ectx, ty: F.Value.t) -> Erase.State<Erase.entry>:
  match keep:
    case False{}: Erase.Return{Erase.Dropped{}}
    case True{}: Erase.bind_state(Eterm.repr,Erase.entry,Erase.repr_of_state(~ops,ec,ty),repr => Erase.Return{Erase.Postulate{repr}})

def Erase.decl_state(~ops: Erase.Semantics, +globals: F.Global.t, budget: C.Budget.t, +name: String, entry: F.Global.entry) -> Erase.State<Erase.entry>:
  match entry:
    case F.Global.Prim{primitive}: Erase.Return{Erase.Dropped{}}
    case F.Global.Axiom{F.Global.AxiomEntry{ty}}:
      +ec : Erase.ectx = Erase.Context{C.Check.make(globals,budget),Nil{},name}
      do Erase.State<Erase.entry>:
        +tyv: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(globals,Nil{},ty))
        keep: Bool <- Erase.runtime_ty_state(~ops,ec,tyv)
        Erase.postulate_state(~ops,keep,ec,tyv)
    case F.Global.Def{F.Global.DefEntry{ty,body,reducible,recursive,partial}}:
      +ec : Erase.ectx = Erase.Context{C.Check.make(globals,budget),Nil{},name}
      do Erase.State<Erase.entry>:
        +tyv: F.Value.t <- Erase.State.lift(F.Value.t, E.Eval.eval(globals,Nil{},ty))
        keep: Bool <- Erase.runtime_ty_state(~ops,ec,tyv)
        Erase.definition_state(~ops,keep,ec,name,tyv,body)

def Erase.program_rows_state(~ops: Erase.Semantics, rows: List<&2,F.Pair2<String,F.Global.entry>>, +budget: C.Budget.t, +globals: F.Global.t) -> Erase.State<List<&2,F.Pair2<String,Erase.entry>>>:
  match rows:
    case Nil{}: Erase.Return{Nil{}}
    case F.Pair2{+name,+entry} <> rest:
      do Erase.State<List<&2,F.Pair2<String,Erase.entry>>>:
        erased: Erase.entry <- Erase.decl_state(~ops,globals,budget,name,entry)
        more: List<&2,F.Pair2<String,Erase.entry>> <- Erase.program_rows_state(~ops,rest,budget,F.Global.add(name,entry,globals))
        Erase.Return{F.Pair2{name,erased} <> more}

def Erase.program_state(~ops: Erase.Semantics, budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> Erase.State<List<&2,F.Pair2<String,Erase.entry>>>:
  Erase.program_rows_state(~ops,rows,budget,globals)

def Erase.bind(-A: Data, -B: Data, result: Result<&2, &2, F.Error.t, A>, next: A -> Result<&2, &2, F.Error.t, B>) -> Result<&2, &2, F.Error.t, B>:
  Result.bind(&2, &2, F.Error.t, A, B, result, next)


def Erase.chain(~ops: Erase.Semantics, +ec: Erase.ectx, acc: Erase.acc, params: List<&2,Eterm.repr>, ty: F.Value.t, term: F.Term.t) -> Result<&2,&2,F.Error.t,Erase.ChainResult>:
  Erase.State.finish(Erase.ChainResult, Erase.chain_state(~ops, ec, acc, params, ty, term), C.Check.budget(Erase.checker(ec)))

def Erase.decl(~ops: Erase.Semantics, +globals: F.Global.t, +budget: C.Budget.t, +name: String, entry: F.Global.entry) -> Result<&2,&2,F.Error.t,Erase.entry>:
  Erase.State.finish(Erase.entry, Erase.decl_state(~ops, globals, budget, name, entry), budget)

def Erase.program(~ops: Erase.Semantics, +budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,Erase.entry>>>:
  Erase.State.finish(List<&2,F.Pair2<String,Erase.entry>>, Erase.program_state(~ops, budget, globals, rows), budget)

def Erase.program_stateful(~ops: Erase.Semantics, +budget: C.Budget.t, globals: F.Global.t, rows: List<&2,F.Pair2<String,F.Global.entry>>) -> F.Pair2<Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,Erase.entry>>>,C.Budget.t>:
  Erase.State.execute(List<&2,F.Pair2<String,Erase.entry>>, Erase.program_state(~ops, budget, globals, rows), budget)

def Erase.repr_of(~ops: Erase.Semantics, +ec: Erase.ectx, value: F.Value.t) -> Result<&2, &2, F.Error.t, Eterm.repr>:
  Erase.State.finish(Eterm.repr, Erase.repr_of_state(~ops, ec, value), C.Check.budget(Erase.checker(ec)))

def Erase.require(-A: Data, value: Maybe<&2, A>, reason: F.Error.t) -> Result<&2, &2, F.Error.t, A>:
  Erase.State.finish(A, Erase.require_state(A, value, reason), C.Budget.unlimited)

def Erase.runtime_ty(~ops: Erase.Semantics, +ec: Erase.ectx, ty: F.Value.t) -> Result<&2, &2, F.Error.t, Bool>:
  Erase.State.finish(Bool, Erase.runtime_ty_state(~ops, ec, ty), C.Check.budget(Erase.checker(ec)))

def Erase.term(~ops: Erase.Semantics, +ec: Erase.ectx, acc: Erase.acc, tail: Bool, expected: Maybe<&2,F.Value.t>, term: F.Term.t) -> Result<&2,&2,F.Error.t,F.Pair2<Eterm.ktm,Erase.acc>>:
  Erase.State.finish(F.Pair2<Eterm.ktm,Erase.acc>, Erase.term_state(~ops, ec, acc, tail, expected, term), C.Check.budget(Erase.checker(ec)))
