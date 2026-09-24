import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import ../lib/kernel_order.bend as O
import ../lib/kernel_pp.bend as Pp
import syntax.bend as S
import parser.bend as P
import elab_requests.bend as R
import elab_common.bend as H
import elab_state.bend as X
import elab_runner.bend as Run
import elab_headers.bend as D

def Elab.rows() -> Data:
  List<&2, F.Pair2<String, F.Global.entry>>

def Elab.checked() -> Data:
  F.Pair2<F.Global.t, Elab.rows>

def Elab.kind(postulate: Bool) -> C.Check.kind:
  match postulate:
    case True{}: C.Check.Postulate{}
    case False{}: C.Check.Definition{}

def Elab.kernel_decl(decl: D.Elab.declaration) -> C.Check.decl:
  D.Elab.Declaration{name, postulate, ty, body} = decl
  C.Check.Decl{name, Elab.kind(postulate), ty, body}

def Elab.kernel_family(header: D.Elab.family_header) -> C.Check.family_decl:
  D.Elab.FamilyHeader{name, params, indices, level} = header
  C.Check.FamilyDecl{name, params, indices, level}

def Elab.kernel_ctors(headers: List<&2, D.Elab.constructor_header>) -> List<&2, C.Check.ctor_decl>:
  match headers:
    case Nil{}: Nil{}
    case Con{D.Elab.ConstructorHeader{name, args, params, indices}, tail}:
      Con{C.Check.CtorDecl{name, args, params, indices}, Elab.kernel_ctors(tail)}

def Elab.check_decls(globals: F.Global.t, decls: List<&2, C.Check.decl>) -> X.Elab.State<Elab.rows>:
  X.Elab.State{budget => K.Check.check_decls_stateful(globals, budget, decls)}

def Elab.declare_family(globals: F.Global.t, header: D.Elab.family_header) -> X.Elab.State<F.Global.t>:
  X.Elab.State{budget => K.Check.declare_family_stateful(globals, budget, Elab.kernel_family(header))}

def Elab.define_ctors(globals: F.Global.t, group: List<&2, String>, name: String, headers: List<&2, D.Elab.constructor_header>) -> X.Elab.State<F.Global.t>:
  X.Elab.State{budget => K.Check.define_ctors_stateful(globals, budget, group, name, Elab.kernel_ctors(headers))}

def Elab.install(rows: Elab.rows, globals: F.Global.t) -> F.Global.t:
  match rows:
    case Nil{}: globals
    case Con{F.Pair2{name, entry}, tail}: Elab.install(tail, F.Global.add(name, entry, globals))

def Elab.family_names(families: List<&2, S.Syntax.fam>) -> List<&2, String>:
  match families:
    case Nil{}: Nil{}
    case Con{S.Syntax.Fam{name, params, ty, ctors}, tail}: Con{name, Elab.family_names(tail)}

@unsafe
def Elab.declare_families(families: List<&2, S.Syntax.fam>, +globals: F.Global.t) -> X.Elab.State<F.Global.t>:
  match families:
    case Nil{}: X.Elab.State.pure(F.Global.t, globals)
    case Con{head, tail}:
      do X.Elab.State<F.Global.t>:
        header : D.Elab.family_header <- Run.Elab.action(D.Elab.family_header, D.Elab.family(head, C.Check.make(globals, C.Budget.unlimited)))
        next : F.Global.t <- Elab.declare_family(globals, header)
        Elab.declare_families(tail, next)

def Elab.ctors_in(telescope: D.Elab.telescope_result, name: String, ctors: List<&2, S.Syntax.fam_ctor>) -> X.Elab.State<List<&2, D.Elab.constructor_header>>:
  D.Elab.Telescope{params, ctx} = telescope
  Run.Elab.action(List<&2, D.Elab.constructor_header>, D.Elab.constructors(ctors, name, ctx))

def Elab.family_ctors(family: S.Syntax.fam, +globals: F.Global.t, group: List<&2, String>) -> X.Elab.State<F.Global.t>:
  S.Syntax.Fam{+name, params, ty, ctors} = family
  do X.Elab.State<F.Global.t>:
    telescope : D.Elab.telescope_result <- Run.Elab.action(D.Elab.telescope_result, D.Elab.telescope(params, C.Check.make(globals, C.Budget.unlimited), Nil{}))
    headers : List<&2, D.Elab.constructor_header> <- Elab.ctors_in(telescope, name, ctors)
    Elab.define_ctors(globals, group, name, headers)

@unsafe
def Elab.define_families(families: List<&2, S.Syntax.fam>, globals: F.Global.t, +group: List<&2, String>) -> X.Elab.State<F.Global.t>:
  match families:
    case Nil{}: X.Elab.State.pure(F.Global.t, globals)
    case Con{head, tail}:
      do X.Elab.State<F.Global.t>:
        next : F.Global.t <- Elab.family_ctors(head, globals, group)
        Elab.define_families(tail, next, group)

def Elab.mu_group(+families: List<&2, S.Syntax.fam>, globals: F.Global.t) -> X.Elab.State<F.Global.t>:
  do X.Elab.State<F.Global.t>:
    declared : F.Global.t <- Elab.declare_families(families, globals)
    Elab.define_families(families, declared, Elab.family_names(families))

type Elab.rec_body is Data:
  Elab.RecBody{name: String, ty: F.Term.t, ty_value: F.Value.t, body: F.Term.t}

def Elab.member_type(+member: S.Syntax.rec_def, ctx: C.Check.ctx) -> R.Elab.Program<F.Pair2<S.Syntax.rec_def, F.Term.t>>:
  S.Syntax.RecDef{name, ty, body} = member
  do R.Elab.Program<F.Pair2<S.Syntax.rec_def, F.Term.t>>:
    term : F.Term.t <- R.Elab.term(ctx, None{}, ty)
    return F.Pair2{member, term}

@unsafe
def Elab.member_types(members: List<&2, S.Syntax.rec_def>, +globals: F.Global.t) -> X.Elab.State<List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>>>:
  match members:
    case Nil{}: X.Elab.State.pure(List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>>, Nil{})
    case Con{head, tail}:
      do X.Elab.State<List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>>>:
        typed : F.Pair2<S.Syntax.rec_def, F.Term.t> <- Run.Elab.action(F.Pair2<S.Syntax.rec_def, F.Term.t>, Elab.member_type(head, C.Check.make(globals, C.Budget.unlimited)))
        rest : List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>> <- Elab.member_types(tail, globals)
        return Con{typed, rest}

def Elab.postulates(typed: List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>>) -> List<&2, C.Check.decl>:
  match typed:
    case Nil{}: Nil{}
    case Con{F.Pair2{S.Syntax.RecDef{name, old_ty, body}, ty}, tail}: Con{C.Check.Decl{name, C.Check.Postulate{}, ty, None{}}, Elab.postulates(tail)}

def Elab.member_body(typed: F.Pair2<S.Syntax.rec_def, F.Term.t>, +ctx: C.Check.ctx) -> R.Elab.Program<Elab.rec_body>:
  F.Pair2{S.Syntax.RecDef{name, old_ty, body}, +ty} = typed
  do R.Elab.Program<Elab.rec_body>:
    +ty_value : F.Value.t <- H.Elab.eval(ctx, ty)
    term : F.Term.t <- R.Elab.term(ctx, Some{ty_value}, body)
    return Elab.RecBody{name, ty, ty_value, term}

@unsafe
def Elab.member_bodies(typed: List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>>, +provisional: F.Global.t) -> X.Elab.State<List<&2, Elab.rec_body>>:
  match typed:
    case Nil{}: X.Elab.State.pure(List<&2, Elab.rec_body>, Nil{})
    case Con{head, tail}:
      do X.Elab.State<List<&2, Elab.rec_body>>:
        body : Elab.rec_body <- Run.Elab.action(Elab.rec_body, Elab.member_body(head, C.Check.make(provisional, C.Budget.unlimited)))
        rest : List<&2, Elab.rec_body> <- Elab.member_bodies(tail, provisional)
        return Con{body, rest}

def Elab.guard_members(bodies: List<&2, Elab.rec_body>) -> List<&2, F.Pair2<String, F.Term.t>>:
  match bodies:
    case Nil{}: Nil{}
    case Con{Elab.RecBody{name, ty, value, body}, tail}: Con{F.Pair2{name, body}, Elab.guard_members(tail)}

def Elab.guard_group(globals: F.Global.t, bodies: List<&2, Elab.rec_body>) -> X.Elab.State<Maybe<&2, O.Order.t>>:
  X.Elab.State{budget => O.Totality.guard_group_stateful(budget, globals, Elab.guard_members(bodies))}

def Elab.definitions(bodies: List<&2, Elab.rec_body>) -> List<&2, C.Check.decl>:
  match bodies:
    case Nil{}: Nil{}
    case Con{Elab.RecBody{name, ty, value, body}, tail}: Con{C.Check.Decl{name, C.Check.Definition{}, ty, Some{body}}, Elab.definitions(tail)}

def Elab.rec_arg(mentions: Bool, arg: Nat) -> Maybe<&2, Nat>:
  match mentions:
    case True{}: Some{arg}
    case False{}: None{}

def Elab.rec_entry(cert: O.Order.t, name: String, ty: F.Term.t, source: F.Term.t, translated: F.Term.t) -> F.Pair2<String, F.Global.entry>:
  O.Order.Certificate{group, arg, rows} = cert
  F.Pair2{name, F.Global.Def{F.Global.DefEntry{ty, translated, True{}, Elab.rec_arg(O.Order.mentions(group, source), arg), False{}}}}

def Elab.check_term(globals: F.Global.t, term: F.Term.t, expected: F.Value.t) -> X.Elab.State<Unit>:
  X.Elab.State{budget => K.Check.check_stateful(C.Check.make(globals, budget), F.Quantity.Many{}, term, expected)}

@unsafe
def Elab.guarded(bodies: List<&2, Elab.rec_body>, +cert: O.Order.t, +provisional: F.Global.t) -> X.Elab.State<Elab.rows>:
  match bodies:
    case Nil{}: X.Elab.State.pure(Elab.rows, Nil{})
    case Con{Elab.RecBody{name, ty, value, +body}, tail}:
      do X.Elab.State<Elab.rows>:
        +translated : F.Term.t <- X.Elab.lift(F.Term.t, O.Order.translate(cert, body))
        valid : Unit <- Elab.check_term(provisional, translated, value)
        rest : Elab.rows <- Elab.guarded(tail, cert, provisional)
        return Con{Elab.rec_entry(cert, name, ty, body, translated), rest}

def Elab.rec_checked(cert: Maybe<&2, O.Order.t>, bodies: List<&2, Elab.rec_body>, globals: F.Global.t, provisional: F.Global.t) -> X.Elab.State<Elab.rows>:
  match cert:
    case None{}: Elab.check_decls(globals, Elab.definitions(bodies))
    case Some{cert}: Elab.guarded(bodies, cert, provisional)

def Elab.rec_group(members: List<&2, S.Syntax.rec_def>, +globals: F.Global.t) -> X.Elab.State<Elab.checked>:
  do X.Elab.State<Elab.checked>:
    +typed : List<&2, F.Pair2<S.Syntax.rec_def, F.Term.t>> <- Elab.member_types(members, globals)
    declared : Elab.rows <- Elab.check_decls(globals, Elab.postulates(typed))
    +provisional : F.Global.t = Elab.install(declared, globals)
    +bodies : List<&2, Elab.rec_body> <- Elab.member_bodies(typed, provisional)
    cert : Maybe<&2, O.Order.t> <- Elab.guard_group(provisional, bodies)
    +out : Elab.rows <- Elab.rec_checked(cert, bodies, globals, provisional)
    return F.Pair2{Elab.install(out, globals), out}

def Elab.one_entry(rows: Elab.rows) -> X.Elab.State<F.Pair2<String, F.Global.entry>>:
  match rows:
    case Con{head, Nil{}}: X.Elab.State.pure(F.Pair2<String, F.Global.entry>, head)
    case _: X.Elab.fail(F.Pair2<String, F.Global.entry>, F.Error.Cannot_infer{"the checker answered no entry for a declaration"})

def Elab.entry_checked(entry: F.Pair2<String, F.Global.entry>, globals: F.Global.t) -> Elab.checked:
  F.Pair2{+name, +value} = entry
  F.Pair2{F.Global.add(name, value, globals), [F.Pair2{name, value}]}

def Elab.basic_decl(decl: S.Syntax.decl, +globals: F.Global.t) -> X.Elab.State<Elab.checked>:
  do X.Elab.State<Elab.checked>:
    row : D.Elab.declaration <- Run.Elab.action(D.Elab.declaration, D.Elab.elab_decl(decl, C.Check.make(globals, C.Budget.unlimited)))
    checked : Elab.rows <- Elab.check_decls(globals, [Elab.kernel_decl(row)])
    entry : F.Pair2<String, F.Global.entry> <- Elab.one_entry(checked)
    return Elab.entry_checked(entry, globals)

def Elab.program_decl(decl: S.Syntax.decl, globals: F.Global.t) -> X.Elab.State<Elab.checked>:
  match decl:
    case S.Syntax.DMu{families}:
      do X.Elab.State<Elab.checked>:
        next : F.Global.t <- Elab.mu_group(families, globals)
        return F.Pair2{next, Nil{}}
    case S.Syntax.DRec{members}: Elab.rec_group(members, globals)
    case _: Elab.basic_decl(decl, globals)

type Elab.program_job is Data:
  Elab.ProgramDecls{decls: List<&2, S.Syntax.decl>, globals: F.Global.t, rows: Elab.rows}
  Elab.ProgramNext{checked: Elab.checked, decls: List<&2, S.Syntax.decl>, rows: Elab.rows}

@unsafe
def Elab.program(job: Elab.program_job) -> X.Elab.State<Elab.checked>:
  match job:
    case Elab.ProgramDecls{decls, globals, rows}:
      match decls:
        case Nil{}: X.Elab.State.pure(Elab.checked, F.Pair2{globals, List.reverse(&2, F.Pair2<String, F.Global.entry>, rows)})
        case Con{head, tail}:
          do X.Elab.State<Elab.checked>:
            checked : Elab.checked <- Elab.program_decl(head, globals)
            Elab.program(Elab.ProgramNext{checked, tail, rows})
    case Elab.ProgramNext{checked, decls, rows}:
      match checked:
        case F.Pair2{globals, out}: Elab.program(Elab.ProgramDecls{decls, globals, List.append(&2, F.Pair2<String, F.Global.entry>, List.reverse(&2, F.Pair2<String, F.Global.entry>, out), rows)})

def Elab.elab_program_in_stateful(globals: F.Global.t, budget: C.Budget.t, decls: List<&2, S.Syntax.decl>) -> F.Pair2<Result<&2, &2, F.Error.t, Elab.checked>, C.Budget.t>:
  X.Elab.execute(Elab.checked, Elab.program(Elab.ProgramDecls{decls, globals, Nil{}}), budget)

def Elab.elab_program_in(globals: F.Global.t, decls: List<&2, S.Syntax.decl>) -> Result<&2, &2, F.Error.t, Elab.checked>:
  X.Elab.result(Elab.checked, Elab.elab_program_in_stateful(globals, C.Budget.unlimited, decls))

def Elab.parsed(parsed: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>, globals: F.Global.t) -> X.Elab.State<Elab.checked>:
  match parsed:
    case Fail{error}: X.Elab.fail(Elab.checked, error)
    case Done{decls}: Elab.program(Elab.ProgramDecls{decls, globals, Nil{}})

def Elab.check_in_stateful(globals: F.Global.t, budget: C.Budget.t, source: String) -> F.Pair2<Result<&2, &2, F.Error.t, Elab.checked>, C.Budget.t>:
  X.Elab.execute(Elab.checked, Elab.parsed(P.Parser.parse(source), globals), budget)

def Elab.check_in(globals: F.Global.t, source: String) -> Result<&2, &2, F.Error.t, Elab.checked>:
  X.Elab.result(Elab.checked, Elab.check_in_stateful(globals, C.Budget.unlimited, source))

def Elab.entry_rows(result: Result<&2, &2, F.Error.t, Elab.checked>) -> Result<&2, &2, F.Error.t, Elab.rows>:
  match result:
    case Fail{error}: Fail{error}
    case Done{F.Pair2{globals, rows}}: Done{rows}

def Elab.check_text(globals: F.Global.t, source: String) -> Result<&2, &2, F.Error.t, Elab.rows>:
  Elab.entry_rows(Elab.check_in(globals, source))

def Elab.entry_text(entry: F.Pair2<String, F.Global.entry>) -> String:
  match entry:
    case F.Pair2{name, F.Global.Def{F.Global.DefEntry{ty, body, reducible, rec_arg, partial}}}: "def " ++ name ++ " : " ++ Pp.Pp.term(Nil{}, ty) ++ " := " ++ Pp.Pp.term(Nil{}, body) ++ "\n"
    case F.Pair2{name, F.Global.Axiom{F.Global.AxiomEntry{ty}}}: "axiom " ++ name ++ " : " ++ Pp.Pp.term(Nil{}, ty) ++ "\n"
    case F.Pair2{name, F.Global.Prim{F.Global.PrimEntry{ty, prim}}}: "prim " ++ name ++ " : " ++ Pp.Pp.term(Nil{}, ty) ++ "\n"

def Elab.checked_form(rows: Elab.rows) -> String:
  match rows:
    case Nil{}: ""
    case Con{head, tail}: Elab.entry_text(head) ++ Elab.checked_form(tail)

def Elab.axiom_names(rows: Elab.rows) -> List<&2, String>:
  match rows:
    case Nil{}: Nil{}
    case Con{F.Pair2{name, F.Global.Axiom{entry}}, tail}: Con{name, Elab.axiom_names(tail)}
    case Con{head, tail}: Elab.axiom_names(tail)
