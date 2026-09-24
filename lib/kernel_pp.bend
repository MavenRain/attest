import Base
import ./foundation.bend as F
import ./kernel_util.bend as U

def Pp.choose(test: Bool, yes: String, no: String) -> String:
  match test:
    case True{}: yes
    case False{}: no

def Pp.escape_char(+c: Char) -> String:
  +n = Char.to_u32(c)
  decimal = "\\" ++ U32.show((n / 100 : U32)) ++ U32.show(((n / 10 : U32) % 10 : U32)) ++ U32.show((n % 10 : U32))
  printable = Pp.choose(Bool.and(U32.is_ge(n, 32), U32.is_lt(n, 127)), SCon{c, SNil{}}, decimal)
  backspace = Pp.choose(U32.is_eq(n, 8), "\\b", printable)
  carriage = Pp.choose(U32.is_eq(n, 13), "\\r", backspace)
  tab = Pp.choose(U32.is_eq(n, 9), "\\t", carriage)
  newline = Pp.choose(U32.is_eq(n, 10), "\\n", tab)
  slash = Pp.choose(U32.is_eq(n, 92), "\\\\", newline)
  Pp.choose(U32.is_eq(n, 34), "\\\"", slash)

def Pp.escape(s: String) -> String:
  match s:
    case SNil{}: ""
    case SCon{h, t}: Pp.escape_char(h) ++ Pp.escape(t)

def Pp.literal(literal: F.Literal.t) -> String:
  match literal:
    case F.Literal.LString{text}: "\"" ++ Pp.escape(text) ++ "\""
    case F.Literal.LInt{n}: F.Bignum.to_string(n)

def Pp.binder_names(binders: List<&2, F.Pair2<F.Quantity.t, String>>) -> List<&2, String>:
  match binders:
    case Nil{}: Nil{}
    case Con{binder, rest}:
      F.Pair2{q, name} = binder
      Con{name, Pp.binder_names(rest)}

def Pp.push(names: List<&2, String>, added: List<&2, String>) -> List<&2, String>:
  U.Kernel.rev_append(String, added, names)

def Pp.under(shape: F.Shape.t<F.Term.t>, names: List<&2, String>) -> List<&2, String>:
  match shape:
    case F.Shape.SPi{q, name, domain}: Con{name, names}
    case F.Shape.SColl{width}: names
    case F.Shape.SPar{a, b}: names
    case F.Shape.SMu{name, indices}: names
    case F.Shape.SNu{name, indices}: names

type Pp.Task is Type:
  Pp.Term{term: F.Term.t, names: List<&2, String>, done: String -> String}
  Pp.Shape{shape: F.Shape.t<F.Term.t>, names: List<&2, String>, done: String -> String}
  Pp.Addr{addr: F.Term.addr, names: List<&2, String>, done: String -> String}
  Pp.Leg{leg: F.Term.leg, names: List<&2, String>, done: String -> String}
  Pp.Terms{terms: List<&2, F.Term.t>, names: List<&2, String>, done: List<&2, String> -> String}
  Pp.Legs{legs: List<&2, F.Term.leg>, names: List<&2, String>, done: List<&2, String> -> String}
  Pp.Motive{motive: Maybe<&2, F.Term.motive>, names: List<&2, String>, done: String -> String}
  Pp.Branches{branches: List<&2, F.Pair2<F.Term.addr, F.Term.leg>>, names: List<&2, String>, done: String -> String}

# This task machine traverses a finite term, but its continuation-built tasks
# do not satisfy Bend's syntactic subterm test. Only termination is unchecked.
@unsafe def Pp.render(task: Pp.Task) -> String:
  match task:
    case Pp.Terms{terms, +names, done}:
      match terms:
        case Nil{}: done(Nil{})
        case Con{term, rest}:
          Pp.render(Pp.Term{term, names, text => Pp.render(Pp.Terms{rest, names, texts => done(Con{text, texts})})})
    case Pp.Legs{legs, +names, done}:
      match legs:
        case Nil{}: done(Nil{})
        case Con{leg, rest}:
          Pp.render(Pp.Leg{leg, names, text => Pp.render(Pp.Legs{rest, names, texts => done(Con{text, texts})})})
    case Pp.Shape{shape, +names, done}:
      match shape:
        case F.Shape.SPi{q, name, domain}:
          Pp.render(Pp.Term{domain, names, text => done("SPi " ++ F.Quantity.to_string(q) ++ " " ++ name ++ " " ++ text)})
        case F.Shape.SColl{width}: done("SColl " ++ Nat.show(width))
        case F.Shape.SPar{a, b}:
          Pp.render(Pp.Term{a, names, x => Pp.render(Pp.Term{b, names, y => done("SPar " ++ x ++ " " ++ y)})})
        case F.Shape.SMu{name, indices}:
          Pp.render(Pp.Terms{indices, names, texts => done("SMu " ++ name ++ " [" ++ String.join(texts, "; ") ++ "]")})
        case F.Shape.SNu{name, indices}:
          Pp.render(Pp.Terms{indices, names, texts => done("SNu " ++ name ++ " [" ++ String.join(texts, "; ") ++ "]")})
    case Pp.Addr{addr, names, done}:
      match addr:
        case F.Term.APt{q, arg}:
          Pp.render(Pp.Term{arg, names, text => done("(APt " ++ F.Quantity.to_string(q) ++ " " ++ text ++ ")")})
        case F.Term.ALeg{k}: done("(ALeg " ++ Nat.show(k) ++ ")")
        case F.Term.ACtor{name}: done("(ACtor " ++ name ++ ")")
    case Pp.Leg{leg, names, done}:
      F.Term.Leg{binders, body} = leg
      +bnames = Pp.binder_names(binders)
      Pp.render(Pp.Term{body, Pp.push(names, bnames), text => done(String.join(bnames, " ") ++ " => " ++ text)})
    case Pp.Motive{motive, names, done}:
      match motive:
        case None{}: done("")
        case Some{mo}:
          F.Term.Motive{ind, indices, +self, body} = mo
          inner = {Con{self, U.Kernel.rev_append(String, indices, names)} : List<&2, String>}
          Pp.render(Pp.Term{body, inner, text => done(" as " ++ self ++ " return " ++ text)})
    case Pp.Branches{branches, +names, done}:
      match branches:
        case Nil{}: done("")
        case Con{branch, rest}:
          F.Pair2{addr, leg} = branch
          Pp.render(Pp.Addr{addr, names, a => Pp.render(Pp.Leg{leg, names, l =>
            Pp.render(Pp.Branches{rest, names, more => done(" | " ++ a ++ " " ++ l ++ more)})})})
    case Pp.Term{term, +names, done}:
      match term:
        case F.Term.Var{+index}:
          done(Maybe.default(&2, String, List.get(&2, String, names, index), "#" ++ Nat.show(index)))
        case F.Term.Univ{level}: done("Type " ++ F.Level.to_string(level))
        case F.Term.Lan{+shape, diagram}:
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Term{diagram, Pp.under(shape, names), d => done("(Lan " ++ s ++ " " ++ d ++ ")")})})
        case F.Term.Ran{+shape, diagram}:
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Term{diagram, Pp.under(shape, names), d => done("(Ran " ++ s ++ " " ++ d ++ ")")})})
        case F.Term.In{shape, addr, args}:
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Addr{addr, names, a =>
            Pp.render(Pp.Terms{args, names, texts => done("(In " ++ s ++ " " ++ a ++ " [" ++ String.join(texts, "; ") ++ "])")})})})
        case F.Term.Sec{shape, legs}:
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Legs{legs, names, texts => done("(Sec " ++ s ++ " [" ++ String.join(texts, "; ") ++ "])")})})
        case F.Term.Out{shape, addr, scrutinee}:
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Addr{addr, names, a =>
            Pp.render(Pp.Term{scrutinee, names, text => done("(Out " ++ s ++ " " ++ a ++ " " ++ text ++ ")")})})})
        case F.Term.Let{+name, ty, value, body}:
          Pp.render(Pp.Term{ty, names, t => Pp.render(Pp.Term{value, names, v =>
            Pp.render(Pp.Term{body, Con{name, names}, b => done("let " ++ name ++ " : " ++ t ++ " := " ++ v ++ " in " ++ b)})})})
        case F.Term.Ann{term, ty}:
          Pp.render(Pp.Term{term, names, text => Pp.render(Pp.Term{ty, names, t => done("(" ++ text ++ " : " ++ t ++ ")")})})
        case F.Term.Global{name}: done(name)
        case F.Term.Lit{literal}: done(Pp.literal(literal))
        case F.Term.Auto{}: done("auto")
        case F.Term.Elim{elimination}:
          F.Term.Elimination{shape, scrutinee, q, motive, branches} = elimination
          Pp.render(Pp.Shape{shape, names, s => Pp.render(Pp.Term{scrutinee, names, text =>
            Pp.render(Pp.Motive{motive, names, m => Pp.render(Pp.Branches{branches, names, br =>
              done("(Elim " ++ s ++ " " ++ text ++ m ++ " with" ++ br ++ ")")})})})})

def Pp.term(names: List<&2, String>, term: F.Term.t) -> String:
  Pp.render(Pp.Term{term, names, text => text})

def Pp.shape(names: List<&2, String>, shape: F.Shape.t<F.Term.t>) -> String:
  Pp.render(Pp.Shape{shape, names, text => text})

def Pp.addr(names: List<&2, String>, addr: F.Term.addr) -> String:
  Pp.render(Pp.Addr{addr, names, text => text})

def Pp.leg(names: List<&2, String>, leg: F.Term.leg) -> String:
  Pp.render(Pp.Leg{leg, names, text => text})

def Pp.elim(names: List<&2, String>, elimination: F.Term.elim) -> String:
  Pp.term(names, F.Term.Elim{elimination})
