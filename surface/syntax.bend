import Base
import ../lib/foundation.bend as F

type Syntax.prim is Data:
  Syntax.PAdd{}
  Syntax.PSub{}
  Syntax.PMul{}
  Syntax.PEq{}
  Syntax.PLt{}

type Syntax.binder_of<-T: Data> is Data:
  Syntax.Binder{b_q: F.Quantity.t, b_name: String, b_ty: T}

type Syntax.motive_of<-T: Data> is Data:
  Syntax.Motive{mo_self: String, mo_ind: Maybe<&2, String>, mo_idx: List<&2, String>, mo_body: T}

type Syntax.field_of<-T: Data> is Data:
  Syntax.Field{fd_q: F.Quantity.t, fd_name: String, fd_ty: Maybe<&2, T>}

type Syntax.branch_of<-T: Data> is Data:
  Syntax.BrLeg{key: F.Bignum.t, binders: List<&2, Syntax.binder_of<T>>, body: T}
  Syntax.BrCtor{name: String, fields: List<&2, Syntax.field_of<T>>, body: T}

type Syntax.t is Data:
  Syntax.SVar{name: String}
  Syntax.SNat{value: F.Bignum.t}
  Syntax.SProp{}
  Syntax.SType{level: F.Bignum.t}
  Syntax.SPrim{prim: Syntax.prim}
  Syntax.SUnit{}
  Syntax.SAuto{}
  Syntax.SPair{fst: Syntax.t, snd: Syntax.t}
  Syntax.STuple{items: List<&2, Syntax.t>}
  Syntax.SSum{items: List<&2, Syntax.t>}
  Syntax.SProd{items: List<&2, Syntax.t>}
  Syntax.SProj{term: Syntax.t, leg: F.Bignum.t}
  Syntax.SInj{leg: F.Bignum.t, arity: F.Bignum.t, term: Syntax.t}
  Syntax.SAbsurd{term: Syntax.t}
  Syntax.SApp{fun: Syntax.t, arg: Syntax.t}
  Syntax.SFun{binders: List<&2, Syntax.binder_of<Syntax.t>>, body: Syntax.t}
  Syntax.SArrow{binder: Syntax.binder_of<Syntax.t>, cod: Syntax.t}
  Syntax.SStar{binder: Syntax.binder_of<Syntax.t>, cod: Syntax.t}
  Syntax.SLet{name: String, ty: Syntax.t, val: Syntax.t, body: Syntax.t}
  Syntax.SAnn{term: Syntax.t, ty: Syntax.t}
  Syntax.SCase{scrut: Syntax.t, motive: Maybe<&2, Syntax.motive_of<Syntax.t>>, branches: List<&2, Syntax.branch_of<Syntax.t>>}
  Syntax.SMatch{scrut: Syntax.t, motive: Maybe<&2, Syntax.motive_of<Syntax.t>>, branches: List<&2, Syntax.branch_of<Syntax.t>>}

def Syntax.binder() -> Data:
  Syntax.binder_of<Syntax.t>

def Syntax.motive() -> Data:
  Syntax.motive_of<Syntax.t>

def Syntax.field() -> Data:
  Syntax.field_of<Syntax.t>

def Syntax.branch() -> Data:
  Syntax.branch_of<Syntax.t>

type Syntax.fam_ctor is Data:
  Syntax.FamCtor{fc_name: String, fc_ty: Syntax.t}

type Syntax.fam is Data:
  Syntax.Fam{fm_name: String, fm_params: List<&2, Syntax.binder>, fm_ty: Syntax.t, fm_ctors: List<&2, Syntax.fam_ctor>}

type Syntax.rec_def is Data:
  Syntax.RecDef{rd_name: String, rd_ty: Syntax.t, rd_body: Syntax.t}

type Syntax.decl is Data:
  Syntax.DDef{name: String, ty: Syntax.t, body: Syntax.t}
  Syntax.DAxiom{name: String, ty: Syntax.t}
  Syntax.DMu{families: List<&2, Syntax.fam>}
  Syntax.DRec{members: List<&2, Syntax.rec_def>}

def Syntax.prim_name(p: Syntax.prim) -> String:
  match p:
    case Syntax.PAdd{}: "natAdd"
    case Syntax.PSub{}: "natSub"
    case Syntax.PMul{}: "natMul"
    case Syntax.PEq{}: "natEq"
    case Syntax.PLt{}: "natLt"

def Syntax.mark(q: F.Quantity.t) -> String:
  match q:
    case F.Quantity.Zero{}: "0 "
    case F.Quantity.One{}: "1 "
    case F.Quantity.Many{}: ""

def Syntax.level_of(s: Syntax.t) -> Nat:
  match s:
    case Syntax.SFun{binders, body}: 0n
    case Syntax.SArrow{binder, cod}: 0n
    case Syntax.SStar{binder, cod}: 0n
    case Syntax.SLet{name, ty, val, body}: 0n
    case Syntax.SCase{scrut, motive, branches}: 0n
    case Syntax.SMatch{scrut, motive, branches}: 0n
    case Syntax.SInj{leg, arity, term}: 1n
    case Syntax.SAbsurd{term}: 1n
    case Syntax.SApp{fun, arg}: 1n
    case _: 2n

type Syntax.print_node is Data:
  Syntax.PrintAt{level: Nat, term: Syntax.t}
  Syntax.PrintRaw{term: Syntax.t}
  Syntax.PrintBinder{binder: Syntax.binder}
  Syntax.PrintBinders{binders: List<&2, Syntax.binder>, prefix: String}
  Syntax.PrintItems{items: List<&2, Syntax.t>}
  Syntax.PrintFields{fields: List<&2, Syntax.field>}
  Syntax.PrintBranches{branches: List<&2, Syntax.branch>}
  Syntax.PrintMotive{motive: Maybe<&2, Syntax.motive>}
  Syntax.PrintCtors{ctors: List<&2, Syntax.fam_ctor>}
  Syntax.PrintFamilies{families: List<&2, Syntax.fam>}
  Syntax.PrintRecs{members: List<&2, Syntax.rec_def>, word: String}
  Syntax.PrintDecls{decls: List<&2, Syntax.decl>}

def Syntax.parenthesize(text: String, needed: Bool) -> String:
  match needed:
    case True{}: "(" ++ text ++ ")"
    case False{}: text

def Syntax.index_names(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}: ""
    case Con{head, tail}: " " ++ head ++ Syntax.index_names(tail)

def Syntax.ind_text(ind: Maybe<&2, String>, idx: List<&2, String>) -> String:
  match ind:
    case None{}: ""
    case Some{value}: " in " ++ value ++ Syntax.index_names(idx)

# The tagged dispatcher preserves the source printer's mutual recursion.
@unsafe
def Syntax.render(node: Syntax.print_node) -> String:
  match node:
    case Syntax.PrintAt{level, +term}:
      Syntax.parenthesize(Syntax.render(Syntax.PrintRaw{term}), Nat.is_lt(Syntax.level_of(term), level))
    case Syntax.PrintRaw{term}:
      match term:
        case Syntax.SVar{name}: name
        case Syntax.SNat{value}: F.Bignum.to_string(value)
        case Syntax.SProp{}: "Prop"
        case Syntax.SType{level}: "Type " ++ F.Bignum.to_string(level)
        case Syntax.SPrim{prim}: Syntax.prim_name(prim)
        case Syntax.SUnit{}: "()"
        case Syntax.SAuto{}: "auto"
        case Syntax.SPair{fst, snd}: "(" ++ Syntax.render(Syntax.PrintAt{0n, fst}) ++ ", " ++ Syntax.render(Syntax.PrintAt{0n, snd}) ++ ")"
        case Syntax.STuple{items}: "tuple (" ++ Syntax.render(Syntax.PrintItems{items}) ++ ")"
        case Syntax.SSum{items}: "sum (" ++ Syntax.render(Syntax.PrintItems{items}) ++ ")"
        case Syntax.SProd{items}: "prod (" ++ Syntax.render(Syntax.PrintItems{items}) ++ ")"
        case Syntax.SProj{term, leg}: Syntax.render(Syntax.PrintAt{2n, term}) ++ "." ++ F.Bignum.to_string(leg)
        case Syntax.SInj{leg, arity, term}: "inj " ++ F.Bignum.to_string(leg) ++ " of " ++ F.Bignum.to_string(arity) ++ " " ++ Syntax.render(Syntax.PrintAt{1n, term})
        case Syntax.SAbsurd{term}: "absurd " ++ Syntax.render(Syntax.PrintAt{1n, term})
        case Syntax.SApp{fun, arg}: Syntax.render(Syntax.PrintAt{1n, fun}) ++ " " ++ Syntax.render(Syntax.PrintAt{2n, arg})
        case Syntax.SFun{binders, body}: "fun " ++ Syntax.render(Syntax.PrintBinders{binders, ""}) ++ " => " ++ Syntax.render(Syntax.PrintAt{0n, body})
        case Syntax.SArrow{binder, cod}: Syntax.render(Syntax.PrintBinder{binder}) ++ " -> " ++ Syntax.render(Syntax.PrintAt{0n, cod})
        case Syntax.SStar{binder, cod}: Syntax.render(Syntax.PrintBinder{binder}) ++ " * " ++ Syntax.render(Syntax.PrintAt{0n, cod})
        case Syntax.SLet{name, ty, val, body}: "let " ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{1n, ty}) ++ " := " ++ Syntax.render(Syntax.PrintAt{1n, val}) ++ " in " ++ Syntax.render(Syntax.PrintAt{0n, body})
        case Syntax.SAnn{term, ty}: "(" ++ Syntax.render(Syntax.PrintAt{0n, term}) ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ ")"
        case Syntax.SCase{scrut, motive, branches}: "case " ++ Syntax.render(Syntax.PrintAt{1n, scrut}) ++ Syntax.render(Syntax.PrintMotive{motive}) ++ " with" ++ Syntax.render(Syntax.PrintBranches{branches})
        case Syntax.SMatch{scrut, motive, branches}: "match " ++ Syntax.render(Syntax.PrintAt{1n, scrut}) ++ Syntax.render(Syntax.PrintMotive{motive}) ++ " with" ++ Syntax.render(Syntax.PrintBranches{branches})
    case Syntax.PrintBinder{binder}:
      Syntax.Binder{q, name, ty} = binder
      "(" ++ Syntax.mark(q) ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ ")"
    case Syntax.PrintBinders{binders, prefix}:
      match binders:
        case Nil{}: ""
        case Con{head, tail}: prefix ++ Syntax.render(Syntax.PrintBinder{head}) ++ Syntax.render(Syntax.PrintBinders{tail, " "})
    case Syntax.PrintItems{items}:
      match items:
        case Nil{}: ""
        case Con{head, tail}:
          match tail:
            case Nil{}: Syntax.render(Syntax.PrintAt{0n, head})
            case Con{h, t}: Syntax.render(Syntax.PrintAt{0n, head}) ++ ", " ++ Syntax.render(Syntax.PrintItems{Con{h, t}})
    case Syntax.PrintFields{fields}:
      match fields:
        case Nil{}: ""
        case Con{head, tail}:
          match head:
            case Syntax.Field{q, name, ty}:
              match ty:
                case None{}: " " ++ Syntax.mark(q) ++ name ++ Syntax.render(Syntax.PrintFields{tail})
                case Some{value}: " " ++ Syntax.render(Syntax.PrintBinder{Syntax.Binder{q, name, value}}) ++ Syntax.render(Syntax.PrintFields{tail})
    case Syntax.PrintBranches{branches}:
      match branches:
        case Nil{}: ""
        case Con{head, tail}:
          match head:
            case Syntax.BrLeg{key, binders, body}: " | " ++ F.Bignum.to_string(key) ++ Syntax.render(Syntax.PrintBinders{binders, " "}) ++ " => " ++ Syntax.render(Syntax.PrintAt{1n, body}) ++ Syntax.render(Syntax.PrintBranches{tail})
            case Syntax.BrCtor{name, fields, body}: " | " ++ name ++ Syntax.render(Syntax.PrintFields{fields}) ++ " => " ++ Syntax.render(Syntax.PrintAt{1n, body}) ++ Syntax.render(Syntax.PrintBranches{tail})
    case Syntax.PrintMotive{motive}:
      match motive:
        case None{}: ""
        case Some{value}:
          Syntax.Motive{self, ind, idx, body} = value
          " as " ++ self ++ Syntax.ind_text(ind, idx) ++ " return " ++ Syntax.render(Syntax.PrintAt{1n, body})
    case Syntax.PrintCtors{ctors}:
      match ctors:
        case Nil{}: ""
        case Con{head, tail}:
          Syntax.FamCtor{name, ty} = head
          "| " ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ "\n" ++ Syntax.render(Syntax.PrintCtors{tail})
    case Syntax.PrintFamilies{families}:
      match families:
        case Nil{}: ""
        case Con{head, tail}:
          Syntax.Fam{name, params, ty, ctors} = head
          "mu " ++ name ++ Syntax.render(Syntax.PrintBinders{params, " "}) ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ " :=\n" ++ Syntax.render(Syntax.PrintCtors{ctors}) ++ Syntax.render(Syntax.PrintFamilies{tail})
    case Syntax.PrintRecs{members, word}:
      match members:
        case Nil{}: ""
        case Con{head, tail}:
          Syntax.RecDef{name, ty, body} = head
          word ++ " " ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ " := " ++ Syntax.render(Syntax.PrintAt{0n, body}) ++ "\n" ++ Syntax.render(Syntax.PrintRecs{tail, "and"})
    case Syntax.PrintDecls{decls}:
      match decls:
        case Nil{}: ""
        case Con{head, tail}:
          match head:
            case Syntax.DDef{name, ty, body}: "def " ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ " := " ++ Syntax.render(Syntax.PrintAt{0n, body}) ++ "\n" ++ Syntax.render(Syntax.PrintDecls{tail})
            case Syntax.DAxiom{name, ty}: "axiom " ++ name ++ " : " ++ Syntax.render(Syntax.PrintAt{0n, ty}) ++ "\n" ++ Syntax.render(Syntax.PrintDecls{tail})
            case Syntax.DRec{members}: Syntax.render(Syntax.PrintRecs{members, "def rec"}) ++ Syntax.render(Syntax.PrintDecls{tail})
            case Syntax.DMu{families}:
              match families:
                case Nil{}: Syntax.render(Syntax.PrintDecls{tail})
                case Con{first, rest}:
                  match rest:
                    case Nil{}: Syntax.render(Syntax.PrintFamilies{Con{first, Nil{}}}) ++ Syntax.render(Syntax.PrintDecls{tail})
                    case Con{second, others}: "mutual\n" ++ Syntax.render(Syntax.PrintFamilies{Con{first, Con{second, others}}}) ++ "end\n" ++ Syntax.render(Syntax.PrintDecls{tail})

def Syntax.at(level: Nat, term: Syntax.t) -> String:
  Syntax.render(Syntax.PrintAt{level, term})

def Syntax.print(decls: List<&2, Syntax.decl>) -> String:
  Syntax.render(Syntax.PrintDecls{decls})

# This encoding includes every field and constructor tag, independently of printing.
def Syntax.encode_string(+text: String) -> String:
  Nat.show(String.length(text)) ++ ":" ++ text

def Syntax.encode_names(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}: "]"
    case Con{head, tail}: "[" ++ Syntax.encode_string(head) ++ Syntax.encode_names(tail)

type Syntax.encoding_node is Data:
  Syntax.EncodeTerm{value: Syntax.t}
  Syntax.EncodeTerms{value: List<&2, Syntax.t>}
  Syntax.EncodeBinder{value: Syntax.binder}
  Syntax.EncodeBinders{value: List<&2, Syntax.binder>}
  Syntax.EncodeMotive{value: Maybe<&2, Syntax.motive>}
  Syntax.EncodeFields{value: List<&2, Syntax.field>}
  Syntax.EncodeBranches{value: List<&2, Syntax.branch>}
  Syntax.EncodeFams{value: List<&2, Syntax.fam>}
  Syntax.EncodeCtors{value: List<&2, Syntax.fam_ctor>}
  Syntax.EncodeRecs{value: List<&2, Syntax.rec_def>}
  Syntax.EncodeDecls{value: List<&2, Syntax.decl>}

@unsafe
def Syntax.encode(node: Syntax.encoding_node) -> String:
  match node:
    case Syntax.EncodeTerm{value}:
      match value:
        case Syntax.SVar{name}: "v" ++ Syntax.encode_string(name)
        case Syntax.SNat{value}: "n" ++ F.Bignum.to_string(value) ++ ";"
        case Syntax.SProp{}: "p"
        case Syntax.SType{level}: "u" ++ F.Bignum.to_string(level) ++ ";"
        case Syntax.SPrim{prim}: "r" ++ Syntax.prim_name(prim) ++ ";"
        case Syntax.SUnit{}: "z"
        case Syntax.SAuto{}: "h"
        case Syntax.SPair{fst, snd}: "a" ++ Syntax.encode(Syntax.EncodeTerm{fst}) ++ Syntax.encode(Syntax.EncodeTerm{snd})
        case Syntax.STuple{items}: "t" ++ Syntax.encode(Syntax.EncodeTerms{items})
        case Syntax.SSum{items}: "s" ++ Syntax.encode(Syntax.EncodeTerms{items})
        case Syntax.SProd{items}: "d" ++ Syntax.encode(Syntax.EncodeTerms{items})
        case Syntax.SProj{term, leg}: "j" ++ F.Bignum.to_string(leg) ++ ";" ++ Syntax.encode(Syntax.EncodeTerm{term})
        case Syntax.SInj{leg, arity, term}: "i" ++ F.Bignum.to_string(leg) ++ ";" ++ F.Bignum.to_string(arity) ++ ";" ++ Syntax.encode(Syntax.EncodeTerm{term})
        case Syntax.SAbsurd{term}: "b" ++ Syntax.encode(Syntax.EncodeTerm{term})
        case Syntax.SApp{fun, arg}: "c" ++ Syntax.encode(Syntax.EncodeTerm{fun}) ++ Syntax.encode(Syntax.EncodeTerm{arg})
        case Syntax.SFun{binders, body}: "f" ++ Syntax.encode(Syntax.EncodeBinders{binders}) ++ Syntax.encode(Syntax.EncodeTerm{body})
        case Syntax.SArrow{binder, cod}: ">" ++ Syntax.encode(Syntax.EncodeBinder{binder}) ++ Syntax.encode(Syntax.EncodeTerm{cod})
        case Syntax.SStar{binder, cod}: "*" ++ Syntax.encode(Syntax.EncodeBinder{binder}) ++ Syntax.encode(Syntax.EncodeTerm{cod})
        case Syntax.SLet{name, ty, val, body}: "l" ++ Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeTerm{val}) ++ Syntax.encode(Syntax.EncodeTerm{body})
        case Syntax.SAnn{term, ty}: ":" ++ Syntax.encode(Syntax.EncodeTerm{term}) ++ Syntax.encode(Syntax.EncodeTerm{ty})
        case Syntax.SCase{scrut, motive, branches}: "e" ++ Syntax.encode(Syntax.EncodeTerm{scrut}) ++ Syntax.encode(Syntax.EncodeMotive{motive}) ++ Syntax.encode(Syntax.EncodeBranches{branches})
        case Syntax.SMatch{scrut, motive, branches}: "m" ++ Syntax.encode(Syntax.EncodeTerm{scrut}) ++ Syntax.encode(Syntax.EncodeMotive{motive}) ++ Syntax.encode(Syntax.EncodeBranches{branches})
    case Syntax.EncodeBinder{value}:
      Syntax.Binder{q, name, ty} = value
      "(" ++ Syntax.encode_string(Syntax.mark(q)) ++ Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty})
    case Syntax.EncodeMotive{value}:
      match value:
        case None{}: "0"
        case Some{value}:
          match value:
            case Syntax.Motive{self, ind, idx, body}:
              match ind:
                case None{}: "10" ++ Syntax.encode_string(self) ++ Syntax.encode_names(idx) ++ Syntax.encode(Syntax.EncodeTerm{body})
                case Some{name}: "11" ++ Syntax.encode_string(self) ++ Syntax.encode_string(name) ++ Syntax.encode_names(idx) ++ Syntax.encode(Syntax.EncodeTerm{body})
    case Syntax.EncodeTerms{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          "[" ++ Syntax.encode(Syntax.EncodeTerm{head}) ++ Syntax.encode(Syntax.EncodeTerms{tail})
    case Syntax.EncodeBinders{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          "[" ++ Syntax.encode(Syntax.EncodeBinder{head}) ++ Syntax.encode(Syntax.EncodeBinders{tail})
    case Syntax.EncodeFields{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          match head:
            case Syntax.Field{q, name, ty}:
              match ty:
                case None{}: Syntax.encode_string(Syntax.mark(q)) ++ Syntax.encode_string(name) ++ "0" ++ Syntax.encode(Syntax.EncodeFields{tail})
                case Some{value}: Syntax.encode_string(Syntax.mark(q)) ++ Syntax.encode_string(name) ++ "1" ++ Syntax.encode(Syntax.EncodeTerm{value}) ++ Syntax.encode(Syntax.EncodeFields{tail})
    case Syntax.EncodeBranches{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          match head:
            case Syntax.BrLeg{key, binders, body}: "0" ++ F.Bignum.to_string(key) ++ ";" ++ Syntax.encode(Syntax.EncodeBinders{binders}) ++ Syntax.encode(Syntax.EncodeTerm{body}) ++ Syntax.encode(Syntax.EncodeBranches{tail})
            case Syntax.BrCtor{name, fields, body}: "1" ++ Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeFields{fields}) ++ Syntax.encode(Syntax.EncodeTerm{body}) ++ Syntax.encode(Syntax.EncodeBranches{tail})
    case Syntax.EncodeFams{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          Syntax.Fam{name, params, ty, ctors} = head
          Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeBinders{params}) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeCtors{ctors}) ++ Syntax.encode(Syntax.EncodeFams{tail})
    case Syntax.EncodeCtors{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          Syntax.FamCtor{name, ty} = head
          Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeCtors{tail})
    case Syntax.EncodeRecs{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          Syntax.RecDef{name, ty, body} = head
          Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeTerm{body}) ++ Syntax.encode(Syntax.EncodeRecs{tail})
    case Syntax.EncodeDecls{value}:
      match value:
        case Nil{}: "]"
        case Con{head, tail}:
          match head:
            case Syntax.DDef{name, ty, body}: "D" ++ Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeTerm{body}) ++ Syntax.encode(Syntax.EncodeDecls{tail})
            case Syntax.DAxiom{name, ty}: "A" ++ Syntax.encode_string(name) ++ Syntax.encode(Syntax.EncodeTerm{ty}) ++ Syntax.encode(Syntax.EncodeDecls{tail})
            case Syntax.DMu{families}: "M" ++ Syntax.encode(Syntax.EncodeFams{families}) ++ Syntax.encode(Syntax.EncodeDecls{tail})
            case Syntax.DRec{members}: "R" ++ Syntax.encode(Syntax.EncodeRecs{members}) ++ Syntax.encode(Syntax.EncodeDecls{tail})

def Syntax.equal_declarations(a: List<&2, Syntax.decl>, b: List<&2, Syntax.decl>) -> Bool:
  String.eq(Syntax.encode(Syntax.EncodeDecls{a}), Syntax.encode(Syntax.EncodeDecls{b}))
