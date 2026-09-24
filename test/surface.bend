import Base
import ../lib/foundation.bend as F
import ../surface/token.bend as T
import ../surface/lexer.bend as L
import ../surface/syntax.bend as S
import ../surface/parser.bend as P
import ../surface/elab.bend as E
import ../lib/kernel_primitives.bend as G
import ../lib/kernel_eval.bend as V
import ../lib/kernel_pp.bend as Pp
import ../lib/kernel_context.bend as C

def SurfaceTest.bytes(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}: ""
    case Con{head, tail}: U32.show(head) ++ "," ++ SurfaceTest.bytes(tail)

def SurfaceTest.kind(+kind: T.Token.kind) -> String:
  match kind:
    case T.Token.Bytes{value}: "bytes[" ++ SurfaceTest.bytes(value) ++ "]"
    case _: T.Token.describe(kind)

def SurfaceTest.tokens(xs: List<&2, T.Token.t>) -> String:
  match xs:
    case Nil{}: ""
    case Con{head, tail}:
      T.Token.Token{kind, loc} = head
      T.Token.Loc{line, col} = loc
      SurfaceTest.kind(kind) ++ "@" ++ Nat.show(line) ++ ":" ++ Nat.show(col) ++ ";" ++ SurfaceTest.tokens(tail)

def SurfaceTest.result(result: Result<&2, &2, F.Error.t, List<&2, T.Token.t>>) -> String:
  match result:
    case Done{tokens}: SurfaceTest.tokens(tokens)
    case Fail{error}:
      match error:
        case F.Error.Parse{message, line, col}: message ++ "@" ++ Nat.show(line) ++ ":" ++ Nat.show(col)
        case _: "unexpected non-parse error"

type SurfaceTest.case is Data:
  SurfaceTest.Case{source: String, expected: String}

def SurfaceTest.verdict(source: String, observed: String, equal: Bool) -> String:
  match equal:
    case True{}: ""
    case False{}: "FAIL " ++ source ++ ": " ++ observed ++ "\n"

def SurfaceTest.one(+source: String, expected: String) -> String:
  +observed : String = SurfaceTest.result(L.Lexer.lex(source))
  SurfaceTest.verdict(source, observed, String.eq(observed, expected))

def SurfaceTest.run(cases: List<&2, SurfaceTest.case>) -> String:
  match cases:
    case Nil{}: ""
    case Con{head, tail}:
      SurfaceTest.Case{source, expected} = head
      SurfaceTest.one(source, expected) ++ SurfaceTest.run(tail)

type SurfaceTest.parser_case is Data:
  SurfaceTest.Round{source: String}
  SurfaceTest.Refuse{source: String, expected: String}
  SurfaceTest.Same{first: String, second: String}

def SurfaceTest.round(result: Result<&2, &2, F.Error.t, Unit>) -> String:
  match result:
    case Done{unit}: ""
    case Fail{error}: F.Error.to_string(error) ++ "\n"

def SurfaceTest.refusal(expected: String, result: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> String:
  match result:
    case Done{tree}: "invalid source parsed\n"
    case Fail{error}:
      +message : String = F.Error.message(error)
      SurfaceTest.verdict("parser refusal", message, String.eq(message, expected))

def SurfaceTest.same_result(first: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>, second: Result<&2, &2, F.Error.t, List<&2, S.Syntax.decl>>) -> String:
  match first second:
    case Fail{error} _: F.Error.to_string(error) ++ "\n"
    case _ Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{a} Done{b}: SurfaceTest.verdict("same tree", "trees differ", S.Syntax.equal_declarations(a, b))

def SurfaceTest.parser_run(cases: List<&2, SurfaceTest.parser_case>) -> String:
  match cases:
    case Nil{}: ""
    case Con{head, tail}:
      match head:
        case SurfaceTest.Round{source}: SurfaceTest.round(P.Parser.round_trip(source)) ++ SurfaceTest.parser_run(tail)
        case SurfaceTest.Refuse{source, expected}: SurfaceTest.refusal(expected, P.Parser.parse(source)) ++ SurfaceTest.parser_run(tail)
        case SurfaceTest.Same{first, second}: SurfaceTest.same_result(P.Parser.parse(first), P.Parser.parse(second)) ++ SurfaceTest.parser_run(tail)

def SurfaceTest.parser_cases() -> List<&2, SurfaceTest.parser_case>:
  [
    SurfaceTest.Round{"mu N : Type 0 := | zero : N | succ (n : N) : N\n"},
    SurfaceTest.Round{"mu N : Type 0 with | zero : N | succ : (n : N) -> N\n"},
    SurfaceTest.Round{"mutual mu A : Type 0 := | a (b : B) : A mu B : Type 0 := | b : B end"},
    SurfaceTest.Round{"mu A : Type 0 with | a : (b : B) -> A and B : Type 0 with | b : B"},
    SurfaceTest.Round{"mu N : Type 0 := | zero : N | succ (n : N) : N\ndef pred : N -> N := fun (n : N) => match n as x in N return N with | zero => zero | succ (p : N) => p"},
    SurfaceTest.Round{"mu N : Type 0 with | zero : N | succ : (n : N) -> N\ndef pred : N -> N := fun (n : N) => case n as x in N return N with | zero => zero | succ p => p"},
    SurfaceTest.Round{"def f : Nat := match n as x in N return Nat with | c (0 i : N) x (1 y : Nat) => y"},
    SurfaceTest.Round{"def f : Nat := match n as x in N return Nat with | z => 0 | s p => (match p as y in N return Nat with | z => 1 | s q => 2)"},
    SurfaceTest.Round{"mu Void : Prop := def exFalso : Void -> Type 0 := fun (v : Void) => match v as x in Void return Type 0 with"},
    SurfaceTest.Round{"def f : Nat := case b with | 0 (x : Nat) => x | 1 (x : Nat) => x"},
    SurfaceTest.Round{"def rec f : Nat -> Nat := fun (x : Nat) => f x and g : Nat := f 0"},
    SurfaceTest.Round{"def f : Type 999999999999999999 := let x : Type 0 := Nat in (x * Nat)"},
    SurfaceTest.Round{"def f : prod (Nat, Nat) := tuple (0, 1) def g : sum (Nat, Nat) := inj 1 of 2 5"},
    SurfaceTest.Round{"axiom ax : Prop def p : Nat := ((0, 1).2 : Nat)"},
    SurfaceTest.Round{"def x : Nat := natAdd 100000000000000000000000000000000 2"},
    SurfaceTest.Round{"def b : Bytes := b\"a\\n\\xFF\""},
    SurfaceTest.Refuse{"def f : Nat := match n with | 0 (x : Nat) => x", "a match branch keys a constructor, not a leg number"},
    SurfaceTest.Refuse{"mutual end", "a mutual group needs at least two mu declarations"},
    SurfaceTest.Refuse{"mutual mu N : Type 0 := end", "a mutual group needs at least two mu declarations"},
    SurfaceTest.Refuse{"mutual mu A : Type 0 := mu B : Type 0 :=", "expected 'mu' or 'end' in a mutual group, found end of input"},
    SurfaceTest.Refuse{"mutual mu A : Type 0 := and B : Type 0 := end", "expected 'mu' or 'end' in a mutual group, found 'and'"},
    SurfaceTest.Refuse{"def f : Type 0 := nu", "nu arrives at M2"},
    SurfaceTest.Refuse{"nu N : Type 0 :=", "nu arrives at M2"},
    SurfaceTest.Refuse{"axiom x : Type 1000000000000000000", "numeric literal too long"},
    SurfaceTest.Refuse{"def x : Nat := 0.", "expected a leg number after '.'"},
    SurfaceTest.Refuse{"def f : Nat := tuple (0,)", "expected a term, found ')'"},
    SurfaceTest.Same{"mu N : Type 0 := | zero : N | succ (n : N) : N\n", "mu N : Type 0 with | zero : N | succ : (n : N) -> N\n"},
    SurfaceTest.Same{"mutual mu A : Type 0 := | a (b : B) : A mu B : Type 0 := | b : B end", "mu A : Type 0 with | a : (b : B) -> A and B : Type 0 with | b : B"}
  ]

def SurfaceTest.checked(result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> Result<&2, &2, F.Error.t, String>:
  match result:
    case Fail{error}: Fail{error}
    case Done{rows}: Done{E.Elab.checked_form(rows)}

def SurfaceTest.same_checked(first: Result<&2, &2, F.Error.t, String>, second: Result<&2, &2, F.Error.t, String>) -> String:
  match first second:
    case Fail{error} _: F.Error.to_string(error) ++ "\n"
    case _ Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{+a} Done{+b}: SurfaceTest.verdict("checked forms", a ++ " versus " ++ b, String.eq(a, b))

def SurfaceTest.match_elaboration() -> String:
  SurfaceTest.same_checked(
    SurfaceTest.checked(E.Elab.check_text(G.Global.initial, "mu N : Type 0 := | zero : N | succ (n : N) : N\ndef pred : N -> N := fun (n : N) => match n as x in N return N with | zero => zero | succ (p : N) => p")),
    SurfaceTest.checked(E.Elab.check_text(G.Global.initial, "mu N : Type 0 with | zero : N | succ : (n : N) -> N\ndef pred : N -> N := fun (n : N) => case n as x in N return N with | zero => zero | succ p => p")))

def SurfaceTest.normal(+globals: F.Global.t, name: String) -> Result<&2, &2, F.Error.t, String>:
  Result.bind(&2, &2, F.Error.t, F.Value.t, String, V.Eval.eval(globals, Nil{}, F.Term.Global{name}),
    value => Result.map(&2, &2, F.Error.t, F.Term.t, String, term => Pp.Pp.term(Nil{}, term), V.Eval.quote(globals, 0n, value)))

def SurfaceTest.computations(pairs: List<&2, F.Pair2<String, String>>, +globals: F.Global.t) -> String:
  match pairs:
    case Nil{}: ""
    case Con{F.Pair2{actual, expected}, tail}:
      SurfaceTest.same_checked(SurfaceTest.normal(globals, actual), SurfaceTest.normal(globals, expected)) ++ SurfaceTest.computations(tail, globals)

def SurfaceTest.neutral(label: String, result: Result<&2, &2, F.Error.t, F.Value.t>) -> String:
  match result:
    case Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{F.Value.VNeutral{head, spine}}: ""
    case Done{value}: label ++ " unfolded before its guarded argument\n"

def SurfaceTest.neutrals(names: List<&2, String>, +globals: F.Global.t) -> String:
  match names:
    case Nil{}: ""
    case Con{+name, tail}: SurfaceTest.neutral(name, V.Eval.eval(globals, Nil{}, F.Term.Global{name})) ++ SurfaceTest.neutrals(tail, globals)

def SurfaceTest.neutral_body(value: Result<&2, &2, F.Error.t, F.Value.t>, globals: F.Global.t) -> String:
  match value:
    case Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{F.Value.VSec{shape, Con{F.Value.Leg{binders, closure}, Nil{}}}}:
      SurfaceTest.neutral("recursive call on a neutral argument", V.Eval.open_closure(globals, closure, [F.Value.var(0n)]))
    case Done{value}: "neutral lambda or leg missing\n"

def SurfaceTest.opaque(entry: Maybe<&2, F.Global.entry>, globals: F.Global.t) -> String:
  match entry:
    case Some{F.Global.Def{F.Global.DefEntry{ty, body, reducible, rec_arg, partial}}}:
      SurfaceTest.neutral("explicitly opaque definition", V.Eval.eval(F.Global.add("double", F.Global.Def{F.Global.DefEntry{ty, body, False{}, rec_arg, partial}}, globals), Nil{}, F.Term.Global{"doubled"}))
    case _: "double definition missing\n"

def SurfaceTest.no_axioms(names: List<&2, String>) -> String:
  match names:
    case Nil{}: ""
    case Con{head, tail}: "provisional recursive axiom leaked: " ++ head ++ "\n"

def SurfaceTest.recursive_values(result: Result<&2, &2, F.Error.t, E.Elab.checked>) -> String:
  match result:
    case Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{F.Pair2{+globals, rows}}:
      SurfaceTest.computations([F.Pair2{"doubled", "four"}, F.Pair2{"mutualValue", "two"}, F.Pair2{"helper", "z"}, F.Pair2{"helperDirect", "z"}, F.Pair2{"spare", "z"}, F.Pair2{"kept", "seven"}, F.Pair2{"chosen", "seven"}, F.Pair2{"indexed", "one"}], globals)
      ++ SurfaceTest.neutrals(["double", "keep", "partial"], globals)
      ++ SurfaceTest.neutral_body(V.Eval.eval(globals, Nil{}, F.Term.Global{"neutral"}), globals)
      ++ SurfaceTest.opaque(F.Global.find("double", globals), globals)
      ++ SurfaceTest.no_axioms(E.Elab.axiom_names(rows))

def SurfaceTest.axiom_names(names: List<&2, String>) -> String:
  match names:
    case [name]: SurfaceTest.verdict("axiom name", "wrong axiom", String.eq(name, "trust"))
    case _: "wrong axiom count\n"

def SurfaceTest.axiom_result(result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> String:
  match result:
    case Fail{error}: F.Error.to_string(error) ++ "\n"
    case Done{+rows}:
      SurfaceTest.same_checked(Done{E.Elab.checked_form(rows)}, Done{"axiom trust : Nat\ndef x : Nat := trust\n"}) ++ SurfaceTest.axiom_names(E.Elab.axiom_names(rows))

def SurfaceTest.budget_empty(result: F.Pair2<Result<&2, &2, F.Error.t, E.Elab.checked>, C.Budget.t>) -> String:
  match result:
    case F.Pair2{Done{value}, C.Budget.Steps{10n}}: ""
    case _: "empty source changed budget\n"

def SurfaceTest.budget_parse(result: F.Pair2<Result<&2, &2, F.Error.t, E.Elab.checked>, C.Budget.t>) -> String:
  match result:
    case F.Pair2{Fail{F.Error.Parse{message, line, col}}, C.Budget.Steps{10n}}: ""
    case _: "parser failure changed budget\n"

def SurfaceTest.budget_spent(result: F.Pair2<Result<&2, &2, F.Error.t, E.Elab.checked>, C.Budget.t>) -> String:
  match result:
    case F.Pair2{Fail{F.Error.Budget_exhausted{message}}, C.Budget.Steps{0n}}: ""
    case _: "checker failed to preserve exhausted budget\n"

def SurfaceTest.elab_refusal(expected: String, result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> String:
  match result:
    case Done{rows}: "invalid source elaborated\n"
    case Fail{error}:
      +message : String = F.Error.message(error)
      SurfaceTest.verdict("elaborator refusal", message, String.eq(message, expected))

def SurfaceTest.elab_success(result: Result<&2, &2, F.Error.t, E.Elab.rows>) -> String:
  match result:
    case Done{rows}: ""
    case Fail{error}: F.Error.to_string(error) ++ "\n"

# The reference eagerly builds this many optional leg types and times out.
# Retain both arity witnesses as parser tests without imposing an elaborator bound.
def SurfaceTest.boundary_width_source(n: String) -> String:
  "def x : sum (Nat, Nat) := inj 0 of " ++ n ++ " 0"

def SurfaceTest.boundary(+n: String) -> String:
  SurfaceTest.elab_refusal("the leg address is outside the collection", E.Elab.check_text(G.Global.initial, "def p : prod (Nat, Nat) := tuple (0, 1) def x : Nat := p." ++ n))
  ++ SurfaceTest.elab_refusal("the leg address is outside the collection", E.Elab.check_text(G.Global.initial, "def x : sum (Nat, Nat) := inj " ++ n ++ " of 2 0"))
  ++ SurfaceTest.elab_refusal("the leg address is outside the collection", E.Elab.check_text(G.Global.initial, "def x : Nat := case (inj 0 of 2 0 : sum (Nat, Nat)) with | " ++ n ++ " (x : Nat) => x | 1 (x : Nat) => x"))
  ++ SurfaceTest.elab_success(E.Elab.check_text(G.Global.initial, "axiom U : Type " ++ n))
  ++ SurfaceTest.round(P.Parser.round_trip(SurfaceTest.boundary_width_source(n)))

def SurfaceTest.additional() -> String:
  SurfaceTest.axiom_result(E.Elab.check_text(G.Global.initial, "axiom trust : Nat def x : Nat := trust"))
  ++ SurfaceTest.budget_empty(E.Elab.check_in_stateful(G.Global.initial, C.Budget.Steps{10n}, ""))
  ++ SurfaceTest.budget_parse(E.Elab.check_in_stateful(G.Global.initial, C.Budget.Steps{10n}, "def"))
  ++ SurfaceTest.budget_spent(E.Elab.check_in_stateful(G.Global.initial, C.Budget.Steps{0n}, "def x : Nat := 0"))
  ++ SurfaceTest.boundary("281474976710656")
  ++ SurfaceTest.boundary("999999999999999999")

def SurfaceTest.recursive_source() -> String:
  "\nmu N : Type 0 with | zero : N | succ : N -> N\nmu A : Type 0 with | leaf : A | node : B -> A\nand B : Type 0 with | cons : A -> B\nmu V : (0 i : N) -> Type 0 with\n| vz : V zero\n| vs : (0 i : N) -> V i -> V (succ i)\ndef rec length : (0 i : N) -> V i -> N := fun (0 i : N) (v : V i) => case v as x in V j return N with | vz => zero | vs 0 j w => succ (length j w)\ndef rec double : N -> N := fun (n : N) => case n as x in N return N with | zero => zero | succ m => succ (succ (double m))\ndef rec sizeA : A -> Nat := fun (a : A) => case a as x in A return Nat with | leaf => 0 | node b => natAdd 1 (sizeB b)\nand sizeB : B -> Nat := fun (b : B) => case b as x in B return Nat with | cons a => natAdd 1 (sizeA a)\ndef rec f : N -> N := fun (n : N) => case n as x in N return N with | zero => zero | succ m => g m\nand g : N -> N := fun (n : N) => zero\nand spare : N := zero\ndef rec keep : Nat -> N -> Nat := fun (a : Nat) => fun (n : N) => case n as x in N return Nat with | zero => a | succ m => keep a m\ndef rec choose : N -> Nat -> Nat := fun (n : N) => case n as x in N return (Nat -> Nat) with | zero => fun (a : Nat) => a | succ m => choose m\ndef doubled : N := double (succ (succ zero))\ndef four : N := succ (succ (succ (succ zero)))\ndef z : N := zero\ndef mutualValue : Nat := sizeA (node (cons leaf))\ndef two : Nat := 2\ndef helper : N := f (succ zero)\ndef helperDirect : N := g zero\ndef kept : Nat := keep 7 (succ (succ zero))\ndef seven : Nat := 7\ndef chosen : Nat := choose (succ (succ zero)) 7\ndef indexed : N := length (succ zero) (vs zero vz)\ndef one : N := succ zero\ndef partial : N -> Nat := keep 7\ndef neutral : N -> Nat := fun (n : N) => keep 7 n\n"

def SurfaceTest.finish(failures: String, passed: Bool) -> IO(Unit):
  match passed:
    case True{}: IO.print("surface: 20 lexer, 28 parser, match elaboration, 13 recursive values, axiom reporting, budget and extreme index checks passed")
    case False{}: IO.die(Unit, 1, failures)

def main() -> IO(Unit):
  +failures : String = SurfaceTest.run([
    SurfaceTest.Case{"", "end of input@1:1;"},
    SurfaceTest.Case{" \t\r\n", "end of input@2:1;"},
    SurfaceTest.Case{"--abc", "end of input@1:6;"},
    SurfaceTest.Case{"--abc\nx", "identifier x@2:1;end of input@2:2;"},
    SurfaceTest.Case{".1 .2 .10 .01 .", "'.1'@1:1;'.2'@1:4;'.'@1:7;number 10@1:8;'.'@1:11;number 1@1:12;'.'@1:15;end of input@1:16;"},
    SurfaceTest.Case{"0 999999999999999999999999999999", "number 0@1:1;number 999999999999999999999999999999@1:3;end of input@1:33;"},
    SurfaceTest.Case{"() ( ) := : -> => * , |", "'()'@1:1;'('@1:4;')'@1:6;':='@1:8;':'@1:11;'->'@1:13;'=>'@1:16;'*'@1:19;','@1:21;'|'@1:23;end of input@1:24;"},
    SurfaceTest.Case{"a_1' b", "identifier a_1'@1:1;identifier b@1:6;end of input@1:7;"},
    SurfaceTest.Case{"b\"\"", "bytes[]@1:1;end of input@1:4;"},
    SurfaceTest.Case{"b\"a\\n\\xFF\\0\"", "bytes[97,10,255,0,]@1:1;end of input@1:13;"},
    SurfaceTest.Case{"b\"unterminated", "unterminated byte literal@1:15"},
    SurfaceTest.Case{"b\"\\", "unterminated byte escape@1:3"},
    SurfaceTest.Case{"b\"\\q\"", "invalid byte escape \\q@1:3"},
    SurfaceTest.Case{"b\"\\x\"", "invalid byte escape \\x@1:3"},
    SurfaceTest.Case{"b\"\\xG0\"", "byte escape requires two hexadecimal digits@1:3"},
    SurfaceTest.Case{"b\"\n\"", "unescaped newline in byte literal@1:3"},
    SurfaceTest.Case{"-", "unexpected character '-'@1:1"},
    SurfaceTest.Case{"=", "unexpected character '='@1:1"},
    SurfaceTest.Case{"@", "unexpected character '@'@1:1"},
    SurfaceTest.Case{"def axiom mu mutual end rec match nu", "'def'@1:1;'axiom'@1:5;'mu'@1:11;'mutual'@1:14;'end'@1:21;'rec'@1:25;'match'@1:29;'nu'@1:35;end of input@1:37;"}
  ])
  +all_failures : String = failures ++ SurfaceTest.parser_run(SurfaceTest.parser_cases) ++ SurfaceTest.match_elaboration ++ SurfaceTest.recursive_values(E.Elab.check_in(G.Global.initial, SurfaceTest.recursive_source)) ++ SurfaceTest.additional
  SurfaceTest.finish(all_failures, String.is_empty(all_failures))
