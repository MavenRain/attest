import Base
import ./foundation.bend as F

def Kernel.fst(-A: Data, -B: Data, pair: F.Pair2<A, B>) -> A:
  F.Pair2{x, y} = pair
  x

def Kernel.snd(-A: Data, -B: Data, pair: F.Pair2<A, B>) -> B:
  F.Pair2{x, y} = pair
  y

def Kernel.first(-A: Data, -B: Data, -C: Data, triple: F.Triple3<A, B, C>) -> A:
  F.Triple3{x, y, z} = triple
  x

def Kernel.second(-A: Data, -B: Data, -C: Data, triple: F.Triple3<A, B, C>) -> B:
  F.Triple3{x, y, z} = triple
  y

def Kernel.third(-A: Data, -B: Data, -C: Data, triple: F.Triple3<A, B, C>) -> C:
  F.Triple3{x, y, z} = triple
  z

# Reusable traversals keep context explicit so template arguments are closed.
def Kernel.map(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B,
  xs: List<&2, A>, +ctx: C) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Con{f(ctx, x), Kernel.map(A, B, C, f, rest, ctx)}

def Kernel.map_result(~A: Data, ~B: Data, ~C: Data,
  ~f: C -> A -> Result<&2, &2, F.Error.t, B>,
  xs: List<&2, A>, +ctx: C) -> Result<&2, &2, F.Error.t, List<&2, B>>:
  match xs:
    case Nil{}:
      Done{Nil{}}
    case Con{x, rest}:
      do Result<&2, &2, F.Error.t, List<&2, B>>:
        y: B <- f(ctx, x)
        ys: List<&2, B> <- Kernel.map_result(A, B, C, f, rest, ctx)
        return Con{y, ys}

def Kernel.from_maybe(-A: Data, value: Maybe<&2, A>, error: F.Error.t)
  -> Result<&2, &2, F.Error.t, A>:
  match value:
    case None{}:
      Fail{error}
    case Some{x}:
      Done{x}

def Kernel.result_option(-A: Data, result: Result<&2, &2, F.Error.t, A>) -> Maybe<&2, A>:
  match result:
    case Fail{error}:
      None{}
    case Done{x}:
      Some{x}

def Kernel.one(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match rest:
        case Nil{}:
          Some{x}
        case Con{y, more}:
          None{}

def Kernel.two(-A: Data, xs: List<&2, A>) -> Maybe<&2, F.Pair2<A, A>>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      match rest:
        case Nil{}:
          None{}
        case Con{y, more}:
          match more:
            case Nil{}:
              Some{F.Pair2{x, y}}
            case Con{z, tail}:
              None{}

def Kernel.join(xs: List<&2, String>, +sep: String) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match rest:
        case Nil{}:
          x
        case Con{y, more}:
          x ++ sep ++ Kernel.join(Con{y, more}, sep)

def Kernel.member(xs: List<&2, String>, +name: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      Bool.or(String.eq(x, name), Kernel.member(rest, name))

def Kernel.rev_append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  List.reverse.go(&2, A, xs, ys)

def Kernel.guard(ok: Bool, error: F.Error.t) -> Result<&2, &2, F.Error.t, Unit>:
  match ok:
    case False{}:
      Fail{error}
    case True{}:
      Done{Unit{}}
