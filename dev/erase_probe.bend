import Base
import ../lib/foundation.bend as F
import ../lib/kernel_context.bend as C
import ../lib/kernel.bend as K
import ../lib/kernel_primitives.bend as G
import ../lib/kernel_eval.bend as V
import ../lib/erasure.bend as R
import ../surface/elab.bend as E
import ../surface/io.bend as I

def Probe.semantics() -> R.Erase.Semantics:
  R.Erase.Semantics{ctx => term => K.Check.infer_univ_stateful(ctx,term),ctx => q => term => K.Check.infer_stateful(ctx,q,term),globals => size => value => V.Eval.quote(globals,size,value)}

def Probe.erased(result:Result<&2,&2,F.Error.t,List<&2,F.Pair2<String,R.Erase.entry>>>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit,1,F.Error.to_string(error))
    case Done{rows}: IO.write(R.Erase.print(rows))

def Probe.checked(result:Result<&2,&2,F.Error.t,E.Elab.checked>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit,1,F.Error.to_string(error))
    case Done{F.Pair2{globals,rows}}: Probe.erased(R.Erase.program(~Probe.semantics,C.Budget.unlimited,globals,rows))

def Probe.read(result:Result<&2,&2,String,String>) -> IO(Unit):
  match result:
    case Fail{error}: IO.die(Unit,1,error)
    case Done{source}: Probe.checked(E.Elab.check_in(G.Global.initial,source))

def Probe.run(args:List<String>) -> IO(Unit):
  match args:
    case path <> Nil{}:
      do IO<Unit>:
        result:Result<&2,&2,String,String> <- I.Sys_io.read_file(path)
        Probe.read(result)
    case other: IO.die(Unit,1,"usage: erase_probe FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    args:List<String> <- IO.args()
    Probe.run(args)
