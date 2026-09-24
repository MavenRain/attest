import Base
import ../lib/foundation.bend as F
import ../surface/io.bend as I
import ../surface/parser.bend as P

def Probe.parsed(result: Result<&2, &2, F.Error.t, Unit>) -> IO(Unit):
  match result:
    case Fail{error}:
      IO.die(Unit, 1, F.Error.to_string(error))
    case Done{unit}:
      IO.print("PARSE round-trip OK")

def Probe.read(result: Result<&2, &2, String, String>) -> IO(Unit):
  match result:
    case Fail{message}:
      IO.die(Unit, 64, message)
    case Done{source}:
      Probe.parsed(P.Parser.round_trip(source))

def Probe.path(path: String, rest: List<String>) -> IO(Unit):
  match rest:
    case Nil{}:
      do IO<Unit>:
        source: Result<&2, &2, String, String> <- I.Sys_io.read_file(path)
        Probe.read(source)
    case Con{arg, more}:
      IO.die(Unit, 64, "usage: parse_probe FILE")

def Probe.args(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.die(Unit, 64, "usage: parse_probe FILE")
    case Con{path, rest}:
      Probe.path(path, rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args: List<String> <- IO.args()
    Probe.args(args)
