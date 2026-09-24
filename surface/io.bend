import Base

# Source text uses one character per input byte, matching OCaml strings.
def Sys_io.push(bytes: List<&2, U32>, reversed: String) -> String:
  match bytes:
    case Nil{}: reversed
    case Con{head, tail}: Sys_io.push(tail, SCon{Chr{head}, reversed})

def Sys_io.reverse(text: String, acc: String) -> String:
  match text:
    case SNil{}: acc
    case SCon{head, tail}: Sys_io.reverse(tail, SCon{head, acc})

type Sys_io.read_job is Type:
  Sys_io.Read{file: File, reversed: String}
  Sys_io.ReadResult{result: File & Result<&1, &1, U32 & String, List<&2, U32>>, reversed: String}

# The recursive effect reads until EOF, with no source-size or fuel bound.
@unsafe
def Sys_io.read_loop(job: Sys_io.read_job) -> IO(Result<&2, &2, String, String>):
  match job:
    case Sys_io.Read{file, reversed}:
      do IO<Result<&2, &2, String, String>>:
        result : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 65536)
        Sys_io.read_loop(Sys_io.ReadResult{result, reversed})
    case Sys_io.ReadResult{(file, result), reversed}:
      match result:
        case Fail{(code, message)}:
          do IO<Result<&2, &2, String, String>>:
            closed : Unit <- File.close(file)
            return Fail{message}
        case Done{Nil{}}:
          do IO<Result<&2, &2, String, String>>:
            closed : Unit <- File.close(file)
            return Done{Sys_io.reverse(reversed, "")}
        case Done{Con{head, tail}}:
          Sys_io.read_loop(Sys_io.Read{file, Sys_io.push(Con{head, tail}, reversed)})

def Sys_io.opened(result: Result<&1, &1, U32 & String, File>, path: String) -> IO(Result<&2, &2, String, String>):
  match result:
    case Fail{(code, message)}: IO.pure(Result<&2, &2, String, String>, Fail{path ++ ": " ++ message})
    case Done{file}: Sys_io.read_loop(Sys_io.Read{file, ""})

def Sys_io.read_file(+path: String) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    result : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Sys_io.opened(result, path)
