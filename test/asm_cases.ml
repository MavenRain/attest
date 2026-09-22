open Assay_asm
open Asm

let block ?(destination = false) ?(stack_in = 0) label body ending =
  { label; destination; stack_in; body; ending }
let stop label body = block label body (Halt Stop)
let zeros n = List.init n (fun _i -> Push "")
let target ?(stack_in = 0) label = block ~destination:true ~stack_in label [] (Halt Stop)
let ref20 =
  [block "write" [Push "2a"; Push ""; Op "SSTORE"] (Goto (1, "read"))]
  @ List.init 4 (fun i -> block ("guard" ^ string_of_int i) [] (Halt Invalid))
  @ [block ~destination:true "read"
       [Push ""; Op "SLOAD"; Push ""; Op "MSTORE"; Push "20"; Push ""] (Halt Return)]
let diamond = [block "entry" [Push "01"] (Branch (1, "yes", "no"));
  block ~destination:true "yes" [Push "2a"] (Goto (1, "join"));
  block ~destination:true "no" [Push "2b"] (Next "join");
  block ~destination:true ~stack_in:1 "join" [Op "POP"] (Halt Stop)]
let loop = [block ~destination:true "loop" [Push "01"] (Branch (2, "loop", "done")); target "done"]
let fixtures = ["ref20", ref20; "diamond", diamond; "loop", loop;
  "pushes", [stop "pushes" (List.init 33 (fun n -> Push (String.make (2 * n) 'f')))];
  "depths", [stop "depths" (zeros 17 @ List.init 16 (fun i -> Dup (i + 1))
                                            @ List.init 16 (fun i -> Swap (i + 1)))]]
let report name good detail =
  Printf.printf "ASM-CASE %s %s %s\n" name (if good then "OK" else "FAIL") detail;
  good
let rejection name program expected =
  Asm.assemble program |> Result.fold
    ~ok:(fun _p -> report name false ("accepted; want=" ^ expected))
    ~error:(fun e -> let got = Asm.error_text e in report name (got = expected) got)
let blocks_of p = List.length (Asm.heights p)
let record p = List.map (fun (h : Asm.height) -> h.incoming, h.outgoing, h.peak) (Asm.heights p)
let acceptance name program expected =
  Asm.assemble program |> Result.fold
    ~ok:(fun p -> report name (Asm.hex p = expected)
      (if String.length expected > 160 then "bytes=" ^ string_of_int (String.length (Asm.hex p) lsr 1) else Asm.hex p),
      blocks_of p)
    ~error:(fun e -> report name false (Asm.error_text e), 0)
let suite () =
  let bad = [
    "empty", [], "EMPTY-PROGRAM";
    "empty-label", [stop "" []], "EMPTY-LABEL";
    "duplicate", [stop "x" []; stop "x" []], "DUPLICATE-LABEL x";
    "entry", [block ~stack_in:1 "x" [] (Halt Stop)], "ENTRY-HEIGHT 1";
    "height-negative", [stop "x" []; target ~stack_in:(-1) "y"], "INVALID-HEIGHT y -1";
    "height-large", [stop "x" []; target ~stack_in:1025 "y"], "INVALID-HEIGHT y 1025";
    "add-underflow", [stop "x" [Push ""; Op "ADD"]], "UNDERFLOW x ADD got=1 need=2";
    "sstore-underflow", [stop "x" [Push ""; Op "SSTORE"]], "UNDERFLOW x SSTORE got=1 need=2";
    "dup-underflow", [stop "x" [Dup 1]], "UNDERFLOW x DUP1 got=0 need=1";
    "swap-underflow", [stop "x" [Push ""; Swap 1]], "UNDERFLOW x SWAP1 got=1 need=2";
    "push-overflow", [stop "x" (zeros 1025)], "OVERFLOW x PUSH0 got=1025";
    "dup-overflow", [stop "x" (zeros 1024 @ [Dup 1])], "OVERFLOW x DUP1 got=1025";
    "goto-overflow", [block "x" (zeros 1024) (Goto (1, "y")); target ~stack_in:1024 "y"],
      "OVERFLOW x PUSH-label got=1025";
    "branch-overflow", [block "x" (zeros 1024) (Branch (1, "y", "y")); target ~stack_in:1023 "y"],
      "OVERFLOW x PUSH-label got=1025";
    "branch-underflow", [block "x" [] (Branch (1, "y", "y")); target "y"],
      "UNDERFLOW x JUMPI got=1 need=2";
    "return-underflow", [block "x" [Push ""] (Halt Return)], "UNDERFLOW x RETURN got=1 need=2";
    "revert-underflow", [block "x" [] (Halt Revert)], "UNDERFLOW x REVERT got=0 need=2";
    "selfdestruct-underflow", [block "x" [] (Halt Selfdestruct)], "UNDERFLOW x SELFDESTRUCT got=0 need=1";
    "unknown-label", [block "x" [] (Goto (1, "y"))], "UNKNOWN-LABEL y";
    "not-destination", [block "x" [] (Goto (1, "y")); stop "y" []], "NOT-DESTINATION y";
    "goto-height", [block "x" [Push ""] (Goto (1, "y")); target "y"],
      "HEIGHT-MISMATCH x y got=1 want=0";
    "branch-yes-height", [block "x" [Push ""] (Branch (1, "y", "z")); target ~stack_in:1 "y"; target "z"],
      "HEIGHT-MISMATCH x y got=0 want=1";
    "branch-no-height", [block "x" [Push ""] (Branch (1, "y", "z")); target "y"; target ~stack_in:1 "z"],
      "HEIGHT-MISMATCH x z got=0 want=1";
    "next-height", [block "x" [Push ""] (Next "y"); target "y"], "HEIGHT-MISMATCH x y got=1 want=0";
    "next-order", [block "x" [] (Next "z"); stop "y" []; stop "z" []], "INVALID-NEXT x z";
    "next-last", [block "x" [] (Next "x")], "INVALID-NEXT x x";
    "unreachable-underflow", [stop "x" []; stop "y" [Op "ADD"]], "UNDERFLOW y ADD got=0 need=2";
    "clz", [stop "x" [Op "CLZ"]], "UNKNOWN-OPCODE CLZ";
    "opcode-case", [stop "x" [Op "add"]], "UNKNOWN-OPCODE add";
    "opcode-push", [stop "x" [Op "PUSH0"]], "UNKNOWN-OPCODE PUSH0";
    "label-width-small", [block "x" [] (Goto (0, "x"))], "INVALID-WIDTH 0";
    "label-width-large", [block "x" [] (Branch (33, "x", "x"))], "INVALID-WIDTH 33";
    "label-overflow", [block "x" (zeros 253) (Goto (1, "y")); target ~stack_in:253 "y"], "LABEL-OVERFLOW y PUSH1"
  ] in
  let malformed = ["0"; "gg"; "AA"; "0x00"; String.make 66 '0'] |> List.mapi (fun i bytes ->
    "push-bad-" ^ string_of_int i, [stop "x" [Push bytes]], "INVALID-PUSH " ^ bytes) in
  let depths = [-1; 0; 17; max_int] |> List.concat_map (fun n ->
    ["dup-bad-" ^ string_of_int n, [stop "x" [Dup n]], Printf.sprintf "INVALID-DEPTH DUP %d" n;
     "swap-bad-" ^ string_of_int n, [stop "x" [Swap n]], Printf.sprintf "INVALID-DEPTH SWAP %d" n]) in
  let controls = ["STOP"; "JUMP"; "JUMPI"; "JUMPDEST"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT"]
    |> List.map (fun name -> "body-" ^ name, [stop "x" [Op name]], "CONTROL-IN-BODY " ^ name) in
  let rejected = List.map (fun (name, program, want) -> rejection name program want, 0)
    (bad @ malformed @ depths @ controls) in
  let good = [
    "ref20", ref20, "602a5f55600b56fefefefe5b5f545f5260205ff3";
    "diamond", diamond, "6001600857600e565b602a6011565b602b5b5000";
    "loop", loop, "5b60016100005761000b565b00";
    "push-zero", [stop "x" [Push ""; Push "00"]], "5f600000";
    "stack-limit", [stop "x" (zeros 1024 @ [Swap 16])], String.concat "" (List.init 1024 (fun _i -> "5f")) ^ "9f00";
    "label-32", [block "x" [] (Goto (32, "y")); target "y"], "7f" ^ String.make 62 '0' ^ "22565b00";
    "revert", [block "x" (zeros 2) (Halt Revert)], "5f5ffd";
    "selfdestruct", [block "x" [Push ""] (Halt Selfdestruct)], "5fff";
    "next-unmarked", [block "x" [] (Next "y"); stop "y" []], "00"
  ] in
  let accepted = List.map (fun (name, program, want) -> acceptance name program want) good in
  let pinned program label pc want =
    Asm.assemble program |> Result.fold ~error:(fun _e -> false, 0) ~ok:(fun p ->
      (List.assoc_opt label (Asm.labels p) = Some pc && record p = want), blocks_of p) in
  let (entry_ok, entry_blocks) = pinned ref20 "read" 11
    [(0, 0, 2); (0, 0, 0); (0, 0, 0); (0, 0, 0); (0, 0, 0); (0, 0, 2)] in
  let (join_ok, join_blocks) = pinned diamond "join" 17
    [(0, 0, 2); (0, 1, 2); (0, 1, 1); (1, 0, 1)] in
  let metadata = report "labels-and-heights" (entry_ok && join_ok) "ref20 diamond",
    entry_blocks + join_blocks in
  let results = metadata :: rejected @ accepted in
  let passed = List.for_all fst results in
  let blocks = List.fold_left (fun acc (_ok, n) -> acc + n) 0 results in
  Printf.printf "STACK-HEIGHT blocks=%d mismatch=%d cases=%d %s\n"
    blocks (List.length (List.filter (fun (ok, _n) -> not ok) results)) (List.length results)
    (if passed then "OK" else "FAIL");
  if passed then 0 else 1

let emit_fixtures () =
  let results = List.map (fun (name, program) -> Asm.assemble program |> Result.fold
    ~ok:(fun p -> Printf.printf "%s %s\n" name (Asm.hex p); true)
    ~error:(fun e -> prerr_endline (Asm.error_text e); false)) fixtures in
  if List.for_all Fun.id results then 0 else 1
let listing bytes = Listing.render bytes |> Result.fold
  ~ok:(fun output -> print_string output; 0)
  ~error:(fun e -> prerr_endline (Listing.error_text e); 2)
let effect name count =
  let families = List.init 33 (fun n -> "PUSH" ^ string_of_int n, Push (String.make (2 * n) '0'))
    @ List.init 16 (fun i -> "DUP" ^ string_of_int (i + 1), Dup (i + 1))
    @ List.init 16 (fun i -> "SWAP" ^ string_of_int (i + 1), Swap (i + 1)) in
  let item = List.assoc_opt name families |> Option.value ~default:(Op name) in
  let result = Result.bind (int_of_string_opt count |> Option.to_result ~none:"invalid count") (fun n ->
      if n < 0 || n > 1024 then Error "invalid count"
      else Asm.assemble [stop "effect" (zeros n @ [item])] |> Result.map_error Asm.error_text) in
  result |> Result.fold ~error:(fun e -> print_endline e; 2)
    ~ok:(fun p -> List.iter (fun (h : Asm.height) -> Printf.printf "%d %d\n" h.outgoing h.peak) (Asm.heights p); 0)
let main () =
  match List.of_seq (Array.to_seq Sys.argv) with
  | [_exe; "suite"] -> suite ()
  | [_exe; "fixtures"] -> emit_fixtures ()
  | [_exe; "listing"; bytes] -> listing bytes
  | [_exe; "effect"; name; count] -> effect name count
  | [_exe; "metadata"] ->
    List.init 256 Asm.decode_opcode |> List.iter (Option.iter (fun row ->
      Printf.printf "%02x %s %d %d\n" row.byte row.name row.pops row.pushes)); 0
  | [] | [_] | [_; _] | [_; _; _]
  | [_; _; _; _] | _ :: _ :: _ :: _ :: _ :: _ ->
    prerr_endline "usage: asm_cases suite | fixtures | listing HEX | effect OPCODE HEIGHT"; 64
let () = exit (main ())
