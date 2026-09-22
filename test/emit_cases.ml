open Kanon_kernel
module E = Assay_emit.Emit
module R = Assay_emit.Recognize
let ( let* ) = Result.bind
let require label yes = if yes then Ok () else Error label
let lit n = Eterm.KLit (Literal.LInt (Z.of_int n))
let value result = Result.map fst result
let env = E.environment ["f", Erase.Code [Eterm.KFun (Eterm.Fid "f", [Eterm.RI31], Eterm.RI31,
  Eterm.KApp (Eterm.KGlobal "natAdd", [Eterm.KVar 0; lit 1]))]]
let eval term = value (E.eval env [] 1000 term)
let good label expected term = require label (eval term = Ok expected)
let bad label expected term = require label (eval term = Error expected)
let unit_tid = Eterm.Tid "tuple<>"
let pair_tid = Eterm.Tid "pair-test"

let constructors () =
  let tests = [
    good "literal" (R.Nat (Z.of_int 7)) (lit 7);
    good "erased" R.Erased Eterm.KErased;
    good "let-var" (R.Nat (Z.of_int 9)) (Eterm.KLet ("x", lit 9, Eterm.KVar 0));
    good "app" (R.Nat (Z.of_int 10)) (Eterm.KApp (Eterm.KGlobal "f", [lit 9]));
    good "tail" (R.Nat (Z.of_int 10)) (Eterm.KTail (Eterm.KGlobal "f", [lit 9]));
    good "struct" (R.Struct (pair_tid, [R.Nat (Z.of_int 8)])) (Eterm.KStruct (pair_tid, [lit 8]));
    good "projection" (R.Nat (Z.of_int 8)) (Eterm.KProj (pair_tid, 0, Eterm.KStruct (pair_tid, [lit 8])));
    good "tag" (R.Tag (pair_tid, 2, [R.Nat (Z.of_int 8)])) (Eterm.KTag (pair_tid, 2, [lit 8]));
    good "case" (R.Nat (Z.of_int 8)) (Eterm.KCase (pair_tid, Eterm.KTag (pair_tid, 2, [lit 8]),
      [{Eterm.tag=2; arity=1; body=Eterm.KVar 0}]));
    good "word-case" (R.Nat (Z.of_int 8)) (Eterm.KCase (R.word_tid, Eterm.KTag (R.word_tid, 0, [lit 8]),
      [{Eterm.tag=0; arity=1; body=Eterm.KVar 0}]));
    bad "closure" E.Higher_order (Eterm.KClos (Eterm.Fid "f", 1, []));
    bad "indirect-app" E.Higher_order (Eterm.KApp (Eterm.KVar 0, [lit 0]));
    bad "partial" E.Higher_order (Eterm.KGlobal "f");
    bad "delay" (E.Later "KDELAY") (Eterm.KDelay (Eterm.Fid "f", []));
    bad "force" (E.Later "KFORCE") (Eterm.KForce (lit 0));
    bad "string" (E.Later "STRING") (Eterm.KLit (Literal.LString "x"));
    bad "bad-index" (E.Invalid_ir "index") (Eterm.KVar (-1));
    bad "missing" (E.Missing "gone") (Eterm.KGlobal "gone");
    require "fuel" (E.eval env [] 0 (lit 1) = Error E.Budget);
    require "runtime-nat" (E.effect 0 (R.Nat Z.zero) = Error E.Nat_runtime);
    good "natSub" (R.Nat Z.zero) (Eterm.KApp (Eterm.KGlobal "natSub", [lit 2; lit 8]));
    good "natMul" (R.Nat (Z.of_int 42)) (Eterm.KApp (Eterm.KGlobal "natMul", [lit 6; lit 7]));
  ] in
  let* () = List.fold_left (fun result test -> let* () = result in test) (Ok ()) tests in
  Printf.printf "EMIT-CONSTRUCTORS cases=%d OK\n" (List.length tests); Ok ()

(* Review round 2026-09-10 (A-2):  ktag, kstruct, words, kclos, ktail and
   fields were literal text in the two markers below.  They are counted from
   the values and the terms the recognizer accepted, so a leak or a lost
   positive case moves the printed number. *)
let leak result = Result.fold ~ok:(fun _ -> 1) ~error:(fun _ -> 0) result

let is_word value = match value with
  | R.Word _ -> true
  | R.Nat _ | R.Erased | R.Struct _ | R.Tag _ | R.Runtime_word _ | R.Closure _ -> false

let words () =
  let high = Z.pred (Z.shift_left Z.one 256) in
  let tests = [
    require "word-zero" (R.tag R.word_tid 0 [R.Nat Z.zero] = Ok (R.Word Z.zero));
    require "word-max" (R.tag R.word_tid 0 [R.Nat high] = Ok (R.Word high));
    require "word-overflow" (R.tag R.word_tid 0 [R.Nat (Z.succ high)] = Error R.Word_range);
    require "word-negative" (R.tag R.word_tid 0 [R.Nat Z.minus_one] = Error R.Word_range);
    require "word-shape" (R.tag R.word_tid 1 [R.Nat Z.zero] = Error R.Word_shape);
    require "word-struct" (R.struct_value R.word_tid [R.Nat Z.zero] = Error R.Word_boxed);
    require "word-leaked-tag" (R.unboxed (R.Tag (R.word_tid, 0, [R.Nat Z.zero])) = Error R.Word_boxed);
    require "word-leaked-struct" (R.unboxed (R.Struct (unit_tid,
      [R.Struct (R.word_tid, [R.Nat Z.zero])])) = Error R.Word_boxed);
    good "word-unbox" (R.Word (Z.of_int 42)) (Eterm.KTag (R.word_tid, 0, [lit 42]));
  ] in
  let* () = List.fold_left (fun result test -> let* () = result in test) (Ok ()) tests in
  let recognized = List.filter_map Result.to_option
    [R.tag R.word_tid 0 [R.Nat Z.zero]; R.tag R.word_tid 0 [R.Nat high]] in
  let evaluated = Option.to_list (Result.to_option (eval (Eterm.KTag (R.word_tid, 0, [lit 42])))) in
  let ktag = leak (R.unboxed (R.Tag (R.word_tid, 0, [R.Nat Z.zero]))) in
  let kstruct = leak (R.struct_value R.word_tid [R.Nat Z.zero])
    + leak (R.unboxed (R.Struct (unit_tid, [R.Struct (R.word_tid, [R.Nat Z.zero])]))) in
  let produced = List.length (List.filter is_word (recognized @ evaluated)) in
  Printf.printf "WORD-UNBOX ktag=%d kstruct=%d words=%d cases=%d OK\n"
    ktag kstruct produced (List.length tests); Ok ()

let storage () =
  let closure = Eterm.KClos (Eterm.Fid "f", 1, []) in
  let lookup name = if name = "hidden" then Some closure else None in
  let clean = Eterm.KStruct (pair_tid, [Eterm.KTag (R.word_tid, 0, [lit 0])]) in
  let boxed = Eterm.KStruct (pair_tid, [closure]) in
  let tailed = Eterm.KTail (Eterm.KGlobal "f", []) in
  let hidden = Eterm.KGlobal "hidden" in
  let slots = R.Struct (pair_tid, [R.Word Z.zero; R.Word Z.one]) in
  let tests = [
    require "storage-clean" (R.no_closure lookup [] clean = Ok ());
    require "storage-closure" (R.no_closure lookup [] boxed = Error R.Storage_closure);
    require "storage-tail" (R.no_closure lookup [] tailed = Error R.Storage_closure);
    require "storage-hidden" (R.no_closure lookup [] hidden = Error R.Storage_closure);
    require "storage-cycle" (R.no_closure (fun name -> Some (Eterm.KGlobal name)) []
      (Eterm.KGlobal "loop") = Error R.Storage_closure);
    require "storage-slots" (R.storage slots = Ok ["field0"; "field1"]);
    require "storage-gap" (R.storage (R.Struct (pair_tid, [R.Word Z.one])) = Error R.Storage_slot);
    require "storage-nat" (R.storage (R.Struct (pair_tid, [R.Nat Z.zero])) = Error R.Storage_shape);
    require "effect-slot" (E.effect 1 (R.Tag (R.eff_tid, 2, [R.Word Z.one])) = Error E.Unknown_slot);
  ] in
  let* () = List.fold_left (fun result test -> let* () = result in test) (Ok ()) tests in
  let kclos = leak (R.no_closure lookup [] boxed) + leak (R.no_closure lookup [] hidden) in
  let ktail = leak (R.no_closure lookup [] tailed) in
  let fields = Result.fold ~ok:List.length ~error:(fun _ -> 0) (R.storage slots) in
  Printf.printf "STORAGE-NOCLOS kclos=%d ktail=%d fields=%d cases=%d OK\n"
    kclos ktail fields (List.length tests); Ok ()

let () =
  let result = match Array.to_list Sys.argv with
    | [_; "constructors"] -> constructors ()
    | [_; "words"] -> words ()
    | [_; "storage"] -> storage ()
    | [_; "layout"] -> print_string (Assay_abi.Layout.print ~contract:"Q\"\\\n" ["a\t"; "b"]); Ok ()
    | [] | _ :: _ -> Error "usage: emit_cases constructors|words|storage|layout" in
  Result.fold ~ok:Fun.id ~error:(fun name -> prerr_endline ("EMIT-CASES FAIL " ^ name); exit 1) result
