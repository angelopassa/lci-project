open MiniTyFunLib.MiniTyFun;;

let () =
  if Array.length Sys.argv != 3 then
    failwith "Run with '<MiniTyFun-program> <input-number>";
  let in_file = open_in Sys.argv.(1) in
  let lexbuf = Lexing.from_channel in_file in
  let program = (MiniTyFunLib.MiniTyFunParser.initial MiniTyFunLib.MiniTyFunScanner.read lexbuf) in
  let num = int_of_string Sys.argv.(2) in
  print_int (eval program num);
  print_newline ();