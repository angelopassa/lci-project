open MiniLang.MiniImp;;

let () =
  if Array.length Sys.argv != 3 then
    failwith "Run with '<MiniImp-program> <input-number>";
  let in_file = open_in Sys.argv.(1) in
  let lexbuf = Lexing.from_channel in_file in
  let program = (MiniLang.MiniImpParser.prg MiniLang.MiniImpScanner.read lexbuf) in
  let num = int_of_string Sys.argv.(2) in
  print_int (eval_p program num);
  print_newline ();