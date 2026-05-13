open MiniLang.MiniImp;;
open MiniLang.MiniRISC;;
open MiniLang.DataFlow_DV;;
open MiniLang.CodeGen;;

type print_list = int list [@@deriving show];;
type register_list = register list [@@deriving show];;

let brop_formatted (brop: brop) =
  match brop with
  | Add -> "add";
  | Sub -> "sub";
  | Mult -> "mult";
  | Less -> "less";
  | And -> "and";;

let biop_formatted (biop: biop) =
  match biop with
  | AddI -> "addI";
  | SubI -> "subI";
  | MultI -> "multI";
  | AndI -> "andI";;

let urop_formatted (urop: urop) =
  match urop with
  | Not -> "not";
  | Copy -> "copy";;

let comm_formatted (comm: comm) =
  match comm with
  | Nop -> "nop"
  | Brop(brop, Reg(r1), Reg(r2), Reg(r3)) -> Printf.sprintf "%s %s %s => %s" (brop_formatted brop) r1 r2 r3
  | Biop(biop, Reg(r1), n, Reg(r2)) -> Printf.sprintf "%s %s %d => %s" (biop_formatted biop) r1 n r2
  | Urop(urop, Reg(r1), Reg(r2)) -> Printf.sprintf "%s %s => %s" (urop_formatted urop) r1 r2
  | Load(Reg(r1), Reg(r2)) -> Printf.sprintf "load %s => %s" r1 r2
  | LoadI(n, Reg(r)) -> Printf.sprintf "loadI %d => %s" n r
  | Store(Reg(r1), Reg(r2)) -> Printf.sprintf "store %s => %s" r1 r2
  | Jump(Lab(l)) -> Printf.sprintf "jump %s" l
  | CJump(Reg(r), Lab(l1), Lab(l2)) -> Printf.sprintf "cjump %s %s %s" r l1 l2;;

let write_to_file (output: out_channel) (blocks: comm list MapLabel.t) =
  let max_length_lab = MapLabel.fold (
      fun (Lab(l)) _ acc -> if String.length l > acc then String.length l else acc
    ) blocks 0 in
  MapLabel.iter (
    fun (Lab(lab)) list -> (
        match list with
        | [] -> failwith "Impossible to reach"
        | x :: xs -> (
            Printf.fprintf output "%*s: %s\n" max_length_lab lab (comm_formatted x);
            List.iter (
              fun (y: comm) -> (
                  let s = comm_formatted y in
                  Printf.fprintf output "  %*s\n" (max_length_lab + String.length s) (comm_formatted y);
                )
            ) xs;
          )
      )
  ) blocks;;

if Array.length Sys.argv < 3 then failwith "Run with '<source_file> <output_file> <regs_num> <?--optimize> <?--undefined>'" else (
  let in_file = open_in Sys.argv.(1) in
  let out_file = open_out Sys.argv.(2) in
  let n_regs = int_of_string Sys.argv.(3) in
  if n_regs < 4 then failwith "Number of registers must be >= 4";
  let has_optimize_flag = Array.exists (fun arg -> arg = "--optimize") Sys.argv in
  let has_undefined_flag = Array.exists (fun arg -> arg = "--undefined") Sys.argv in
  let lexbuf = Lexing.from_channel in_file in
  let Main(in_var, out_var, program) = MiniLang.MiniImpParser.prg MiniLang.MiniImpScanner.read lexbuf in
  let (nodes_m, in_edges, out_edges, start, ends) = build_miniimp_cfg program in
  let nodes_r = construct_risc_cfg nodes_m in_var out_var in
  if has_undefined_flag && not (is_safe nodes_m in_edges start ends in_var out_var) then failwith "Undefined variable found";
  let nodes_r = if has_optimize_flag then merge_reg nodes_r out_edges ends else nodes_r in
  let nodes_red = reduce_reg nodes_r n_regs start ends in
  let nodes, _start_label = risc_cfg_to_code nodes_red out_edges start in
  write_to_file out_file nodes;
  close_out out_file;
);;