open Cfg;;
open MiniImp;;

type register = Reg of string [@@deriving show];;
type label = Lab of string [@@deriving show];;

module Label = struct
  type t = label
  let compare (Lab x) (Lab y) = compare x y
end

module Register = struct
  type t = register
  let compare (Reg x) (Reg y) = compare x y
end

module MapReg = Map.Make(Register);;
module RegSet = Set.Make(Register);;
module MapLabel = Map.Make(Label);;

type brop = Add | Sub | Mult | And | Less [@@deriving show];;

type biop = AddI | SubI | MultI | AndI [@@deriving show];;

type urop = Not | Copy [@@deriving show];;

type comm =
    Nop 
  | Brop of brop * register * register * register
  | Biop of biop * register * int * register
  | Urop of urop * register * register
  | Load of register * register
  | LoadI of int * register
  | Store of register * register
  | Jump of label
  | CJump of register * label * label
[@@deriving show];;

type scomm =
    Nop
  | Brop of brop * register * register * register
  | Biop of biop * register * int * register
  | Urop of urop * register * register
  | Load of register * register
  | LoadI of int * register
  | Store of register * register
[@@deriving show];;

type jump_type = Single | Double | NoJump;;

let count_reg = ref 0;;

let next_reg () =
  count_reg := !count_reg + 1;
  Reg(String.cat "r" (string_of_int !count_reg));;

let rec bop_translate (bop: n_value) (regs: register MapString.t) f =
  match bop with
  | Plus(bop1, bop2) | Minus(bop1, bop2) | Times(bop1, bop2) -> (
      let res = next_reg () in
      let (new_f, new_regs, reg1, reg2, value) = (
        match (bop1, bop2) with
        | (_, Number(n)) -> (
            let (reg_res1, f1, new_regs_1) = bop_translate bop1 regs f in
            f1, new_regs_1, reg_res1, None, Some(n)    
          )
        | (Number(n), _) when bop != (Minus(bop1, bop2)) -> (
            let (reg_res2, f2, new_regs_2) = bop_translate bop2 regs f in
            f2, new_regs_2, reg_res2, None, Some(n)
          )
        | (_, _) -> (
            let (reg_res1, f1, new_regs) = bop_translate bop1 regs f in
            let (reg_res2, f2, new_regs_2) = bop_translate bop2 new_regs f1 in
            f2, new_regs_2, reg_res1, Some(reg_res2), None
          )
      ) in
      (
        match (reg2, value) with
        | (Some(r2), _) -> (
            match bop with
            | Plus(_, _) -> (res, (fun x -> new_f (Brop(Add, reg1, r2, res) :: x)), new_regs)
            | Minus(_, _) -> (res, (fun x -> new_f (Brop(Sub, reg1, r2, res) :: x)), new_regs)
            | Times(_, _) -> (res, (fun x -> new_f (Brop(Mult, reg1, r2, res) :: x)), new_regs)
            | _ -> failwith "Impossible to reach"
          )
        | (_, Some(v)) -> (
            match bop with
            | Plus(_, _) -> (res, (fun x -> new_f (Biop(AddI, reg1, v, res) :: x)), new_regs)
            | Minus(_, _) -> (res, (fun x -> new_f (Biop(SubI, reg1, v, res) :: x)), new_regs)
            | Times(_, _) -> (res, (fun x -> new_f (Biop(MultI, reg1, v, res) :: x)), new_regs)
            | _ -> failwith "Impossible to reach"
          )
        | (_, _) -> failwith "Impossible to reach"
      )
    )
  | Var(x) -> (
      match MapString.find_opt x regs with
      | None -> (
          let reg_x = next_reg () in
          (reg_x, f, MapString.add x reg_x regs)
        )
      | Some(v) -> (v, f, regs)
    )
  | Number(n) -> let reg = next_reg () in (reg, (fun x -> f (LoadI(n, reg) :: x)), regs);;

let rec bool_translate (bool: b_value) (regs: register MapString.t) f =
  let res = next_reg () in
  match bool with
  | And(b1, b2) -> (
      match (b1, b2) with
      | (v, _) when v = True || v = False -> (
          let (reg_res2, f2, new_regs) = bool_translate b2 regs f in
          (res, (fun x -> f2 (Biop(AndI, reg_res2, (if v = True then 1 else 0), res) :: x)), new_regs)
        )
      | (_, v) when v = True || v = False -> (
          let (reg_res1, f1, new_regs) = bool_translate b1 regs f in
          (res, (fun x -> f1 (Biop(AndI, reg_res1, (if v = True then 1 else 0), res) :: x)), new_regs)
        )
      | (_, _) -> (
          let (reg_res1, f1, new_regs) = bool_translate b1 regs f in
          let (reg_res2, f2, new_regs_2) = bool_translate b2 new_regs f1 in
          (res, (fun x -> f2 (Brop(And, reg_res1, reg_res2, res) :: x)), new_regs_2)
        )
    )
  | Not(b) -> (
      let (reg_res_b, f_b, new_regs) = bool_translate b regs f in
      (res, (fun x -> f_b (Urop(Not, reg_res_b, res) :: x)), new_regs)
    )
  | LessThan(n1, n2) -> (
      let (reg_res1, f1, new_regs) = bop_translate n1 regs f in
      let (reg_res2, f2, new_regs_2) = bop_translate n2 new_regs f1 in
      (res, (fun x -> f2 (Brop(Less, reg_res1, reg_res2, res) :: x)), new_regs_2)
    )
  | True -> (res, (fun x -> f (LoadI(1, res) :: x)), regs)
  | False -> (res, (fun x -> f (LoadI(0, res) :: x)), regs);;

let rec translate_list (l: miniimp_cfg list) (regs: register MapString.t) f =
  match l with
  | [] -> (regs, f)
  | x :: xs -> (
      let (new_regs, new_f) = (match x with
          | Assign(var, value) -> (
              let (res, f_new, new_regs_2) = bop_translate value regs f in
              match MapString.find_opt var new_regs_2 with
              | None -> let reg = next_reg () in (MapString.add var reg new_regs_2, fun z -> f_new (Urop(Copy, res, reg) :: z))
              | Some(v) -> (new_regs_2, fun z -> f_new (Urop(Copy, res, v) :: z))
            )
          | Guard(bool) -> (
              let (_, f_new, new_regs_2) = bool_translate bool regs f in
              (new_regs_2, f_new)
            )
          | Skip -> (regs, fun x -> f (Nop :: x)))
      in
      translate_list xs new_regs new_f
    );;

let construct_risc_cfg (nodes_imp: miniimp_cfg node MapInt.t) (in_var: variable) (out_var: variable) =
  let rec to_risc_cfg (list: (int * miniimp_cfg node) list) (regs: register MapString.t) =
    match list with
    | [] -> MapInt.empty
    | (n, Block(l)) :: xs -> (
        let (new_regs, new_f) = translate_list l regs (fun x -> x) in
        MapInt.add n (Block(new_f [])) (to_risc_cfg xs new_regs)
      )
  in
  to_risc_cfg (MapInt.to_list nodes_imp) (MapString.of_list [(in_var, Reg("in")); (out_var, Reg("out"))]);;

let from_scomm_to_comm (stmt: scomm) : (comm * register) = 
  match stmt with
  | Nop -> (Nop, Reg("nop"))
  | Brop(bop, r1, r2, r3) -> (Brop(bop, r1, r2, r3), r3)
  | Biop(bop, r1, n, r2) -> (Biop(bop, r1, n, r2), r2)
  | Urop(op, r1, r2) -> (Urop(op, r1, r2), r2)
  | Load(r1, r2) -> (Load(r1, r2), r2)
  | LoadI(n, r) -> (LoadI(n, r), r)
  | Store(r1, r2) -> (Store(r1, r2), r1);;

let rec block_to_code (l: scomm list) (jump: jump_type) (labels: label * label) : comm list =
  match l with
  | x :: [] -> (
      let stmt, last_reg = from_scomm_to_comm x in
      match (last_reg, labels, jump) with
      | (r, (l1, l2), Double) -> stmt :: [CJump(r, l1, l2)]
      | (_, (l1, _), Single) -> stmt :: [Jump(l1)]
      | (_, (_, _), NoJump) -> [stmt]
    )
  | x :: xs -> (
      let stmt, _ = from_scomm_to_comm x in
      stmt :: block_to_code xs jump labels
    )
  | _ -> failwith "Impossible to reach";;

let risc_cfg_to_code (nodes_risc: scomm node MapInt.t) (edges_risc: int list MapInt.t) (start: int) =
  let rec node_to_code (list: (int * scomm node) list) =
    match list with
    | [] -> MapLabel.empty
    | (idx, node) :: xs -> (
        let label_of_node = Lab(if idx == start then "main" else String.cat "l" (string_of_int idx)) in
        let code = (
          match (MapInt.find_opt idx edges_risc, node) with
          | (Some([x; y]), Block(l)) -> block_to_code l Double (Lab(String.cat "l" (string_of_int x)), Lab(String.cat "l" (string_of_int y)))
          | (Some([x]),  Block(l)) -> block_to_code l Single (Lab(String.cat "l" (string_of_int x)), Lab(String.cat "l" (string_of_int x)))
          | (None, Block(l)) -> block_to_code l NoJump (Lab("l"), Lab("l"))
          | (_, _) -> failwith "Impossible to reach"
        ) in
        MapLabel.add label_of_node code (node_to_code xs)
      )
  in
  node_to_code (MapInt.to_list nodes_risc), Lab("main");;

let rec run_risc_block (list: comm list) (blocks: comm list MapLabel.t) (regs: int MapReg.t) (mem: int MapInt.t) =
  (
    match list with
    | [] -> (regs, mem)
    | x :: xs -> (
        match x with
        | Nop -> run_risc_block xs blocks regs mem
        | Brop(bop, r1, r2, r3) -> (
            match bop with
            | Add -> run_risc_block xs blocks (MapReg.add r3 ((MapReg.find r1 regs) + (MapReg.find r2 regs)) regs) mem
            | Sub -> run_risc_block xs blocks (MapReg.add r3 ((MapReg.find r1 regs) - (MapReg.find r2 regs)) regs) mem
            | Mult | And -> run_risc_block xs blocks (MapReg.add r3 ((MapReg.find r1 regs) * (MapReg.find r2 regs)) regs) mem
            | Less -> run_risc_block xs blocks (MapReg.add r3 (if (MapReg.find r1 regs) < (MapReg.find r2 regs) then 1 else 0) regs) mem
          )
        | Biop(bop, r1, n, r2) -> (
            match bop with
            | AddI -> run_risc_block xs blocks (MapReg.add r2 ((MapReg.find r1 regs) + n) regs) mem
            | SubI -> run_risc_block xs blocks (MapReg.add r2 ((MapReg.find r1 regs) - n) regs) mem
            | MultI | AndI -> run_risc_block xs blocks (MapReg.add r2 ((MapReg.find r1 regs) * n) regs) mem
          )
        | Urop(op, r1, r2) -> (
            match op with
            | Not -> run_risc_block xs blocks (MapReg.add r2 (1 - (MapReg.find r1 regs)) regs) mem
            | Copy -> run_risc_block xs blocks (MapReg.add r2 (MapReg.find r1 regs) regs) mem
          )
        | Load(r1, r2) -> run_risc_block xs blocks (MapReg.add r2 (MapInt.find (MapReg.find r1 regs) mem) regs) mem
        | LoadI(n, r) -> run_risc_block xs blocks (MapReg.add r n regs) mem
        | Store(r1, r2) -> run_risc_block xs blocks regs (MapInt.add (MapReg.find r2 regs) (MapReg.find r1 regs) mem)
        | Jump(l) -> run_risc_block (MapLabel.find l blocks) blocks regs mem
        | CJump(r, l1, l2) -> if (MapReg.find r regs) == 1 then run_risc_block (MapLabel.find l1 blocks) blocks regs mem else run_risc_block (MapLabel.find l2 blocks) blocks regs mem
      )
  );;

let run_risc (blocks: comm list MapLabel.t) (start_l: label) (in_value: int) =
  let regs, _ = run_risc_block (MapLabel.find start_l blocks) blocks (MapReg.singleton (Reg("in")) in_value) MapInt.empty in
  MapReg.find (Reg("out")) regs;;