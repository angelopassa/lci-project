open Cfg;;
open MiniImp;;

module StringSet = Set.Make(String);;

let rec compute_def_max_block (l: miniimp_cfg list) =
  match l with
  | [] -> StringSet.empty
  | x :: xs -> (
      match x with
      | Skip -> compute_def_max_block xs
      | Guard(_) -> compute_def_max_block xs
      | Assign(x, _) -> StringSet.add x (compute_def_max_block xs)
    );;

let compute_top_def (nodes: miniimp_cfg node MapInt.t) (in_var: variable) =
  MapInt.fold (fun _ (Block(l)) set -> StringSet.union (compute_def_max_block l) set) nodes (StringSet.singleton in_var);;

let compute_reaching_def (nodes: miniimp_cfg node MapInt.t) (start: int) (in_edges: int list MapInt.t) (in_var: variable) =
  let defined = MapInt.map (fun (Block(l)) -> compute_def_max_block l) nodes in
  let top = compute_top_def nodes in_var in
  let def_in = MapInt.map (fun _ -> top) nodes in
  let def_out = MapInt.map (fun _ -> top) nodes in
  let rec fixpoint def_in def_out =
    let new_def_in = MapInt.mapi (
        fun i _ -> if i = start then StringSet.singleton in_var else (
            MapInt.fold (fun _ x acc -> StringSet.inter x acc) (
              MapInt.filter (fun j _ -> List.mem j (match MapInt.find_opt i in_edges with | None -> [] | Some(v) -> v)) def_out
            ) top
          )
      ) def_in in
    let new_def_out = MapInt.mapi (
        fun i _ -> StringSet.union (MapInt.find i new_def_in) (MapInt.find i defined)
      ) def_out in
    if (MapInt.equal (fun x y -> StringSet.equal x y) def_in new_def_in) && (MapInt.equal (fun x y -> StringSet.equal x y) def_out new_def_out)
    then (new_def_in, new_def_out)
    else fixpoint new_def_in new_def_out
  in
  fixpoint def_in def_out;;

let is_safe (nodes: miniimp_cfg node MapInt.t) (in_edges: int list MapInt.t) (start: int) (ends: int) (in_var: variable) (out_var: variable) =
  let def_in, _ = compute_reaching_def nodes start in_edges in_var in
  let rec is_safe_num n def_in =
    match n with
    | Var(x) -> StringSet.mem x def_in
    | Number(_) -> true
    | Plus(n1, n2) | Minus(n1, n2) | Times(n1, n2) -> is_safe_num n1 def_in && is_safe_num n2 def_in
  in
  let rec is_safe_guard b def_in =
    match b with
    | True | False -> true
    | And(b1, b2) -> is_safe_guard b1 def_in && is_safe_guard b2 def_in
    | Not(bo) -> is_safe_guard bo def_in
    | LessThan(n1, n2) -> is_safe_num n1 def_in && is_safe_num n2 def_in
  in
  let rec is_safe_block i (l: miniimp_cfg list) def_in =
    match l with
    | [] -> if i = ends then StringSet.mem out_var def_in else true
    | x :: xs -> (
        match x with
        | Skip -> is_safe_block i xs def_in
        | Guard(b) -> is_safe_guard b def_in && is_safe_block i xs def_in
        | Assign(v, n) -> is_safe_num n def_in && is_safe_block i xs (StringSet.add v def_in)
      )
  in
  MapInt.fold (fun i (Block(l)) acc -> is_safe_block i l (MapInt.find i def_in) && acc) nodes true;;