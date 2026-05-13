open Cfg;;

type variable = string [@@deriving show];;

type n_value =
    Var of variable
  | Number of int
  | Plus of n_value * n_value
  | Minus of n_value * n_value
  | Times of n_value * n_value
[@@deriving show];;

type b_value =
    True
  | False
  | And of b_value * b_value
  | Not of b_value
  | LessThan of n_value * n_value
[@@deriving show];;

type command =
    Skip
  | Assign of variable * n_value
  | Sequence of command * command
  | IfThenElse of b_value * command * command
  | While of b_value * command
[@@deriving show];;

type main = Main of variable * variable * command [@@deriving show];;

let rec eval_v abt mem =
  match abt with
  | Var(x) -> (
      match MapString.find_opt x mem with
      | Some(v) -> v
      | None -> failwith "Variable not bounded in memory"
    )
  | Number(n) -> n
  | Plus(n1, n2) -> (eval_v n1 mem) + (eval_v n2 mem)
  | Minus(n1, n2) -> (eval_v n1 mem) - (eval_v n2 mem)
  | Times(n1, n2) -> (eval_v n1 mem) * (eval_v n2 mem);;

let rec eval_b abt mem =
  match abt with
  | True -> true
  | False -> false
  | And(b1, b2) -> (eval_b b1 mem) && (eval_b b2 mem)
  | Not(b) -> not (eval_b b mem)
  | LessThan(n1, n2) -> (eval_v n1 mem) < (eval_v n2 mem);;

let rec eval_c abt mem =
  match abt with
  | Skip -> mem
  | Assign(var, value) -> MapString.add var (eval_v value mem) mem
  | Sequence(c1, c2) -> eval_c c2 (eval_c c1 mem)
  | IfThenElse(b, c1, c2) -> if eval_b b mem then eval_c c1 mem else eval_c c2 mem
  | While(b, c) -> if eval_b b mem then eval_c (Sequence(c, abt)) mem else mem;;

let eval_p (Main(input_var, out_var, c)) input_val =
  match MapString.find_opt out_var (eval_c c (MapString.add input_var input_val MapString.empty)) with
  | Some(v) -> v
  | None -> failwith "Output variable not bounded in memory";;

type miniimp_cfg = 
    Guard of b_value 
  | Assign of variable * n_value 
  | Skip
[@@deriving show];;

let count_node = ref 0;;

let next_node () =
  count_node := !count_node + 1;
  !count_node;;

let update_nodes (nodes: miniimp_cfg node MapInt.t) (key: int) (value: miniimp_cfg) =
  let f y =
    match (value, y) with
    | (_, None) -> Some(Block([value]))
    | (Skip, Some(Block(_ :: _))) -> y
    | (_, Some(Block([]))) -> Some(Block([value]))
    | (_, Some(Block(Skip :: xs))) -> Some(Block(value :: xs))
    | (_, Some(Block(x :: xs))) -> Some(Block(value :: x :: xs))
  in MapInt.update key f nodes;;

let rec miniimp_cfg (ast: command) (nodes: miniimp_cfg node MapInt.t) (in_edges: int list MapInt.t) (out_edges: int list MapInt.t) (current_node: int) =
  let (current_node, in_edges, out_edges) = (
    if ast != Skip && (MapInt.mem current_node in_edges) then (
      let n = next_node () in
      (n, MapInt.add_to_list current_node n in_edges, MapInt.add n [current_node] out_edges)
    ) else (current_node, in_edges, out_edges)
  ) in
  match ast with
  | Skip -> update_nodes nodes current_node Skip, in_edges, out_edges, current_node, current_node
  | Assign(var, value) -> update_nodes nodes current_node (Assign(var, value)), in_edges, out_edges, current_node, current_node
  | Sequence(c1, c2) -> (
      let (nodes_c2, in_edges_c2, out_edges_c2, start_c2, end_c2) = miniimp_cfg c2 nodes in_edges out_edges current_node in
      let (nodes_c1, in_edges_c1, out_edges_c1, start_c1, _) = miniimp_cfg c1 nodes_c2 in_edges_c2 out_edges_c2 start_c2 in
      nodes_c1, in_edges_c1, out_edges_c1, start_c1, end_c2
    )
  | IfThenElse(b, c1, c2) -> (
      let guard_id = next_node () in
      let c1_b = next_node () in
      let c2_b = next_node () in
      let nodes_b = MapInt.add c1_b (Block([Skip])) (MapInt.add c2_b (Block([Skip])) (MapInt.add guard_id (Block([Guard(b)])) nodes)) in
      let (nodes_c1, in_edges_c1, out_edges_c1, start_c1, end_c1) = miniimp_cfg c1 nodes_b in_edges out_edges c1_b in
      let (nodes_c2, in_edges_c2, out_edges_c2, start_c2, end_c2) = miniimp_cfg c2 nodes_c1 in_edges_c1 out_edges_c1 c2_b in
      let new_in_edges = MapInt.add_to_list start_c1 guard_id (MapInt.add_to_list start_c2 guard_id (MapInt.add_to_list current_node end_c1 (MapInt.add_to_list current_node end_c2 in_edges_c2))) in
      let new_out_edges = MapInt.add guard_id ([start_c1; start_c2]) (MapInt.add_to_list end_c1 current_node (MapInt.add_to_list end_c2 current_node out_edges_c2)) in
      nodes_c2, new_in_edges, new_out_edges, guard_id, current_node
    )
  | While(b, c) -> (
      let guard_id = next_node () in
      let c_b = next_node () in
      let new_nodes = MapInt.add c_b (Block([Skip])) (MapInt.add guard_id (Block([Guard(b)])) nodes) in
      let (new_nodes_2, in_edges_c, out_edges_c, start_c, end_c) = miniimp_cfg c new_nodes in_edges out_edges c_b in
      let new_in_edges = MapInt.add_to_list start_c guard_id (MapInt.add_to_list current_node guard_id (MapInt.add_to_list guard_id end_c in_edges_c)) in
      let new_out_edges = MapInt.add guard_id ([start_c; current_node]) (MapInt.add_to_list end_c guard_id out_edges_c) in
      new_nodes_2, new_in_edges, new_out_edges, guard_id, current_node
    );;

let build_miniimp_cfg ast =
  let (nodes, in_edges, out_edges, start, ends) = miniimp_cfg ast (MapInt.add 0 (Block([Skip])) MapInt.empty) MapInt.empty MapInt.empty 0 in
  if MapInt.mem start in_edges then (
    let n = next_node () in
    (MapInt.add n (Block[Skip]) nodes, MapInt.add_to_list start n in_edges, MapInt.add n [start] out_edges, n, ends)
  ) else (nodes, in_edges, out_edges, start, ends);;