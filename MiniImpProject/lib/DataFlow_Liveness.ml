open Cfg;;
open MiniRISC;;

let rec compute_used_max_block (l: scomm list) =
  match l with
  | [] -> RegSet.empty
  | x :: xs -> (
      let (used, def) = (
        match x with
        | Nop -> (RegSet.empty, RegSet.empty)
        | Brop(_, r1, r2, r3) -> (RegSet.of_list ([r1; r2]), RegSet.singleton r3)
        | Biop(_, r1, _, r2) -> (RegSet.singleton r1, RegSet.singleton r2)
        | Urop(_, r1, r2) -> (RegSet.singleton r1, RegSet.singleton r2)
        | Load(r1, r2) -> (RegSet.singleton r1, RegSet.singleton r2)
        | LoadI(_, r) -> (RegSet.empty, RegSet.singleton r)
        | Store(r1, r2) -> (RegSet.of_list [r1; r2], RegSet.empty)
      ) in RegSet.union (RegSet.diff (compute_used_max_block xs) def) used
    );;

let rec compute_def_max_block (l: scomm list) =
  match l with
  | [] -> RegSet.empty
  | x :: xs -> (
      match x with
      | Nop -> compute_def_max_block xs
      | Brop(_, _, _, r) -> RegSet.add r (compute_def_max_block xs)
      | Biop(_, _, _, r) -> RegSet.add r (compute_def_max_block xs)
      | Urop(_, _, r) -> RegSet.add r (compute_def_max_block xs)
      | Load(_, r) -> RegSet.add r (compute_def_max_block xs)
      | LoadI(_, r) -> RegSet.add r (compute_def_max_block xs)
      | Store(_, _) -> compute_def_max_block xs
    );;

let compute_liveness (nodes: scomm node MapInt.t) (out_edges: int list MapInt.t) (ends: int) =
  let used = MapInt.map (fun (Block(l)) -> compute_used_max_block l) nodes in
  let defined = MapInt.map (fun (Block(l)) -> compute_def_max_block l) nodes in
  let (live_in: RegSet.t MapInt.t) = used in
  let (live_out: RegSet.t MapInt.t) = MapInt.mapi (
      fun x _ -> if x = ends then RegSet.singleton (Reg("out")) else RegSet.empty
    ) nodes in
  let rec fixpoint live_in live_out =
    let new_live_out = MapInt.mapi (
        fun x _ -> (
            if x = ends then RegSet.singleton (Reg("out")) else
              MapInt.fold (fun _ y acc -> RegSet.union y acc) (
                MapInt.filter (fun i _ -> List.mem i (match MapInt.find_opt x out_edges with | None -> [] | Some(v) -> v)) live_in
              ) RegSet.empty
          )
      ) live_out in
    let new_live_in = MapInt.mapi (
        fun x _ -> (
            RegSet.union (MapInt.find x used) (RegSet.diff (MapInt.find x new_live_out) (MapInt.find x defined))
          )
      ) live_in in
    if (MapInt.equal (fun x y -> RegSet.equal x y) live_in new_live_in) && (MapInt.equal (fun x y -> RegSet.equal x y) live_out new_live_out)
    then (new_live_in, new_live_out)
    else fixpoint new_live_in new_live_out
  in fixpoint live_in live_out;;