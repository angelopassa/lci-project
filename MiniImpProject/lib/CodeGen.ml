open Cfg;;
open MiniRISC;;
open DataFlow_Liveness;;

let count_reg = ref 0;;

let next_reg () =
  count_reg := !count_reg + 1;
  !count_reg;;

let compute_conflicts (nodes: scomm node MapInt.t) (out_edges: int list MapInt.t) (ends: int) =
  let _, live_out = compute_liveness nodes out_edges ends in
  let rec live_max_block (l: scomm list) (live_out: RegSet.t) cjump =
    match l with
    | [] -> live_out, MapReg.empty
    | x :: xs -> (
        let live_out, coll = (
          match (xs, cjump) with
          | [], true -> (
              match x with
              | Brop(_, _, _, r) | Biop(_, _, _, r) | Urop(_, _, r) | LoadI(_, r) -> live_max_block [Nop] (RegSet.add r live_out) false 
              | _ -> failwith "Impossible to reach"
            )
          | _, _ -> live_max_block xs live_out cjump
        ) in
        let live_in = (
          match x with
          | Nop -> live_out
          | Brop(_, r1, r2, r3) ->  RegSet.union (RegSet.of_list [r1; r2]) (RegSet.diff live_out (RegSet.singleton r3))
          | Biop(_, r1, _, r2) | Urop(_, r1, r2) | Load(r1, r2) -> RegSet.add r1 (RegSet.diff live_out (RegSet.singleton r2))
          | LoadI(_, r) -> RegSet.add r live_out
          | Store(r1, r2) -> RegSet.union (RegSet.of_list [r1; r2]) live_out
        )
        in
        let new_map = RegSet.fold (
            fun x coll -> (
                MapReg.update x (
                  fun y -> match y with
                    | Some(v) -> Some(RegSet.union v (RegSet.remove x live_in))
                    | None -> Some(RegSet.remove x live_in)
                ) coll
              )
          ) live_in coll in
        live_in, new_map
      )
  in
  MapInt.fold (
    fun i x map_reg -> (
        let _, map = (
          match (MapInt.find_opt i out_edges, MapInt.find i nodes) with
          | Some([_; _]), Block(l) -> live_max_block l x true
          | _, Block(l) -> live_max_block l x false
        ) in
        MapReg.union (fun _ x y -> Some(RegSet.union x y)) map map_reg
      )
  ) live_out MapReg.empty;;

let merge_reg (nodes: scomm node MapInt.t) (out_edges: int list MapInt.t) (ends: int) =
  let map_coll = compute_conflicts nodes out_edges ends in
  let map_coll = if MapReg.mem (Reg("in")) map_coll then map_coll else MapReg.add (Reg("in")) RegSet.empty map_coll in
  let map_coll = if MapReg.mem (Reg("out")) map_coll then map_coll else MapReg.add (Reg("out")) RegSet.empty map_coll in
  let rec merge (map: RegSet.t MapReg.t) (map_v_to_p: register MapReg.t) =
    if MapReg.is_empty map then map, map_v_to_p else (
      let r, next = (
        if MapReg.mem (Reg("in")) map then Reg("in"), Reg("in") else (
          if MapReg.mem (Reg("out")) map then Reg("out"), Reg("out") else (
            let r, _ = MapReg.choose map in r, Reg(String.cat "r" (string_of_int (next_reg ())))
          )
        )
      ) in
      let new_map, set = MapReg.fold (
          fun t s (acc1, acc2) -> (
              if not (RegSet.is_empty (RegSet.inter s acc2)) || (r = Reg("in") && t = Reg("out")) then acc1, acc2 else (MapReg.add t next acc1, RegSet.add t acc2)
            )
        ) map (MapReg.add r next map_v_to_p, RegSet.singleton r) in
      merge (MapReg.filter (fun r _ -> not (RegSet.mem r set)) map) new_map
    )
  in
  let _, map_v_to_p = merge map_coll MapReg.empty in
  MapInt.map (
    fun (Block(l)) -> (
        Block((
            let f, last_instr = (List.fold_left (
                fun (func, last_instr) x -> (
                    let last_instr, current_instr = (
                      match x with
                      | Nop -> last_instr, Some(Nop)
                      | Brop(bop, r1, r2, r3) -> (
                          let r3 = (
                            match MapReg.find_opt r3 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          last_instr, Some(Brop(bop, MapReg.find r1 map_v_to_p, MapReg.find r2 map_v_to_p, r3))
                        )
                      | Biop(bop, r1, n, r2) -> (
                          let r2 = (
                            match MapReg.find_opt r2 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          last_instr, Some(Biop(bop, MapReg.find r1 map_v_to_p, n, r2))
                        )
                      | Urop(Not, r1, r2) -> (
                          let r2 = (
                            match MapReg.find_opt r2 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          last_instr, Some(Urop(Not, MapReg.find r1 map_v_to_p, r2))
                        )
                      | Urop(Copy, r1, r2) -> (
                          let r2 = (
                            match MapReg.find_opt r2 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          let r1 = (
                            match MapReg.find_opt r1 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          if r1 = r2 then last_instr, None else (
                            match last_instr with
                            | Some(i) -> (
                                match i with
                                | Biop(_, _, _, r) | Brop(_, _, _, r) | LoadI(_, r) | Urop(Not, _, r) when r = r1 -> (
                                    (match i with
                                     | Biop(biop, rb1, n, _) -> Some(Biop(biop, rb1, n, r2))
                                     | Brop(brop, rb1, rb2, _) -> Some(Brop(brop, rb1, rb2, r2))
                                     | LoadI(n, _) -> Some(LoadI(n, r2))
                                     | Urop(Not, rb1, _) -> Some(Urop(Not, rb1, r2))
                                     | _ -> failwith "Impossible to reach"), None
                                  )
                                | _ -> last_instr, Some(Urop(Copy, r1, r2))
                              )
                            | None -> last_instr, Some(Urop(Copy, r1, r2))
                          )
                        )
                      | Load(r1, r2) -> (
                          let r2 = (
                            match MapReg.find_opt r2 map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          last_instr, Some(Load(MapReg.find r1 map_v_to_p, r2))
                        )
                      | LoadI(n, r) -> (
                          let r = (
                            match MapReg.find_opt r map_v_to_p with
                            | None -> let _, r = MapReg.choose map_v_to_p in r
                            | Some(v) -> v
                          ) in
                          last_instr, Some(LoadI(n, r))
                        )
                      | Store(r1, r2) -> last_instr, Some(Store(MapReg.find r1 map_v_to_p, MapReg.find r2 map_v_to_p))
                    ) in match last_instr with
                    | None -> func, current_instr
                    | Some(i) -> (fun y -> func (i :: y)), current_instr
                  )
              ) ((fun x -> x), None) l) in (
              match last_instr with
              | None -> f []
              | Some(i) -> f [i]
            )
          ))
      )
  ) nodes;;

let plus_one (r: register) (map: int MapReg.t) =
  MapReg.update r (
    fun x -> match x with
      | Some(v) -> Some(v + 1)
      | None -> Some(1)
  ) map;;

let compute_freq (nodes: scomm node MapInt.t) =
  MapInt.fold (
    fun _ (Block(l)) acc -> (
        List.fold_left (
          fun acc x -> (
              match x with
              | Brop(_, r1, r2, r3) -> plus_one r1 (plus_one r2 (plus_one r3 acc))
              | Nop -> acc
              | Biop(_, r1, _, r2) | Urop(_, r1, r2) | Load(r1, r2) | Store(r1, r2) -> plus_one r1 (plus_one r2 acc)
              | LoadI(_, r) -> plus_one r acc
            ) 
        ) acc l
      )
  ) nodes MapReg.empty;;

let reduce_reg (nodes: scomm node MapInt.t) (max_n: int) (start: int) (ends: int) =
  let rec create_addr (map: int MapReg.t) (inv_map: RegSet.t MapInt.t) (addr: int) =
    if (MapReg.cardinal map) == (max_n - 2)
    then MapReg.empty, map
    else (
      let n, set = MapInt.min_binding inv_map in
      let reg = RegSet.choose set in
      let new_map, new_freq = create_addr (MapReg.remove reg map) (
          MapInt.update n (fun set -> (
                match set with
                | Some(v) -> let new_set = RegSet.remove reg v in if RegSet.is_empty new_set then None else Some(new_set)
                | None -> failwith "Impossible to reach"
              )) inv_map
        ) (addr + 1) in
      MapReg.add reg addr new_map, new_freq
    )
  in
  let freqs = compute_freq nodes in
  if (MapReg.cardinal freqs) <= max_n then nodes else (
    let inverted_freq = MapReg.fold (fun reg f acc -> (
          MapInt.update f (fun set -> (
                match set with
                | Some(v) -> Some(RegSet.add reg v)
                | None -> Some(RegSet.singleton reg)
              )) acc
        )) freqs MapInt.empty in
    let map_addr, freqs = create_addr freqs inverted_freq 0 in
    let rec names_pool (n: int) =
      match n with
      | 0 -> RegSet.empty
      | _ -> RegSet.add (Reg(String.cat "r" (string_of_int n))) (names_pool (n - 1))
    in
    let renames, _ = MapReg.fold (
        fun reg _ (acc, pool) -> (
            match reg with
            | Reg("in") | Reg("out") -> MapReg.add reg reg acc, pool
            | _ -> (
                let r = RegSet.choose pool in
                MapReg.add reg r acc, RegSet.remove r pool
              )
          )
      ) freqs (MapReg.empty, (
        let pool = names_pool (max_n - 4) in
        let pool = if not (MapReg.mem (Reg("in")) freqs) then RegSet.add (Reg("in")) pool else pool in
        if not (MapReg.mem (Reg("out")) freqs) then RegSet.add (Reg("out")) pool else pool
      )) in
    MapInt.mapi (
      fun i (Block(l)) -> (
          Block(
            let m = (List.fold_left (
                fun acc x -> (
                    match x with
                    | Nop -> fun y -> acc (Nop :: y)
                    | Brop(bop, r1, r2, r3) -> (
                        let load_r1, load_r2, load_r3 = MapReg.mem r1 map_addr, MapReg.mem r2 map_addr, MapReg.mem r3 map_addr in
                        fun y -> acc (
                            let store = if load_r3 then LoadI(MapReg.find r3 map_addr, Reg("ra")) :: Store(Reg("rb"), Reg("ra")) :: y else y in
                            let op = Brop(bop, (if load_r1 then Reg("ra") else MapReg.find r1 renames), (if load_r2 then Reg("rb") else MapReg.find r2 renames), if load_r3 then Reg("rb") else MapReg.find r3 renames) :: store in
                            let second_op = if load_r2 then LoadI(MapReg.find r2 map_addr, Reg("rb")) :: Load(Reg("rb"), Reg("rb")) :: op else op in
                            let first_op = if load_r1 then LoadI(MapReg.find r1 map_addr, Reg("ra")) :: Load(Reg("ra"), Reg("ra")) :: second_op else second_op in
                            first_op
                          )
                      )
                    | Biop(bop, r1, n, r2) -> (
                        let load_r1, load_r2 = MapReg.mem r1 map_addr, MapReg.mem r2 map_addr in
                        fun y -> acc (
                            let store = if load_r2 then LoadI(MapReg.find r2 map_addr, Reg("ra")) :: Store(Reg("rb"), Reg("ra")) :: y else y in
                            let op = Biop(bop, (if load_r1 then Reg("ra") else MapReg.find r1 renames), n, if load_r2 then Reg("rb") else MapReg.find r2 renames) :: store in
                            let first_op = if load_r1 then LoadI(MapReg.find r1 map_addr, Reg("ra")) :: Load(Reg("ra"), Reg("ra")) :: op else op in
                            first_op
                          )
                      )
                    | Urop(op, r1, r2) -> (
                        let load_r1, load_r2 = MapReg.mem r1 map_addr, MapReg.mem r2 map_addr in
                        fun y -> acc (
                            let store = if load_r2 then LoadI(MapReg.find r2 map_addr, Reg("ra")) :: Store(Reg("rb"), Reg("ra")) :: y else y in
                            let op = Urop(op, (if load_r1 then Reg("ra") else MapReg.find r1 renames), if load_r2 then Reg("rb") else MapReg.find r2 renames) :: store in
                            let first_op = if load_r1 then LoadI(MapReg.find r1 map_addr, Reg("ra")) :: Load(Reg("ra"), Reg("ra")) :: op else op in
                            first_op
                          )
                      )
                    | Load(r1, r2) -> (
                        let load_r1, load_r2 = MapReg.mem r1 map_addr, MapReg.mem r2 map_addr in
                        fun y -> acc (
                            let store = if load_r2 then LoadI(MapReg.find r2 map_addr, Reg("ra")) :: Store(Reg("rb"), Reg("ra")) :: y else y in
                            let op = Load((if load_r1 then Reg("ra") else MapReg.find r1 renames), if load_r2 then Reg("rb") else MapReg.find r2 renames) :: store in
                            let first_op = if load_r1 then LoadI(MapReg.find r1 map_addr, Reg("ra")) :: Load(Reg("ra"), Reg("ra")) :: op else op in
                            first_op
                          )
                      )
                    | LoadI(n, r) -> (
                        let load_r = MapReg.mem r map_addr in
                        fun y -> acc (
                            let store = if load_r then LoadI(MapReg.find r map_addr, Reg("ra")) :: Store(Reg("rb"), Reg("ra")) :: y else y in
                            let op = LoadI(n, if load_r then Reg("rb") else MapReg.find r renames) :: store in
                            op
                          )
                      )
                    | Store(r1, r2) -> (
                        let load_r1, load_r2 = MapReg.mem r1 map_addr, MapReg.mem r2 map_addr in
                        fun y -> acc (
                            let op = Load((if load_r1 then Reg("ra") else MapReg.find r1 renames), if load_r2 then Reg("rb") else MapReg.find r2 renames) :: y in
                            let second_op = if load_r2 then LoadI(MapReg.find r2 map_addr, Reg("rb")) :: Load(Reg("rb"), Reg("rb")) :: op else op in
                            let first_op = if load_r1 then LoadI(MapReg.find r1 map_addr, Reg("ra")) :: Load(Reg("ra"), Reg("ra")) :: second_op else second_op in
                            first_op
                          )
                      )
                  )
              ) (fun x -> x) l) (
                if i = ends && MapReg.mem (Reg("out")) map_addr
                then [LoadI(MapReg.find (Reg("out")) map_addr, Reg("ra")); Load(Reg("ra"), Reg("out"))]
                else []
              ) in
            if i = start && MapReg.mem (Reg("in")) map_addr
            then LoadI(MapReg.find (Reg("in")) map_addr, Reg("ra")) :: Store(Reg("in"), Reg("ra")) :: m
            else m)
        )
    ) nodes
  );;