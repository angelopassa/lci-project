type variable = string;;

type bop = Plus | Minus | Times | LessThan | And;;

type tau = TInt | TBool | Arrow of tau * tau;;

module Gamma = Map.Make(String);;

type term =
    Int of int
  | Bool of bool
  | Var of string
  | Fun of variable * tau * term
  | App of term * term
  | Bop of term * term * bop
  | Not of term
  | IfThenElse of term * term * term
  | Let of variable * term * term
  | LetFun of variable * tau * variable * term * term;;

let type_check_bop tau_1 tau_2 op =
  match op with
  | Plus | Minus | Times -> (
      match (tau_1, tau_2) with
      | (Some(TInt), Some(TInt)) -> Some(TInt)
      | (_, _) -> None
    )
  | And -> (
      match (tau_1, tau_2) with
      | (Some(TBool), Some(TBool)) -> Some(TBool)
      | (_, _) -> None
    )
  | LessThan -> (
      match (tau_1, tau_2) with
      | (Some(TInt), Some(TInt)) -> Some(TBool)
      | (_, _) -> None
    );;

let rec type_check t context =
  match t with
  | Int(_) -> Some(TInt)
  | Bool(_) -> Some(TBool)
  | Var(v) -> Gamma.find_opt v context
  | Fun(x, x_tau, t) -> (
      match type_check t (Gamma.add x x_tau context) with
      | Some(tau_t) -> Some(Arrow(x_tau, tau_t))
      | None -> None
    )
  | App(t1, t2) -> (
      match (type_check t1 context, type_check t2 context) with
      | (Some(Arrow(tau_1, tau_2)), Some(tau_3)) when tau_1 = tau_3 -> Some(tau_2)
      | (_, _) -> None
    )
  | Bop(t1, t2, op) -> type_check_bop (type_check t1 context) (type_check t2 context) op
  | Not(t) -> (
      match type_check t context with
      | Some(TBool) as t -> t
      | _ -> None
    )
  | IfThenElse(t1, t2, t3) -> (
      match (type_check t1 context, type_check t2 context, type_check t3 context) with
      | (Some(TBool), Some(tau_2), Some(tau_3)) when tau_2 = tau_3 -> Some(tau_2)
      | (_, _, _) -> None
    )
  | Let(x, t1, t2) -> (
      match type_check t1 context with
      | Some(tau_1) -> type_check t2 (Gamma.add x tau_1 context)
      | _ -> None
    )
  | LetFun(f, tau_fun, x, t1, t2) -> (
      match (tau_fun) with
      | Arrow(tau_x, tau_r) as fun_type -> (
          match type_check t1 (Gamma.add x tau_x (Gamma.add f fun_type context)) with
          | Some(tau_ret) -> if tau_r = tau_ret then type_check t2 (Gamma.add f fun_type context) else None
          | _ -> None
        )
      | _ -> None
    );;

let get_type t = type_check t Gamma.empty;;

let map_bop (bop: bop) : MiniFunLib.MiniFun.bop =
  match bop with
  | Plus -> Plus
  | Minus -> Minus
  | Times -> Times
  | And -> And
  | LessThan -> LessThan;;

let rec untyped_fun (t: term) : MiniFunLib.MiniFun.term =
  match t with
  | Fun(v, _, term) -> Fun(v, untyped_fun term)
  | LetFun(v1, _, v2, t1, t2) -> LetFun(v1, v2, untyped_fun t1, untyped_fun t2)
  | IfThenElse(b, t1, t2) -> IfThenElse(untyped_fun b, untyped_fun t1, untyped_fun t2)
  | Let(v, t1, t2) -> Let(v, untyped_fun t1, untyped_fun t2)
  | App(t1, t2) -> App(untyped_fun t1, untyped_fun t2)
  | Bop(t1, t2, bop) -> Bop(untyped_fun t1, untyped_fun t2, map_bop bop)
  | Not(t) -> Not(untyped_fun t)
  | Int(v) -> Int(v)
  | Bool(v) -> Bool(v)
  | Var(v) -> Var(v);;

let eval t (n: int) = match get_type t with
  | Some(Arrow(TInt, TInt)) -> (
      match MiniFunLib.MiniFun.eval (untyped_fun t) (Int(n)) with
      | MiniFunLib.MiniFun.Int(v) -> v
      | _ -> failwith "Wrong return type"
    )
  | None -> failwith "Typechecker failed"
  | _ -> failwith "The program must be a function from integers to integers";;