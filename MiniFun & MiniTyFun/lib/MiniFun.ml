type variable = string;;

type bop = Plus | Minus | Times | LessThan | And;;

module Rho = Map.Make(String);;

type term =
    Int of int
  | Bool of bool
  | Var of string
  | Fun of variable * term
  | App of term * term
  | Bop of term * term * bop
  | Not of term
  | IfThenElse of term * term * term
  | Let of variable * term * term
  | LetFun of variable * variable * term * term;;

type values = 
    Int of int 
  | Bool of bool 
  | Closure of variable * term * (values Rho.t)
  | RecClosure of variable * variable * term * (values Rho.t);;

let rec eval_bop v1 v2 bop =
  match (v1, v2, bop) with
  | (Int(u1), Int(u2), Plus) -> Int(u1 + u2)
  | (Int(u1), Int(u2), Minus) -> Int(u1 - u2)
  | (Int(u1), Int(u2), Times) -> Int(u1 * u2)
  | (Int(u1), Int(u2), LessThan) -> Bool(u1 < u2)
  | (Bool(u1), Bool(u2), And) -> Bool(u1 && u2)
  | (_, _, _) -> failwith "Operator and values not compatible";;

let rec eval_t (term: term) mem =
  match term with
  | Int(v) -> Int(v)
  | Bool(v) -> Bool(v)
  | Var(x) -> (
      match Rho.find_opt x mem with
      | Some(v) -> v
      | None -> failwith "Variable not bounded in memory"
    )
  | Bop(t1, t2, bop) -> eval_bop (eval_t t1 mem) (eval_t t2 mem) bop
  | Not(t) -> (
      match eval_t t mem with
      | Bool(b) -> Bool(not(b))
      | _ -> failwith "'Not' operator applied to a non boolean value"
    )
  | IfThenElse(t1, t2, t3) -> (
      match eval_t t1 mem with
      | Bool(true) -> eval_t t2 mem
      | Bool(false) -> eval_t t3 mem
      | _ -> failwith "Not boolean value in if-then-else"
    )
  | Fun(x, t) -> Closure(x, t, mem)
  | Let(x, t1, t2) -> eval_t t2 (Rho.add x (eval_t t1 mem) mem)
  | App(t1, t2) -> (
      match eval_t t1 mem with
      | Closure(x, tc, memc) -> eval_t tc (Rho.add x (eval_t t2 mem) memc)
      | RecClosure(f, x, tc, memc) -> eval_t tc (Rho.add f (RecClosure(f, x, tc, memc)) (Rho.add x (eval_t t2 mem) memc))
      | _ -> failwith "First term of application is not a closure"
    )
  | LetFun(f, x, t1, t2) -> eval_t t2 (Rho.add f (RecClosure(f, x, t1, mem)) mem);;

let eval t n = eval_t (App(t, n)) Rho.empty;;