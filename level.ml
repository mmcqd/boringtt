open Core

type t =
  | Const of int
  | Omega
  [@@deriving equal,show]

let (<) x y =
  match x,y with
    | Const i,Const j -> i < j
    | Const _,Omega -> true
    | Omega,_ -> false

let (+) x y =
  match x,y with
    | Const i, Const j -> Const (i + j)
    | _ -> Omega
