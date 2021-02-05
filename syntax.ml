
open! Core

type ident = string
  [@@deriving show]

type 'a binder = ident * 'a
  [@@deriving show]

type 'a binder3 = ident * ident * ident * 'a
  [@@deriving show]

type 'a tele = (ident * 'a) list
  [@@deriving show]

type 'a spine =
  | Nil
  | Snoc of 'a spine * 'a
  [@@deriving show]



type term = 
  | Var of ident
  | Lift of (ident * int)
  | Type of Level.t
  | Pi of term tele * term
  | Lam of ident list * term
  | Spine of term * term spine
  | Ascribe of term * term
  | Sg of term tele * term
  | Tuple of term list
  | Proj1 of term
  | Proj2 of term
  | One
  | Id of term * term * term
  | Refl of term
  | J of {mot : term binder3 option ; case : term binder ; scrut : term }
  | Meta
  | Sum of term * term
  | Inj1 of term
  | Inj2 of term
  | Case of {mot : term binder option ; case1 : term binder ; case2 : term binder ; scrut : term}
  | Zero
  | ZeroInd of {mot : term option ; scrut : term}
  | Let of (term * term binder)
  [@@deriving show]

type t = term

let fresh_var =
  let r = ref 0 in
  fun () -> r := !r + 1;"x"^Int.to_string !r


type stm = 
  | Eval of term
  | Decl of string * term
  | Axiom of string * term
