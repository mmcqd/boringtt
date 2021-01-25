open Core

type loc = {line : int ; col : int}
  [@@deriving equal,show]


let of_position (pos : Lexing.position) : loc =
  Lexing.{ line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 (* 1-indexed *) }


type level =
  | Const of int
  | Omega
  [@@deriving equal,show]

let level_lt x y =
  match x,y with
    | Const i,Const j -> i < j
    | Const _,Omega -> true
    | Omega,_ -> false

let level_plus x y =
  match x,y with
    | Const i, Const j -> Const (i + j)
    | _ -> Omega

type ident = string
  [@@deriving show]


module Env = String.Map
let (++) env (key,data) = Env.set env ~key ~data

type 'a binder = ident * 'a
  [@@deriving show]
type 'a binder3 = ident * ident * ident * 'a
  [@@deriving show]

type term = 
  | Var of ident
  | Lift of (ident * int)
  | Type of level
  | Pi of (term * term binder)
  | Lam of term binder
  | App of (term * term)
  | Ascribe of term * term
  | Sg of (term * term binder)
  | Pair of (term * term)
  | Proj1 of term
  | Proj2 of term
  | One
  | Unit
  | Id of term * term * term
  | Refl of term
  | J of {mot : term binder3 ; case : term binder ; scrut : term }
  | Meta of {id : int ; mutable sol : term option}
  [@@deriving show]
(*
  | Sum of term * term
  | Inj1 of term
  | Inj2 of term
  | Case of {mot : term binder ; case1 : term binder ; case2 : term binder ; scrut : term}
  | Zero
  | ZeroInd of {mot : term ; scrut : term}
  | Meta of int
*)

(* Disabling warning 30 so I can have two record types with duplicate field names, perhaps sus *)
[@@@ocaml.warning "-30"]
type value =
  | VNeutral of {ty : value ; neu : neutral}
  | VType of level
  | VPi of value * closure
  | VLam of closure
  | VSg of value * closure
  | VPair of value * value
  | VOne
  | VUnit
  | VId of value * value * value
  | VRefl of value
(*
  | VSum of value * value
  | VInj1 of value
  | VInj2 of value
  | VId of value * value * value
  | VRefl of value
  | VZero *)


and neutral = 
  | NVar of ident
  | NApp of neutral * normal
  | NProj1 of neutral
  | NProj2 of neutral
  | NJ of {mot : closure3 ; case : closure ; left : value ; right : value ; ty : value ; scrut : neutral}

and closure = {env : value Env.t ; name : ident ; body : term}

and closure3 = {env : value Env.t ; names : ident * ident * ident ; body : term}

and normal = {ty : value ; tm : value}
[@@@ocaml.warning "+30"]

type stm = 
  | Eval of term
  | Decl of string * term


let closure_name {name ; _} = name
let closure3_names {names ; _} = names

let rec freshen used x =
  if String.Set.mem used x then freshen used (x ^ "'") else x

let freshen3 used (x,y,z) = 
  let x = freshen used x in
  let used = String.Set.add used x in
  let y = freshen used y in
  let used = String.Set.add used y in
  let z = freshen used z in
  x,y,z

let rec_map_term (f : term -> term) (e : term) : term =
  match e with
    | Type (Const j) -> Type (Const j)
    | Lift (x,j) -> Lift (x, j)
    | Lam (x,e) -> Lam (x,f e)
    | Pi (t,(x,e)) -> Pi (f t,(x,f e))
    | App (e1,e2) -> App (f e1,f e2)
    | Sg (t,(x,e)) -> Sg (f t,(x,f e))
    | Pair (e1,e2) -> Pair (f e1,f e2)
    | Proj1 e -> Proj1 (f e)
    | Proj2 e -> Proj2 (f e)
    | Ascribe (e,t) -> Ascribe (f e,f t)
    | Type Omega -> Type Omega
    | Var x -> Var x
    | One -> One
    | Unit -> Unit
    | Id (t,e1,e2) -> Id (f t,f e1,f e2)
    | Refl e -> Refl (f e)
    | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} -> J {mot = (x,y,z,f mot) ; case = (a,f case) ; scrut = f scrut}
    | Meta {id ; sol} -> Meta {id ; sol = Option.map ~f sol}

let rec bottom_up (f : term -> term) (e : term) : term = e |> rec_map_term (bottom_up f) |> f
let rec top_down (f : term -> term) (e : term) : term = e |> f |> rec_map_term (top_down f)

let lift (i : int) : term -> term = bottom_up (function Type (Const j) -> Type (Const (i + j)) | x -> x)

let to_env (ctx : value Env.t) : value Env.t = Env.mapi ctx ~f:(fun ~key ~data -> VNeutral {neu = NVar key ; ty = data})


let alpha_equiv (e1 : term) (e2 : term) : bool = 
  let rec go (i : int) (g1 : int Env.t) (e1 : term) (g2 : int Env.t) (e2 : term) : bool =
    match e1,e2 with
      | Var x,Var y ->
        begin
        match Env.find g1 x,Env.find g2 y with
          | Some i, Some j -> i = j
          | None,None -> String.equal x y
          | _ -> false
        end
      | Lift (x,i),Lift (y,j) -> i = j && String.equal x y
      | App (e1,e2),App (e1',e2') 
      | Pair (e1,e2), Pair (e1',e2') ->
        go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | Lam (x,e), Lam (y,e') ->
        go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Pi (t,(x,e)),Pi (t',(y,e')) 
      | Sg (t,(x,e)), Sg (t',(y,e')) -> 
        go i g1 t g2 t' && go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Type i, Type j -> equal_level i j
      | Ascribe (e,t), Ascribe (e',t') ->
        go i g1 e g2 e' && go i g1 t g2 t'
      | Proj1 e, Proj1 e' 
      | Proj2 e, Proj2 e' 
      | Refl e, Refl e' ->
        go i g1 e g2 e' 
      | Id (t,e1,e2), Id (t',e1',e2') ->
        go i g1 t g2 t' && go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut = scrut},J {mot = (x',y',z',mot') ; case = (a',case') ; scrut = scrut'} ->
        go (i+3) (g1 ++ (x,i) ++ (y,i) ++ (z,i)) mot (g2 ++ (x',i) ++ (y',i) ++ (z',i)) mot' &&
        go (i+1) (g1 ++ (a,i)) case (g2 ++ (a',i)) case' &&
        go i g1 scrut g2 scrut'
      | One,One | Unit,Unit -> true
      | Meta {sol = Some e ; _}, Meta {sol = Some e'; _} -> go i g1 e g2 e'
      | Meta {sol = None; id = id},Meta {sol = None; id = id'} -> id = id'
      | _ -> false
  in go 0 Env.empty e1 Env.empty e2


let replace_term (e : term) (e1 : term) : term -> term = 
  bottom_up (fun x -> if alpha_equiv x e then e1 else x)


let paren (e : string) : string = "("^e^")"

let rec pp_term (e : term) : string =
  match e with
    | Lam (x,e) -> sprintf "fn %s => %s" x (pp_term e)
    | Pi (Pi _ as t,("_",e)) -> sprintf "(%s) -> %s" (pp_term t) (pp_term e)
    | Pi (t,("_",e)) -> sprintf "%s -> %s" (pp_term t) (pp_term e)
    | Pi (t,(x,e)) -> sprintf "[%s : %s] -> %s" x (pp_term t) (pp_term e)
    | App (Lam _ as e1,e2) -> sprintf "(%s) %s" (pp_term e1) (pp_term e2)
    | App (e1,(App _ as e2)) -> sprintf "%s (%s)" (pp_term e1) (pp_term e2)
    | App (e1,e2) -> sprintf "%s %s" (pp_term e1) (pp_term e2)
    | Sg (t,("_",e)) -> sprintf "%s * %s" (pp_term t) (pp_term e)
    | Sg (t,(x,e)) -> sprintf "[%s : %s] * %s" x (pp_term t) (pp_term e)
    | Pair (e1,e2) -> sprintf "%s,%s" (pp_term e1) (pp_term e2)
    | Id (t,e1,e2) -> sprintf "Id %s %s %s" (pp_atomic t) (pp_atomic e1) (pp_atomic e2)
    | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} -> 
      sprintf "match %s at %s %s %s => %s with refl %s => %s" (pp_term scrut) x y z (pp_term mot) a (pp_term case)
    | Meta {sol = Some e; _} -> pp_term e
    | _ -> pp_atomic e

  
and pp_atomic (e : term) : string =
  match e with
    | Var x -> x
    | Meta {sol = None ; id} -> sprintf "_%i" id
    | Lift (x,i) -> sprintf "%s^%i" x i
    | Type Omega -> "TypeOmega"
    | Type (Const i) -> sprintf "Type^%i" i
    | One -> "One"
    | Unit -> "<>"
    | Proj1 e -> sprintf "%s.1" (pp_atomic e)
    | Proj2 e -> sprintf "%s.2" (pp_atomic e)
    | Ascribe (e,t) -> sprintf "(%s : %s)" (pp_term e) (pp_term t)
    | Refl e -> sprintf "refl %s" (pp_atomic e)
    | _ -> paren (pp_term e)

let pp_context g = 
  let xs = String.Map.to_alist g in
  List.fold_left xs ~init:"" ~f:(fun s (x,t) -> sprintf "%s\n  %s : %s" s x (pp_term t))
