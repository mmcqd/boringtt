

type ident = Syntax.ident
(* Disabling warning 30 so I can have two record types with duplicate field names, perhaps sus *)
[@@@ocaml.warning "-30"]
type value =
  | VNeutral of {ty : value ; neu : neutral}
  | VType of Level.t
  | VPi of value * closure
  | VLam of closure
  | VSg of value * closure
  | VPair of value * value
  | VOne
  | VUnit
  | VId of value * value * value
  | VRefl of value
  | VSum of value * value
  | VInj1 of value
  | VInj2 of value
  | VZero


and neutral = 
  | NVar of ident
  | NApp of neutral * normal
  | NProj1 of neutral
  | NProj2 of neutral
  | NJ of {mot : closure3 ; case : closure ; left : value ; right : value ; ty : value ; scrut : neutral}
  | NCase of {mot : closure ; case1 : closure ; case2 : closure ; left : value ; right : value ; scrut : neutral}
  | NZeroInd of {mot : value ; scrut : neutral}

and closure = {env : value Env.t ; name : ident ; body : Core_tt.term}

and closure3 = {env : value Env.t ; names : ident * ident * ident ; body : Core_tt.term}

and normal = {ty : value ; tm : value}
[@@@ocaml.warning "+30"]

let closure_name {name ; _} = name
let closure3_names {names ; _} = names

let ctx_to_env (ctx : value Env.t) : value Env.t = Env.mapi ctx ~f:(fun ~key ~data -> VNeutral {neu = NVar key ; ty = data})

type t = value