open Core

type 'ast astF =
  | F of string
  | B of int
  | Lift of (string * int)
  | Type of int
  | Bind of ('ast binder) * (string * 'ast)
  | App of 'ast * 'ast
  | Pair of 'ast * 'ast
  | Proj1 of 'ast
  | Proj2 of 'ast
  | Annot of 'ast * 'ast
  | Meta of int
  | Id of ('ast * 'ast * 'ast)
  | Refl
  | J of ('ast * 'ast * 'ast * 'ast * 'ast * 'ast)
  [@@deriving map,show,equal]

and 'ast binder = 
  | Pi of 'ast
  | Sigma of 'ast
  | Lam
  [@@deriving map,show,equal]

let map_depth_astF d f = function
  | Bind (b,(x,e)) -> Bind (map_binder (f d) b,(x,f (d+1) e))
  | x -> map_astF (f d) x 