
open Core

let var_stream = ref 0

type 'a binder = string * 'a
  [@@deriving map,show,equal]
type 'a binder2 = string * string * 'a
  [@@deriving map,show,equal]
type 'a binder3 = string * string * string * 'a
  [@@deriving map,show,equal]

type level = 
  | Omega
  | Nat of int
  [@@deriving equal,show]

let level_lt x y =
  match x,y with
    | Nat i,Nat j -> i < j
    | Nat _,Omega -> true
    | Omega,_ -> false

let level_plus x y =
  match x,y with
    | Nat i, Nat j -> Nat (i + j)
    | _ -> Omega


type 'ast astF =
  | F of string
  | B of int
  | Lift of (string * int)
  | Type of level
  | Pi of 'ast * 'ast binder
  | Sg of 'ast * 'ast binder
  | Lam of 'ast binder
  | App of 'ast * 'ast
  | Pair of 'ast * 'ast
  | Proj1 of 'ast
  | Proj2 of 'ast
  | Annot of 'ast * 'ast
  | Meta of {id : int; mutable sol : 'ast option}
  | Id of ('ast * 'ast * 'ast)
  | Refl of 'ast
  | J of ('ast binder3 * 'ast binder * 'ast)
  | Sum of ('ast * 'ast)
  | Inj1 of 'ast
  | Inj2 of 'ast
  | Case of ('ast binder * 'ast binder * 'ast binder * 'ast)
  | One
  | Unit
  | OneInd of ('ast binder * 'ast * 'ast)
  | Zero
  | ZeroInd of ('ast * 'ast)
  [@@deriving map,show,equal]


let map_depth_astF d f = function
  | Pi (b,(x,e)) -> Pi ((f d) b,(x,f (d+1) e))
  | Sg (b,(x,e)) -> Sg ((f d) b,(x,f (d+1) e))
  | Lam (x,e) ->  Lam (x,f (d+1) e)
  | J ((a,b,c,mot),(x,e),prf) -> J ((a,b,c,f (d+3) mot),(x,f (d+1) e),f d prf)
  | Case ((a,mot),(x,e1),(y,e2),e) -> Case ((a,f (d+1) mot),(x,f (d+1) e1),(y,f (d+1) e2),f d e)
  | OneInd ((a,mot),e1,e) -> OneInd ((a,f (d+1) mot),f d e1,f d e)
  | x -> map_astF (f d) x 

let mono_map_depth_astF d f = function
  | Meta m -> m.sol <- Option.map ~f:(f d) m.sol; Meta m
  | x -> map_depth_astF d f x

let mono_map_astF f = mono_map_depth_astF 0 (const f)


type loc = {line : int ; col : int}
  [@@deriving equal,show]

type ast = In of ast astF * (loc * loc) option
  [@@deriving show]

let rec equal_ast (In (f,_)) (In (f',_)) = equal_astF equal_ast f f'

type stm = 
  | Decl of string * ast
  | Eval of ast
  | Postulate of string * ast



(* let meta_sols : ast Int.Map.t ref = ref Int.Map.empty
let set_meta_sol key data = meta_sols := Int.Map.set !meta_sols ~key ~data
let find_meta_sol *)

let into f = In (f,None)
let out (In (f,_)) = f

let show_loc {line ; col} = sprintf "%s.%s" (Int.to_string line) (Int.to_string col)

let show_span (s,e) = sprintf "%s:%s" (show_loc s) (show_loc e)

let of_position (pos : Lexing.position) : loc =
  Lexing.{ line = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol + 1 (* 1-indexed *) }


let set_span x (In (f,_)) = In (f,x)

let mark pos1 pos2 (In (f,_)) = In (f,Some (of_position pos1,of_position pos2))

let get_span (In (_,x)) = x

let mark_as e1 e2 = set_span (get_span e1) e2

let span_str (In (_,x)) =
  match x with
    | None -> ""
    | Some s -> show_span s



let f x = into (F x)
let b x = into (B x)
let typ x = into (Type x)
let lift x = into (Lift x)
let pi (t,(x,e)) = into (Pi (t,(x,e)))
let sigma (t,(x,e)) = into (Sg (t,(x,e)))
let app (e1,e2) = into (App (e1,e2))
let lam (x,e) = into (Lam (x,e))
let pair (e1,e2) = into (Pair (e1,e2))
let proj1 e = into (Proj1 e)
let proj2 e = into (Proj2 e)
let annot (e,t) = into (Annot (e,t))
let meta ?(sol=None) id = into (Meta {id ; sol})
let id x = into (Id x)
let j x = into (J x)
let refl x = into (Refl x)
let sum x = into (Sum x)
let inj1 x = into (Inj1 x)
let inj2 x = into (Inj2 x)
let case x = into (Case x)
let one = into One
let unit = into Unit
let one_ind x = into (OneInd x)
let zero = into Zero
let zero_ind x = into (ZeroInd x)


let rec fold f ast = ast |> out |> map_astF (fold f) |> f (get_span ast)
let fold_depth f ast = 
  let rec go f d ast = ast |> out |> map_depth_astF d (go f) |> f d (get_span ast) in
  go f 0 ast



let rec unfold f s = s |> f |> map_astF (unfold f) |> into
let unfold_depth f s =
  let rec go f d s = s |> f d |> map_depth_astF d (go f) |> into in
  go f 0 s


let bottom_up_depth f ast = 
  let rec go f d ast = ast |> out |> mono_map_depth_astF d (go f) |> f d |> into |> mark_as ast in
  go f 0 ast

let bottom_up f = bottom_up_depth (const f)

let top_down_depth f ast =
  let rec go f d ast = ast |> out |> f d |> mono_map_depth_astF d (go f) |> into |> mark_as ast in
  go f 0 ast

let top_down f = top_down_depth (const f) 

let copy = fold (fun l x -> set_span l (into x))


let bindn xs = 
  let l = List.length xs in
  top_down_depth (fun d -> function
    | F v ->
      begin
      match List.findi xs ~f:(fun _ x -> String.equal v x) with
        | Some (i,_) -> B (d + l - 1 - i)
        | None -> F v 
      end
    | x -> x
  )


let bind x = bindn [x]
let bind3 (x,y,z) = bindn [x;y;z]


let bind_all = bottom_up (function
  | Pi (b,(x,e)) -> Pi (b,(x,bind x e))
  | Sg (b,(x,e)) -> Sg (b,(x,bind x e))
  | Lam (x,e) -> Lam (x,bind x e)
  | J ((x,y,z,mot),(d,e2),prf) -> J ((x,y,z,bind3 (x,y,z) mot),(d,bind d e2),prf)
  | Case ((a,mot),(x,e1),(y,e2),e) -> Case ((a,bind a mot),(x,bind x e1),(y,bind y e2),e)
  | OneInd ((a,mot),e1,e) -> OneInd ((a,bind a mot),e1,e)
  | x -> x
)

let instantiate n x = top_down_depth (fun d -> function
  | B i when i = d + n -> F x
  | x -> x
) 


let freshen x = var_stream := !var_stream + 1; x ^ "@" ^ Int.to_string !var_stream
let reset_var_stream () = var_stream := 0

let unbindn fresh (xs,e) = 
  let l = List.length xs in
  let xs' = List.map2_exn xs fresh ~f:(fun v f -> if f then freshen v else v) in
  xs',List.fold_right ~init:Fun.id ~f:(fun f g x -> f (g x)) (List.mapi xs' ~f:(fun i v -> instantiate (l - 1 - i) v)) e

let unbind ?(fresh=true) (x,e) = 
  let [@warning "-8"] [x],e = unbindn [fresh] ([x],e) in
  x,e
  
let unbind3 ?(fresh=(true,true,true)) (x,y,z,e) =
  let (a,b,c) = fresh in
  let [@warning "-8"] [x;y;z],e = unbindn [a;b;c] ([x;y;z],e) in
  x,y,z,e

let free_in x = fold (fun _ -> function
  | F y when String.equal x y -> true
  | (Pi (t, (_,e)) | Sg (t,(_,e))) -> t || e
  | Lam (_,e) -> e
  | Pair (e1,e2) | App (e1,e2) | Annot (e1,e2) | Sum (e1,e2) -> e1 || e2
  | Proj1 e | Proj2 e | Inj1 e | Inj2 e | Refl e -> e
  | J ((_,_,_,mot),(_,e2),eq) -> mot || e2 || eq
  | Id (t,m,n) -> t || m || n
  | Case ((_,mot),(_,e1),(_,e2),e) -> mot || e1 || e2 || e
  | OneInd ((_,mot),e1,e) -> mot || e1 || e
  | ZeroInd (mot,e) -> mot || e
  | Meta {sol = Some e; _} -> e
  | F _ | B _ | Meta _ | One | Unit | Zero | Lift _ | Type _ -> false
)

let unbind_all = top_down (function
  | Pi (b,(x,e)) -> Pi (b,unbind ~fresh:(free_in x e) (x,e)) 
  | Sg (b,(x,e)) -> Sg (b,unbind ~fresh:(free_in x e) (x,e))
  | Lam (x,e) -> Lam (unbind ~fresh:(free_in x e) (x,e))
  | J ((a,b,c,mot),(d,e2),prf) -> J (unbind3 ~fresh:(free_in a mot,free_in b mot,free_in c mot) (a,b,c,mot),unbind ~fresh:(free_in d e2) (d,e2),prf)
  | Case ((a,mot),(x,e1),(y,e2),e) -> Case (unbind ~fresh:(free_in a mot) (a,mot),unbind ~fresh:(free_in x e1) (x,e1),unbind ~fresh:(free_in y e2) (y,e2),e)
  | OneInd ((a,mot),e1,e) -> OneInd ((unbind ~fresh:(free_in a mot) (a,mot)),e1,e)
  | x -> x
)


let paren e = "(" ^ e ^ ")"
let pretty ?(debug=false) ast =
  let rec atomic ast =
    match out ast with
      | B i -> sprintf "B%i" i (* failwith "Should never print bound vars" *)
      | Annot (e,t) -> sprintf "(%s : %s)" (expr e) (expr t)
      | F x -> x
      | Meta {sol = None; id} -> sprintf "_%i" id
      | Meta {sol = Some e; _} -> sprintf "{%s}" (expr e)
      | Lift (x,n) -> sprintf "%s^%i" x n
      | Type (Nat i) -> sprintf "Type%i" i
      | Type Omega -> "TypeOmega"
      | Refl r -> sprintf "refl %s" (atomic r)
      | Proj1 e -> sprintf "%s.1" (atomic e)
      | Proj2 e -> sprintf "%s.2" (atomic e)
      | Inj1 e -> sprintf "1.%s" (atomic e)
      | Inj2 e -> sprintf "2.%s" (atomic e)
      | One -> "One"
      | Unit -> "<>"
      | Zero -> "Zero"
      | _ -> sprintf "(%s)" (expr ast)
      
  and expr ast =
    match out ast with
      | App (e1,e2) -> sprintf "%s %s" (atomic e1) (atomic e2)
      | Lam (x,e) -> sprintf "fn %s => %s" x (expr e)
      | Id (t,m,n) -> sprintf "Id %s %s %s" (atomic t) (atomic m) (atomic n)
      | Pi (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] -> %s" x (expr t) (expr e) else
        sprintf "%s -> %s" (atomic t) (expr e)
      | Sg (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] * %s" x (expr t) (expr e) else
        sprintf "%s * %s" (atomic t) (atomic e)
      | Pair (e1,e2) -> sprintf "%s , %s" (expr e1) (expr e2)
      | J ((a,b,c,e1),(d,e2),p) -> sprintf "match %s at %s %s %s => %s with refl %s => %s" (expr p) a b c (expr e1) d (expr e2)
      | Sum (e1,e2) -> sprintf "%s + %s" (expr e1) (expr e2)
      | Case ((a,mot),(x,e1),(y,e2),e) -> sprintf "match %s at %s => %s with 1.%s => %s | 2.%s => %s" (expr e) a (expr mot) x (expr e1) y (expr e2)
      | OneInd ((a,mot),e1,e) -> sprintf "match %s at %s => %s with <> => %s" (expr e) a (expr mot) (expr e1) 
      | ZeroInd (mot,e) -> sprintf "match %s at %s" (expr e) (expr mot)
      | _ -> atomic ast
  in ast |> (if not debug then unbind_all else Fun.id) |> expr

module Context = String.Map
let (++) g (key,data) = Context.set g ~key ~data 
let pp_context g = 
  let xs = String.Map.to_alist g in
  List.fold_left xs ~init:"" ~f:(fun s (x,t) -> sprintf "%s\n%s : %s" s x (pretty t))