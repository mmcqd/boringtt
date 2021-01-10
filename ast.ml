
open Core

let r = ref 0



type z = Z
type _ s = S



type 'a binder = string * 'a
  [@@deriving map,show,equal]
type 'a binder2 = string * string * 'a
  [@@deriving map,show,equal]
type 'a binder3 = string * string * string * 'a
  [@@deriving map,show,equal]


type 'ast astF =
  | F of string
  | B of int
  | Lift of (string * int)
  | Type of int
  | Pi of 'ast * 'ast binder
  | Sg of 'ast * 'ast binder
  | Lam of 'ast binder
  | App of 'ast * 'ast
  | Pair of 'ast * 'ast
  | Proj1 of 'ast
  | Proj2 of 'ast
  | Annot of 'ast * 'ast
  | Meta of int
  | Id of ('ast * 'ast * 'ast)
  | Refl
  | J of ('ast * 'ast binder3 * 'ast binder * 'ast * 'ast * 'ast)
  [@@deriving map,show,equal]


let map_depth_astF d f = function
  | Pi (b,(x,e)) -> Pi ((f d) b,(x,f (d+1) e))
  | Sg (b,(x,e)) -> Sg ((f d) b,(x,f (d+1) e))
  | Lam (x,e) ->  Lam (x,f (d+1) e)
  | J (t,(x,y,eq,c),(z,b),m,n,prf) -> J (f d t,(x,y,eq,f (d+3) c),(z,f (d+1) b),f d m,f d n,f d prf)
  | x -> map_astF (f d) x 


type loc = {line : int ; col : int}
  [@@deriving equal,show]

type ast = In of ast astF * (loc * loc) option
  [@@deriving show]

let rec equal_ast (In (f,_)) (In (f',_)) = equal_astF equal_ast f f'

type stm = 
  | Decl of string * ast
  | Eval of ast
  | Postulate of string * ast

module Context = String.Map
let (++) g (key,data) = Context.set g ~key ~data

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
let meta i = into (Meta i)
let id x = into (Id x)
let j x = into (J x)
let refl = into Refl


let rec fold f ast = ast |> out |> map_astF (fold f) |> f (get_span ast)
let fold_depth f ast = 
  let rec go f d ast = ast |> out |> map_depth_astF d (go f) |> f d (get_span ast) in
  go f 0 ast



let rec unfold f s = s |> f |> map_astF (unfold f) |> into
let unfold_depth f s =
  let rec go f d s = s |> f d |> map_depth_astF d (go f) |> into in
  go f 0 s


let bottom_up f = fold (fun span x -> set_span span @@ into (f x)) 
let bottom_up_depth f = fold_depth (fun d span x -> set_span span @@ into (f d x))


let rec top_down f ast = ast |> out |> f |> map_astF (top_down f) |> into |> mark_as ast
let top_down_depth f ast =
  let rec go f d ast = ast |> out |> f d |> map_depth_astF d (go f) |> into |> mark_as ast in
  go f 0 ast



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
  | J (t,(a,b,c,e1),(d,e2),m,n,prf) -> J (t,(a,b,c,bind3 (a,b,c) e1),(d,bind d e2),m,n,prf)
  | x -> x
)

let instantiate n x = top_down_depth (fun d -> function
  | B i when i = d + n -> F x
  | x -> x
) 


let freshen x = r := !r + 1; x ^ "@" ^ Int.to_string !r
let reset_var_stream () = r := 0

let unbindn fresh (xs,e) = 
  let l = List.length xs in
  let xs' = List.map2_exn xs fresh ~f:(fun v f -> if f then freshen v else v) in
  xs',List.fold_right ~init:Fun.id ~f:(fun f g x -> f (g x)) (List.mapi xs' ~f:(fun i v -> instantiate (l - 1 - i) v)) e

let unbind ?(fresh=[true]) (x,e) = 
  let [@warning "-8"] [x],e = unbindn fresh ([x],e) in
  x,e
  
let unbind3 ?(fresh=[true;true;true]) (x,y,z,e) = 
  let [@warning "-8"] [x;y;z],e = unbindn fresh ([x;y;z],e) in
  x,y,z,e

let free_in x = fold (fun _ -> function
  | F y when String.equal x y -> true
  | (Pi (t, (_,e)) | Sg (t,(_,e))) -> t || e
  | Lam (_,e) -> e
  | Pair (e1,e2) | App (e1,e2) | Annot (e1,e2) -> e1 || e2
  | Proj1 e | Proj2 e -> e
  | J (t,(_,_,_,e1),(_,e2),m,n,eq) -> t || e1 || e2 || m || n || eq
  | Id (t,m,n) -> t || m || n
  | _ -> false
)

let unbind_all = top_down (function
  | Pi (b,(x,e)) -> Pi (b,unbind ~fresh:[free_in x e] (x,e)) 
  | Sg (b,(x,e)) -> Sg (b,unbind ~fresh:[free_in x e] (x,e))
  | Lam (x,e) -> Lam (unbind ~fresh:[free_in x e] (x,e))
  | J (t,(a,b,c,e1),(d,e2),m,n,prf) -> J (t,unbind3 ~fresh:([free_in a e1;free_in b e1;free_in c e1]) (a,b,c,e1),unbind ~fresh:[free_in d e2] (d,e2),m,n,prf)
  | x -> x
)


let paren e = "(" ^ e ^ ")"
let pretty ast =
  let rec atomic ast =
    match out ast with
      | B _ -> failwith "Should never print bound vars"
      | Annot _ -> failwith "Annotations should always be reduced away"
      | F x -> x
      | Meta i -> sprintf "_%i" i
      | Lift (x,n) -> sprintf "%s^%i" x n
      | Type i -> sprintf "Type%i" i
      | Refl -> "refl"
      | Proj1 e -> sprintf "%s.1" (atomic e)
      | Proj2 e -> sprintf "%s.2" (atomic e)
      | _ -> sprintf "(%s)" (expr ast)
      
  and expr ast =
    match out ast with
      | App (e1,e2) -> sprintf "%s %s" (atomic e1) (atomic e2)
      | Lam (x,e) -> sprintf "\\[%s] %s" x (expr e)
      | Id (t,m,n) -> sprintf "Id %s %s %s" (atomic t) (atomic m) (atomic n)
      | Pi (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] -> %s" x (expr t) (expr e) else
        sprintf "%s -> %s" (atomic t) (expr e)
      | Sg (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] * %s" x (expr t) (expr e) else
        sprintf "%s * %s" (atomic t) (expr e)
      | Pair (e1,e2) -> sprintf "%s , %s" (expr e1) (expr e2)
      | J (t,(a,b,c,e1),(d,e2),m,n,p) -> sprintf "J (%s;[%s %s %s] %s;[%s] %s;%s;%s;%s)" (expr t) a b c (expr e1) d (expr e2) (expr m) (expr n) (expr p)
      | _ -> atomic ast
  in ast |> unbind_all |> expr

(*
  let rec pretty ast = 
    match out ast with
      | B _ -> failwith "Should never print bound vars"
      | Meta i -> sprintf "_%i" i
      | F x -> x
      | Lift (x,n) -> sprintf "%s^%i" x n
      | Pi (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] -> %s" x (pretty t) (pretty e) else
        let t' = (match out t with Pi _ -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s -> %s" t' (pretty e)
      | Sg (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] * %s" x (pretty t) (pretty e) else
        let t' = (match out t with (Pi _ | Sg _) -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s * %s" t' (pretty e)
      | App (e1,e2) ->
        begin
        match out e1,out e2 with
          | _,App _ | _, Lam _ | _, Pi _ | _, Sg _ -> sprintf "%s (%s)" (pretty e1) (pretty e2)
          | Lam _,_ -> sprintf "(%s) %s" (pretty e1) (pretty e2)
          | _ -> sprintf "%s %s" (pretty e1) (pretty e2)
        end
      | Lam (x,e) -> sprintf "\\[%s] %s" x (pretty e)
      | Pair (e1,e2) -> sprintf "(%s , %s)" (pretty e1) (pretty e2)
      | Proj1 e -> sprintf "%s.1" (pretty e)
      | Proj2 e -> sprintf "%s.2" (pretty e)
      | Type i -> "Type" ^ Int.to_string i
      | Annot (e,t) -> sprintf "(%s : %s)" (pretty e) (pretty t)
      | Id (t,x,y) -> sprintf "Id %s %s %s" (pretty t) (pretty x) (pretty y)
      | Refl -> "refl"
      | J (t,(a,b,c,e1),(d,e2),m,n,p) -> sprintf "J (%s;[%s %s %s] %s;[%s] %s;%s;%s;%s)" (pretty t) a b c (pretty e1) d (pretty e2) (pretty m) (pretty n) (pretty p)
  in ast |> unbind_all |> pretty
*)