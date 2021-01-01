
open Core

let r = ref 0



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
  [@@deriving map,show,equal]

and 'ast binder = 
  | Pi of 'ast
  | Sigma of 'ast
  | Lam
  [@@deriving map,show,equal]

let map_depth_astF d f = function
  | Bind (b,(x,e)) -> Bind (map_binder (f d) b,(x,f (d+1) e))
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
let pi (t,(x,e)) = into (Bind (Pi t,(x,e)))
let sigma (t,(x,e)) = into (Bind (Sigma t,(x,e)))
let app (e1,e2) = into (App (e1,e2))
let lam (x,e) = into (Bind (Lam,(x,e)))
let pair (e1,e2) = into (Pair (e1,e2))
let proj1 e = into (Proj1 e)
let proj2 e = into (Proj2 e)
let annot (e,t) = into (Annot (e,t))
let meta i = into (Meta i)



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


let bind x = top_down_depth (fun d -> function
  | F y when String.equal x y -> B d
  | x -> x
)

let bind_all = bottom_up (function
  | Bind (b,(x,e)) -> Bind (b,(x,bind x e))
  | x -> x
)

let instantiate x = top_down_depth (fun d -> function
  | B i when i = d -> F x
  | x -> x
) 


let freshen x = r := !r + 1; x ^ "@" ^ Int.to_string !r
let reset_var_stream () = r := 0

let unbind (x,e) = let x' = freshen x in (x',instantiate x' e)


let free_in x = fold (fun _ -> function
  | F y when String.equal x y -> true
  | Bind ((Pi t | Sigma t),(_,e)) -> t || e
  | Bind (Lam, (_,e)) -> e
  | Pair (e1,e2) | App (e1,e2) | Annot (e1,e2) -> e1 || e2
  | Proj1 e | Proj2 e -> e
  | _ -> false
)

let unbind_all = top_down (function
  | Bind (b,(x,e)) -> if free_in x e then Bind (b,unbind (x,e)) else Bind (b,(x,instantiate x e))
  | x -> x
)


let paren e = "(" ^ e ^ ")"
let pretty ast =
  let rec pretty ast = 
    match out ast with
      | B _ -> failwith "Should never print bound vars"
      | Meta i -> sprintf "_%i" i
      | F x -> x
      | Lift (x,n) -> sprintf "%s^%i" x n
      | Bind (Pi t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] -> %s" x (pretty t) (pretty e) else
        let t' = (match out t with (Bind (Pi _,_)) -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s -> %s" t' (pretty e)
      | Bind (Sigma t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] * %s" x (pretty t) (pretty e) else
        let t' = (match out t with (Bind ((Pi _ | Sigma _),_)) -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s * %s" t' (pretty e)
      | App (e1,e2) ->
        begin
        match out e1,out e2 with
          | _,App _ | _, Bind (Lam,_) | _, Bind (Pi _,_) | _, Bind (Sigma _,_) -> sprintf "%s (%s)" (pretty e1) (pretty e2)
          | Bind (Lam,_),_ | Bind (Pi _,_),_ -> sprintf "(%s) %s" (pretty e1) (pretty e2)
          | _ -> sprintf "%s %s" (pretty e1) (pretty e2)
        end
      | Bind (Lam, (x,e)) -> sprintf "\\[%s] %s" x (pretty e)
      | Pair (e1,e2) -> sprintf "(%s , %s)" (pretty e1) (pretty e2)
      | Proj1 e -> sprintf "%s.1" (pretty e)
      | Proj2 e -> sprintf "%s.2" (pretty e)
      | Type i -> "Type" ^ Int.to_string i
      | Annot (e,t) -> sprintf "(%s : %s)" (pretty e) (pretty t)
  in ast |> unbind_all |> pretty
    
