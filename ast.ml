
open Core

let r = ref 0

type var = string
  [@@deriving equal,show]

type 'ast astF =
  | F of var
  | B of int
  | Type of int
  | Pi of 'ast * (var * 'ast)
  | Lam of (var * 'ast)
  | App of 'ast * 'ast
  | Sigma of 'ast * (var * 'ast)
  | Pair of 'ast * 'ast
  | Proj1 of 'ast
  | Proj2 of 'ast
  | Annot of 'ast * 'ast
  | Lift of 'ast * int
  [@@deriving equal,map,show]

let map_depth_astF d f = function
  | Lam (x,e) -> Lam (x,f (d+1) e)
  | Pi (t,(x,e)) -> Pi (f d t,(x,f (d+1) e))
  | Sigma (t,(x,e)) -> Sigma (f d t,(x,f (d+1) e))
  | x -> map_astF (f d) x 


type ast = In of ast astF
  [@@deriving equal,show]


type stm = 
  | Decl of var * ast
  | Eval of ast

module Context = String.Map
let (++) g (key,data) = Context.set g ~key ~data




let f x = In (F x)
let b x = In (B x)
let typ x = In (Type x)
let pi (t,(x,e)) = In (Pi (t,(x,e)))
let sigma (t,(x,e)) = In (Sigma (t,(x,e)))
let app (e1,e2) = In (App (e1,e2))
let lam (x,e) = In (Lam (x,e))
let pair (e1,e2) = In (Pair (e1,e2))
let proj1 e = In (Proj1 e)
let proj2 e = In (Proj2 e)
let annot (e,t) = In (Annot (e,t))
let lift (e,n) = In (Lift (e,n))


let into f = In f
let out (In f) = f

let rec fold f ast = ast |> out |> map_astF (fold f) |> f
let fold_depth f ast = 
  let rec go f d ast = ast |> out |> map_depth_astF d (go f) |> f d in
  go f 0 ast



let rec unfold f s = s |> f |> map_astF (unfold f) |> into
let unfold_depth f s =
  let rec go f d s = s |> f d |> map_depth_astF d (go f) |> into in
  go f 0 s


let bottom_up f = fold (fun x -> into (f x)) 
let bottom_up_depth f = fold_depth (fun d x -> into (f d x))

let top_down f = unfold (fun x -> f (out x))
let top_down_depth f = unfold_depth (fun d x -> f d (out x))


let bind x = top_down_depth (fun d -> function
  | F y when equal_var x y -> B d
  | x -> x
)

let bind_all = top_down (function
  | Pi (t,(x,e)) -> Pi (t,(x,bind x e))
  | Sigma (t,(x,e)) -> Sigma (t,(x,bind x e))
  | Lam (x,e) -> Lam (x,bind x e)
  | x -> x
)

let instantiate t = top_down_depth (fun d -> function
  | B i when i = d -> t
  | x -> x
) 


let freshen x = r := !r + 1; x ^ Int.to_string !r

let unbind (x,e) = let x' = freshen x in (x',instantiate (F x') e)


let free_in x = fold (function
  | F y when equal_var x y -> true
  | Lam (_,e) -> e
  | Pi (t,(_,e)) | Sigma (t,(_,e)) -> t || e
  | Pair (e1,e2) | App (e1,e2) | Annot (e1,e2) -> e1 || e2
  | Proj1 e | Proj2 e -> e
  | Lift (e,_) -> e
  | _ -> false
)

let unbind_all = top_down (function
  | Pi (t,(x,e)) -> if free_in x e then Pi (t,unbind (x,e)) else Pi (t, (x,instantiate (F x) e))
  | Sigma (t,(x,e)) -> if free_in x e then Sigma (t,unbind (x,e)) else Sigma (t, (x,instantiate (F x) e))
  | Lam (x,e) -> if free_in x e then Lam (unbind (x,e)) else Lam (x,instantiate (F x) e)
  | x -> x
)


let paren e = "(" ^ e ^ ")"
let pretty ast =
  let rec pretty ast = 
    match out ast with
      | B _ -> failwith "Should never print bound vars"
      | F x -> x
      | Pi (t,(x,e)) ->
        if free_in x e then sprintf "[%s : %s] -> %s" x (pretty t) (pretty e) else
        let t' = (match out t with Pi _ -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s -> %s" t' (pretty e)
      | Sigma (t,(x,e)) ->
        if free_in x e then sprintf "(%s : %s) * %s" x (pretty t) (pretty e) else
        let t' = (match out t with Pi _ | Sigma _ -> paren (pretty t) | _ -> pretty t) in
        sprintf "%s * %s" t' (pretty e)
      | App (e1,e2) ->
        begin
        match out e1,out e2 with
          | _,App _ | _, Lam _ | _, Pi _ | _, Sigma _ -> sprintf "%s (%s)" (pretty e1) (pretty e2)
          | Lam _,_ | Pi _,_ -> sprintf "(%s) %s" (pretty e1) (pretty e2)
          | _ -> sprintf "%s %s" (pretty e1) (pretty e2)
        end
      | Lam (x,e) -> sprintf "\\[%s] %s" x (pretty e)
      | Pair (e1,e2) -> sprintf "(%s , %s)" (pretty e1) (pretty e2)
      | Proj1 e -> sprintf "%s.1" (pretty e)
      | Proj2 e -> sprintf "%s.2" (pretty e)
      | Type i -> "Type" ^ Int.to_string i
      | Annot (e,t) -> sprintf "(%s : %s)" (pretty e) (pretty t)
      | Lift (e,n) -> sprintf "%s^%s" (pretty e) (Int.to_string n)
  in ast |> unbind_all |> pretty
    
