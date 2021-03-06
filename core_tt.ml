open Core
open Env





type ident = Syntax.ident
type 'a binder = 'a Syntax.binder
type 'a binder3 = 'a Syntax.binder3
type 'a tele = 'a Syntax.tele



type term = 
  | Var of ident
  | Lift of (ident * int)
  | Type of Level.t
  | Pi of term * term binder
  | Lam of term binder
  | App of term * term
  | Sg of term * term binder
  | Pair of term * term
  | Proj1 of term
  | Proj2 of term
  | One
  | Unit
  | Id of term * term * term
  | Refl of term
  | J of {mot : term binder3 ; case : term binder ; scrut : term }
  | Sum of term * term
  | Inj1 of term
  | Inj2 of term
  | Case of {mot : term binder ; case1 : term binder ; case2 : term binder ; scrut : term}
  | Zero
  | ZeroInd of {mot : term ; scrut : term}
  | Let of (term * term binder)
  (* | DataTyCon of {name : ident ; params : term list; lvl : Level.t}
  | DataCon of {name : ident ; src : ident ; args : term list} *)

type t = term

let rec freshen used x =
  match x with
    | "_" -> "_"
    | _ -> if String.Set.mem used x then freshen used (x ^ "'") else x

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
    | Type Omega -> Type Omega
    | Var x -> Var x
    | One -> One
    | Unit -> Unit
    | Id (t,e1,e2) -> Id (f t,f e1,f e2)
    | Refl e -> Refl (f e)
    | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} -> J {mot = (x,y,z,f mot) ; case = (a,f case) ; scrut = f scrut}
    | Sum (e1,e2) -> Sum (f e1, f e2)
    | Inj1 e -> Inj1 (f e)
    | Inj2 e -> Inj2 (f e)
    | Case {mot = (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} -> Case {mot = (x,f mot) ; case1 = (a,f case1) ; case2 = (b,f case2) ; scrut = f scrut}
    | Zero -> Zero
    | ZeroInd {mot ; scrut} -> ZeroInd {mot = f mot ; scrut = f scrut}
    | Let (e1,(x,e2)) -> Let (f e1,(x,f e2))

let rec bottom_up (f : term -> term) (e : term) : term = e |> rec_map_term (bottom_up f) |> f
let rec top_down (f : term -> term) (e : term) : term = e |> f |> rec_map_term (top_down f)

let lift (i : int) : term -> term = bottom_up (function Type (Const j) -> Type (Const (i + j)) | x -> x)


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
      | Pair (e1,e2), Pair (e1',e2') 
      | Sum (e1,e2), Sum (e1',e2') 
      | ZeroInd {mot = e1 ; scrut = e2}, ZeroInd {mot = e1' ; scrut = e2'} ->
        go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | Lam (x,e), Lam (y,e') ->
        go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Pi (t,(x,e)),Pi (t',(y,e')) 
      | Sg (t,(x,e)), Sg (t',(y,e')) 
      | Let (t,(x,e)),Let(t',(y,e')) -> 
        go i g1 t g2 t' && go (i+1) (g1 ++ (x,i)) e (g2 ++ (y,i)) e'
      | Type i, Type j -> Level.equal i j
      | Proj1 e, Proj1 e' 
      | Proj2 e, Proj2 e' 
      | Refl e, Refl e' 
      | Inj1 e, Inj1 e'
      | Inj2 e, Inj2 e' ->
        go i g1 e g2 e' 
      | Id (t,e1,e2), Id (t',e1',e2') ->
        go i g1 t g2 t' && go i g1 e1 g2 e1' && go i g1 e2 g2 e2'
      | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut = scrut},J {mot = (x',y',z',mot') ; case = (a',case') ; scrut = scrut'} ->
        go (i+3) (g1 ++ (x,i) ++ (y,i) ++ (z,i)) mot (g2 ++ (x',i) ++ (y',i) ++ (z',i)) mot' &&
        go (i+1) (g1 ++ (a,i)) case (g2 ++ (a',i)) case' &&
        go i g1 scrut g2 scrut'
      | Case {mot = (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut = scrut}, Case {mot = (x',mot') ; case1 = (a',case1') ; case2 = (b',case2') ; scrut = scrut'} ->
        go (i+1) (g1 ++ (x,i)) mot (g2 ++ (x',i)) mot' &&
        go (i+1) (g1 ++ (a,i)) case1 (g2 ++ (a',i)) case1' &&
        go (i+1) (g1 ++ (b,i)) case2 (g2 ++ (b',i)) case2' &&
        go i g1 scrut g2 scrut'
      | One,One | Unit,Unit | Zero,Zero -> true
      | _ -> false
  in go 0 Env.empty e1 Env.empty e2

let replace_term (e : term) (e1 : term) : term -> term = 
  bottom_up (fun x -> if alpha_equiv x e then e1 else x)


let paren (e : string) : string = "("^e^")"

let rec pp_term (e : term) : string =
  match e with
    | Lam (x,e) -> sprintf "λ %s ⇒ %s" x (pp_term e)
    | Pi (Pi _ as t,("_",e)) -> sprintf "(%s) → %s" (pp_term t) (pp_term e)
    | Pi (t,("_",e)) -> sprintf "%s → %s" (pp_term t) (pp_term e)
    | Pi (t,(x,e)) -> sprintf "(%s : %s) → %s" x (pp_term t) (pp_term e)
    | App ((Lam _ | J _ | ZeroInd _ | Case _) as e1,e2) -> sprintf "(%s) %s" (pp_term e1) (pp_term e2)
    | App (e1,(App _ as e2)) -> sprintf "%s (%s)" (pp_term e1) (pp_term e2)
    | App (e1,e2) -> sprintf "%s %s" (pp_term e1) (pp_atomic e2)
    | Sg (t,("_",e)) -> sprintf "%s × %s" (pp_atomic t) (pp_atomic e)
    | Sg (t,(x,e)) -> sprintf "(%s : %s) × %s" x (pp_term t) (pp_atomic e)
    | Pair (e1,e2) -> sprintf "%s, %s" (pp_atomic e1) (pp_atomic e2)
    | Id (t,e1,e2) -> sprintf "Id %s %s %s" (pp_atomic t) (pp_atomic e1) (pp_atomic e2)
    | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} -> 
      sprintf "match %s at %s %s %s ⇒ %s with refl %s ⇒ %s" (pp_term scrut) x y z (pp_term mot) a (pp_term case)
    | Sum (e1,e2) -> sprintf "%s + %s" (pp_atomic e1) (pp_atomic e2)
    | Case {mot = (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} ->
      sprintf "match %s at %s => %s with 1.%s ⇒ %s | 2.%s ⇒ %s" (pp_term scrut) x (pp_term mot) a (pp_term case1) b (pp_term case2)
    | ZeroInd {mot ; scrut} -> 
      sprintf "match %s at %s" (pp_term scrut) (pp_term mot)
    | Let (e1,(x,e2)) -> 
      sprintf "let %s = %s in %s" x (pp_term e1) (pp_term e2)
    | Refl e -> sprintf "refl %s" (pp_atomic e)
    | _ -> pp_atomic e

  
and pp_atomic (e : term) : string =
  match e with
    | Var x -> x
    | Lift (x,i) -> sprintf "%s^%i" x i
    | Type Omega -> "Type^ω"
    | Type (Const 0) -> "Type"
    | Type (Const i) -> sprintf "Type^%i" i
    | One -> "𝟙"
    | Unit -> "()"
    | Zero -> "𝟘"
    | Proj1 e -> sprintf "%s.1" (pp_atomic e)
    | Proj2 e -> sprintf "%s.2" (pp_atomic e)
    | Inj1 e -> sprintf "1.%s" (pp_atomic e)
    | Inj2 e -> sprintf "2.%s" (pp_atomic e)
    | _ -> paren (pp_term e)

let pp_context g = 
  let xs = String.Map.to_alist g in
  List.fold_left xs ~init:"" ~f:(fun s -> function ("_",_) -> "" | (x,t) -> sprintf "%s\n  %s : %s" s x (pp_term t))


(*


Spine ("cons",Snoc (Snoc (Nil,tt),xs))

*)