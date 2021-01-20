
open Core
open Ast


let subst e x = bottom_up (function
  | F y when String.equal x y -> out e
  | x -> x
)

let subst_ast e1 e2 = bottom_up (function
  | x when equal_ast (into x) e2 -> out e1
  | x -> x
)

let lift n = top_down (function
  | Type i -> Type (level_plus i (Nat n))
  | Lift (x,i) -> Lift (x,i + n)
  | x -> x
)


let rec beta ((s,g) as c) ast =
  match out ast with
    | F x -> 
      begin
      match Context.find g x with 
        | Some x -> x 
        | None ->
          match Context.find s x with
            | Some (e,_) -> e
            | None -> f x
      end
    | Lift (x,n) ->
      begin
      match Context.find s x with
        | Some (e,_) -> lift n e
        | None -> failwith "Should be precluded by typechecking"
      end
    | Lam (x,e) -> 
      let (x',e') = unbind (x,e) in
      mark_as ast @@ lam (x,bind x' (beta c e'))
    | App (e1,e2) ->
      begin
      match out (beta c e1),out (beta c e2) with
        | Lam (x,e), e2' -> 
          let (x',e') = unbind (x,e) in
          mark_as e2 @@ beta (s,g ++ (x',into e2')) e'
        | e1',e2' -> mark_as ast @@ app (into e1',into e2')
      end
    | Pair (e1,e2) -> mark_as ast @@ pair (mark_as e1 @@ beta c e1,mark_as e2 @@ beta c e2)
    | Proj1 e ->
      begin
      match out (beta c e) with
        | Pair (e1,_) -> mark_as e1 @@ beta c e1
        | e' -> mark_as ast @@ proj1 (into e')
      end
    | Proj2 e ->
      begin
      match out (beta c e) with
        | Pair (_,e2) -> mark_as e2 @@ beta c e2
        | e' -> mark_as ast @@ proj2 (into e')
      end
    | Pi (t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      mark_as ast @@ pi (mark_as t @@ beta c t,(x,bind x' (mark_as e @@ beta c e')))
    | Sg (t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      mark_as ast @@ sigma (mark_as t @@ beta c t,(x,bind x' (mark_as e @@ beta c e')))
    | Annot (e,_) -> mark_as e @@ beta c e
    | Refl r -> mark_as ast @@ refl (beta c r)
    | J ((x,y,z,mot),(a,e2),prf) ->
      begin
      match out @@ beta c prf with
        | Refl e -> let (a,e2) = unbind (a,e2) in mark_as e2 (beta (s,g ++ (a,e)) e2)
        | prf' ->
          let (x',y',z',mot) = unbind3 (x,y,z,mot) in
          let (a',e2) = unbind (a,e2) in
          mark_as ast @@ j ((x,y,z,bind3 (x',y',z') (beta c mot)),(a,bind a' (beta c e2)),mark_as prf @@ into prf')
      end
    | Id (t,m,n) -> mark_as ast @@ id (beta c t,beta c m,beta c n)
    | Sum (t1,t2) -> mark_as ast @@ sum (beta c t1,beta c t2)
    | Inj1 e -> mark_as ast @@ inj1 (beta c e)
    | Inj2 e -> mark_as ast @@ inj2 (beta c e)
    | Case ((a,mot),(x,e1),(y,e2),e) ->
      begin
      match out @@ beta c e with
        | Inj1 e -> 
          let (x,e1) = unbind (x,e1) in
          mark_as e1 @@ beta (s,g ++ (x,e)) e1
        | Inj2 e ->
          let (y,e2) = unbind (y,e2) in
          mark_as e2 @@ beta (s,g ++ (y,e)) e2
        | e' ->
          let (a',mot) = unbind (a,mot) in
          let (x',e1) = unbind (x,e1) in
          let (y',e2) = unbind (y,e2) in
          mark_as ast @@ case ((a,bind a' (beta c mot)),(x,bind x' (beta c e1)),(y,bind y' (beta c e2)),mark_as e @@ into e')
      end
    | OneInd ((a,mot),e1,e) ->
      begin
      match out @@ beta c e with
        | Unit -> beta c e1
        | e' ->
          let (a',mot) = unbind (a,mot) in
          mark_as ast @@ one_ind ((a,bind a' (beta c mot)),beta c e1,mark_as e @@ into e')
      end
    | ZeroInd (mot,e) -> mark_as ast @@ zero_ind (beta c mot,beta c e)
    | Meta {sol = Some e; _} -> beta c e
    | _ -> ast


let eta = bottom_up (function
  | Lam (_,In (App (e,In (B 0,_)),_)) -> out e
  | Pair (In (Proj1 x,_), In (Proj2 y, _)) when equal_ast x y -> out y 
  | x -> x
)

let beta s x = beta (s,Context.empty) x

let beta_equal s e1 e2 = equal_ast (eta @@ beta s e1) (eta @@ beta s e2)
