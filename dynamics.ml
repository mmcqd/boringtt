

open Ast


let subst e x = bottom_up (function
  | F y when String.equal x y -> out e
  | x -> x
)

let lift n = top_down (function
  | Type i -> Type (i + n)
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
    | Bind (Lam , (x,e)) -> 
      let (x',e') = unbind (x,e) in 
      mark_as ast @@ lam (x,bind x' (beta c e'))
    | App (e1,e2) ->
      begin
      match out (beta c e1),out (beta c e2) with
        | Bind (Lam, (x,e)), e2' -> 
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
        | e' -> mark_as ast @@ proj1 (into e')
      end
    | Bind (Pi t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      mark_as ast @@ pi (mark_as t @@ beta c t,(x,bind x' (mark_as e @@ beta c e')))
    | Bind (Sigma t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      mark_as ast @@ sigma (mark_as t @@ beta c t,(x,bind x' (mark_as e @@ beta c e')))
    | Annot (e,_) -> mark_as e @@ beta c e
    | _ -> ast

let beta s = beta (s,Context.empty)

let beta_equal s e1 e2 = equal_ast (beta s e1) (beta s e2)

(* let eta = bottom_up (function
  | Bind (Lam, (_,In (App (e,In (B 0))))) -> out e
  | x -> x
) *)