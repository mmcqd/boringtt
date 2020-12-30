

open Ast


let subst e x = bottom_up (function
  | F y when equal_var x y -> out e
  | x -> x
)


let lift n = top_down (function
  | Type i -> Type (i + n)
  | x -> x
)

let rec beta g ast =
  match out ast with
    | F x -> (match Context.find g x with None -> f x | Some e -> e)
    | Bind ((Lam | ALam _) , (x,e)) -> 
      let (x',e') = unbind (x,e) in 
      lam (x,bind x' (beta g e'))
    | App (e1,e2) ->
      begin
      match out (beta g e1),out (beta g e2) with
        | Bind (Lam, (x,e)), e2' -> 
          let (x',e') = unbind (x,e) in
          beta (g ++ (x',into e2')) e'
        | e1',e2' -> app (into e1',into e2')
      end
    | Pair (e1,e2) -> pair (beta g e1,beta g e2)
    | Proj1 e ->
      begin
      match out (beta g e) with
        | Pair (e1,_) -> beta g e1
        | e' -> proj1 (into e')
      end
    | Proj2 e ->
      begin
      match out (beta g e) with
        | Pair (_,e2) -> beta g e2
        | e' -> proj1 (into e')
      end
    | Bind (Pi t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      pi (beta g t,(x,bind x' (beta g e')))
    | Bind (Sigma t,(x,e)) -> 
      let (x',e') = unbind (x,e) in
      sigma (beta g t,(x,bind x' (beta g e')))
    | Annot (e,_) -> beta g e
    | Lift (e,n) -> lift n @@ beta g e
    | x -> into x


let beta_equal g e1 e2 = equal_ast (beta g e1) (beta g e2)

let eta = bottom_up (function
  | Bind (Lam, (_,In (App (e,In (B 0))))) -> out e
  | x -> x
)