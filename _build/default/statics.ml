open Core
open Ast
open Dynamics


exception TypeError of string

let rec synth ((g,d) as c) e =
  match out e with
    | F x -> (match Context.find g x with | Some t -> t | None -> raise @@ TypeError (sprintf "Unbound variable: %s" x))
    | Type i -> typ (i + 1)
    | Pi (a,(x,b)) | Sigma (a,(x,b)) -> 
      let (x,b) = unbind (x,b) in
      begin
      match out (beta d (synth c a)) with
        | Type i ->
          let g' = g ++ (x,a) in
          begin
          match out (beta d (synth (g',d) b)) with
            | Type j -> typ (Int.max i j)
            | _ -> raise @@ TypeError (sprintf "The term %s must be a Type to appear in a quantifer" (pretty b))
          end
        | _ -> raise @@ TypeError (sprintf "The term %s must be a Type to appear in a quantifier" (pretty a))
      end
    | App (e1,e2) ->
      begin
      match out (beta d (synth c e1)) with
        | Pi (a,(x,b)) -> 
          let (x,b) = unbind (x,b) in
          check c e2 a; beta (d ++ (x,e2)) b
        | t -> raise @@ TypeError (sprintf "%s has type %s, it cannot be applied" (pretty e1) (pretty (into t)))
      end
    | Proj1 e ->
      begin
      match out (beta d (synth c e)) with
        | Sigma (a,_) -> beta d a
        | t -> raise @@ TypeError (sprintf "%s has type %s, it cannot be projected from" (pretty e) (pretty (into t)))
      end
    | Proj2 e ->
      begin
      match out (beta d (synth c e)) with
        | Sigma (_,(x,b)) -> 
          let (x,b) = unbind (x,b) in 
          beta (d ++ (x,proj1 e)) b
        | t -> raise @@ TypeError (sprintf "%s has type %s, it cannot be projected from" (pretty e) (pretty (into t)))
      end
    | Annot (e,t) -> check c e t; beta d t
    | e -> raise @@ TypeError (sprintf "Cannot synthesize a type for %s" (pretty (into e)))
 
    and check ((g,d) as c) e t = 
      assuming (synth c t);
      match out e,out (beta d t) with
        | Type i, Type j -> if i >= j then raise @@ TypeError (sprintf "Type%s does not contain Type%s" (Int.to_string j) (Int.to_string i))
        | Lam (_,e), Pi (a,(y,b)) ->
          let (y,b) = unbind (y,b) in
          let (x,e) = y,instantiate (F y) e in
          check (g ++ (x,a) ++ (y,a),d) e b
        | Pair (e1,e2), Sigma (a,(x,b)) ->
          let (x,b) = unbind (x,b) in
          check c e1 a; check (g ++ (x,a),d) e2 (beta (d ++ (x,e1)) b)
        | _ ->
          let a = synth c e in 
          if not @@ beta_equal d a t then raise @@ TypeError (sprintf "Expected %s to have type %s, but it has type %s" (pretty e) (pretty t) (pretty a)) 


    and assuming _ = ()
