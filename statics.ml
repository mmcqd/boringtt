open Core
open Ast
open Dynamics


exception Unsolved of string
exception SynthFailed of string
exception CheckFailed of string

let assuming _ = ()

let parse s = 
  let lexbuf = Lexing.from_string s in
  match Parser.init Lexer.initial lexbuf with
    | [Eval e] -> e
    | _ -> failwith "whoops"



let resolve_lam_pi_binders (x,e) (y,b) =
  match y with
    | "" -> let (x,e) = unbind (x,e) in x,e,instantiate 0 x b
    | _  -> let (y,b) = unbind (y,b) in y,instantiate 0 y e,b


let rec synth ((s,g) as c) ast =
  (* print_endline ("SYNTH "^ pretty ast); *)
  match out ast with
    | F x ->
      begin
      match Context.find g x with
        | Some t -> t
        | None ->
          match Context.find s x with
            | Some (_,t) -> t
            | _ -> raise @@ SynthFailed (sprintf "%s - Unbound variable: %s" (span_str ast) x)
      end
    | Lift (x,n) ->
      begin
      match Context.find s x with
        | Some (_,t) -> lift n t
        | None -> raise @@ SynthFailed (sprintf "%s - Cannot lift non-toplevel defintion: %s" (span_str ast) x)
      end
    | App (e1,e2) ->
      begin
      match out (beta s (synth c e1)) with
        | Pi (a, b) -> 
          let (x,b) = unbind b in
          check c e2 a; subst e2 x b 
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be applied" (span_str ast) (pretty e1) (pretty (into t)))
      end
    | Proj1 e ->
      begin
      match out (beta s (synth c e)) with
        | Sg (a,_) -> a
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be projected from" (span_str e) (pretty e) (pretty (into t)))
      end
    | Proj2 e ->
      begin
      match out (beta s (synth c e)) with
        | Sg (_,b) -> 
          let (x,b) = unbind b in 
          subst (proj1 e) x b
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be projected from" (span_str e) (pretty e) (pretty (into t)))
      end
    | Annot (e,t) -> (try check c e t; t with CheckFailed e -> raise @@ SynthFailed e)
    | J (a,b,prf) ->
      let (x,y,z,e1) = unbind3 a in
      let (a,e2) = unbind b in
      begin
      match out (beta s (synth c prf)) with
        | Id (t,m,n) ->
          check (s,g ++ (x,t) ++ (y,t) ++ (z,id (t,f x,f y))) e1 (typ Omega);
          check (s,g ++ (a,t)) e2 (e1 |> subst (f a) x |> subst (f a) y |> subst (refl m) z);
          e1 |> subst m x |> subst n y |> subst prf z
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it is not an equality" (span_str prf) (pretty prf) (pretty (into t)))
      end
    | Meta _ -> raise @@ Unsolved "Unknown Type"
    | _ -> raise @@ SynthFailed (sprintf "%s - Cannot synthesize a type for %s" (span_str ast) (pretty ast))
  
  and check ((s,g) as c) e t =
    (* print_endline ("CHECK "^ pretty e ^ " AT " ^ pretty t); *)
    let t = beta s t in
    match out @@ e, out @@ t with
      | Meta _, t -> raise @@ Unsolved (pretty (into t))
      | Type i, Type j -> if not (level_lt i j) then raise @@ CheckFailed (sprintf "%s - %s too large to be contained in %s" (span_str e) (pretty e) (pretty t))
      | (Pi (a,b) | Sg (a,b)), Type i ->
        let (x,b) = unbind b in
        check c a (typ i); check (s,(g ++ (x,a))) b (typ i)
      | Id (t,m,n) , Type i ->
        check c t (typ i);
        check c m t;
        check c n t 
      | Lam (x,e), Pi (a,(y,b)) ->
        check c t (typ Omega);
        let x,e,b = resolve_lam_pi_binders (x,e) (y,b) in
        check (s,g ++ (x,a)) e b
      | Pair (e1,e2), Sg (a, b) ->
        check c t (typ Omega);
        let (x,b) = unbind b in
        check c e1 a; check c e2 (subst e1 x b)
      | Refl r, Id (_,x,y) ->
        check c t (typ Omega);
        if not @@ beta_equal s x y then raise @@ CheckFailed (sprintf "%s - %s and %s are not equal, they cannot be identified" (span_str e) (pretty x) (pretty y));
        begin
        match out (beta s r.ast) with
          | Meta _ -> r.ast <- x
          | _ -> if not @@ beta_equal s x r.ast then raise @@ CheckFailed (sprintf "%s - %s and %s are not equal, they cannot be identified" (span_str e) (pretty x) (pretty e));
        end
      | _,t' ->
        let t' = into t' in
        let a = beta s @@ synth c e in
        if not @@ sub c a t' then
        raise @@ CheckFailed (sprintf "%s - Expected %s to have type %s, but it has type %s" (span_str e) (pretty e) (pretty t') (pretty a))


  and sub c t1 t2 = if beta_equal (fst c) t1 t2 then true else
    match out t1,out t2 with
      | Type i, Type j  -> level_lt i j
      | Sg (a,(x,b)), Sg (a',(x',b')) ->
        let (_,b) = unbind (x,b) in
        let (_,b') = unbind (x',b') in
        sub c a a' && sub c b b'
      | Pi (a,(x,b)), Pi (a',(x',b')) ->
        let (_,b) = unbind (x,b) in
        let (_,b') = unbind (x',b') in
        sub c a' a && sub c b b'
      | Id (a,_,_), Id (a',_,_) -> sub c a a'
      | _ -> false

let synthtype s = synth (s,Context.empty)