open Core
open Ast
open Dynamics


exception Unsolved of string
exception SynthFailed of string
exception CheckFailed of string

let assuming _ = ()

let rec sub t1 t2 =
  match out t1,out t2 with
    | Type i, Type j  -> i < j
    | Bind (Sigma a,(x,b)), Bind (Sigma a',(x',b')) ->
      let (_,b) = unbind (x,b) in
      let (_,b') = unbind (x',b') in
      sub a a' && sub b b'
    | Bind (Pi a,(x,b)), Bind (Pi a',(x',b')) ->
      let (_,b) = unbind (x,b) in
      let (_,b') = unbind (x',b') in
      sub a' a && sub b b'
    | _ -> false



let resolve_lam_pi_binders (x,e) (y,b) =
  match y with
    | "" -> let (x,e) = unbind (x,e) in x,e,instantiate x b
    | _  -> let (y,b) = unbind (y,b) in y,instantiate y e,b


let rec synth ((s,g) as c) ast =
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
        | Bind (Pi a, b) -> 
          let (x,b) = unbind b in
          check c e2 a; subst e2 x b 
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be applied" (span_str ast) (pretty e1) (pretty (into t)))
      end
    | Proj1 e ->
      begin
      match out (beta s (synth c e)) with
        | Bind (Sigma a,_) -> a
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be projected from" (span_str e) (pretty e) (pretty (into t)))
      end
    | Proj2 e ->
      begin
      match out (beta s (synth c e)) with
        | Bind (Sigma _,b) -> 
          let (x,b) = unbind b in 
          subst (proj1 e) x b
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be projected from" (span_str e) (pretty e) (pretty (into t)))
      end
    | Annot (e,t) -> (try check c e t; t with CheckFailed e -> raise @@ SynthFailed e)
    | _ -> raise @@ SynthFailed (sprintf "%s - Cannot synthesize a type for %s" (span_str ast) (pretty ast))
  
  and check ((s,g) as c) e t =
    assuming @@ is_type c t;
    match out @@ e, out @@ beta s t with
      | Meta _, t -> raise @@ Unsolved (pretty (into t))
      | Type i, Type j -> if i >= j then raise @@ CheckFailed (sprintf "%s - Type%i to large to be contained in Type%i" (span_str e) i j)
      | Bind ((Pi a | Sigma a),b), Type i ->
        let (x,b) = unbind b in
        check c a (typ i); check (s,(g ++ (x,a))) b (typ i)
      | Bind (Lam, (x,e)), Bind (Pi a,(y,b)) ->
        let x,e,b = resolve_lam_pi_binders (x,e) (y,b) in
        check (s,g ++ (x,a)) e b
      | Pair (e1,e2), Bind (Sigma a, b) ->
        let (x,b) = unbind b in
        check c e1 a; check c e2 (subst e1 x b)
      | _ ->
        let a = 
          try synth c e with 
            | SynthFailed _ -> raise @@ CheckFailed (sprintf "%s - Failed to check %s against type %s" (span_str e) (pretty e) (pretty t))
         in
        if not @@ (beta_equal s a t || sub (beta s a) (beta s t)) then
        raise @@ CheckFailed (sprintf "%s - Expected %s to have type %s, but it has type %s" (span_str e) (pretty e) (pretty t) (pretty a))

  and is_type (s,g) ast =
    match out ast with
      | Type _ -> ()
      | Bind ((Pi a | Sigma a),b) ->
        let (x,b) = unbind b in
        is_type (s,g) a; is_type (s,(g ++ (x,a))) b
      | _ -> is_type' (beta s @@ synth (s,g) ast)
  
  and is_type' ast =
    match out ast with
      | Type _ -> ()
      | _ -> raise @@ CheckFailed (sprintf "%s - Expected %s to be a type" (span_str ast) (pretty ast))


let synthtype s = synth (s,Context.empty)