open Core
open Ast
open Dynamics


exception Unsolved of string
exception SynthFailed of string
exception CheckFailed of string



let (++) (s,v,g) (key,data) = (s,key::v,Context.set g ~key ~data)


let resolve_lam_pi_binders (x,e) (y,b) =
  match y with
    | "" -> let (x,e) = unbind (x,e) in x,e,instantiate 0 x b
    | _  -> let (y,b) = unbind (y,b) in y,instantiate 0 y e,b


let rec synth ((s,_,g) as c) ast =
  (* print_endline ("SYNTH "^ pretty ~debug:true ast); *)
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
    | Annot (e,t) -> (try check c t (typ Omega); check c e t; t with CheckFailed e -> raise @@ SynthFailed e)
    | J (a,b,prf) ->
      begin
      match out (beta s (synth c prf)) with
        | Id (t,m,n) ->
          let (x,y,z,e1) = unbind3 a in
          let (a,e2) = unbind b in
          check (c ++ (x,t) ++ (y,t) ++ (z,id (t,f x,f y))) e1 (typ Omega);
          check (c ++ (a,t)) e2 (e1 |> subst (f a) x |> subst (f a) y |> subst (refl m) z);
          e1 |> subst m x |> subst n y |> subst prf z
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it is not an equality" (span_str prf) (pretty prf) (pretty (into t)))
      end
    | Case (mot,l,r,e) ->
      begin
      match out @@ beta s (synth c e) with
        | Sum (t1,t2) ->
          let (a,mot) = unbind mot in
          let (x,l) = unbind l in
          let (y,r) = unbind r in
          check (c ++ (a,sum (t1,t2))) mot (typ Omega);
          check (c ++ (x,t1)) l (subst (inj1 (f x)) a mot);
          check (c ++ (y,t2)) r (subst (inj2 (f y)) a mot);
          subst e a mot
        | t -> raise @@ SynthFailed(sprintf "%s - %s has type %s, it cannot be cased on" (span_str e) (pretty e) (pretty (into t)))
      end
    | OneInd (mot,e1,e) ->
      begin
      match out @@ beta s (synth c e) with
        | One ->
          let (a,mot) = unbind mot in
          check c e1 (subst unit a mot);
          subst e a mot
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be One-cased on" (span_str e) (pretty e) (pretty (into t)))
      end
    | ZeroInd (mot,e) ->
      begin
      match out @@ beta s (synth c e) with
        | Zero -> mot
        | t -> raise @@ SynthFailed (sprintf "%s - %s has type %s, it cannot be Zero-cased on" (span_str e) (pretty e) (pretty (into t))) 
      end
    | Meta {sol = Some e; _} -> synth c e
    | Meta {sol = None; _} -> raise @@ Unsolved "Unknown Type"
    | _ -> raise @@ SynthFailed (sprintf "%s - Cannot synthesize a type for %s" (span_str ast) (pretty ast))
  
  and check ((s,v,g) as c) ast t =
    (* print_endline ("CHECK "^ pretty ~debug:true ast ^ " AT " ^ pretty ~debug:true t); *)
    let t = beta s t in
    match out @@ ast, out @@ t with
      | Type i, Type j -> if not (level_lt i j) then raise @@ CheckFailed (sprintf "%s - %s too large to be contained in %s" (span_str ast) (pretty ast) (pretty t))
      | One, Type _ -> ()
      | Unit, One -> ()
      | Zero, Type _ -> ()
      | (Pi (a,b) | Sg (a,b)), Type i ->
        let (x,b) = unbind b in
        check c a (typ i); check (c ++ (x,a)) b (typ i)
      | Id (t,m,n) , Type i ->
        check c t (typ i);
        check c m t;
        check c n t 
      | Lam (x,e), Pi (a,(y,b)) ->
        let x,e,b = resolve_lam_pi_binders (x,e) (y,b) in
        check (c ++ (x,a)) e b
      | Pair (e1,e2), Sg (a, b) ->
        let (x,b) = unbind b in
        check c e1 a; check c e2 (subst e1 x b)
      | Refl r, Id (_,x,y) ->
        if not @@ beta_equal s x y then raise @@ CheckFailed (sprintf "%s - %s and %s are not equal, they cannot be identified" (span_str ast) (pretty x) (pretty y));
        begin
        match out r with
          | Meta m -> m.sol <- Some (bindn (List.rev v) x)
          | _ ->
        if not @@ beta_equal s x r then raise @@ CheckFailed (sprintf "%s - %s and %s are not equal, they cannot be identified" (span_str ast) (pretty x) (pretty r));
        end
      | Sum (a,b), Type _ ->
        check c a t;
        check c b t
      | Inj1 e, Sum (a,_) ->
        check c e a
      | Inj2 e, Sum (_,b) ->
        check c e b
      | Case ((a,In (Meta ({sol = None;_} as m),_)),l,r,e),_ ->
        let mot = subst_ast (f a) e (copy t) in
        m.sol <- Some (bindn (List.rev (a::v)) mot);
        check c (mark_as ast @@ case ((a,bind a mot),l,r,e)) t
      | OneInd ((a,In (Meta ({sol = None;_} as m),_)),e1,e),_ ->
        let mot = subst_ast (f a) e (copy t) in
        m.sol <- Some (bindn (List.rev (a::v)) mot); 
        check c (mark_as ast @@ one_ind ((a,bind a mot),e1,e)) t
      | J ((x,y,z,In (Meta ({sol = None;_} as m),_)),e1,prf),_ ->
        begin
        match out (beta s (synth c prf)) with
          | Id (_,a,b) ->
            let mot = t |> copy |> subst_ast (f x) a |> subst_ast (f y) b |> subst_ast (f z) prf in
            m.sol <- Some (bindn (List.rev (z::y::x::v)) mot);
            check c (mark_as ast @@ j ((x,y,z,bind3 (x,y,z) mot),e1,prf)) t
          | t -> raise @@ CheckFailed (sprintf "%s - %s has type %s, it is not an equality" (span_str prf) (pretty prf) (pretty (into t)))
        end
      | ZeroInd (In (Meta ({sol = None; _} as m),_),_),_ ->
        m.sol <- Some (bindn (List.rev v) (copy t))
      | Meta {sol = Some e; _},_ -> check c e t
      | Meta {sol = None;_}, _ -> raise @@ Unsolved (sprintf "Context:%s\n\nGoal:\n%s" (pp_context g) (pretty t))
      | _ ->
        let a = beta s @@ synth c ast in
        if not @@ sub s a t then
        raise @@ CheckFailed (sprintf "%s - Expected %s to have type %s, but it has type %s" (span_str ast) (pretty ast) (pretty t) (pretty a))


  and sub s t1 t2 = if beta_equal s t1 t2 then true else
    match out t1,out t2 with
      | Type i, Type j  -> level_lt i j
      | Sg (a,(x,b)), Sg (a',(x',b')) ->
        let (_,b) = unbind (x,b) in
        let (_,b') = unbind (x',b') in
        sub s a a' && sub s b b'
      | Pi (a,(x,b)), Pi (a',(x',b')) ->
        let (_,b) = unbind (x,b) in
        let (_,b') = unbind (x',b') in
        sub s a' a && sub s b b'
      | Id (a,_,_), Id (a',_,_) -> sub s a a'
      | _ -> false

let synthtype s = synth (s,[],Context.empty)