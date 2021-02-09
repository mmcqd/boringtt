open Core
open Syntax
open Core_tt
open Value
open Eval
open Env

exception TypeError of string
exception ParseError of string

let pp_ty (sg : normal Env.t) (ctx : value Env.t) (t : value) : string =
  pp_term @@ read_back sg (Env.key_set ctx) (VType Omega) t

let parse_refinement s = 
  let lexbuf = Lexing.from_string s in
  try 
    match Parser.init Lexer.initial lexbuf with
      | [Eval e] -> e
      | _ -> raise @@ ParseError "Refinement must be a term"
  with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s:%s" (show_loc s) (show_loc e))



let rec elab_synth (sg : Value.normal Env.t) (ctx : Value.t Env.t) (tm : Syntax.t) : Core_tt.t * Value.t =
  (* print_endline @@ "SYNTH " ^ Syntax.show_term tm; *)
  match tm with
    | Var x ->
      begin
      match Env.find ctx x with
        | Some ty -> Var x,ty
        | None ->
          match Env.find sg x with
            | Some {ty ; _} -> Var x,ty
            | None -> raise @@ TypeError (sprintf "Unbound variable: %s" x)
      end
    | Lift (x,i) ->
      begin
      match Env.find sg x with
        | Some {ty ; _} -> Lift (x,i), eval sg (ctx_to_env ctx) (lift i (read_back sg (Env.key_set ctx) (VType Omega) ty))
        | None -> raise @@ TypeError (sprintf "Cannot lift non-top level definition: %s" x)
      end
    | Spine (e,Nil) -> elab_synth sg ctx e
    | Spine (e,Snoc (spine,arg)) ->
      begin
      match elab_synth sg ctx (Spine (e,spine)) with
        | sp', VPi (dom,ran) ->
          let arg' = elab_check sg ctx arg dom in
          App (sp',arg'),eval_closure sg ran (eval sg (ctx_to_env ctx) arg')
        | sp',t -> raise @@ TypeError (sprintf "%s has type %s, it is not a function, it cannot be applied" (pp_term sp') (pp_ty sg ctx t))
      end
    | Proj1 e ->
      begin
      match elab_synth sg ctx e with
        | e',VSg (fst,_) -> Proj1 e',fst
        | e',t -> raise @@ TypeError (sprintf "%s has type %s, it is not a tuple, it cannot be projected from" (pp_term e') (pp_ty sg ctx t))
      end
    | Proj2 e ->
      begin
      match elab_synth sg ctx e with
        | e',VSg (_,snd) -> Proj2 e',eval_closure sg snd (do_proj1 sg (eval sg (ctx_to_env ctx) e'))
        | e',t -> raise @@ TypeError (sprintf "%s has type %s, it is not a tuple, it cannot be projected from" (pp_term e') (pp_ty sg ctx t))
      end
    | J {mot = Some (x,y,z,mot) ; case = (a,case) ; scrut} ->
      begin
      match elab_synth sg ctx scrut with
        | scrut',VId (t,e1,e2) ->
          let env = ctx_to_env ctx in
          let x_val = VNeutral {ty = t ; neu = NVar x} in
          let y_val = VNeutral {ty = t ; neu = NVar y} in
          let a_val = VNeutral {ty = t ; neu = NVar a} in
          let mot' = elab_check sg (ctx ++ (x,t) ++ (y,t) ++ (z,VId (t,x_val,y_val))) mot (VType Omega) in
          let case' = elab_check sg (ctx ++ (a,t)) case (eval sg (env ++ (x,a_val) ++ (y,a_val) ++ (z,VRefl a_val)) mot') in
          J {mot = (x,y,z,mot') ; case = (a,case') ; scrut = scrut'}, eval sg (env ++ (x,e1) ++ (y,e2) ++ (z,eval sg env scrut')) mot'

        | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not an equality proof, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
      end
    | Case {mot = Some (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} ->
      begin
      match elab_synth sg ctx scrut with
        | scrut',VSum (e1,e2) -> 
          let env = ctx_to_env ctx in
          let a_val = VNeutral {ty = e1 ; neu = NVar a} in
          let b_val = VNeutral {ty = e2 ; neu = NVar b} in    
          let mot' = elab_check sg (ctx ++ (x,VSum (e1,e2))) mot (VType Omega) in
          let case1' = elab_check sg (ctx ++ (a,e1)) case1 (eval sg (env ++ (x,VInj1 a_val)) mot') in
          let case2' = elab_check sg (ctx ++ (b,e2)) case2 (eval sg (env ++ (x,VInj2 b_val)) mot') in
          Case {mot = (x,mot') ; case1 = (a,case1') ; case2 = (b,case2') ; scrut = scrut'},eval sg (env ++ (x,eval sg env scrut')) mot'
           
        | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not a sum, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
      end
    | ZeroInd {mot = Some mot; scrut} ->
      begin
      match elab_synth sg ctx scrut with
        | scrut',VZero -> 
          let mot' = elab_check sg ctx mot (VType Omega) in
          ZeroInd {mot = mot' ; scrut = scrut'},eval sg (ctx_to_env ctx) mot'
        | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not in Zero, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
      end
    | Let (e1,(x,e2)) ->
      let e1',t = elab_synth sg ctx e1 in
      let e2',t2 = elab_synth sg (ctx ++ (x,t)) e2 in
      Let (e1',(x,e2')),t2
    | Ascribe (e,t) -> 
      let t' = elab_check sg ctx t (VType Omega) in
      let t' = eval sg (ctx_to_env ctx) t' in
      let e' = elab_check sg ctx e t' in
      e',t'
    | _ -> raise @@ TypeError "Failed to synthesize/elaborate"

    

  and elab_check (sg : Value.normal Env.t) (ctx : Value.t Env.t) (tm : Syntax.t) (ty : Value.t) : Core_tt.t =
    (* print_endline @@ "CHECK " ^ Syntax.show_term tm ^ " AT " ^ pp_ty sg ctx ty; *)
    match tm,ty with
      | Meta ,_ ->
        let ctx' = Env.map ctx ~f:(read_back sg (Env.key_set ctx) (VType Omega)) in
        printf "\nHole:%s\n\n%s\n  %s\n" (pp_context ctx') (String.init ~f:(const '-') 45) (pp_ty sg ctx ty);
        let rec interactive () =
          print_string "\nRefinement: ";
          let txt = Stdlib.read_line () in
          match txt with
            | "" -> interactive ()
            | _ -> 
            let r = parse_refinement txt in
            elab_check sg ctx r ty
        in interactive ()
      | Type i,VType j -> 
        if Level.(<) i j then Type i else
        raise @@ TypeError (sprintf "%s too large to be contained in %s" (pp_term (Type i)) (pp_ty sg ctx ty))
      | Pi ([],ran),VType i -> elab_check sg ctx ran (VType i)
      | Pi ((x,t)::tele,ran),VType i ->
        let t' = elab_check sg ctx t (VType i) in
        let pi = elab_check sg (ctx ++ (x,eval sg (ctx_to_env ctx) t')) (Pi (tele,ran)) (VType i) in
        Pi (t',(x,pi)) 
      | Sg ([],last),VType i -> elab_check sg ctx last (VType i)
      | Sg ((x,t)::tele,last),VType i ->
        let t' = elab_check sg ctx t (VType i) in
        let sg = elab_check sg (ctx ++ (x,eval sg (ctx_to_env ctx) t')) (Sg (tele,last)) (VType i) in
        Sg (t',(x,sg))
      | Lam ([],e),_ -> elab_check sg ctx e ty
      | Lam (x::xs,e),VPi (dom,ran) ->
        let x_val = VNeutral {neu = NVar x ; ty = dom} in
        let e' = elab_check sg (ctx ++ (x,dom)) (Lam (xs,e)) (eval_closure sg ran x_val) in
        Lam (x,e')
      | Tuple [],VOne -> Unit
      | Tuple [e],_ -> elab_check sg ctx e ty
      | Tuple (e::es),VSg (fst,snd) ->
        let e' = elab_check sg ctx e fst in
        let es' = elab_check sg ctx (Tuple es) (eval_closure sg snd (eval sg (ctx_to_env ctx) e')) in
        Pair (e',es')
      | One, VType _ -> One
      | Zero,VType _ -> Zero
      | Id (t,e1,e2),VType i ->
        let t' = elab_check sg ctx t (VType i) in
        let t'v = eval sg (ctx_to_env ctx) t' in
        let e1' = elab_check sg ctx e1 t'v in
        let e2' = elab_check sg ctx e2 t'v in
        Id (t',e1',e2')
      | Refl e, VId (t,e1,e2) ->
        let used = Env.key_set ctx in
        let e1',e2' = read_back sg used t e1,read_back sg used t e2 in
        if not @@ alpha_equiv e1' e2' then raise @@ TypeError (sprintf "%s and %s are not equal, they cannot be identified" (pp_term e1') (pp_term e2'));
        begin
        match e with
          | Meta -> 
            Refl e1'
          | _ ->
            let e' = elab_check sg ctx e t in
            if not @@ alpha_equiv (read_back sg used t (eval sg (ctx_to_env ctx) e')) e1' then 
              raise @@ TypeError (sprintf "%s and %s are not equal, they cannot be identified" (pp_term e') (pp_term e1'));
            Refl e'
        end
      | Sum (t1,t2),VType i ->
        Sum (elab_check sg ctx t1 (VType i),elab_check sg ctx t2 (VType i))
      | Inj1 e,VSum (t1,_) ->
        Inj1 (elab_check sg ctx e t1)
      | Inj2 e, VSum (_,t2) ->
        Inj2 (elab_check sg ctx e t2)
      | J {mot = None ; case = (a,case) ; scrut},_ ->
        begin
        match elab_synth sg ctx scrut with
          | scrut',VId (t,e1,e2) ->
            let used = Env.key_set ctx in
            let x,y,z = fresh_var (),fresh_var (),fresh_var () in
            let mot' = ty |> read_back sg used (VType Omega) |> 
                            replace_term (read_back sg used t e1) (Var x) |> 
                            replace_term (read_back sg used t e2) (Var y) |> 
                            replace_term scrut' (Var z) in
            let env = ctx_to_env ctx in
            let a_val = VNeutral {ty = t ; neu = NVar a} in
            let case' = elab_check sg (ctx ++ (a,t)) case (eval sg (env ++ (x,a_val) ++ (y,a_val) ++ (z,VRefl a_val)) mot') in
            J {mot = (x,y,z,mot') ; case = (a,case') ; scrut = scrut'}
          | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not an equality proof, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
        end
      | Case {mot = None ; scrut ; case1 = (a,case1) ; case2 = (b,case2)},_ ->
        begin
        match elab_synth sg ctx scrut with
          | scrut',VSum (e1,e2) ->
            let x = fresh_var () in
            let mot' = replace_term scrut' (Var x) (read_back sg (Env.key_set ctx) (VType Omega) ty) in
            let env = ctx_to_env ctx in
            let a_val = VNeutral {ty = e1 ; neu = NVar a} in
            let b_val = VNeutral {ty = e2 ; neu = NVar b} in    
            let case1' = elab_check sg (ctx ++ (a,e1)) case1 (eval sg (env ++ (x,VInj1 a_val)) mot') in
            let case2' = elab_check sg (ctx ++ (b,e2)) case2 (eval sg (env ++ (x,VInj2 b_val)) mot') in
            Case {mot = (x,mot') ; case1 = (a,case1') ; case2 = (b,case2') ; scrut = scrut'}

          | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not a sum, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
        end
      | ZeroInd {mot = None ; scrut},_ ->
       begin
        match elab_synth sg ctx scrut with
          | scrut',VZero -> 
            ZeroInd {mot = read_back sg (Env.key_set ctx) (VType Omega) ty ; scrut = scrut'}
          | scrut',t -> raise @@ TypeError (sprintf "%s has type %s, it is not in Zero, it cannot be matched on" (pp_term scrut') (pp_ty sg ctx t))
        end
      | Spine (e,Nil),_ ->
        elab_check sg ctx e ty
      | _ ->
        let tm',ty' = elab_synth sg ctx tm in
        if sub sg ctx ty' ty then tm' else
        raise @@ TypeError (sprintf "Expected %s to have to have type %s, but it has type %s" 
          (pp_term tm') (pp_ty sg ctx ty) (pp_ty sg ctx ty'))
  

  and sub (sg : Value.normal Env.t) (ctx : Value.t Env.t) (t1 : Value.t) (t2 : Value.t) : bool =
    let used = Env.key_set ctx in
    if alpha_equiv (read_back sg used (VType Omega) t1) (read_back sg used (VType Omega) t2) then true else
    match t1,t2 with
      | VType i, VType j -> Level.(<) i j
      | VPi (t,c), VPi (t',c') ->
        let used = Env.key_set ctx in
        let x,x' = freshen used (closure_name c),freshen used (closure_name c') in
        sub sg ctx t' t &&
        sub sg ctx (eval_closure sg c (VNeutral {ty = t ; neu = NVar x})) (eval_closure sg c (VNeutral {ty = t' ; neu = NVar x'}))
      | VSg (t,c),VSg (t',c') -> 
        let used = Env.key_set ctx in
        let x,x' = freshen used (closure_name c),freshen used (closure_name c') in
        sub sg ctx t t' &&
        sub sg ctx (eval_closure sg c (VNeutral {ty = t ; neu = NVar x})) (eval_closure sg c (VNeutral {ty = t' ; neu = NVar x'}))
      | VSum (e1,e2),VSum(e1',e2') ->
        sub sg ctx e1 e1' &&
        sub sg ctx e2 e2'
      | VId (t,e1,e2),VId (t',e1',e2') ->
        sub sg ctx t t' &&
        alpha_equiv (read_back sg used t e1) (read_back sg used t' e1') &&
        alpha_equiv (read_back sg used t e2) (read_back sg used t' e2')
      | _ -> false


let elaborate (sg : Value.normal Env.t) (e : Syntax.t) : Value.t * Value.t = 
  let e',t = elab_synth sg Env.empty e in
  eval sg Env.empty e',t