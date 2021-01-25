open Core
open Ast
open Eval

exception TypeError of string
exception Unsolved of string

let pp_ty (sg : normal Env.t) (ctx : value Env.t) (t : value) : string =
  pp_term @@ read_back sg (Env.key_set ctx) (VType Omega) t

let rec synth (sg : normal Env.t) (ctx : value Env.t) (tm : term) : value =
  (* print_endline @@ "SYNTH "^ pp_term tm; *)
  match tm with
    | Var x ->
      begin
      match Env.find ctx x with
        | Some ty -> ty
        | None ->
          match Env.find sg x with
            | Some {ty ; _} -> ty
            | None -> raise @@ TypeError (sprintf "Unbound variable: %s" x)
      end
    | Lift (x,i) ->
      begin
      match Env.find sg x with
        | Some {ty ; _} -> eval sg (to_env ctx) (lift i (read_back sg (Env.key_set ctx) (VType Omega) ty))
        | None -> raise @@ TypeError (sprintf "Cannot lift non-top level definition: %s" x)
      end
    | App (e1,e2) ->
      begin
      match synth sg ctx e1 with
        | VPi (t,c) ->
          check sg ctx e2 t;
          eval_closure sg c (eval sg (to_env ctx) e2)
        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not a function, it cannot be applied" (pp_term e1) (pp_ty sg ctx t))
      end
    | Proj1 e ->
      begin
      match synth sg ctx e with
        | VSg (t,_) -> t
        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not a pair, it cannot be projected from" (pp_term e) (pp_ty sg ctx t))
      end
    | Proj2 e -> 
      begin
      match synth sg ctx e with
        | VSg (_,c) -> eval_closure sg c (proj1 sg (eval sg (to_env ctx) e))
        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not a pair, it cannot be projected from" (pp_term e) (pp_ty sg ctx t))
      end

    | J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} ->
      begin
      match synth sg ctx scrut with
        | VId (t,e1,e2) ->
        (* Might need to freshen here, honestly not quite sure *)
          let env = to_env ctx in
          let x_val = VNeutral {ty = t ; neu = NVar x} in
          let y_val = VNeutral {ty = t ; neu = NVar y} in
          let a_val = VNeutral {ty = t ; neu = NVar a} in
          check sg (ctx ++ (x,t) ++ (y,t) ++ (z,VId (t,x_val,y_val))) mot (VType Omega);
          check sg (ctx ++ (a,t)) case (eval sg (env ++ (x,a_val) ++ (y,a_val) ++ (z,VRefl a_val)) mot);
          eval sg (env ++ (x,e1) ++ (y,e2) ++ (z,eval sg env scrut)) mot

        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not an equality proof, it cannot be matched on" (pp_term scrut) (pp_ty sg ctx t))
      end
    | Case {mot = (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} ->
      begin
      match synth sg ctx scrut with
        | VSum (e1,e2) -> 
          let env = to_env ctx in
          let a_val = VNeutral {ty = e1 ; neu = NVar a} in
          let b_val = VNeutral {ty = e2 ; neu = NVar b} in    
          check sg (ctx ++ (x,VSum (e1,e2))) mot (VType Omega);
          check sg (ctx ++ (a,e1)) case1 (eval sg (env ++ (x,VInj1 a_val)) mot);
          check sg (ctx ++ (b,e2)) case2 (eval sg (env ++ (x,VInj2 b_val)) mot);
          eval sg (env ++ (x,eval sg env scrut)) mot
           
        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not a sum, it cannot be matched on" (pp_term scrut) (pp_ty sg ctx t))
      end
    | ZeroInd {mot ; scrut} ->
      begin
      match synth sg ctx scrut with
        | VZero -> eval sg (to_env ctx) mot
        | t -> raise @@ TypeError (sprintf "%s has type %s, it is not in Zero, it cannot be matched on" (pp_term scrut) (pp_ty sg ctx t))
      end
    | Ascribe (e,t) -> 
      check sg ctx t (VType Omega);
      let t' = eval sg (to_env ctx) t in
      check sg ctx e t';
      t'
    | Meta {sol = Some e; _} -> synth sg ctx e
    | _ -> raise @@ TypeError (sprintf "Cannot synthesize a type for %s" (pp_term tm))

  and check (sg : normal Env.t) (ctx : value Env.t) (tm : term) (ty : value) : unit = 
    (* print_endline @@ "CHECK "^ pp_term tm^" AT "^ (pp_ty sg ctx ty); *)
    match tm,ty with
      | Meta {sol = None;_},_ ->
        let ctx' = Env.map ctx ~f:(read_back sg (Env.key_set ctx) (VType Omega)) in
        raise @@ Unsolved (sprintf "Context:%s\n\nGoal:\n  %s" (pp_context ctx') (pp_ty sg ctx ty))
        
      | Type i,VType j -> if not @@ level_lt i j then raise @@ TypeError (sprintf "%s too large to be contained in %s" (pp_term tm) (pp_ty sg ctx ty))
      | (Pi (t,(x,e)) | Sg (t,(x,e))),VType i ->
        check sg ctx t (VType i);
        check sg (ctx ++ (x,eval sg (to_env ctx) t)) e (VType i)
      | Lam (x,e),VPi (t,c) ->
        check sg (ctx ++ (x,t)) e (eval_closure sg c (VNeutral {neu = NVar x ; ty = t}))
      | Pair (e1,e2),VSg (t,c) ->
        check sg ctx e1 t;
        check sg ctx e2 (eval_closure sg c (eval sg (to_env ctx) e1)) 
      | One, VType _ -> ()
      | Unit, VOne -> ()
      | Zero, VType _ -> ()
      | Id (t,e1,e2),VType i ->
        let t' = eval sg (to_env ctx) t in
        check sg ctx t (VType i);
        check sg ctx e1 t';
        check sg ctx e2 t'
      | Refl e, VId (t,e1,e2) ->
        let used = Env.key_set ctx in
        let e1',e2' = read_back sg used t e1,read_back sg used t e2 in
        if not @@ alpha_equiv e1' e2' then raise @@ TypeError (sprintf "%s and %s are not equal, they cannot be identified" (pp_term e1') (pp_term e2'));
        begin
        match e with
          | Meta m -> 
            m.sol <- Some e1'
          | _ ->
            check sg ctx e t;
            let e' = read_back sg used t (eval sg (to_env ctx) e) in
            if not @@ alpha_equiv e' e1' then raise @@ TypeError (sprintf "%s and %s are not equal, they cannot be identified" (pp_term e') (pp_term e1'));
        end
      | J {mot = (x,y,z,Meta ({sol = None;_} as m)); scrut ; _}, _ ->
        begin
        match synth sg ctx scrut with
          | VId (t,e1,e2) ->
            let used = Env.key_set ctx in
            let mot = ty |> read_back sg used (VType Omega) |> 
                            replace_term (read_back sg used t e1) (Var x) |> 
                            replace_term (read_back sg used t e2) (Var y) |> 
                            replace_term scrut (Var z) in
            m.sol <- Some mot;
            check sg ctx tm ty
          | t -> raise @@ TypeError (sprintf "%s has type %s, it is not an equality proof, it cannot be matched on" (pp_term scrut) (pp_ty sg ctx t))
        end
      | Sum (e1,e2), VType i ->
        check sg ctx e1 (VType i);
        check sg ctx e2 (VType i)
      | Inj1 e, VSum (e1,_) ->
        check sg ctx e e1
      | Inj2 e, VSum (_,e2) ->
        check sg ctx e e2
      | Case {mot = (x,Meta ({sol = None; _} as m)) ; scrut ; _},_ ->
        let mot = replace_term scrut (Var x) (read_back sg (Env.key_set ctx) (VType Omega) ty) in
        m.sol <- Some mot;
        check sg ctx tm ty
      | ZeroInd {mot = Meta ({sol = None; _} as m) ; _},_ ->
        m.sol <- Some (read_back sg (Env.key_set ctx) (VType Omega) ty);
        check sg ctx tm ty
      | Meta {sol = Some e;_},_ ->
        check sg ctx e ty
      | _ ->
        let ty' = synth sg ctx tm in
        if sub sg ctx ty' ty then () else
        raise @@ TypeError (sprintf "Expected %s to have to have type %s, but it has type %s" 
          (pp_term tm) (pp_ty sg ctx ty) (pp_ty sg ctx ty'))



  and sub (sg : normal Env.t) (ctx : value Env.t) (t1 : value) (t2 : value) : bool =
    let used = Env.key_set ctx in
    if alpha_equiv (read_back sg used (VType Omega) t1) (read_back sg used (VType Omega) t2) then true else
    match t1,t2 with
      | VType i, VType j -> level_lt i j
      | VPi (t,c), VPi (t',c') ->
        let used = Env.key_set ctx in
        let x,x' = freshen used (closure_name c),freshen used (closure_name c') in
        sub sg ctx t' t &&
        sub sg ctx (eval_closure sg c (VNeutral {ty = t ; neu = NVar x})) (eval_closure sg c (VNeutral {ty = t' ; neu = NVar x'}))
      | _ -> false

let synthtype (sg : normal Env.t) (e : term) : value = 
  synth sg Env.empty e