open Core
open Core_tt
open Value
open Env

let add3 used (x,y,z) = String.Set.add (String.Set.add (String.Set.add used x) y) z

let rec eval (sg : normal Env.t) (env : value Env.t) (e : term) : value =
  (* print_endline ("EVAL "^pp_term e); *)
  match e with
    | Var x -> 
      begin
        match Env.find env x with
          | Some e -> e
          | None -> (Env.find_exn sg x).tm
      end
    | Lift (x,i) -> eval sg env @@ lift i @@ read_back_normal sg (Env.key_set env) (Env.find_exn sg x)
    | One -> VOne
    | Unit -> VUnit
    | Lam (name,body) -> VLam {env ; name ; body}
    | Pi (t,(name,body)) -> VPi (eval sg env t,{env ; name ; body})
    | Type i -> VType i
    | App (e1,e2) -> do_app sg (eval sg env e1) (eval sg env e2)
    | Sg (t,(name,body)) -> VSg (eval sg env t,{env ; name ; body})
    | Pair (e1,e2) -> VPair (eval sg env e1, eval sg env e2)
    | Proj1 e -> do_proj1 sg (eval sg env e)
    | Proj2 e -> do_proj2 sg (eval sg env e)
    | Id (t,e1,e2) -> VId (eval sg env t,eval sg env e1, eval sg env e2)
    | Refl e -> VRefl (eval sg env e)
    | J {mot ; case ; scrut} -> do_j sg env mot case (eval sg env scrut)
    | Sum (e1,e2) -> VSum (eval sg env e1, eval sg env e2)
    | Inj1 e -> VInj1 (eval sg env e)
    | Inj2 e -> VInj2 (eval sg env e)
    | Case {mot ; case1 ; case2 ; scrut} ->
      do_case sg env mot case1 case2 (eval sg env scrut)
    | Zero -> VZero
    | ZeroInd {mot ; scrut} -> do_zero_ind (eval sg env mot) (eval sg env scrut)
    | Let (e1,(x,e2)) -> eval sg (env ++ (x,eval sg env e1)) e2

  and do_app (sg : normal Env.t) (v1 : value) (v2 : value) : value =
    match v1 with
      | VLam c -> eval_closure sg c v2
      | VNeutral {ty = VPi (t,c) ; neu} ->
        VNeutral {neu = NApp (neu,{ty = t; tm = v2}) ; ty = eval_closure sg c v2}
      | VPi _ -> failwith "A type"
      | _ -> failwith "Should be caught by type checker - app"

 
  and do_proj1 (_ : normal Env.t) (v : value) : value =
    match v with
      | VPair (e,_) -> e
      | VNeutral {ty = VSg (t,_) ; neu} ->
        VNeutral {ty = t ; neu = NProj1 neu}
      | _ -> failwith "Should be caught by type checker - proj1"

  and do_proj2 (sg : normal Env.t) (v : value) : value =
    match v with
      | VPair (_,e) -> e
      | VNeutral {ty = VSg (_,c) ; neu} ->
        VNeutral {ty = eval_closure sg c (do_proj1 sg v) ; neu = NProj2 neu}
      | _ -> failwith "Should be caught by type checker - proj2"

  and do_j (sg : normal Env.t) (env : value Env.t) ((x,y,z,mot) : term binder3) ((a,case) : term binder) (scrut : value) : value = 
    match scrut with
      | VRefl v -> eval sg (env ++ (a,v)) case
      | VNeutral {ty = VId (t,e1,e2) ; neu} ->
        VNeutral {ty = eval sg (env ++ (x,e1) ++ (y,e2) ++ (z,scrut)) mot ; 
                  neu = NJ {mot = {env ; names = (x,y,z) ; body = mot} ; 
                            case = {env ; name = a ; body = case} ;
                            ty = t;
                            left = e1;
                            right = e2;
                            scrut = neu
                           }
                  }
      | _ -> failwith "Should be caught by type checker - j"

  and do_case (sg : normal Env.t) (env : value Env.t) ((x,mot) : term binder) ((a,case1) : term binder) ((b,case2) : term binder) (scrut : value) : value =
    match scrut with
      | VInj1 e -> eval sg (env ++ (a,e)) case1
      | VInj2 e -> eval sg (env ++ (b,e)) case2
      | VNeutral {ty = VSum (e1,e2) ; neu} ->
        VNeutral {ty = eval sg (env ++ (x,scrut)) mot ;
                  neu = NCase {mot = {env ; name = x ; body = mot} ;
                               case1 = {env ; name = a; body = case1} ;
                               case2 = {env ; name = b; body = case2} ;
                               left = e1;
                               right = e2;
                               scrut = neu
                              }
                  }
      | _ -> failwith "Should be caught by type checker - case"

  and do_zero_ind (mot : value) (scrut : value) =
    match scrut with
      | VNeutral {ty = VZero ; neu} ->
        VNeutral {ty = mot ; neu = NZeroInd {mot = mot ; scrut = neu}}
      | _ -> failwith "Should be caught by type checker - zero_ind"


  and eval_closure (sg : normal Env.t) ({env ; name ; body} : closure) (v : value) : value =
    eval sg (env ++ (name,v)) body

  and eval_closure3 (sg : normal Env.t)({env ; names = (x,y,z) ; body} : closure3) (v1,v2,v3 : value * value * value) : value =
    eval sg (env ++ (x,v1) ++ (y,v2) ++ (z,v3)) body

and read_back (sg : normal Env.t) (used : String.Set.t) (ty : value) (v : value) : term =
  match ty,v with
    | VType _,VType j -> Type j
    | VType i,VPi (t,c) ->
      let x = freshen used (closure_name c) in
      let x_val = VNeutral {neu = NVar x ; ty = t} in
      Pi (read_back sg used (VType i) t, (x,read_back sg (String.Set.add used x) (VType i) (eval_closure sg c x_val)))
    | VType i,VSg (t,c) ->
      let x = freshen used (closure_name c) in
      let x_val = VNeutral {neu = NVar x ; ty = t} in
      Sg (read_back sg used (VType i) t, (x,read_back sg (String.Set.add used x) (VType i) (eval_closure sg c x_val)))
    | VPi (t,({name = "_" ; _} as c)), (VLam c' as f) ->
      let x = freshen used (closure_name c') in
      let x_val = VNeutral {neu = NVar x ; ty = t} in
      Lam (x,read_back sg (String.Set.add used x) (eval_closure sg c x_val) (do_app sg f x_val))
    | VPi (t,({name = "_" ; _} as c)), f ->
      let x = freshen used "x" in
      let x_val = VNeutral {neu = NVar x ; ty = t} in
      Lam (x,read_back sg (String.Set.add used x) (eval_closure sg c x_val) (do_app sg f x_val))
    | VPi (t,c), f ->
      let x = freshen used (closure_name c) in
      let x_val = VNeutral {neu = NVar x ; ty = t} in
      Lam (x,read_back sg (String.Set.add used x) (eval_closure sg c x_val) (do_app sg f x_val))
    | VSg (t,c), p ->
      let p1 = do_proj1 sg p in
      Pair (read_back sg used t p1, read_back sg used (eval_closure sg c p1) (do_proj2 sg p))
    | VType _, VOne -> One
    | VOne, _ -> Unit
    | VType i,VId (t,e1,e2) -> Id (read_back sg used (VType i) t,read_back sg used t e1, read_back sg used t e2)
    | VId (t,_,_), VRefl e -> Refl (read_back sg used t e)
    | VType i,VSum (e1,e2) -> Sum (read_back sg used (VType i) e1, read_back sg used (VType i) e2)
    | VSum (e1,_),VInj1 e -> Inj1 (read_back sg used e1 e)
    | VSum (_,e2),VInj2 e -> Inj2 (read_back sg used e2 e)
    | VType _,VZero -> Zero
    | _,VNeutral {neu ; _} -> read_back_neutral sg used neu
    | _ -> failwith "Should be caught by type checker - read_back"

  and read_back_neutral (sg : normal Env.t) (used : String.Set.t) (neu : neutral) : term =
    match neu with
      | NVar x -> Var x
      | NApp (neu,norm) -> App (read_back_neutral sg used neu,read_back_normal sg used norm)
      | NProj1 neu -> Proj1 (read_back_neutral sg used neu)
      | NProj2 neu -> Proj2 (read_back_neutral sg used neu)
      | NJ {mot ; case ; ty ; left = _; right = _ ; scrut} ->
        let x,y,z = freshen3 used (closure3_names mot) in
        let x_val = VNeutral {ty ; neu = NVar x} in
        let y_val = VNeutral {ty ; neu = NVar y} in
        let z_val = VNeutral {ty = VId (ty,x_val,y_val) ; neu = NVar z} in
        let a = freshen used (closure_name case) in
        let a_val = VNeutral {ty ; neu = NVar a} in
        let mot' = read_back sg (add3 used (x,y,z)) (VType Omega) (eval_closure3 sg mot (x_val,y_val,z_val)) in
        let case' = read_back sg (String.Set.add used a) (eval_closure3 sg mot (a_val,a_val,VRefl a_val)) (eval_closure sg case a_val) in
        J {mot = (x,y,z,mot') ; case = (a,case') ; scrut = read_back_neutral sg used scrut}

      | NCase {mot ; case1 ; case2 ; left ; right ; scrut} ->
        let x = freshen used (closure_name mot) in
        let a = freshen used (closure_name case1) in
        let b = freshen used (closure_name case2) in
        let x_val = VNeutral {ty = VSum (left,right) ; neu = NVar x} in
        let a_val = VNeutral {ty = left ; neu = NVar a} in
        let b_val = VNeutral {ty = right ; neu = NVar b} in
        let mot' = read_back sg (String.Set.add used x) (VType Omega) (eval_closure sg mot x_val) in
        let case1' = read_back sg (String.Set.add used a) (eval_closure sg mot (VInj1 a_val)) (eval_closure sg case1 a_val) in
        let case2' = read_back sg (String.Set.add used b) (eval_closure sg mot (VInj2 b_val)) (eval_closure sg case2 b_val) in
        Case {mot = (x,mot') ; case1 = (a,case1') ; case2 = (b,case2') ; scrut = read_back_neutral sg used scrut}

      | NZeroInd {mot ; scrut} -> ZeroInd {mot = read_back sg used (VType Omega) mot ; scrut = read_back_neutral sg used scrut}

  and read_back_normal (sg : normal Env.t) (used : String.Set.t) ({tm ; ty} : normal) : term =
    read_back sg used ty tm