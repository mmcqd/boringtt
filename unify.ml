open Core
open Ast


let unify e1 e2 = 
  let bindings = ref Int.Map.empty in
  let bind x e = bindings := Int.Map.set !bindings ~key:x ~data:e in
  let find = Int.Map.find !bindings in
  let rec loop = function
    | [] -> ()
    | (a,b)::cs ->
      match out a, out b with
        | Meta i, Meta j ->
          begin
          match find i, find j with
            | None, None -> bind i (meta j); loop cs
            | Some x, None -> bind j x; loop cs
            | None, Some y -> bind i y; loop cs
            | Some x, Some y -> loop @@ (x,y)::cs
          end
        | Meta i, y | y, Meta i ->
          begin
          match find i with
            | None -> bind i (into y); loop cs
            | Some x ->
              match out x with
                | Meta j -> bind j (into y); loop cs
                | _ -> loop @@ (x,into y)::cs
          end
        | (Type i, Type j | B i, B j) when i = j -> loop cs
        | F x, F y when equal_var x y -> loop cs
        | Bind ((Pi a | Sigma a),(_,b)), Bind ((Pi a' | Sigma a'),(_,b')) -> loop @@ (a,a')::(b,b')::cs
        | App (a,b), App (a',b') -> loop @@ (a,a')::(b,b')::cs
        | _ -> failwith "Couldn't unify"
  in loop [(e1,e2)]; !bindings


  