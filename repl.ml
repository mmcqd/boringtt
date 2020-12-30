open Core
open Ast
open Statics
open Dynamics
open Unify

let parse s = 
  let lexbuf = Lexing.from_string s in
  Parser.init Lexer.initial lexbuf


let parse_file s =
  let p = Stdlib.open_in s in
  let lexbuf = Lexing.from_channel p in
  Parser.init Lexer.initial lexbuf

let run_stm (g,d) = reset_var_stream (); function
  | Eval e ->
    let e = bind_all e in
    let t = synth (g,d) e in 
    printf "_ : %s\n" (pretty @@ beta d t);
    printf "_ = %s\n\n" (pretty @@ beta d e);
    (g,d)
  | Decl (x,e) -> 
    let e = bind_all e in
    let t = synth (g,d) e in
    let e',t' = beta d e, beta d t in
    printf "%s : %s\n" x (pretty t');
    printf "%s = %s\n\n" x (pretty e');
    (g ++ (x,t'),d ++ (x,e'))
  | Postulate (x,t) ->
    let t' = beta d (bind_all t) in
    printf "postulate %s : %s\n\n" x (pretty t');
    (g ++ (x,t'),d)
    

let rec repl (g,d) = 
  print_string "-- ";
  let s = Stdlib.read_line () in
  if String.equal s "" then repl (g,d);
  try repl @@ List.fold (parse s) ~init:(g,d) ~f:run_stm with 
    | TypeError e -> printf "Type Error: %s\n" e;repl (g,d)
    | Unsolved e  -> printf "Unsolved Meta-var : %s\n" e; repl (g,d)
    | _           -> printf "Parse Error\n"; repl (g,d)


let parse_string e = e |> parse |> List.hd_exn |> (function (Eval e) -> e | _ -> failwith "") |> bind_all

let e1 = parse_string "[x : Type] -> x" 

let e2 = parse_string "Type -> _"

let _ : unit = Int.Map.iteri (unify e1 e2) ~f:(fun ~key ~data -> printf "Meta %s --> %s\n" (Int.to_string key) (show_ast data))

let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl (Context.empty,Context.empty);
  let s = parse_file args.(1) in
  try repl @@ List.fold s ~init:(Context.empty,Context.empty) ~f:run_stm with 
      | TypeError e -> printf "Type Error: %s\n" e
      | Unsolved e  -> printf "Unsolved Meta-var : %s\n" e
      | _           -> printf "Parse Error\n"
