open Core
open Ast
open Statics
open Dynamics

let parse s = 
  let lexbuf = Lexing.from_string s in
  Parser.init Lexer.initial lexbuf


let parse_file s =
  let p = Stdlib.open_in s in
  let lexbuf = Lexing.from_channel p in
  Parser.init Lexer.initial lexbuf

let run_stm (g,d) = function
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
    printf "%s : %s\n" x (pretty @@ t');
    printf "%s = %s\n\n" x (pretty @@ e');
    (g ++ (x,t'),d ++ (x,e'))

let rec repl (g,d) = 
  print_string "-- ";
  let s = Stdlib.read_line () in
  if String.equal s "" then repl (g,d);
  try repl @@ List.fold (parse s) ~init:(g,d) ~f:run_stm with 
    | TypeError e -> printf "Type Error: %s\n" e;repl (g,d)



let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl (Context.empty,Context.empty);
  let s = parse_file args.(1) in
  repl @@ List.fold s ~init:(Context.empty,Context.empty) ~f:run_stm
