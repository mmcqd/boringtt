open Core
open Ast
open Eval
open Typechecker

exception ParseError of string

let parse s = 
  let lexbuf = Lexing.from_string s in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s:%s" (show_loc s) (show_loc e))

let parse_file s =
  let p = Stdlib.open_in s in
  let lexbuf = Lexing.from_channel p in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s:%s" (show_loc s) (show_loc e))


let run_stm sg = function
  | Eval e ->
    let t = synthtype sg e in 
    let e' = eval sg Env.empty e in
    printf "_ : %s\n" (pp_term (read_back sg String.Set.empty (VType Omega) t));
    printf "_ = %s\n\n" (pp_term (read_back sg String.Set.empty t e'));
    sg
  | Decl (x,e) -> 
    let t = synthtype sg e in
    let e' = eval sg Env.empty e in
    let public_t = (match e with Ascribe (_,t) -> t | _ -> read_back sg String.Set.empty (VType Omega) t) in
    printf "%s : %s\n\n" x (pp_term public_t);
    (* printf "%s = %s\n\n" x (pp_term (read_back sg String.Set.empty t e')); *)
    sg ++ (x, {tm = e' ; ty = t})



let rec repl s = 
  print_string "-- ";
  let txt = Stdlib.read_line () in
  if String.equal txt "" then repl s;
  try repl @@ List.fold (parse txt) ~init:s ~f:run_stm with 
    | TypeError e -> printf "Type Error: %s\n" e;repl s
    | ParseError e -> printf "Parse Error: %s\n" e; repl s
    | Unsolved e -> printf "Unsolved Meta-Var\n%s" e; repl s



let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl Env.empty;
  let s = parse_file args.(1) in
  try repl @@ List.fold s ~init:Env.empty ~f:run_stm with 
      | TypeError e -> printf "Type Error: %s\n" e
      | ParseError e -> printf "Parse Error: %s\n" e
      | Unsolved e -> printf "Unsolved Meta-Var\n%s" e
