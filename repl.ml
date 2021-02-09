open Core
open! Elab
open! Syntax
open! Core_tt
open! Eval
open! Env

exception ParseError of string

let parse s = 
  let lexbuf = Lexing.from_string s in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s-%s" (show_loc s) (show_loc e))

let parse_file s =
  let p = Stdlib.open_in s in
  let lexbuf = Lexing.from_channel p in
  try Parser.init Lexer.initial lexbuf with
    | _ ->
      let (s,e) = of_position lexbuf.lex_start_p,of_position lexbuf.lex_curr_p in
      raise @@ ParseError (sprintf "%s:%s" (show_loc s) (show_loc e))


let run_stm sg = function
  | Eval e ->
    let e',t = elaborate sg e in 
    printf "_ : %s\n" (pp_term (read_back sg String.Set.empty (VType Omega) t));
    printf "_ = %s\n\n" (pp_term (read_back sg String.Set.empty t e'));
    sg
  | Decl (x,e) -> 
    let e',t = elaborate sg e in
    printf "def %s \n\n" x;
    sg ++ (x, {tm = e' ; ty = t})
  | Axiom (x,t) ->
    let t' = eval sg Env.empty (elab_check sg Env.empty t (VType Omega)) in
    printf "axiom %s \n\n" x;
    sg ++ (x,{tm = VNeutral {ty = t' ; neu = NVar x} ; ty = t'})


let rec repl s = 
  print_string "-- ";
  let txt = Stdlib.read_line () in
  if String.equal txt "" then repl s;
  try repl @@ List.fold (parse txt) ~init:s ~f:run_stm with 
    | TypeError e -> printf "Type Error: %s\n" e;repl s
    | ParseError e -> printf "Parse Error: %s\n" e; repl s
    (* | Unsolved e -> printf "\n%s\n" e; repl s *)



let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl Env.empty;
  let s = parse_file args.(1) in
  try repl @@ List.fold s ~init:Env.empty ~f:run_stm with 
      | TypeError e -> printf "Type Error: %s\n" e
      | ParseError e -> printf "Parse Error: %s\n" e
      (* | Unsolved e -> printf "\n%s\n" e *)
