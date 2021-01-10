open Core
open Ast
open Statics
open Dynamics


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


let run_stm s = reset_var_stream (); function
  | Eval e ->
    let e = bind_all e in
    let t = synthtype s e in 
    printf "_ : %s\n" (pretty @@ beta s t);
    printf "_ = %s\n\n" (pretty @@ beta s e);
    s
  | Decl (x,e) -> 
    let e = bind_all e in
    let t = synthtype s e in
    let e',t' = beta s e, beta s t in
    printf "%s : %s\n" x (pretty t');
    printf "%s = %s\n\n" x (pretty e');
    s ++ (x, (e',t'))
  | Postulate (x,t) ->
    let t' = beta s (bind_all t) in
    printf "postulate %s : %s\n\n" x (pretty t');
    s ++ (x, (f x,t'))
    

let rec repl s = 
  print_string "-- ";
  let txt = Stdlib.read_line () in
  if String.equal txt "" then repl s;
  try repl @@ List.fold (parse txt) ~init:s ~f:run_stm with 
    | SynthFailed e | CheckFailed e -> printf "Type Error: %s\n" e;repl s
    | Unsolved e   -> printf "Unsolved Meta-var : %s\n" e; repl s
    | ParseError e -> printf "Parse Error: %s\n" e; repl s


let parse_string e = e |> parse |> List.hd_exn |> (function (Eval e) -> e | _ -> failwith "") |> bind_all

(* let e1 = parse_string "[x : Type] -> x" 

let e2 = parse_string "Type -> _"

let _ : unit = Int.Map.iteri (unify e1 e2) ~f:(fun ~key ~data -> printf "Meta %s --> %s\n" (Int.to_string key) (show_ast data)) *)

let _ : unit = 
  let args = Sys.get_argv () in
  if Array.length args = 1 then repl Context.empty;
  let s = parse_file args.(1) in
  try repl @@ List.fold s ~init:Context.empty ~f:run_stm with 
      | SynthFailed e | CheckFailed e -> printf "Type Error: %s\n" e
      | Unsolved e  -> printf "Unsolved Meta-var : %s\n" e
      | ParseError e -> printf "Parse Error: %s\n" e
