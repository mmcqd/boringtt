
(* The type of tokens. *)

type token = 
  | Type
  | Star
  | R_paren
  | Let
  | Lambda
  | L_paren
  | Ident of (string)
  | Equal
  | Eof
  | DotTwo
  | DotOne
  | Dec_const of (int)
  | Comma
  | Colon
  | Arrow

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val init: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.stm list)
