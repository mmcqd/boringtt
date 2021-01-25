{

open Core
open Parser

}

let ident = [^ '(' ')' '[' ']' '\\' ':' ',' '=' ' ' '\t' '\n' '.' '^' '_' ';' '|' '?']+
let dec_num = ("0" | ['1'-'9'](['0'-'9']*))

let whitespace = [' ' '\t' '\r']

rule initial = parse
  | whitespace+ { initial lexbuf }
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | '(' { L_paren }
  | ')' { R_paren }
  | '[' { L_square }
  | ']' { R_square }
  | '?' { Question_mark }
  | "fn" | "λ" { Lambda }
  | "->" | "→" { Arrow }
  | "=>" { Thick_arrow }
  | '^' { Caret }
  | ':' { Colon }
  | '_' { Underbar }
  | '*' | "×" { Star }
  | ',' { Comma }
  | ".1" { DotOne }
  | ".2" { DotTwo }
  | "One" | "⊤" | "𝟙" { One }
  | "<>"  { Unit }
  | "Zero" | "⊥" | "𝟘" { Zero }
  | "Type" { Type }
  | "let" { Let }
  | "=" { Equal }
  | '|' { Bar }
  | "Id" { Id }
  | "refl" { Refl }
  | '+' { Plus }
  | "1." { OneDot }
  | "2." { TwoDot }
  | "match" { Match }
  | "at" { At }
  | "with" { With }
  | dec_num as d { Dec_const (Int.of_string d) }
  | "{-" { comment 1 lexbuf }
  | "-}" { failwith "Unbalanced comments" }
  | "--" { comment_line lexbuf }
  | ident as name { Ident name }
  | eof { Eof }
  | _ as x { failwith ("illegal char: " ^ (Char.to_string x)) }

(*
  | "postulate" { T.Postulate }
*)

and comment nesting = parse
  | '\n' { Lexing.new_line lexbuf; comment nesting lexbuf }
  | "{-" { comment (nesting + 1) lexbuf }
  | "-}" { match nesting - 1 with | 0 -> initial lexbuf | n' -> comment n' lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment nesting lexbuf }

and comment_line = parse
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment_line lexbuf }