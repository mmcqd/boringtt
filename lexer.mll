{

open Core
module T = Parser

}



let ident = [^ '(' ')' '[' ']' '\\' ':' '*' ',' '=' ' ' '\t' '\n' '.' '^' '_' ]+
let dec_num = ("0" | ['1'-'9'](['0'-'9']*))

let whitespace = [' ' '\t' '\n']

rule initial = parse
  | whitespace+ { initial lexbuf }
  | '(' { T.L_paren }
  | ')' { T.R_paren }
  | '[' { T.L_square }
  | ']' { T.R_square }
  | '\\' | "λ" { T.Lambda }
  | ':' { T.Colon }
  | '_' { T.Underbar }
  | '*' | "×" { T.Star }
  | ',' { T.Comma }
  | '^' { T.Carat }
  | ".1" { T.DotOne }
  | ".2" { T.DotTwo }
  | "->" | "→" { T.Arrow }
  | "Type" { T.Type }
  | "let" { T.Let }
  | "postulate" { T.Postulate }
  | "=" { T.Equal }
  | dec_num as d { T.Dec_const (Int.of_string d) }
  | "{-" { comment 1 lexbuf }
  | "-}" { failwith "Unbalanced comments" }
  | "--" { comment_line lexbuf }
  | ident as name { T.Ident name }
  | eof { T.Eof }
  | _ as x { failwith ("illegal char: " ^ (Char.to_string x)) }

and comment nesting = parse
  | "{-" { comment (nesting + 1) lexbuf }
  | "-}" { match nesting - 1 with | 0 -> initial lexbuf | n' -> comment n' lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment nesting lexbuf }

and comment_line = parse
  | '\n' { initial lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment_line lexbuf }