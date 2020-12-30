{

open Core
module T = Parser

}



let ident = [^ '(' ')' '[' ']' '\\' ':' '*' ',' '=' ' ' '\t' '\n' '.' '^' ]+
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
  | '*' | "×" { T.Star }
  | ',' { T.Comma }
  | '^' { T.Carat }
  | ".1" { T.DotOne }
  | ".2" { T.DotTwo }
  | "->" | "→" { T.Arrow }
  | "Type" { T.Type }
  | "let" { T.Let }
  | "=" { T.Equal }
  | dec_num as d { T.Dec_const (Int.of_string d) }
  | ident as name { T.Ident name }
  | eof { T.Eof }
  | _ as x { failwith ("illegal char: " ^ (Char.to_string x)) }
