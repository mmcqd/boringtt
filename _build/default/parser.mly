
%{

%}

%token Eof
%token Let Equal
%token Lambda Colon Comma DotOne DotTwo
%token Arrow Star
%token L_paren R_paren
%token <string> Ident
%token <int> Dec_const
%token Type

%right Arrow
%right Star
%right Comma

%type <Ast.stm list> init

%start init

%%


let init := ~ = nonempty_list(stm); Eof; <>

let paren(x) == L_paren; ~ = x; R_paren; <>



let stm := 
  | Let; ~ = Ident; Equal; ~ = expr; <Ast.Decl>
  | Let; x = Ident; Colon; t = expr; Equal; e = expr; { Ast.Decl (x,Ast.annot (e,t)) }  
  | ~ = expr; <Ast.Eval>

let annot_arg :=
  | ~ = Ident ; Colon ; ~ = expr ; <>

let expr :=
  | Lambda; x = paren(Ident); e = expr; <Ast.lam>
  | app_expr

let app_expr :=
  | e1 = app_expr; e2 = simple_expr; <Ast.app>
  | simple_expr

let simple_expr := 
  | ~ = Ident ; <Ast.f>
  | a = paren(annot_arg); Arrow; e = expr; { let (x,t) = a in Ast.pi (t,(x,e)) }
  | t1 = expr; Arrow; t2 = expr; { Ast.pi (t1,("",t2)) }
  | a = paren(annot_arg); Star; e = expr; {let (x,t) = a in Ast.sigma (t,(x,e)) }
  | t1 = expr; Star; t2 = expr; { Ast.sigma (t1,("",t2)) }
  | e1 = expr; Comma; e2 = expr; { Ast.pair (e1,e2) }
  | L_paren; e = expr; Colon; t = expr; R_paren; <Ast.annot>
  | ~ = expr; DotOne; <Ast.proj1>
  | ~ = expr; DotTwo; <Ast.proj2>
  | Type; d = Dec_const; <Ast.typ>
  | Type; {Ast.typ 0}
  | paren(expr)