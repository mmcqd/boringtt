
%{

let arg_fold (xs,e) = Core.List.fold_right xs ~init:e ~f:(fun x e -> Ast.lam (x,e))

let typ_arg_fold c (xs,t,e) = Core.List.fold_right xs ~init:e ~f:(fun x e -> c (t,(x,e)))


%}

%token Eof
%token Let Equal
%token Lambda Colon Comma DotOne DotTwo
%token Arrow Star
%token L_paren R_paren L_square R_square
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
let square(x) == L_square; ~ = x; R_square; <>

let stm := 
  | Let; ~ = Ident; Equal; ~ = expr; <Ast.Decl>
  | Let; x = Ident; Colon; t = expr; Equal; e = expr; { Ast.Decl (x,Ast.annot (e,t)) }  
  | ~ = expr; <Ast.Eval>

let annot_args :=
  | ~ = nonempty_list(Ident) ; Colon ; ~ = expr ; <>

let expr :=
  | Lambda; xs = square(nonempty_list(Ident)); e = expr; <arg_fold>
  | app_expr


let app_expr :=
  | e1 = app_expr; e2 = simple_expr; <Ast.app> %prec Comma
  | simple_expr

let simple_expr := 
  | ~ = Ident ; <Ast.f>
  | a = square(annot_args); Arrow; e = expr; { let (xs,t) = a in typ_arg_fold Ast.pi (xs,t,e) }
  | t1 = expr; Arrow; t2 = expr; { Ast.pi (t1,("",t2)) }
  | a = square(annot_args); Star; e = expr; { let (xs,t) = a in typ_arg_fold Ast.sigma (xs,t,e) }
  | t1 = expr; Star; t2 = expr; { Ast.sigma (t1,("",t2)) }
  | e1 = expr; Comma; e2 = expr; { Ast.pair (e1,e2) }
  | ~ = simple_expr; DotOne; <Ast.proj1>
  | ~ = simple_expr; DotTwo; <Ast.proj2>
  | L_paren; e = expr; Colon; t = expr; R_paren; <Ast.annot> 
  | Type; ~ = Dec_const; <Ast.typ>
  | Type; {Ast.typ 0}
  | paren(expr)