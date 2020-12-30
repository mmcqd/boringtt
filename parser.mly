
%{

let fresh =
  let r = ref 0 in
  fun () -> r := !r + 1; !r

let arg_fold (xs,e) = Core.List.fold_right xs ~init:e ~f:(fun x e -> Ast.lam (x,e))

let annot_arg_fold c (xs,t,e) = Core.List.fold_right xs ~init:e ~f:(fun x e -> c (t,(x,e)))

let multi_annot_arg_fold c (xss,e) = Core.List.fold_right xss ~init:e ~f:(fun (xs,t) e -> annot_arg_fold c (xs,t,e))

%}

%token Eof
%token Underbar
%token Let Equal Postulate 
%token Lambda Colon Comma DotOne DotTwo Carat
%token Arrow Star
%token L_paren R_paren L_square R_square
%token <string> Ident
%token <int> Dec_const
%token Type

%right Arrow
%right Star
%right Comma
%nonassoc Carat

%type <Ast.stm list> init

%start init

%%


let init := ~ = nonempty_list(stm); Eof; <>

let paren(x) == L_paren; ~ = x; R_paren; <>
let square(x) == L_square; ~ = x; R_square; <>

let stm := 
  | Let; ~ = bound_name; Equal; ~ = expr; <Ast.Decl>
  | Let; x = bound_name; Colon; t = expr; Equal; e = expr; { Ast.Decl (x,Ast.annot (e,t)) } 
  | Postulate; ~ = bound_name; Colon; ~ = expr; <Ast.Postulate> 
  | ~ = expr; <Ast.Eval>

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = expr ; <>

let expr :=
  | Lambda; ~ = square(nonempty_list(bound_name)); ~ = expr; <arg_fold>
  | Lambda; args = nonempty_list(square(annot_args)); e = expr; { multi_annot_arg_fold Ast.alam (args,e) }
  | app_expr


let app_expr :=
  | e1 = app_expr; e2 = simple_expr; <Ast.app> %prec Comma
  | simple_expr

let simple_expr := 
  | ~ = Ident ; <Ast.f>
  | Underbar; { Ast.meta (fresh ()) } 
  | ~ = expr; Carat; ~ = Dec_const; <Ast.lift>
  | args = nonempty_list(square(annot_args)); Arrow; e = expr; { multi_annot_arg_fold Ast.pi (args,e) }
  | t1 = expr; Arrow; t2 = expr; { Ast.pi (t1,("",t2)) }
  | args = nonempty_list(square(annot_args)); Star; e = expr; { multi_annot_arg_fold Ast.sigma (args,e) }
  | t1 = expr; Star; t2 = expr; { Ast.sigma (t1,("",t2)) }
  | e1 = expr; Comma; e2 = expr; { Ast.pair (e1,e2) }
  | ~ = simple_expr; DotOne; <Ast.proj1>
  | ~ = simple_expr; DotTwo; <Ast.proj2>
  | L_paren; e = expr; Colon; t = expr; R_paren; <Ast.annot> 
  | Type; ~ = Dec_const; <Ast.typ>
  | Type; {Ast.typ 0}
  | paren(expr)