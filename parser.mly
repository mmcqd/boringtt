
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
%token <int> Type

%right Arrow
%right Star
%right Comma

%type <Ast.stm list> init

%start init

%%


let m(x) == x = x; { Ast.mark $startpos(x) $endpos(x) x}

let init := ~ = nonempty_list(stm); Eof; <>

let paren(x) == L_paren; ~ = x; R_paren; <>
let square(x) == L_square; ~ = x; R_square; <>

let stm := 
  | Let; ~ = bound_name; Equal; ~ = m(expr); <Ast.Decl>
  | Let; x = bound_name; Colon; t = m(expr); Equal; e = m(expr); { Ast.Decl (x, Ast.mark_as e @@ Ast.annot (e,t)) } 
  | Postulate; ~ = bound_name; Colon; ~ = m(expr); <Ast.Postulate> 
  | ~ = m(expr); <Ast.Eval>

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = m(expr) ; <>

let expr :=
  | Lambda; ~ = square(nonempty_list(bound_name)); ~ = m(expr); <arg_fold>
  | app_expr


let app_expr :=
  | e1 = m(app_expr); e2 = m(simple_expr); <Ast.app>
  | simple_expr

let simple_expr := 
  | ~ = Ident ; <Ast.f>
  | Underbar; { Ast.meta (fresh ()) } 
  | ~ = Ident; Carat; ~ = Dec_const; <Ast.lift>
  | args = nonempty_list(square(annot_args)); Arrow; e = m(expr); { multi_annot_arg_fold Ast.pi (args,e) }
  | t1 = m(expr); Arrow; t2 = m(expr); { Ast.pi (t1,("",t2)) }
  | args = nonempty_list(square(annot_args)); Star; e = m(expr); { multi_annot_arg_fold Ast.sigma (args,e) }
  | t1 = m(expr); Star; t2 = m(expr); { Ast.sigma (t1,("",t2)) }
  | e1 = m(expr); Comma; e2 = m(expr); { Ast.pair (e1,e2) }
  | ~ = m(simple_expr); DotOne; <Ast.proj1>
  | ~ = m(simple_expr); DotTwo; <Ast.proj2>
  | L_paren; e = m(expr); Colon; t = m(expr); R_paren; <Ast.annot> 
  | ~ = Type; <Ast.typ>
  | paren(expr)