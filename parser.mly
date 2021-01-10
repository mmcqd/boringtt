
%{

open Core.List

let fresh =
  let r = ref 0 in
  fun () -> r := !r + 1; !r

let arg_fold (xs,e) = fold_right xs ~init:e ~f:(fun x e -> Ast.lam (x,e))

let annot_arg_fold c (xs,t,e) = fold_right xs ~init:e ~f:(fun x e -> c (t,(x,e)))

let multi_annot_arg_fold c (xss,e) = fold_right xss ~init:e ~f:(fun (xs,t) e -> annot_arg_fold c (xs,t,e))
  
let func_syntax (xss,t,e) =
  let args = concat @@ map ~f:fst xss in
  Ast.annot (arg_fold (args,e), multi_annot_arg_fold Ast.pi (xss,t))

let app_fold (x,xs) = fold_left xs ~init:x ~f:(fun x e -> Ast.app (x,e))


%}

%token Eof
%token Underbar
%token Let Equal Postulate 
%token Lambda Colon Comma DotOne DotTwo Carat
%token Arrow Star
%token Id Refl J Semicolon
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
  | Let; x = bound_name; args = nonempty_list(square(annot_args)); Colon; t = m(expr); Equal; e = m(expr); { Ast.Decl (x,func_syntax (args,t,e)) }
  | Postulate; ~ = bound_name; Colon; ~ = m(expr); <Ast.Postulate> 
  | ~ = m(expr); <Ast.Eval>

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = m(expr) ; <>


let atomic :=
  | paren(expr)
  | ~ = Ident ; <Ast.f>
  | Underbar; { Ast.meta (fresh ()) } 
  | ~ = Ident; Carat; ~ = Dec_const; <Ast.lift>
  | L_paren; e = m(expr); Colon; t = m(expr); R_paren; <Ast.annot> 
  | ~ = Type; <Ast.typ>
  | Refl; { Ast.refl }
  | ~ = m(atomic); DotOne; <Ast.proj1>
  | ~ = m(atomic); DotTwo; <Ast.proj2>

let expr :=
  | e1 = m(atomic); args = list(m(atomic)); { app_fold (e1,args) }
  | Lambda; ~ = square(nonempty_list(bound_name)); ~ = m(expr); <arg_fold>
  | Id; 
    t = m(atomic);
    m = m(atomic);
    n = m(atomic); 
    { Ast.id (t,m,n) }
  | args = nonempty_list(square(annot_args)); Arrow; e = m(expr); { multi_annot_arg_fold Ast.pi (args,e) }
  | t1 = m(expr); Arrow; t2 = m(expr); { Ast.pi (t1,("",t2)) }
  | args = nonempty_list(square(annot_args)); Star; e = m(expr); { multi_annot_arg_fold Ast.sigma (args,e) }
  | t1 = m(expr); Star; t2 = m(expr); { Ast.sigma (t1,("",t2)) }
  | e1 = m(expr); Comma; e2 = m(expr); { Ast.pair (e1,e2) }
  | J; 
    L_paren; 
    e1 = m(expr); Semicolon;
    L_square;
    a = bound_name;
    b = bound_name;
    c = bound_name;
    R_square;
    e2 = m(expr);
    Semicolon;
    L_square;
    d = bound_name;
    R_square;
    e3 = m(expr);
    Semicolon; 
    e4 = m(expr); Semicolon; 
    e5 = m(expr); Semicolon; 
    e6 = m(expr);
    R_paren;
    { Ast.j (e1,(a,b,c,e2),(d,e3),e4,e5,e6) } 
(*
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
  | Id; 
    t = m(simple_expr);
    m = m(simple_expr);
    n = m(simple_expr); 
    { Ast.id (t,m,n) }
  | Refl; { Ast.refl }
  | J; 
    L_paren; 
    e1 = m(expr); Semicolon;
    L_square;
    a = bound_name;
    b = bound_name;
    c = bound_name;
    R_square;
    e2 = m(expr);
    Semicolon;
    L_square;
    d = bound_name;
    R_square;
    e3 = m(expr);
    Semicolon; 
    e4 = m(expr); Semicolon; 
    e5 = m(expr); Semicolon; 
    e6 = m(expr);
    R_paren;
    { Ast.j (e1,(a,b,c,e2),(d,e3),e4,e5,e6) } 

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
*)