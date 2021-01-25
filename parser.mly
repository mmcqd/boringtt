%{

open Core.List


let fresh_var = 
  let r = ref 0 in
  fun () -> r := !r + 1; "x"^Core.Int.to_string !r

let fresh_meta =
  let r = ref 0 in
  fun () -> r := !r + 1; Ast.Meta {id = !r ; sol = None}

let arg_fold (xs,e) = fold_right xs ~init:e ~f:(fun x e -> Ast.Lam (x,e))

let annot_arg_fold c (xs,t,e) = fold_right xs ~init:e ~f:(fun x e -> c (t,(x,e)))

let multi_annot_arg_fold c (xss,e) = fold_right xss ~init:e ~f:(fun (xs,t) e -> annot_arg_fold c (xs,t,e))

let func_syntax (xss,t,e) =
  let args = concat @@ map ~f:fst xss in
  Ast.Ascribe (arg_fold (args,e), multi_annot_arg_fold (fun x -> Ast.Pi x) (xss,t))

let app_fold (x,xs) = fold_left xs ~init:x ~f:(fun x e -> Ast.App (x,e))

%}

%token Eof
%token L_paren R_paren L_square R_square
%token Lambda Thick_arrow Arrow
%token Comma DotOne DotTwo Star
%token One Unit
%token Zero
%token Id Refl Match At With Bar
%token Plus OneDot TwoDot
%token Type Caret
%token Colon
%token Underbar Question_mark
%token Let Equal
%token <string> Ident
%token <int> Dec_const


%right Arrow
%right Star
%right Comma


%type <Ast.stm list> init

%start init

%%

let paren(x) == L_paren; ~ = x; R_paren; <>
let square(x) == L_square; ~ = x; R_square; <>

let init := ~ = nonempty_list(stm); Eof; <>


let stm := 
  | Let; ~ = bound_name; Equal; ~ = term; <Ast.Decl>
  | Let; x = bound_name; Colon; t = term; Equal; e = term; { Ast.Decl (x, Ast.Ascribe (e,t)) } 
  | Let; x = bound_name; args = nonempty_list(square(annot_args)); Colon; t = term; Equal; e = term; { Ast.Decl (x,func_syntax (args,t,e)) }
  | ~ = term; <Ast.Eval>

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = term ; <>

let atomic :=
  | paren(term)
  | x = Ident; { Ast.Var x }
  | Question_mark; { fresh_meta () }
  | One; { Ast.One }
  | Unit; { Ast.Unit }
  | Zero; { Ast.Zero }
  | L_paren; e = term; Colon; t = term; R_paren; { Ast.Ascribe (e,t) }
  | Type; Caret; i = Dec_const; { Ast.Type (Ast.Const i) }
  | Type; { Ast.Type (Ast.Const 0) }
  | ~ = Ident; Caret; ~ = Dec_const; <Ast.Lift>
  | ~ = atomic; DotOne; <Ast.Proj1>
  | ~ = atomic; DotTwo; <Ast.Proj2>
  | OneDot; ~ = atomic; <Ast.Inj1>
  | TwoDot; ~ = atomic; <Ast.Inj2>

let term :=
  | e1 = atomic; args = list(atomic); { app_fold (e1,args) }
  | Lambda; ~ = nonempty_list(bound_name); Thick_arrow; ~ = term; <arg_fold>
  | args = nonempty_list(square(annot_args)); Arrow; e = term; { multi_annot_arg_fold (fun x -> Ast.Pi x) (args,e) }
  | t1 = term; Arrow; t2 = term; { Ast.Pi (t1,("_",t2)) }
  | args = nonempty_list(square(annot_args)); Star; e = term; { multi_annot_arg_fold (fun x -> Ast.Sg x) (args,e) }
  | t1 = term; Star; t2 = term; { Ast.Sg (t1,("_",t2)) }
  | t1 = term; Plus; t2 = term; { Ast.Sum (t1,t2) }

  | e1 = term; Comma; e2 = term; { Ast.Pair (e1,e2) }
  | Refl; ~ = atomic; <Ast.Refl>
  | Refl; { Ast.Refl (fresh_meta ()) }
  | Id; t = atomic; e1 = atomic; e2 = atomic; <Ast.Id>

  | Match; scrut = term; At; x = bound_name; y = bound_name; z = bound_name; Thick_arrow; mot = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Ast.J {mot = (x,y,z,mot) ; case = (a,case) ; scrut} }
  
  | Match; scrut = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Ast.J {mot = (fresh_var(),fresh_var(),fresh_var(),fresh_meta()) ; case = (a,case) ; scrut } }

  | Match; scrut = term; At; x = bound_name; Thick_arrow; mot = term; With;
    option(Bar); OneDot; a = bound_name; Thick_arrow; case1 = term;
    Bar; TwoDot; b = bound_name; Thick_arrow; case2 = term;
    { Ast.Case {mot = (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} }
  
  | Match; scrut = term; With;
    option(Bar); OneDot; a = bound_name; Thick_arrow; case1 = term;
    Bar; TwoDot; b = bound_name; Thick_arrow; case2 = term;
    { Ast.Case {mot = (fresh_var(),fresh_meta()) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} }
  
  | Match; scrut = term; At; mot = term;
    { Ast.ZeroInd {mot ; scrut} }
  
  | Match; scrut = term;
    { Ast.ZeroInd {mot = fresh_meta (); scrut} }