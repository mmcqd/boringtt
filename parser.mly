%{

open Core.List

let rec args_to_tele = function
  | [] -> []
  | (xs,t)::args -> map xs ~f:(fun x -> (x,t)) @ args_to_tele args

let func_syntax (args,t,e) =
  let tele = args_to_tele args in
  Syntax.Ascribe (Syntax.Lam (map ~f:fst tele,e),Syntax.Pi (tele,t) )



%}

%token Eof
%token L_paren R_paren
%token Lambda Thick_arrow Arrow
%token Comma DotOne DotTwo Star
%token One
%token Zero
%token Id Refl Match At With Bar
%token Plus OneDot TwoDot
%token Type Caret
%token Colon
%token Underbar Question_mark
%token Def Equal Axiom
%token Let In
%token <string> Ident
%token <int> Dec_const


%right Arrow
%right Star


%type <Syntax.stm list> init

%start init

%%

let paren(x) == L_paren; ~ = x; R_paren; <>

let init := ~ = nonempty_list(stm); Eof; <>


let stm := 
  | Def; ~ = bound_name; Equal; ~ = term; <Syntax.Decl>
  | Def; x = bound_name; Colon; t = term; Equal; e = term; { Syntax.Decl (x, Syntax.Ascribe (e,t)) } 
  | Def; x = bound_name; args = nonempty_list(paren(annot_args)); Colon; t = term; Equal; e = term; { Syntax.Decl (x,func_syntax (args,t,e)) }
  | Axiom; ~ = bound_name; Colon; ~ = term; <Syntax.Axiom>
  | ~ = term; <Syntax.Eval>

let bound_name :=
  | Ident
  | Underbar; { "_" }

let annot_args :=
  | ~ = nonempty_list(bound_name) ; Colon ; ~ = term ; <>

let atomic :=
  | paren(term)
  | x = Ident; { Syntax.Var x }
  | Question_mark; { Syntax.Meta }
  | One; { Syntax.One }
  | ~ = paren(separated_list(Comma,term)); <Syntax.Tuple>
  | Zero; { Syntax.Zero }
  | L_paren; e = term; Colon; t = term; R_paren; { Syntax.Ascribe (e,t) }
  | Type; Caret; i = Dec_const; { Syntax.Type (Level.Const i) }
  | Type; { Syntax.Type (Level.Const 0) }
  | ~ = Ident; Caret; ~ = Dec_const; <Syntax.Lift>
  | ~ = atomic; DotOne; <Syntax.Proj1>
  | ~ = atomic; DotTwo; <Syntax.Proj2>
  | OneDot; ~ = atomic; <Syntax.Inj1>
  | TwoDot; ~ = atomic; <Syntax.Inj2>
  | Refl; { Syntax.Refl Meta }



let spine :=
  | { Syntax.Nil }
  | ~ = spine; ~ = atomic; <Syntax.Snoc>

let nonempty_spine :=
  | ~ = spine; ~ = atomic; <Syntax.Snoc>

let term :=
  | atomic
  | ~ = atomic; ~ = nonempty_spine; <Syntax.Spine>
  | Lambda; xs = nonempty_list(bound_name); Thick_arrow; e = term; <Syntax.Lam>
  | args = nonempty_list(paren(annot_args)); Arrow; e = term; { Syntax.Pi (args_to_tele args,e) }
  | t1 = term; Arrow; t2 = term; { Syntax.Pi ([("_",t1)],t2) }
  | args = nonempty_list(paren(annot_args)); Star; e = term; { Syntax.Sg (args_to_tele args,e) }
  | t1 = term; Star; t2 = term; { Syntax.Sg ([("_",t1)],t2) }
  | t1 = term; Plus; t2 = term; { Syntax.Sum (t1,t2) }
  | Refl; ~ = atomic; <Syntax.Refl>
  | Id; t = atomic; e1 = atomic; e2 = atomic; <Syntax.Id>

  | Let; x = bound_name; Equal; e1 = term; In; e2 = term; {Syntax.Let (e1,(x,e2)) }
  | Let; x = bound_name; Colon; t = term; Equal; e1 = term; In; e2 = term; { Syntax.Let (Syntax.Ascribe (e1,t),(x,e2)) } 

  | Match; scrut = term; At; x = bound_name; y = bound_name; z = bound_name; Thick_arrow; mot = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Syntax.J {mot = Some (x,y,z,mot) ; case = (a,case) ; scrut} }
  
  | Match; scrut = term; With;
    option(Bar); Refl; a = bound_name; Thick_arrow; case = term;
    { Syntax.J {mot = None ; case = (a,case) ; scrut } }

  | Match; scrut = term; At; x = bound_name; Thick_arrow; mot = term; With;
    option(Bar); OneDot; a = bound_name; Thick_arrow; case1 = term;
    Bar; TwoDot; b = bound_name; Thick_arrow; case2 = term;
    { Syntax.Case {mot = Some (x,mot) ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} }
  
  | Match; scrut = term; With;
    option(Bar); OneDot; a = bound_name; Thick_arrow; case1 = term;
    Bar; TwoDot; b = bound_name; Thick_arrow; case2 = term;
    { Syntax.Case {mot = None ; case1 = (a,case1) ; case2 = (b,case2) ; scrut} }
  
  | Match; scrut = term; At; mot = term;
    { Syntax.ZeroInd {mot = Some mot ; scrut} }
  
  | Match; scrut = term;
    { Syntax.ZeroInd {mot = None; scrut} }