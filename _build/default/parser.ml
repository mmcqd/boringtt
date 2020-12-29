
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | Type
    | Star
    | R_paren
    | Let
    | Lambda
    | L_paren
    | Ident of (
# 11 "parser.mly"
       (string)
# 17 "parser.ml"
  )
    | Equal
    | Eof
    | DotTwo
    | DotOne
    | Dec_const of (
# 12 "parser.mly"
       (int)
# 26 "parser.ml"
  )
    | Comma
    | Colon
    | Arrow
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState36
  | MenhirState34
  | MenhirState29
  | MenhirState25
  | MenhirState22
  | MenhirState20
  | MenhirState16
  | MenhirState12
  | MenhirState10
  | MenhirState9
  | MenhirState5
  | MenhirState0

# 2 "parser.mly"
  


# 67 "parser.ml"

let rec _menhir_goto_nonempty_list_stm_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.stm list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.stm))), _, (xs : (Ast.stm list))) = _menhir_stack in
        let _v : (Ast.stm list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 80 "parser.ml"
         in
        _menhir_goto_nonempty_list_stm_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Eof ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (_1 : (Ast.stm list))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.stm list) = _1 in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (Ast.stm list)) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        ();
        Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
        assert false

and _menhir_goto_stm : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.stm) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | Let ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | Eof ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (Ast.stm))) = _menhir_stack in
        let _v : (Ast.stm list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 132 "parser.ml"
         in
        _menhir_goto_nonempty_list_stm_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44

and _menhir_run16 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_run18 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (expr : (Ast.ast))) = _menhir_stack in
    let _2 = () in
    let _v : (Ast.ast) = 
# 57 "parser.mly"
                       Ast.proj2 
# 167 "parser.ml"
     expr in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run19 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (expr : (Ast.ast))) = _menhir_stack in
    let _2 = () in
    let _v : (Ast.ast) = 
# 56 "parser.mly"
                       Ast.proj1 
# 180 "parser.ml"
     expr in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run20 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | R_paren ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (_1 : (
# 11 "parser.mly"
       (string)
# 244 "parser.ml"
            ))), _, (expr : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _v : (string * Ast.ast) = let _1_1 = _1 in
            (_1_1, expr) in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | R_paren ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Arrow ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | Ident _v ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
                    | L_paren ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                    | Lambda ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                    | Type ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
                | Star ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | Ident _v ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
                    | L_paren ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState34
                    | Lambda ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState34
                    | Type ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState34
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Arrow | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t1 : (Ast.ast))), _, (t2 : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.ast) = 
# 53 "parser.mly"
                                ( Ast.sigma (t1,("",t2)) )
# 331 "parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Arrow | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Star | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Ast.ast))), _, (e2 : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.ast) = 
# 54 "parser.mly"
                                 ( Ast.pair (e1,e2) )
# 358 "parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t1 : (Ast.ast))), _, (t2 : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _v : (Ast.ast) = 
# 51 "parser.mly"
                                 ( Ast.pi (t1,("",t2)) )
# 410 "parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Colon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Ident _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
            | L_paren ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | Lambda ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | Type ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | R_paren ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (x : (Ast.ast))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ast) = x in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | R_paren ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Ast.ast))), _, (t : (Ast.ast))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ast) = 
# 55 "parser.mly"
                                                  Ast.annot 
# 490 "parser.ml"
             (e, t) in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Arrow | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (string * Ast.ast))), _, (e : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ast) = let a = x in
            
# 52 "parser.mly"
                                          (let (x,t) = a in Ast.sigma (t,(x,e)) )
# 524 "parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (string * Ast.ast))), _, (e : (Ast.ast))) = _menhir_stack in
            let _2 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.ast) = let a = x in
            
# 50 "parser.mly"
                                           ( let (x,t) = a in Ast.pi (t,(x,e)) )
# 558 "parser.ml"
             in
            _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Colon | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (x : (
# 11 "parser.mly"
       (string)
# 587 "parser.ml"
            ))), _, (e : (Ast.ast))) = _menhir_stack in
            let _3 = () in
            let _1_inlined1 = () in
            let _1 = () in
            let _v : (Ast.ast) = let x =
              let _1 = _1_inlined1 in
              x
            in
            
# 41 "parser.mly"
                                         Ast.lam 
# 599 "parser.ml"
             (x, e) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Eof | Ident _ | L_paren | Lambda | Let | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (_2 : (
# 11 "parser.mly"
       (string)
# 628 "parser.ml"
            ))), _, (expr : (Ast.ast))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.stm) = let _2_1 = _2 in
            
# 33 "parser.mly"
                                      Ast.Decl 
# 636 "parser.ml"
             (_2_1, expr) in
            _menhir_goto_stm _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Ident _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
            | L_paren ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState42
            | Lambda ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState42
            | Type ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState42
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Eof | Ident _ | L_paren | Lambda | Let | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), (x : (
# 11 "parser.mly"
       (string)
# 703 "parser.ml"
            ))), _, (t : (Ast.ast))), _, (e : (Ast.ast))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Ast.stm) = 
# 34 "parser.mly"
                                                      ( Ast.Decl (x,Ast.annot (e,t)) )
# 711 "parser.ml"
             in
            _menhir_goto_stm _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | Arrow ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | Comma ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | DotOne ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | DotTwo ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack)
        | Star ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack)
        | Eof | Ident _ | L_paren | Lambda | Let | Type ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (expr : (Ast.ast))) = _menhir_stack in
            let _v : (Ast.stm) = 
# 35 "parser.mly"
               Ast.Eval 
# 741 "parser.ml"
             expr in
            _menhir_goto_stm _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_app_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | Arrow | Colon | Comma | DotOne | DotTwo | Eof | Equal | Let | R_paren | Star ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (_1 : (Ast.ast))) = _menhir_stack in
        let _v : (Ast.ast) = _1 in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_goto_simple_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.ast) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState0 | MenhirState44 | MenhirState42 | MenhirState40 | MenhirState5 | MenhirState9 | MenhirState36 | MenhirState34 | MenhirState29 | MenhirState10 | MenhirState25 | MenhirState20 | MenhirState16 | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : (Ast.ast)) = _v in
        let _v : (Ast.ast) = _1 in
        _menhir_goto_app_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (e2 : (Ast.ast)) = _v in
        let (_menhir_stack, _menhir_s, (e1 : (Ast.ast))) = _menhir_stack in
        let _v : (Ast.ast) = 
# 45 "parser.mly"
                                      Ast.app 
# 793 "parser.ml"
         (e1, e2) in
        _menhir_goto_app_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce9 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 11 "parser.mly"
       (string)
# 800 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (_1 : (
# 11 "parser.mly"
       (string)
# 806 "parser.ml"
    ))) = _menhir_stack in
    let _v : (Ast.ast) = let _1_1 = _1 in
    
# 49 "parser.mly"
                 Ast.f 
# 812 "parser.ml"
     _1_1 in
    _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Dec_const _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (
# 12 "parser.mly"
       (int)
# 892 "parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Ast.ast) = 
# 58 "parser.mly"
                          Ast.typ 
# 899 "parser.ml"
         d in
        _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
    | Arrow | Colon | Comma | DotOne | DotTwo | Eof | Equal | Ident _ | L_paren | Lambda | Let | R_paren | Star | Type ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Ast.ast) = 
# 59 "parser.mly"
          (Ast.typ 0)
# 909 "parser.ml"
         in
        _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Colon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Ident _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
            | L_paren ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | Lambda ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | Type ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
        | Equal ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Ident _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
            | L_paren ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState5
            | Lambda ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
            | Type ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState5
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | L_paren ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Ident _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | R_paren ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Ident _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
                | L_paren ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState9
                | Lambda ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState9
                | Type ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState9
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState10 in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Colon ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Ident _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
            | L_paren ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | Lambda ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | Type ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState12
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12)
        | Arrow | Comma | DotOne | DotTwo | Ident _ | L_paren | Lambda | R_paren | Star | Type ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 11 "parser.mly"
       (string)
# 1077 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack)

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.stm list) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Ident _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | L_paren ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Lambda ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Let ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Type ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 269 "<standard.mly>"
  

# 1126 "parser.ml"
