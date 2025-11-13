open Pretty

type mode = Expr | Ty

let mode = ref Expr

let set_mode m () = mode := m

let positionals = ref []

type backend = Typechecker | Typeinference

let backend = ref Typechecker

let set_backend name =
  let value =
    match String.lowercase_ascii name with
    | "typechecker" | "checker" -> Typechecker
    | "typeinference" | "inference" | "infer" -> Typeinference
    | _ ->
        raise
          (Arg.Bad
             (Printf.sprintf "Unknown engine %s (expected typechecker or typeinference)" name))
  in
  backend := value

let infer_with_backend expr =
  match !backend with
  | Typechecker ->
      (try
         let ty = Typechecker.infer expr in
         Ok (Typechecker.string_of_ty ty)
       with
      | Typechecker.Error err -> Error (Typechecker.string_of_error err)
      | Typechecker.Mode_error msg -> Error msg)
  | Typeinference ->
      (try
         let ty = Typeinference.infer expr in
         Ok (Typeinference.string_of_ty ty)
       with
      | Typeinference.Error err -> Error (Typeinference.string_of_error err))

let () =
  let usage_msg =
    "Usage: mox [--type] [--engine ENGINE] [FILE]\n       mox record PATH   (PATH may be a file or directory)"
  in
  let spec =
    [ "--type", Arg.Unit (set_mode Ty), "Parse input as a type instead of an expression";
      "--expr", Arg.Unit (set_mode Expr), "Parse input as an expression (default)";
      ( "--engine",
        Arg.String set_backend,
        "Select typing backend: typechecker (default) or typeinference" ) ]
  in
  let handle_anon arg = positionals := arg :: !positionals in
  Arg.parse spec handle_anon usage_msg;
  let run_expr_from_channel channel filename =
    let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let result =
      try
        match !mode with
        | Expr ->
            let expr = Parser.expr_eof Lexer.token lexbuf in
            `Expr expr
        | Ty ->
            let ty = Parser.ty_eof Lexer.token lexbuf in
            `Ty ty
      with
      | Lexer.Lexing_error msg ->
          prerr_endline msg;
          exit 1
      | Parser.Error ->
          let pos = lexbuf.Lexing.lex_curr_p in
          prerr_endline
            (Printf.sprintf "Parse error at %s:%d:%d" filename pos.Lexing.pos_lnum
               (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1));
          exit 1
    in
    match result with
    | `Expr e -> (
        match infer_with_backend e with
        | Ok ty -> Printf.printf "%s : %s\n" (string_of_expr e) ty
        | Error msg ->
            prerr_endline msg;
            exit 1)
    | `Ty t -> print_endline (string_of_ty t)
  in
  match List.rev !positionals with
  | ["record"] ->
      prerr_endline "record expects a PATH argument.";
      exit 1
  | "record" :: path :: rest ->
      if rest <> [] then (
        prerr_endline "record accepts exactly one PATH argument.";
        exit 1);
      if !mode <> Expr then (
        prerr_endline "Cannot combine record with --type/--expr flags.";
        exit 1);
      (try Expect.process_path ~infer:infer_with_backend path with
      | Expect.Error msg ->
          prerr_endline msg;
          exit 1)
  | [] ->
      run_expr_from_channel stdin "<stdin>"
  | [filename] ->
      let channel = open_in filename in
      Fun.protect
        ~finally:(fun () -> close_in channel)
        (fun () -> run_expr_from_channel channel filename)
  | _ ->
      prerr_endline "At most one positional argument is allowed.";
      exit 1
