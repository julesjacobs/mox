open Ast

exception Error of string

type chunk =
  | Blank of string
  | Expr of { start_line : int; lines : string list }

type expectation =
  | Type of string
  | Error of string

type processed =
  | PBlank of string
  | PExpr of string list * expectation

let is_type_line line =
  let trimmed = String.trim line in
  String.length trimmed > 0 && trimmed.[0] = '>'

let is_blank_line line = String.trim line = ""

let finalize_expr acc current start_line =
  match current, start_line with
  | [], _ -> acc
  | lines, Some line_no ->
      let block = Expr { start_line = line_no; lines = List.rev lines } in
      block :: acc
  | _ -> acc

let parse_chunks lines =
  (* Test files are organised as blocks of non-empty lines (an expression)
     optionally followed by one or more blank lines. A line starting with '>'
     stores the previously computed type and is ignored when re-reading. *)
  let rec loop line_no acc current start_line remaining =
    match remaining with
    | [] -> List.rev (finalize_expr acc current start_line)
    | line :: rest when is_type_line line ->
        let acc = finalize_expr acc current start_line in
        loop (line_no + 1) acc [] None rest
    | line :: rest when is_blank_line line ->
        let acc =
          match current with
          | [] -> Blank line :: acc
          | _ -> Blank line :: finalize_expr acc current start_line
        in
        loop (line_no + 1) acc [] None rest
    | line :: rest ->
        let start_line = match start_line with None -> Some line_no | Some _ as s -> s in
        loop (line_no + 1) acc (line :: current) start_line rest
  in
  loop 1 [] [] None lines

let read_lines path =
  let ic = open_in path in
  let rec aux acc =
    match input_line ic with
    | line -> aux (line :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
  aux []

let parse_expr_from_lines ~filename ~start_line lines =
  let source = String.concat "\n" lines in
  let lexbuf = Lexing.from_string source in
  let open Lexing in
  lexbuf.lex_curr_p <-
    { pos_fname = filename; pos_lnum = start_line; pos_bol = 0; pos_cnum = 0 };
  try Parser.expr_eof Lexer.token lexbuf with
  | Lexer.Lexing_error msg -> raise (Error (Printf.sprintf "%s:%d: %s" filename start_line msg))
  | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let col = pos.pos_cnum - pos.pos_bol + 1 in
      raise (Error (Printf.sprintf "%s:%d:%d: parse error" filename pos.pos_lnum col))

let process_chunk ~filename chunk =
  match chunk with
  | Blank line -> PBlank line
  | Expr { start_line; lines } ->
      let expr = parse_expr_from_lines ~filename ~start_line lines in
      try
        let ty = Typechecker.infer expr in
        PExpr (lines, Type (Pretty.string_of_ty ty))
      with Typechecker.Error err ->
        let msg = Typechecker.string_of_error err in
        PExpr (lines, Error msg)

let render processed =
  let rec aux acc = function
    | [] -> List.rev acc
    | PBlank line :: rest -> aux (line :: acc) rest
    | PExpr (lines, expect) :: rest ->
        let acc =
          List.fold_left (fun acc line -> line :: acc) acc lines
        in
        let rendered =
          match expect with
          | Type ty -> "> " ^ ty
          | Error msg -> "> error: " ^ msg
        in
        aux (rendered :: acc) rest
  in
  aux [] processed

let process_lines ?(filename = "<tests>") lines =
  let chunks = parse_chunks lines in
  let processed = List.map (process_chunk ~filename) chunks in
  render processed

let process_file path =
  let lines = read_lines path in
  let rendered = process_lines ~filename:path lines in
  let oc = open_out path in
  List.iter
    (fun line ->
      output_string oc line;
      output_char oc '\n')
    rendered;
  close_out oc

let rec process_path path =
  if not (Sys.file_exists path) then
    raise (Error (Printf.sprintf "No such file or directory: %s" path))
  else if Sys.is_directory path then
    let entries = Sys.readdir path in
    Array.sort String.compare entries;
    Array.iter
      (fun entry ->
        if entry <> "." && entry <> ".." then
          let child = Filename.concat path entry in
          process_path child)
      entries
  else if Filename.check_suffix path ".mox" then
    process_file path
  else
    ()
