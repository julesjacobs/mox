open Modes

let parse_names text =
  let lexbuf = Lexing.from_string text in
  Parser.modes_eof Lexer.token lexbuf

let parse_mode text =
  text |> parse_names |> Mode.of_strings

let print_mode mode =
  Printf.printf "mode: %s\n" (match Mode.to_string mode with "" -> "<default>" | s -> s);
  let past = Past.to_string mode.Mode.past in
  let future = Future.to_string mode.Mode.future in
  Printf.printf "past: %s\n" (if past = "" then "<default>" else past);
  Printf.printf "future: %s\n" (if future = "" then "<default>" else future)

let string_of_list lst =
  "[" ^ String.concat ", " lst ^ "]"

let parse_ty text =
  let lexbuf = Lexing.from_string text in
  Parser.ty_eof Lexer.token lexbuf

let%expect_test "uniqueness extract" =
  let value, rest = Uniqueness.extract [ "unique"; "shared" ] in
  Printf.printf "value=%s rest=%s\n" (Uniqueness.to_string value) (string_of_list rest);
  [%expect {|value=unique rest=[shared]|}]

let%expect_test "uniqueness default" =
  let value, rest = Uniqueness.extract [ "shared" ] in
  Printf.printf "value=%s rest=%s\n" (Uniqueness.to_string value) (string_of_list rest);
  [%expect {|value=aliased rest=[shared]|}]

let%expect_test "uniqueness duplicate" =
  (match Uniqueness.extract [ "unique"; "unique" ] with
  | _ -> Printf.printf "unexpected success\n"
  | exception Invalid_argument msg -> Printf.printf "%s\n" msg);
  [%expect {|Mode unique provided multiple times|}]

let%expect_test "parse default mode" =
  parse_mode "[]" |> print_mode;
  [%expect {|
    mode: <default>
    past: <default>
    future: <default>
  |}]

let%expect_test "parse custom mode" =
  parse_mode "[unique contended portable local once]" |> print_mode;
  [%expect {|
    mode: unique contended local once portable
    past: unique contended
    future: local once portable
  |}]

let%expect_test "parse leftover error" =
  (match parse_mode "[unique foo]" with
  | _ -> Printf.printf "unexpected success\n"
  | exception Invalid_argument msg -> Printf.printf "%s\n" msg);
  [%expect {|Unrecognised mode names: foo|}]

let%expect_test "type arrow default" =
  parse_ty "unit -> unit"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit -> unit)|}]

let%expect_test "type arrow custom" =
  parse_ty "unit ->[local once portable] unit"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit ->[local once portable] unit)|}]

let%expect_test "type arrow portable only" =
  parse_ty "unit ->[portable] unit"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit ->[portable] unit)|}]

let%expect_test "type arrow mode rejection" =
  (match parse_ty "unit ->[shared] unit" with
  | _ -> Printf.printf "unexpected success\n"
  | exception Invalid_argument msg -> Printf.printf "%s\n" msg);
  [%expect {|Modes [shared] not allowed on functions|}]

let%expect_test "type pair default" =
  parse_ty "unit * unit"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit * unit)|}]

let%expect_test "type pair custom" =
  parse_ty "unit *[unique local] unit"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit *[unique local] unit)|}]

let%expect_test "type pair invalid mode" =
  (match parse_ty "unit *[portable] unit" with
  | _ -> Printf.printf "unexpected success\n"
  | exception Invalid_argument msg -> Printf.printf "%s\n" msg);
  [%expect {|Modes [portable] not allowed on products/sums|}]

let%expect_test "type sum custom" =
  parse_ty "unit +[unique local] empty"
  |> Pretty.string_of_ty
  |> Printf.printf "%s\n";
  [%expect {|(unit +[unique local] empty)|}]

let%expect_test "mode pair custom" =
  Typechecker.mode_of_type (parse_ty "unit *[unique local] unit")
  |> Modes.Mode.to_string
  |> Printf.printf "%s\n";
  [%expect {|unique contended local portable|}]

let%expect_test "mode arrow custom" =
  Typechecker.mode_of_type (parse_ty "unit ->[local once portable] unit")
  |> Modes.Mode.to_string
  |> Printf.printf "%s\n";
  [%expect {|contended local once portable|}]

let%expect_test "mode violation" =
  (match
     Typechecker.mode_of_type
       (parse_ty "(unit *[unique local] unit) *[aliased global] unit")
   with
  | _ -> Printf.printf "unexpected success\n"
  | exception Typechecker.Mode_error msg -> Printf.printf "%s\n" msg);
  [%expect {|Component uniqueness unique exceeds annotation aliased|}]

let%expect_test "subtype modes" =
  let t1 = parse_ty "unit *[unique local] unit" in
  let t2 = parse_ty "unit *[aliased local] unit" in
  (match Typechecker.subtype t1 t2 with
  | () -> print_endline "ok"
  | exception Typechecker.Error (Typechecker.Not_a_subtype _) -> print_endline "fail");
  [%expect {|ok|}]
