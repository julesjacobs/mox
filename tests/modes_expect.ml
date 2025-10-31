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
