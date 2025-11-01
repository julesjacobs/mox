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

let parse_expr text =
  let lexbuf = Lexing.from_string text in
  Parser.expr_eof Lexer.token lexbuf

let run_infer text =
  match Typechecker.infer (parse_expr text) with
  | ty -> Printf.printf "type=%s\n" (Pretty.string_of_ty ty)
  | exception Typechecker.Error err ->
      Printf.printf "error=%s\n" (Typechecker.string_of_error err)
  | exception Typechecker.Mode_error msg ->
      Printf.printf "mode_error=%s\n" msg

let run_process text =
  let lines =
    text
    |> String.trim
    |> String.split_on_char '\n'
  in
  Expect.process_lines lines |> List.iter print_endline

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

let%expect_test "mode violation" =
  (match
     Typechecker.check_mode
       (parse_ty "(unit *[unique local] unit) *[aliased global] unit") Modes.Mode.top_in
   with
  | () -> Printf.printf "unexpected success\n"
  | exception Typechecker.Mode_error msg -> Printf.printf "%s\n" msg);
  [%expect {|Mode unique contended local portable exceeds allowed once|}]

let%expect_test "check mode success" =
  Typechecker.check_mode (parse_ty "unit *[unique local] unit") Modes.Mode.top_in;
  print_endline "ok";
  [%expect {|ok|}]

let%expect_test "check mode violation" =
  (match
     Typechecker.check_mode
       (parse_ty "unit *[unique local] unit") Modes.Mode.bottom_in
   with
  | () -> print_endline "unexpected success"
  | exception Typechecker.Mode_error msg -> print_endline msg);
  [%expect {|Mode unique contended local portable exceeds allowed contended portable|}]

let%expect_test "check mode arrow success" =
  Typechecker.check_mode (parse_ty "unit ->[local once portable] unit") Modes.Mode.top_in;
  print_endline "ok";
  [%expect {|ok|}]

let%expect_test "check mode arrow violation" =
  (match
     Typechecker.check_mode
       (parse_ty "unit ->[local once portable] unit") Modes.Mode.bottom_in
   with
  | () -> print_endline "unexpected success"
  | exception Typechecker.Mode_error msg -> print_endline msg);
  [%expect {|Mode contended local once portable exceeds allowed contended portable|}]

let%expect_test "subtype modes" =
  let t1 = parse_ty "unit *[unique local] unit" in
  let t2 = parse_ty "unit *[aliased local] unit" in
  (match Typechecker.subtype t1 t2 with
  | () -> print_endline "ok"
  | exception Typechecker.Error (Typechecker.Not_a_subtype _) -> print_endline "fail");
  [%expect {|ok|}]

let%expect_test "lock_many_unique_pair_error" =
  run_infer
    {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair) : (unit ->[local many] (unit *[unique local] unit)))
|};
  [%expect {| error=(unit *[local] unit) is not a subtype of (unit *[unique local] unit) |}]

let%expect_test "lock_once_unique_pair_ok" =
  run_infer
    {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair) : (unit ->[local once] (unit *[unique local] unit)))
|};
  [%expect {| type=(unit ->[local once] (unit *[unique local] unit)) |}]

let%expect_test "lock_many_alias_pair_ok" =
  run_infer
    {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair) : (unit ->[local many] (unit *[aliased local] unit)))
|};
  [%expect {| type=(unit ->[local] (unit *[local] unit)) |}]

let%expect_test "lock_many_sum_unique_error" =
  run_infer
    {|
let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum) : (unit ->[local many] (unit +[unique local] unit)))
|};
  [%expect {| error=(unit +[local] unit) is not a subtype of (unit +[unique local] unit) |}]

let%expect_test "lock_many_sum_alias_ok" =
  run_infer
    {|
let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum) : (unit ->[local many] (unit +[aliased local] unit)))
|};
  [%expect {| type=(unit ->[local] (unit +[local] unit)) |}]

let%expect_test "lock_once_function_many_error" =
  run_infer
    {|
let aliased_fun = ((fun x => x) : (unit ->[local many] unit)) in
((fun _ => aliased_fun) : (unit ->[local once] (unit ->[local many] unit)))
|};
  [%expect {| mode_error=Variable aliased_fun is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once. Captured value had type (unit ->[local] unit). |}]

let%expect_test "lock_many_function_once_ok" =
  run_infer
    {|
let linear_fun = ((fun x => x) : (unit ->[local once] unit)) in
((fun _ => linear_fun) : (unit ->[local many] (unit ->[local once] unit)))
|};
  [%expect {| type=(unit ->[local] (unit ->[local once] unit)) |}]

let%expect_test "lock_once_pair_function_path_left" =
  run_infer
    {|
let bundle =
  (((fun x => x) : (unit ->[local many] unit)), unit)
  : ((unit ->[local many] unit) *[unique local] unit)
in
((fun _ => bundle)
 : (unit ->[local once] ((unit ->[local many] unit) *[unique local] unit)))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via pair.left). Captured value had type ((unit ->[local] unit) *[unique local] unit). |}]

let%expect_test "lock_once_pair_function_path_right" =
  run_infer
    {|
let bundle =
  (unit,
   ((fun x => x) : (unit ->[local many] unit)))
  : (unit *[unique local] (unit ->[local many] unit))
in
((fun _ => bundle)
 : (unit ->[local once] (unit *[unique local] (unit ->[local many] unit))))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via pair.right). Captured value had type (unit *[unique local] (unit ->[local] unit)). |}]

let%expect_test "lock_once_sum_function_path_left" =
  run_infer
    {|
let bundle =
  (left(((fun x => x) : (unit ->[local many] unit))))
  : ((unit ->[local many] unit) +[unique local] unit)
in
((fun _ => bundle)
 : (unit ->[local once] ((unit ->[local many] unit) +[unique local] unit)))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via sum.left). Captured value had type ((unit ->[local] unit) +[unique local] unit). |}]

let%expect_test "lock_once_sum_function_path_right" =
  run_infer
    {|
let bundle =
  (right(((fun x => x) : (unit ->[local many] unit))))
  : (unit +[unique local] (unit ->[local many] unit))
in
((fun _ => bundle)
 : (unit ->[local once] (unit +[unique local] (unit ->[local many] unit))))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via sum.right). Captured value had type (unit +[unique local] (unit ->[local] unit)). |}]

let%expect_test "lock_once_nested_pair_path" =
  run_infer
    {|
let nested =
  ((unit,
    ((fun x => x) : (unit ->[local many] unit)))
   : (unit *[unique local] (unit ->[local many] unit)))
in
let bundle =
  (nested, unit)
  : ((unit *[unique local] (unit ->[local many] unit)) *[unique local] unit)
in
((fun _ => bundle)
 : (unit
    ->[local once]
    ((unit *[unique local] (unit ->[local many] unit)) *[unique local] unit)))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via pair.right -> pair.left). Captured value had type ((unit *[unique local] (unit ->[local] unit)) *[unique local] unit). |}]

let%expect_test "lock_once_nested_sum_path" =
  run_infer
    {|
let nested =
  (left(((fun x => x) : (unit ->[local many] unit))))
  : ((unit ->[local many] unit) +[unique local] unit)
in
let bundle =
  (right(nested))
  : (unit +[unique local] ((unit ->[local many] unit) +[unique local] unit))
in
((fun _ => bundle)
 : (unit
    ->[local once]
    (unit +[unique local] ((unit ->[local many] unit) +[unique local] unit))))
|};
  [%expect {| mode_error=Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via sum.left -> sum.right). Captured value had type (unit +[unique local] ((unit ->[local] unit) +[unique local] unit)). |}]

let%expect_test "lock_many_nested_pair_alias_ok" =
  run_infer
    {|
let nested =
  ((unit,
    ((fun x => x) : (unit ->[local once] unit)))
   : (unit *[unique local] (unit ->[local once] unit)))
in
let bundle =
  (nested, unit)
  : ((unit *[unique local] (unit ->[local once] unit)) *[unique local] unit)
in
((fun _ => bundle)
 : (unit
    ->[local many]
    ((unit *[aliased local] (unit ->[local once] unit)) *[local] unit)))
|};
  [%expect {| type=(unit ->[local] ((unit *[local] (unit ->[local once] unit)) *[local] unit)) |}]

let%expect_test "lock_many_nested_sum_alias_ok" =
  run_infer
    {|
let nested =
  (left(((fun x => x) : (unit ->[local once] unit))))
  : ((unit ->[local once] unit) +[unique local] unit)
in
let bundle =
  (right(nested))
  : (unit +[unique local] ((unit ->[local once] unit) +[unique local] unit))
in
((fun _ => bundle)
 : (unit
    ->[local many]
    (unit +[local]
          ((unit ->[local once] unit) +[local] unit))))
|};
  [%expect {| type=(unit ->[local] (unit +[local] ((unit ->[local once] unit) +[local] unit))) |}]

let%expect_test "process_locking_pair" =
  run_process
    {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair)
 : (unit ->[local many] (unit *[unique local] unit)))
|};
  [%expect {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair)
 : (unit ->[local many] (unit *[unique local] unit)))
> error: (unit *[local] unit) is not a subtype of (unit *[unique local] unit)
|}]

let%expect_test "process_locking_sum" =
  run_process
    {|
let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum)
 : (unit ->[local many] (unit +[unique local] unit)))
|};
  [%expect {|
let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum)
 : (unit ->[local many] (unit +[unique local] unit)))
> error: (unit +[local] unit) is not a subtype of (unit +[unique local] unit)
|}]

let%expect_test "process_locking_nested_pair" =
  run_process
    {|
let nested =
  ((unit,
    ((fun x => x) : (unit ->[local many] unit)))
   : (unit *[unique local] (unit ->[local many] unit))) in
((fun _ => nested)
 : (unit ->[local once] (unit *[unique local] (unit ->[local many] unit))))
|};
  [%expect {|
let nested =
  ((unit,
    ((fun x => x) : (unit ->[local many] unit)))
   : (unit *[unique local] (unit ->[local many] unit))) in
((fun _ => nested)
 : (unit ->[local once] (unit *[unique local] (unit ->[local many] unit))))
> error: Variable nested is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via pair.right). Captured value had type (unit *[unique local] (unit ->[local] unit)).
|}]

let%expect_test "process_locking_function_path" =
  run_process
    {|
let bundle =
  (((fun x => x) : (unit ->[local many] unit)), unit)
  : ((unit ->[local many] unit) *[unique local] unit) in
((fun _ => bundle)
 : (unit ->[local once] ((unit ->[local many] unit) *[unique local] unit)))
|};
  [%expect {|
let bundle =
  (((fun x => x) : (unit ->[local many] unit)), unit)
  : ((unit ->[local many] unit) *[unique local] unit) in
((fun _ => bundle)
 : (unit ->[local once] ((unit ->[local many] unit) *[unique local] unit)))
> error: Variable bundle is unavailable inside a local once closure: captured function expects mode local, but closure runs at local once (via pair.left). Captured value had type ((unit ->[local] unit) *[unique local] unit).
|}]

let%expect_test "process_locking_mix" =
  run_process
    {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair)
 : (unit ->[local once] (unit *[unique local] unit)))

let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum)
 : (unit ->[local many] (unit +[unique local] unit)))
|};
  [%expect {|
let unique_pair = ((unit, unit) : (unit *[unique local] unit)) in
((fun _ => unique_pair)
 : (unit ->[local once] (unit *[unique local] unit)))
> (unit ->[local once] (unit *[unique local] unit))

let unique_sum = (left(unit) : (unit +[unique local] unit)) in
((fun _ => unique_sum)
 : (unit ->[local many] (unit +[unique local] unit)))
> error: (unit +[local] unit) is not a subtype of (unit +[unique local] unit)
|}]
