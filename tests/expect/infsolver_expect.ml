open Infsolver

let fmt n = if n = infinity then "+oo" else string_of_int n

let dump labeled =
  List.iter
    (fun (label, v) ->
      Printf.printf "%s: [%s, %s]\n" label (fmt (get_lower v))
        (fmt (get_upper v)))
    labeled

let%expect_test "propagates through chains" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  let z = create_var ~name:"z" () in
  assert_leq x y;
  assert_leq y z;
  assert_eq_const x 3;
  dump [ ("x", x); ("y", y); ("z", z) ];
  [%expect
    {|
    x: [3, 3]
    y: [3, +oo]
    z: [3, +oo]
  |}]

let%expect_test "predecessor enforces successor floor" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_predecessor x y;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [1, +oo]
    y: [0, +oo]
  |}]

let%expect_test "contradiction when predecessor clashes with bound" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_eq_const x 0;
  (try assert_predecessor x y with
  | Contradiction msg -> Printf.printf "contradiction: %s\n" msg);
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    contradiction: Variable 'x' Inconsistent: Lower(1) > Upper(0)
    x: [1, 0]
    y: [0, +oo]
  |}]

let%expect_test "infinity sticks through predecessor" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_eq_const x infinity;
  assert_predecessor x y;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [+oo, +oo]
    y: [+oo, +oo]
  |}]
