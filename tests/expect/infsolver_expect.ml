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

let%expect_test "simple leq propagation" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_leq x y;
  assert_eq_const x 10;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [10, 10]
    y: [10, +oo]
  |}]

let%expect_test "transitive leq chain" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  let z = create_var ~name:"z" () in
  assert_leq x y;
  assert_leq y z;
  assert_eq_const x 50;
  dump [ ("x", x); ("y", y); ("z", z) ];
  [%expect {|
    x: [50, 50]
    y: [50, +oo]
    z: [50, +oo]
  |}]

let%expect_test "constant pinning sets both bounds" =
  reset ();
  let x = create_var ~name:"x" () in
  assert_eq_const x 100;
  dump [ ("x", x) ];
  [%expect {| x: [100, 100] |}]

let%expect_test "predecessor forward propagation" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_predecessor x y;
  assert_eq_const x 10;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [10, 10]
    y: [9, +oo]
  |}]

let%expect_test "predecessor backward propagation" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_predecessor x y;
  assert_eq_const y 20;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [21, +oo]
    y: [20, 20]
  |}]

let%expect_test "contradiction on tightening past upper bound" =
  reset ();
  let x = create_var ~name:"x" () in
  (try
     assert_eq_const x 10;
     assert_eq_const x 11
   with Contradiction msg -> Printf.printf "contradiction: %s\n" msg);
  dump [ ("x", x) ];
  [%expect {|
    contradiction: Variable 'x' Inconsistent: Lower(11) > Upper(10)
    x: [11, 10]
  |}]

let%expect_test "contradiction from leq violation" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_eq_const x 10;
  assert_eq_const y 5;
  (try assert_leq x y with
  | Contradiction msg -> Printf.printf "contradiction: %s\n" msg);
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    contradiction: Variable 'y' Inconsistent: Lower(10) > Upper(5)
    x: [10, 10]
    y: [10, 5]
  |}]

let%expect_test "contradiction from predecessor and leq cycle with constant" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_predecessor x y;
  assert_leq x y;
  (try assert_eq_const y 100 with
  | Contradiction msg -> Printf.printf "contradiction: %s\n" msg);
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    contradiction: Variable 'y' Inconsistent: Lower(+oo) > Upper(100)
    x: [3, +oo]
    y: [+oo, 100]
  |}]

let%expect_test "infinity propagation through leq" =
  reset ();
  let x = create_var ~name:"x" () in
  let y = create_var ~name:"y" () in
  assert_leq x y;
  assert_eq_const x infinity;
  dump [ ("x", x); ("y", y) ];
  [%expect {|
    x: [+oo, +oo]
    y: [+oo, +oo]
  |}]
