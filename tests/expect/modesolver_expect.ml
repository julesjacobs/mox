let print_relation ~to_string_a ~to_string_b rel =
  rel
  |> Relations.to_list
  |> List.map (fun (a, b) ->
         Printf.sprintf "%s -> %s" (to_string_a a) (to_string_b b))
  |> List.sort String.compare
  |> List.iter print_endline

let%expect_test "uniqueness leq_to closure" =
  let module U = Modesolver.Uniqueness in
  let x = U.new_var () in
  let y = U.new_var () in
  U.assert_relation U.relation_to x y;
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Uniqueness.to_string
    (U.get_relation x y);
  [%expect
    {|
    aliased -> aliased
    unique -> aliased
    unique -> unique
  |}]

let%expect_test "domain restriction narrows diagonal" =
  let module U = Modesolver.Uniqueness in
  let v = U.new_var () in
  U.restrict_domain [ Modes.Uniqueness.Unique ] v;
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Uniqueness.to_string
    (U.get_relation v v);
  [%expect {|
    unique -> unique
  |}]

let%expect_test "cross-axis relation encoding" =
  let module U = Modesolver.Uniqueness in
  let module C = Modesolver.Contention in
  let u = U.new_var () in
  let c = C.new_var () in
  let cross =
    Relations.make
      [
        (Modes.Uniqueness.Unique, Modes.Contention.Uncontended);
        (Modes.Uniqueness.Aliased, Modes.Contention.Shared);
      ]
  in
  Modesolver.assert_relation cross u c;
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Contention.to_string
    (Modesolver.get_relation u c);
  [%expect {|
    aliased -> shared
    unique -> uncontended
  |}]

let%expect_test "transitive tightening propagates" =
  let module U = Modesolver.Uniqueness in
  let x = U.new_var () in
  let y = U.new_var () in
  let z = U.new_var () in
  U.assert_relation U.relation_to x y;
  U.assert_relation U.relation_to y z;
  U.restrict_domain [ Modes.Uniqueness.Unique ] z;
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Uniqueness.to_string
    (U.get_relation x z);
  [%expect {|
    unique -> unique
  |}]

let%expect_test "inconsistent restriction raises" =
  let module U = Modesolver.Uniqueness in
  let v = U.new_var () in
  (try U.restrict_domain [] v with
  | Modesolver.Inconsistent msg -> Printf.printf "inconsistent: %s\n" msg);
  [%expect {|
    inconsistent: empty domain restriction
  |}]

let diag value = Relations.make [ (value, value) ]

let%expect_test "assert_predicate trims portability" =
  let module P = Modesolver.Portability in
  let v = P.new_var () in
  P.assert_predicate (diag Modes.Portability.Portable) v;
  print_relation ~to_string_a:Modes.Portability.to_string
    ~to_string_b:Modes.Portability.to_string
    (P.get_relation v v);
  [%expect {|
    portable -> portable
  |}]

let%expect_test "areality default relation is cartesian product" =
  let module A = Modesolver.Areality in
  let x = A.new_var () in
  let y = A.new_var () in
  print_relation ~to_string_a:Modes.Areality.to_string
    ~to_string_b:Modes.Areality.to_string
    (A.get_relation x y);
  [%expect {|
    global -> global
    global -> local
    global -> regional
    local -> global
    local -> local
    local -> regional
    regional -> global
    regional -> local
    regional -> regional
  |}]

let%expect_test "relation intersections refine results" =
  let module A = Modesolver.Areality in
  let x = A.new_var () in
  let y = A.new_var () in
  let rel1 =
    Relations.make
      [
        (Modes.Areality.Global, Modes.Areality.Regional);
        (Modes.Areality.Regional, Modes.Areality.Local);
      ]
  in
  let rel2 = Relations.make [ (Modes.Areality.Regional, Modes.Areality.Local) ] in
  A.assert_relation rel1 x y;
  A.assert_relation rel2 x y;
  print_relation ~to_string_a:Modes.Areality.to_string
    ~to_string_b:Modes.Areality.to_string
    (A.get_relation x y);
  [%expect {|
    regional -> local
  |}]

let%expect_test "assert_leq_in for contention reverses ordering" =
  let module C = Modesolver.Contention in
  let a = C.new_var () in
  let b = C.new_var () in
  C.assert_leq_in a b;
  print_relation ~to_string_a:Modes.Contention.to_string
    ~to_string_b:Modes.Contention.to_string
    (C.get_relation a b);
  [%expect {|
    contended -> contended
    shared -> contended
    shared -> shared
    uncontended -> contended
    uncontended -> shared
    uncontended -> uncontended
  |}]

let%expect_test "cross-axis composition propagates restrictions" =
  let module U = Modesolver.Uniqueness in
  let module C = Modesolver.Contention in
  let module L = Modesolver.Linearity in
  let u = U.new_var () in
  let c = C.new_var () in
  let l = L.new_var () in
  let rel_uc =
    Relations.make
      [
        (Modes.Uniqueness.Unique, Modes.Contention.Uncontended);
        (Modes.Uniqueness.Aliased, Modes.Contention.Shared);
      ]
  in
  let rel_cl =
    Relations.make
      [
        (Modes.Contention.Uncontended, Modes.Linearity.Many);
        (Modes.Contention.Shared, Modes.Linearity.Once);
      ]
  in
  Modesolver.assert_relation rel_uc u c;
  Modesolver.assert_relation rel_cl c l;
  L.restrict_domain [ Modes.Linearity.Once ] l;
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Contention.to_string
    (Modesolver.get_relation u c);
  [%expect {|
    aliased -> shared
  |}];
  print_relation ~to_string_a:Modes.Uniqueness.to_string
    ~to_string_b:Modes.Linearity.to_string
    (Modesolver.get_relation u l);
  [%expect {|
    aliased -> once
  |}]

let%expect_test "restrict_domain on axis var keeps multiple values" =
  let module C = Modesolver.Contention in
  let v = C.new_var () in
  C.restrict_domain
    [ Modes.Contention.Shared; Modes.Contention.Contended ]
    v;
  print_relation ~to_string_a:Modes.Contention.to_string
    ~to_string_b:Modes.Contention.to_string
    (C.get_relation v v);
  [%expect {|
    contended -> contended
    shared -> shared
  |}]

let%expect_test "assert_predicate after relation narrows outgoing edges" =
  let module P = Modesolver.Portability in
  let module A = Modesolver.Areality in
  let p = P.new_var () in
  let a = A.new_var () in
  let rel =
    Relations.make
      [
        (Modes.Portability.Portable, Modes.Areality.Global);
        (Modes.Portability.NonPortable, Modes.Areality.Local);
      ]
  in
  Modesolver.assert_relation rel p a;
  P.assert_predicate (diag Modes.Portability.Portable) p;
  print_relation ~to_string_a:Modes.Portability.to_string
    ~to_string_b:Modes.Areality.to_string
    (Modesolver.get_relation p a);
  [%expect {|
    portable -> global
 |}]

let%expect_test "inconsistent cross-axis assertion raises" =
  let module U = Modesolver.Uniqueness in
  let module C = Modesolver.Contention in
  let u = U.new_var () in
  let c = C.new_var () in
  C.restrict_domain [ Modes.Contention.Shared ] c;
  let rel =
    Relations.make [ (Modes.Uniqueness.Unique, Modes.Contention.Uncontended) ]
  in
  (try Modesolver.assert_relation rel u c with
  | Modesolver.Inconsistent msg -> Printf.printf "boom: %s\n" msg);
  [%expect {|
    boom: relation became empty
  |}]

type color = Red | Green | Blue
type size = Small | Large

let%expect_test "custom typed solver variable" =

  let encode_color = function Red -> 0 | Green -> 1 | Blue -> 2 in
  let decode_color = function
    | 0 -> Red
    | 1 -> Green
    | 2 -> Blue
    | _ -> failwith "bad color"
  in
  let encode_size = function Small -> 0 | Large -> 1 in
  let decode_size = function
    | 0 -> Small
    | 1 -> Large
    | _ -> failwith "bad size"
  in
  let c = Modesolver.new_var ~encode:encode_color ~decode:decode_color
      ~domain:[ Red; Green; Blue ]
  in
  let s = Modesolver.new_var ~encode:encode_size ~decode:decode_size
      ~domain:[ Small; Large ]
  in
  let rel =
    Relations.make [ (Red, Small); (Green, Large); (Blue, Large) ]
  in
  Modesolver.assert_relation rel c s;
  Modesolver.restrict_domain [ Large ] s;
  print_relation
    ~to_string_a:(function Red -> "red" | Green -> "green" | Blue -> "blue")
    ~to_string_b:(function Small -> "small" | Large -> "large")
    (Modesolver.get_relation c s);
  [%expect {|
    blue -> large
    green -> large
  |}]

type tag = A | B

let%expect_test "assert_relation intersection between custom vars" =
  let encode = function A -> 0 | B -> 1 in
  let decode = function 0 -> A | 1 -> B | _ -> failwith "tag" in
  let x = Modesolver.new_var ~encode ~decode ~domain:[ A; B ] in
  let y = Modesolver.new_var ~encode ~decode ~domain:[ A; B ] in
  let rel1 = Relations.make [ (A, A); (A, B); (B, B) ] in
  let rel2 = Relations.make [ (A, B) ] in
  Modesolver.assert_relation rel1 x y;
  Modesolver.assert_relation rel2 x y;
  print_relation
    ~to_string_a:(function A -> "A" | B -> "B")
    ~to_string_b:(function A -> "A" | B -> "B")
    (Modesolver.get_relation x y);
  [%expect {|
    A -> B
  |}]

let%expect_test "domain restriction via predicate after cross relation" =
  let module L = Modesolver.Linearity in
  let module P = Modesolver.Portability in
  let l = L.new_var () in
  let p = P.new_var () in
  let rel =
    Relations.make
      [
        (Modes.Linearity.Many, Modes.Portability.NonPortable);
        (Modes.Linearity.Once, Modes.Portability.Portable);
      ]
  in
  Modesolver.assert_relation rel l p;
  P.assert_predicate (diag Modes.Portability.Portable) p;
  print_relation ~to_string_a:Modes.Linearity.to_string
    ~to_string_b:Modes.Portability.to_string
    (Modesolver.get_relation l p);
  [%expect {|
    once -> portable
  |}]

let%expect_test "linearity join_to produces upper bounds" =
  let module L = Modesolver.Linearity in
  let many = L.new_var ~domain:[ Modes.Linearity.Many ] () in
  let once = L.new_var ~domain:[ Modes.Linearity.Once ] () in
  let join = L.join_to many once in
  print_relation
    ~to_string_a:Modes.Linearity.to_string
    ~to_string_b:Modes.Linearity.to_string
    (L.get_relation join join);
  [%expect {|
    once -> once
    once -> never
    never -> never
  |}]

let%expect_test "linearity join_to bounded by constraint" =
  let module L = Modesolver.Linearity in
  let once = L.new_var ~domain:[ Modes.Linearity.Once ] () in
  let never = L.new_var ~domain:[ Modes.Linearity.Never ] () in
  let join = L.join_to once never in
  let bound = L.new_var ~domain:[ Modes.Linearity.Never ] () in
  L.assert_leq_to join bound;
  print_relation
    ~to_string_a:Modes.Linearity.to_string
    ~to_string_b:Modes.Linearity.to_string
    (L.get_relation join join);
  [%expect {|
    never -> never
  |}]
