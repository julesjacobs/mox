type ('a, 'b) t = ('a * 'b) list

let make pairs =
  let sorted = List.sort compare pairs in
  let rec dedup acc = function
    | [] -> List.rev acc
    | x :: xs ->
      (match acc with
       | y :: _ when y = x -> dedup acc xs
       | _ -> dedup (x :: acc) xs)
  in
  dedup [] sorted

let to_list r = r

let equal a b = to_list a = to_list b

let intersection r1 r2 =
  let filtered = List.filter (fun pair -> List.exists ((=) pair) r2) r1 in
  make filtered

let compose r1 r2 =
  let step (a, b) acc =
    let produced =
      List.filter_map
        (fun (b', c) -> if b = b' then Some (a, c) else None)
        r2
    in
    produced @ acc
  in
  make (List.fold_right step r1 [])

let restrict_diagonal r =
  make (List.filter (fun (a, b) -> a = b) r)
