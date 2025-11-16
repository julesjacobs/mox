open Relations

exception Inconsistent of string

type var = int
type relation = (int, int) Relations.t

module PairTbl = Hashtbl.Make (struct
  type t = int * int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

let fresh_var =
  let counter = ref 0 in
  fun () ->
    let v = !counter in
    incr counter;
    v

let domains : (var, int list) Hashtbl.t = Hashtbl.create 32
let relation_tbl : relation PairTbl.t = PairTbl.create 64
let outgoing : (var, int list) Hashtbl.t = Hashtbl.create 32
let incoming : (var, int list) Hashtbl.t = Hashtbl.create 32

let add_edge tbl src dst =
  let neighbors = Hashtbl.find_opt tbl src |> Option.value ~default:[] in
  if List.mem dst neighbors then ()
  else Hashtbl.replace tbl src (dst :: neighbors)

let add_relation_entry src dst rel =
  PairTbl.replace relation_tbl (src, dst) rel;
  add_edge outgoing src dst;
  add_edge incoming dst src

let domain v =
  match Hashtbl.find_opt domains v with
  | Some d -> d
  | None -> invalid_arg "intsolver: unknown variable"

let full_relation v1 v2 =
  let d1 = domain v1 in
  let d2 = domain v2 in
  let pairs =
    List.fold_left
      (fun acc a ->
        List.fold_left (fun acc b -> (a, b) :: acc) acc d2)
      [] d1
    |> List.rev
  in
  Relations.make pairs

let clamp_relation v1 v2 rel =
  let d1 = domain v1 in
  let d2 = domain v2 in
  let allowed (a, b) = List.mem a d1 && List.mem b d2 in
  Relations.make (List.filter allowed (Relations.to_list rel))

let current_relation v1 v2 =
  match PairTbl.find_opt relation_tbl (v1, v2) with
  | Some rel -> rel
  | None -> full_relation v1 v2

let relation_is_empty rel = Relations.to_list rel = []

let queue_take_opt q =
  if Queue.is_empty q then None else Some (Queue.pop q)

let rec domain_from_diagonal rel =
  Relations.to_list rel
  |> List.filter_map (fun (a, b) -> if a = b then Some a else None)
  |> List.sort_uniq compare

and reassert_full queue v1 v2 =
  let full = full_relation v1 v2 in
  ignore (ensure_relation queue v1 v2 full)

and restrict_domain queue v allowed =
  if allowed = [] then raise (Inconsistent "domain restriction emptied domain");
  let allowed = List.sort_uniq compare allowed in
  let current = domain v in
  if allowed = current then ()
  else (
    Hashtbl.replace domains v allowed;
    let outs = Hashtbl.find_opt outgoing v |> Option.value ~default:[] in
    List.iter (fun dst -> reassert_full queue v dst) outs;
    let ins = Hashtbl.find_opt incoming v |> Option.value ~default:[] in
    List.iter (fun src -> reassert_full queue src v) ins)

and restrict_domain_from_diagonal queue v rel =
  let allowed = domain_from_diagonal rel in
  restrict_domain queue v allowed

and restrict_domain_from_relation queue projection rel v =
  let projection_values =
    Relations.to_list rel
    |> List.map projection
    |> List.sort_uniq compare
  in
  restrict_domain queue v projection_values

and ensure_relation queue v1 v2 rel =
  let rel = clamp_relation v1 v2 rel in
  let existing = current_relation v1 v2 in
  let intersected = Relations.intersection existing rel in
  if Relations.equal existing intersected then false
  else (
    if relation_is_empty intersected then
      raise (Inconsistent "relation became empty");
    add_relation_entry v1 v2 intersected;
    if v1 = v2 then
      restrict_domain_from_diagonal queue v1 intersected
    else (
      restrict_domain_from_relation queue fst intersected v1;
      restrict_domain_from_relation queue snd intersected v2);
    Queue.push (v1, v2) queue;
    true
  )

let rec saturate queue =
  match queue_take_opt queue with
  | None -> ()
  | Some (src, dst) ->
    let rel_src_dst = current_relation src dst in
    let forward_neighbors = Hashtbl.find_opt outgoing dst |> Option.value ~default:[] in
    List.iter
      (fun target ->
        let dst_target = current_relation dst target in
        let composed = Relations.compose rel_src_dst dst_target in
        if ensure_relation queue src target composed then ()
      )
      forward_neighbors;
    let backward_neighbors = Hashtbl.find_opt incoming src |> Option.value ~default:[] in
    List.iter
      (fun origin ->
        let origin_src = current_relation origin src in
        let composed = Relations.compose origin_src rel_src_dst in
        if ensure_relation queue origin dst composed then ()
      )
      backward_neighbors;
    saturate queue

let newvar domain_values =
  let clean =
    domain_values
    |> List.sort_uniq compare
  in
  if clean = [] then invalid_arg "intsolver: empty domain";
  let v = fresh_var () in
  Hashtbl.replace domains v clean;
  v

let assert_rel rel v1 v2 =
  let rel = clamp_relation v1 v2 rel in
  let top = full_relation v1 v2 in
  if Relations.equal rel top then ()
  else (
    let queue = Queue.create () in
    if ensure_relation queue v1 v2 rel then saturate queue )

let get_rel v1 v2 = current_relation v1 v2
