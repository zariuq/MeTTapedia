type 'a tree = Empty | Node of 'a tree * 'a * 'a tree

let rec append left right =
  match left with [] -> right | value :: rest -> value :: append rest right

let rec map_list transform values =
  match values with
  | [] -> []
  | value :: rest -> transform value :: map_list transform rest

let rec map_tree transform tree =
  match tree with
  | Empty -> Empty
  | Node (left, value, right) ->
      Node (map_tree transform left, transform value, map_tree transform right)

let rec flatten tree =
  match tree with
  | Empty -> []
  | Node (left, value, right) -> append (flatten left) (value :: flatten right)

let shape tree =
  match tree with
  | Empty -> "empty"
  | Node (Empty, _, Empty) -> "leaf"
  | Node (_, _, _) -> "branch"

let use_polymorphic_identity () =
  let identity value = value in
  (identity 7, identity true, identity "task")
