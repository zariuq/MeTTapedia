type task = Task of string * int * bool

let rec insert task tasks =
  match task, tasks with
  | _, [] -> [task]
  | Task (_, score, _), (Task (_, next_score, _) as next) :: rest ->
      if score >= next_score then task :: tasks
      else next :: insert task rest

let rec rank tasks =
  match tasks with
  | [] -> []
  | (Task (_, _, eligible) as task) :: rest ->
      let ranked = rank rest in
      if eligible then insert task ranked else ranked

let rec take count tasks =
  if count <= 0 then []
  else match tasks with
    | [] -> []
    | task :: rest -> task :: take (count - 1) rest

let top count tasks = take count (rank tasks)

let rec names tasks =
  match tasks with
  | [] -> []
  | Task (name, _, _) :: rest -> name :: names rest

let score_above threshold =
  fun task -> match task with Task (_, score, _) -> score > threshold
