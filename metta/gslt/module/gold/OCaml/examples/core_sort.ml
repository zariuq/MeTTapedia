(* Equal elements are retained. (* Nested comments are lexical data. *) *)
let rec insert x xs = match xs with
  [] -> [x]
| y :: rest -> if x <= y then x :: xs else y :: insert x rest;;
let rec sort xs = match xs with [] -> [] | x :: rest -> insert x (sort rest);;
sort [3; 1; 2; 1];;
