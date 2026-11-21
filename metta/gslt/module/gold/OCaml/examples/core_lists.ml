let rec map f xs = match xs with [] -> [] | x :: rest -> f x :: map f rest;;
let rec fold_left f acc xs = match xs with [] -> acc | x :: rest -> fold_left f (f acc x) rest;;
let rec append xs ys = match xs with [] -> ys | x :: rest -> x :: append rest ys;;
let rec rev acc xs = match xs with [] -> acc | x :: rest -> rev (x :: acc) rest;;
(map (fun x -> x + 1) [1; 2; 3], fold_left (fun x y -> x + y) 0 [1; 2; 3],
 append [1; 2] [3; 4], rev [] [1; 2; 3]);;
