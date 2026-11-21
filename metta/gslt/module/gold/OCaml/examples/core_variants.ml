type expr = Num of int | Add of expr * expr | Mul of expr * expr | Neg of expr;;
let rec eval e = match e with
  Num n -> n
| Add (left, right) -> eval left + eval right
| Mul (left, right) -> eval left * eval right
| Neg x -> 0 - eval x;;
let simplify e = match e with
  Add (Num 0, x) -> x
| Add (x, Num 0) -> x
| x -> x;;
(eval (Mul (Num 6, Num 7)), eval (simplify (Add (Num 0, Num 9))));;
