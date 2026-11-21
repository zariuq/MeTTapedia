let rec factorial n = if n = 0 then 1 else n * factorial (n - 1);;
let rec fibonacci n = if n < 2 then n else fibonacci (n - 1) + fibonacci (n - 2);;
(factorial 6, fibonacci 10);;
