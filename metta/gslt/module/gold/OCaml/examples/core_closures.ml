let make_adder n = fun x -> x + n;;
let compose f g x = f (g x);;
let captured = 3;;
let plus_captured x = x + captured;;
let captured = 100;;
let add_two = make_adder 2;;
(plus_captured 4, add_two 5, compose add_two (make_adder 10) 1);;
