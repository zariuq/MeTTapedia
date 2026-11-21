let rec even n = if n = 0 then true else odd (n - 1)
and odd n = if n = 0 then false else even (n - 1);;
(even 8, odd 7, even 7);;
