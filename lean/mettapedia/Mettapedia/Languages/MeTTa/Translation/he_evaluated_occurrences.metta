; Stored copies produce two occurrences. Re-entering the held argument would
; incorrectly multiply them when the caller returns its enclosing expression.
(= (g $x) (wrap $x))
(= (fr $x) NotReducible)
(= (fr $x) NotReducible)
!(collapse (g (fr 1)))
