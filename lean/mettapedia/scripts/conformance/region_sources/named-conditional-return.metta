(= (in $f $x)
  (not (== (collapse (once (match &self (sat $f $x) t))) ())))

(= (outer $f $x)
  (let $kept 9
    (let $result (if (in $f $x) (quote held) (cut))
      (quote ($result $kept)))))
(= (outer $f $x) later)

!(collapse (outer 10 1))
!(add-atom &self (sat 10 1))
!(add-atom &self (sat 10 1))
!(collapse (outer 10 1))

(= (double-in $f $x) (in $f $x))
(= (double-in $f $x) (in $f $x))
!(collapse (if (double-in 10 1) (quote held) (quote absent)))
