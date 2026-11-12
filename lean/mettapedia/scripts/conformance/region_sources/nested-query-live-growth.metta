(seed)
(seed)
(fr 10 0 1)

(= (in $f $x)
  (not (== (collapse (once (match &self (sat $f $x) t))) ())))
(= (grow $f)
  (size-atom (collapse
    (match &self (seed)
      (match &self (fr $f $round $x)
        (if (in $f $x) (empty)
          (let $ignored (add-atom &self (sat $f $x))
            (add-atom &self (fr $f 1 2)))))))))

!(grow 10)
!(collapse (match &self (sat 10 $x) $x))
!(collapse (match &self (fr 10 1 $x) $x))
!(grow 10)
