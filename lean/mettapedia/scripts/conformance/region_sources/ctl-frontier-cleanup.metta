(fr f 0 1)
(fr f 0 1)
(fr f 0 2)
(fr f 1 3)
(fr g 0 4)

(= (drop $f $k)
  (size-atom (collapse
    (match &self (fr $f $k $x) (remove-atom &self (fr $f $k $x))))))

!(drop f 0)
!(collapse (match &self (fr f 0 $x) $x))
!(collapse (match &self (fr f 1 $x) $x))
!(collapse (match &self (fr g 0 $x) $x))
!(drop f 0)
