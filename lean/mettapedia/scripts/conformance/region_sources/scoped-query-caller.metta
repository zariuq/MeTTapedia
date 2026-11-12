(row 7)
(row 8)
(payload (add-atom &self (unexpected)))

!(size-atom (collapse
  (let $collected (collapse (match &self (row $x) (add-atom &self (mark $x))))
    (add-atom &self (mark 99)))))
!(collapse (match &self (mark $x) $x))

!(size-atom (collapse (match &self (row $x)
  (let $ignored (add-atom &self (child $x))
    (add-atom &self (child 99))))))
!(collapse (match &self (child $x) $x))

!(collapse (let $result (match &self (row $x) (quote ok))
  (quote ($result $x))))
!(size-atom (collapse (let $value (match &self (payload $x) $x)
  (quote ($value $x)))))
!(collapse (match &self (unexpected) t))
