!(let $graph (new-space)
  (let $inserted (add-atom $graph (e $stored-origin 1 3))
    (collapse (match $graph (e 0 $vertex $weight) (quote ($vertex $weight))))))
