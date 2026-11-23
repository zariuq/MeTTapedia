(= (pick $x#0) (let (row $p) (get-state scope-cell) (let $p b $p)))
!(change-state! scope-cell (row $x))
!(pick a)
