; Calibration fixture: add-comma-is-one-atom
!(let $s (new-space) (let $_ (add-atom $s (, a b)) (collapse (match $s $row $row))))
