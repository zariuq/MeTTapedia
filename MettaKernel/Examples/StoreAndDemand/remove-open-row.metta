; Calibration fixture: remove-open-row
!(let $s (new-space) (let $_ (add-atom $s (item $stored)) (let $removed (remove-atom $s (item a)) (let $left (collapse (match $s (item $x) $x)) (result $removed $left)))))
