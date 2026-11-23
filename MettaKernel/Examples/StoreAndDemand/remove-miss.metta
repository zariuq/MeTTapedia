; Calibration fixture: remove-miss
!(let $s (new-space) (let $_ (add-atom $s (item b)) (let $removed (remove-atom $s (item a)) (let $left (collapse (match $s (item $x) $x)) (result $removed $left)))))
