; Calibration fixture: remove-multiplicity
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item a)) (let $removed (remove-atom $s (item a)) (let $left (collapse (match $s (item $x) $x)) (result $removed $left))))))
