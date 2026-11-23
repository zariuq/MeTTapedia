; Calibration fixture: remove-independent-bindings
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $removed (remove-atom $s (item $x)) (let $left (collapse (match $s (item $x) $x)) (result $removed $left))))))
