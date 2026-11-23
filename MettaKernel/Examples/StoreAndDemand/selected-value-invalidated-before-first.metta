; Calibration fixture: selected-value-invalidated-before-first
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $chosen (match $s (item $x) $x) (let $_ (remove-atom $s (item $chosen)) (let $answers (collapse (transform $s (take (item $chosen)) yes)) (let $left (collapse (match $s (item $x) $x)) (result $answers $left)))))))
