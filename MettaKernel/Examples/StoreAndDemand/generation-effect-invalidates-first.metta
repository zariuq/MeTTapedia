; Calibration fixture: generation-effect-invalidates-first
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $answers (collapse (transform $s (, (take (item $x)) (let $_ (remove-atom $s (item $x)))) yes)) (let $left (collapse (match $s (item $x) $x)) (result $answers $left)))))
