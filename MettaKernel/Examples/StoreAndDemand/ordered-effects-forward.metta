; Calibration fixture: ordered-effects-forward
!(let $s (new-space) (let $_ (add-atom $s (n 1)) (let $answers (collapse (let $op (superpose (double inc)) (let $old (match $s (n $v) $v) (let $new (if (== $op double) (* $old 2) (+ $old 1)) (let $_ (remove-atom $s (n $old)) (let $_ (add-atom $s (n $new)) 7)))))) (let $final (collapse (match $s (n $v) $v)) (result $answers $final)))))
