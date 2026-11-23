; Calibration fixture: read-take-accepted
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item a)) (let $answers (collapse (transform $s (, (read (item a)) (take (item a))) yes)) (let $left (collapse (match $s (item $x) $x)) (result $answers $left))))))
