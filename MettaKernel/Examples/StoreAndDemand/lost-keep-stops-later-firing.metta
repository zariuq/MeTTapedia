; Calibration fixture: lost-keep-stops-later-firing
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $_ (add-atom $s (lock)) (let $answers (collapse (transform $s (, (read (lock)) (take (item $x))) (let $_ (remove-atom $s (lock)) (got $x)))) (let $left (collapse (match $s (item $x) $x)) (result $answers $left)))))))
