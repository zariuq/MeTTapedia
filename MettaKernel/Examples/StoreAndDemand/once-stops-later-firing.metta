; Calibration fixture: once-stops-later-firing
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $answers (collapse (once (transform $s (take (item $x)) (got $x)))) (let $left (collapse (match $s (item $x) $x)) (result $answers $left))))))
