; Calibration fixture: uniqueness-spoiled-by-addition
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $_ (add-atom $s (rate old)) (let $answers (collapse (transform $s (, (unique (rate $r)) (take (item $x))) (rate new) $s)) (let $left (collapse (match $s (item $x) $x)) (let $rates (collapse (match $s (rate $r) $r)) (result $answers $left $rates))))))))
