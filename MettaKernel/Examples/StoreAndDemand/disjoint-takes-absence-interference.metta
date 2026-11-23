; Calibration fixture: disjoint-takes-absence-interference
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $answers (collapse (transform $s (, (take (item $x)) (absent (blocked))) (blocked) $s)) (let $left (collapse (match $s (item $x) $x)) (let $blocked (collapse (match $s (blocked) yes)) (result $answers $left $blocked)))))))
