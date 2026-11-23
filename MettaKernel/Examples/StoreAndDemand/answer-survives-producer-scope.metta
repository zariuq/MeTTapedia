; Calibration fixture: answer-survives-producer-scope
!(let $value (let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (once (transform $s (item $x) (retained ($x nested))))))) (let $parts (cdr-atom $value) (result $value $parts)))
