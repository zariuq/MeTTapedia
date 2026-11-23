; Calibration fixture: answerless-firing-prefix
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $answers (collapse (once (transform $s (take (item $x)) (if (== $x a) (empty) (got $x))))) (let $left (collapse (match $s (item $x) $x)) (result $answers $left))))))
