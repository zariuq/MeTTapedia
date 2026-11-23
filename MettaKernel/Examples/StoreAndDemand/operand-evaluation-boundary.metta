; Calibration fixture: operand-evaluation-boundary
!(let $s (new-space) (let $answer (once (superpose ((let $_ (add-atom $s (seen first)) a) (let $_ (add-atom $s (seen later)) b)))) (let $seen (collapse (match $s (seen $x) $x)) (result $answer $seen))))
