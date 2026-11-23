; Calibration fixture: independent-writers-both-fire
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (let $answers (collapse (transform $s (take (item $x)) (done $x) $s)) (let $left (collapse (match $s (item $x) $x)) (let $done (collapse (match $s (done $x) $x)) (result $answers $left $done)))))))
