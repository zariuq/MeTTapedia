; Calibration fixture: routing-error-retains-take
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $result (case (transform $s (take (item $x)) done 42) (((Error $site $reason) caught) ($_ normal))) (let $left (collapse (match $s (item $x) $x)) (result $result $left)))))
