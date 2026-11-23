; Calibration fixture: source-error-retains-earlier-effect
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $result (case (transform $s (, (let $_ (add-atom $s (seen))) (let $v (Error bad boom)) (take (item $x))) done) (((Error $site $reason) caught) ($_ normal))) (let $left (collapse (match $s (item $x) $x)) (let $seen (collapse (match $s (seen) yes)) (result $result $left $seen))))))
