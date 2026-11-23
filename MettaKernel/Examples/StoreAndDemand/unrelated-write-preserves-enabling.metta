; Calibration fixture: unrelated-write-preserves-enabling
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (other)) (let $answers (collapse (transform $s (take (item a)) yes)) (let $other (collapse (match $s (other) yes)) (result $answers $other))))))
