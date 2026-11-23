; Calibration fixture: record-unobserved
!(let $s (new-space) (let $log (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $log (made a)) (let $rows (collapse (match $s (item $x) $x)) (let $records (collapse (match $log (made $x) $x)) $rows))))))
