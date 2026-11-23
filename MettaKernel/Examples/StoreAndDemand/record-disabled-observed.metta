; Calibration fixture: record-disabled-observed
!(let $s (new-space) (let $log (new-space) (let $_ (add-atom $s (item a)) (let $rows (collapse (match $s (item $x) $x)) (let $records (collapse (match $log (made $x) $x)) (result $rows $records))))))
