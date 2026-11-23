; Calibration fixture: sequential-adds
!(let $s (new-space) (let $_ (add-atom $s (item a)) (let $_ (add-atom $s (item b)) (collapse (match $s (item $x) $x)))))
