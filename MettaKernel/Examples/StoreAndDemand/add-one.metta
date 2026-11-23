; Calibration fixture: add-one
!(let $s (new-space) (let $_ (add-atom $s (item a)) (collapse (match $s (item $x) $x))))
