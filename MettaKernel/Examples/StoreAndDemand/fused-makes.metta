; Calibration fixture: fused-makes
!(let $s (new-space) (let $_ (transform $s () (, (item a) (item b)) $s) (collapse (match $s (item $x) $x))))
