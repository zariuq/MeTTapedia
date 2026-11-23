; Calibration fixture: destination-count
!(let $s (new-space) (let $count (transform $s () (, (item a) (item b)) $s) (let $left (collapse (match $s (item $x) $x)) (result $count $left))))
