; Calibration fixture: petta-raise-stops-tail
!(let $s (new-space) (let $fault (catch (let $_ (get-state store-demand-missing-state) (add-atom $s (later)))) (let $tag (car-atom $fault) (let $left (collapse (match $s (later) yes)) (result $tag $left)))))
