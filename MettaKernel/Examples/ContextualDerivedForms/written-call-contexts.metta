; Calibration fixture: written-call-contexts
(= (worker) done)
!(worker)
!(let $unused anything (worker))
!(collapse (let $r (worker) $r))
!(case (worker) ((done matched) ($_ wrong)))
