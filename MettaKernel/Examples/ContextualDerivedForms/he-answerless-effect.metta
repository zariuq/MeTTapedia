; Calibration fixture: no answer suppresses the continuation, not earlier effects.
!(bind! &q (new-space))
!(collapse (chain (metta (let $_ (add-atom &q seen) (empty)) %Undefined% &self) $ignored
    (eval (add-atom &q wrong))))
!(collapse (match &q $x $x))
