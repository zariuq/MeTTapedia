; Calibration fixture: full evaluation and one invocation have different boundaries.
!(collapse (chain (metta (empty) %Undefined% &self) $x nope))
!(collapse (chain (eval (empty)) $x invocation-result))
!(collapse (chain (evalc (empty) &self) $x invocation-result))
