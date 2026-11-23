; Calibration fixture: evaluation demand survives an inert chain context.
(: computed (-> Number))
(= (computed) (+ 1 2))
!(chain data $unused (metta (computed) Number &self))
!(chain data $unused
    (chain (metta (+ 1 2) Atom &self) $held (eval (== $held (+ 1 2)))))
!(chain data $unused
    (chain (metta (+ 1 2) Atom &self) $held (eval (== $held 3))))
