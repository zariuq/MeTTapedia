; Calibration fixture: an inert unused chain binder preserves template execution.
!(chain data $unused (eval (+ 1 2)))
!(chain data $unused (chain more-data $also-unused (eval (+ 2 3))))
!(chain data $unused (eval (transform &self () (+ 3 4))))
