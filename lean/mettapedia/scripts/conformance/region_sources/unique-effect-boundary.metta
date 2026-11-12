!(collapse (once (unique
  (let $v (superpose (1 1 2))
    (let $written (add-atom &self (outer-once $v)) $v)))))
!(collapse (match &self (outer-once $v) $v))

!(collapse (unique (once
  (let $v (superpose (1 1 2))
    (let $written (add-atom &self (inner-once $v)) $v)))))
!(collapse (match &self (inner-once $v) $v))

!(collapse (unique
  (let $written (add-atom &self (silent-effect 9)) (empty))))
!(collapse (match &self (silent-effect $v) $v))
