(sat 1 7)
(sat 1 7)
(sat 1 8)

!(let $formula 1
  (let $node 7
    (let $payload t
      (not (== (collapse (once (match
        (let $ignored (println! captured-prefix) &self)
        (sat $formula $node) $payload))) ())))))
!(let $formula 1
  (let $node 9
    (let $payload false
      (not (== (collapse (once (match &self (sat $formula $node) $payload))) ())))))
!(let $formula 1
  (let $node 7
    (let $payload false
      (collapse (once (match &self (sat $formula $node) $payload))))))
