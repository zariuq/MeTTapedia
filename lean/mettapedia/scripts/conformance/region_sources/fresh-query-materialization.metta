(edge 0 1)
(edge 0 2)

!(size-atom (collapse
  (match &self (edge $x $y)
    (let $payload (quote (sat f $x))
      (if (== (collapse (match &self $payload true)) ())
          (add-atom &self $payload)
          (empty))))))
!(size-atom (collapse (match &self (sat f $x) true)))
!(size-atom (collapse
  (match &self (edge $x $y)
    (let $payload (quote (sat f $x))
      (if (== (collapse (match &self $payload true)) ())
          (add-atom &self $payload)
          (empty))))))
!(size-atom (collapse (match &self (sat f $x) true)))
!(size-atom (collapse
  (match &self (edge $x $y)
    (let $payload (quote (sat f $x))
      (if (== (collapse (match &self $payload true)) ())
          (add-atom &self $payload)
          true)))))
