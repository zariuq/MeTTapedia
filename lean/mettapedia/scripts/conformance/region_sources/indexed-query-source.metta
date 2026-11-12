(edge 0 1)
(edge 0 1)
(edge 1 2)
(edge 2 0)

!(size-atom (collapse
  (match &self (edge $x $y)
    (match &self (edge $y $z)
      (match &self (edge $z $x) true)))))

!(size-atom (collapse
  (match &self (edge 0 $y)
    (match &self (edge $y $z)
      (match &self (edge $z 0) true)))))

!(size-atom (collapse (match &self (edge $x $x) true)))

!(size-atom (collapse
  (match &self (edge 0 $y)
    (match &self (edge 0 $y) true))))

!(size-atom (collapse true))
