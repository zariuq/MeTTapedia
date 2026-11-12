(edge $u 1)
(sat f $u)

!(size-atom (collapse (match &self (edge 0 $y) true)))
!(size-atom (collapse (match &self (sat f 0) true)))
!(if (== (collapse (match &self (sat f 0) true)) ()) absent present)
