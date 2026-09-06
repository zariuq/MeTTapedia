; Prime Motivation 03: two independent maps and the missing parallel license.
; Dialect: Hyperon Experimental MeTTa.
;
; `pair-map` is ordinary MeTTa.  A future Prime execution may use parallel
; span only after effect analysis constructs the retained separation proof.
; Failure to construct it leaves this same term available to the normal
; evaluator.
;
; Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.
;     compiledSchedule_workSpan
;   Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.Examples.
;     contested_analysis_produces_no_schedule
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost.
;     parallel_two_events_ne_sequential

(= (flip zero) one)
(= (flip one) zero)

(= (map-flip Nil) Nil)
(= (map-flip (Cons $bit $rest))
   (Cons (flip $bit) (map-flip $rest)))

(= (pair-map $left $right)
   (Pair (map-flip $left) (map-flip $right)))

(= (describe-wave $left-resource $right-resource $left $right)
   (Wave
     (Uses $left-resource (map-flip $left))
     (Uses $right-resource (map-flip $right))))

!(assertEqual
  (pair-map
    (Cons zero (Cons one Nil))
    (Cons one (Cons one Nil)))
  (Pair
    (Cons one (Cons zero Nil))
    (Cons zero (Cons zero Nil))))

!(assertEqual
  (describe-wave
    purse-left purse-right
    (Cons zero Nil) (Cons one Nil))
  (Wave (Uses purse-left (Cons one Nil))
        (Uses purse-right (Cons zero Nil))))

!(assertEqual
  (describe-wave
    shared-purse shared-purse
    (Cons zero Nil) (Cons one Nil))
  (Wave (Uses shared-purse (Cons one Nil))
        (Uses shared-purse (Cons zero Nil))))
