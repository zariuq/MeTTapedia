; Prime Motivation 03: two independent maps and the missing parallel license.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: flip every bit in two lists and return both results.  The
; source can also describe a proposed wave and the resources claimed by each
; branch.  It cannot prove that the resource occurrences are separate.
;
; Prime payoff: CostEffectSeparation retains an exact common-source multiset
; decomposition.  A certificate compiles to an indexed ParallelCostSchedule
; with WorkSpan <2,1>; a contested single purse has no license.  The ordinary
; pair-map still runs when analysis cannot establish separation.
; Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.
;     compiledSchedule_workSpan
;   Mettapedia.Languages.MeTTa.Prime.NativeFibredCost.Examples.
;     contested_has_no_prime_parallel_license
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.
;     CostEffectSeparation.realizes_productSquare
;
; The type/effect layer licenses parallel execution; it does not redefine map.

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

!(test
  (pair-map
    (Cons zero (Cons one Nil))
    (Cons one (Cons one Nil)))
  (Pair
    (Cons one (Cons zero Nil))
    (Cons zero (Cons zero Nil))))

!(test
  (describe-wave
    purse-left purse-right
    (Cons zero Nil) (Cons one Nil))
  (Wave (Uses purse-left (Cons one Nil))
        (Uses purse-right (Cons zero Nil))))

; Negative teaching case: ordinary data can describe a contested resource.
; Prime must refuse the parallel license, not refuse evaluation of this term.
!(test
  (describe-wave
    shared-purse shared-purse
    (Cons zero Nil) (Cons one Nil))
  (Wave (Uses shared-purse (Cons one Nil))
        (Uses shared-purse (Cons zero Nil))))
