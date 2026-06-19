; ============================================================================
; DoF 3 — Evidence total vs evidence ratio (why <s,c> needs TWO numbers)
; ----------------------------------------------------------------------------
; THE KNOB.  Strength reads the +/- RATIO; confidence reads the TOTAL amount.
;   s = n+/(n+ + n-)        c = N/(N + kappa),  N = n+ + n-
;   So (1,1) and (100,100) share strength 0.5 but NOT confidence; and (1,1)
;   and (2,0) can share total evidence but differ in strength.  This is the
;   basic reason the two coordinates cannot be collapsed into one.
;
; WHY KEEP IT.  Reporting only strength hides "how much do we know"; reporting
;   only confidence hides "which way."  Both are needed.
;
; Lean oracle: PLNTruthTower  (strength / total separation, strength_mem_unit_of_total_ne_zero).
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (strength $pos $neg) (/ $pos (+ $pos $neg)))
(= (conf $pos $neg $kappa) (/ (+ $pos $neg) (+ (+ $pos $neg) $kappa)))

; Same ratio (strength 0.5), rising total -> rising confidence:
!(strength 1.0 1.0)        ; 0.5
!(conf 1.0 1.0 1.0)        ; 0.6667
!(conf 10.0 10.0 1.0)      ; 0.9524
!(conf 100.0 100.0 1.0)    ; 0.9950

; Same total (N=2), different ratio -> same confidence, different strength:
!(strength 1.0 1.0)        ; 0.5   balanced
!(strength 2.0 0.0)        ; 1.0   one-sided
!(conf 1.0 1.0 1.0)        ; 0.6667
!(conf 2.0 0.0 1.0)        ; 0.6667  (identical confidence)

; POSITIVE: a benchmark with 100/100 is more trustworthy than 1/1 at the same strength.
; NEGATIVE: collapsing to a single number would equate 1/1 and 100/100 (or 1/1 and 2/0).
