; ============================================================================
; DoF 6 — Interval point selector
; ----------------------------------------------------------------------------
; THE KNOB.  A nontrivial credal interval [L,U] does NOT force a single displayed
;   point.  Lower, midpoint, upper, or a risk-adjusted selector are all valid
;   read-offs of the same interval, for different decisions.
;
; WHY KEEP IT.  Safety-critical planning reads the lower envelope; exploratory
;   ranking reads the midpoint; opportunity search reads the upper.  The paper
;   uses midpoint as the neutral PLN strength display, but that is a choice.
;
; Lean oracle: PLNTruthTheoryIndex  generic_itv_does_not_force_point_projection
;   (the typed ITV selector ranges over lower/midpoint/upper).
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (sel-lower $L $U) $L)
(= (sel-mid   $L $U) (/ (+ $L $U) 2.0))
(= (sel-upper $L $U) $U)

; Same interval [0.2, 0.8], three policies:
!(sel-lower 0.2 0.8)   ; 0.2   safety: act on the worst case
!(sel-mid   0.2 0.8)   ; 0.5   neutral ranking
!(sel-upper 0.2 0.8)   ; 0.8   opportunity: act on the best case

; A thresholded decision flips with the selector at threshold 0.6:
;   lower 0.2 < 0.6 -> reject ; upper 0.8 > 0.6 -> accept.
; POSITIVE: clinical go/no-go uses sel-lower (conservative).
; NEGATIVE: reporting only sel-mid hides that the same interval would be rejected
;   under a safety policy — the selector is a real, decision-bearing knob.
