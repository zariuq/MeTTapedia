; ============================================================================
; DoF 4 — Confidence chart (which map from evidence-weight to a [0,1] display)
; ----------------------------------------------------------------------------
; THE KNOB.  Recovering evidence only needs SOME invertible chart on total
;   weight.  It does NOT by itself force the PLN/NARS odds chart.  The extra
;   semantic law that singles out odds is width-complement compatibility (DoF 5).
;   Below, the SAME decoded evidence is shown by three different charts:
;     pln-c        w/(w+k)                 (PLN/NARS odds — the forced one once gated)
;     reservehalf  w/(2w+k)               (a reconstructive chart; NOT width-complement)
;     arctan       (2/pi) * atan(w/k)     (a compressed display chart)
;
; WHY KEEP IT.  A user-facing risk dashboard may want a compressed visual scale.
;   But REVISION must run in evidence-weight space, not in a display chart.
;
; Lean oracle: PLNConfidenceWeight  walley_width_complement_forces_plnOdds (the odds chart is
;   forced after the bridge)  and  reserveHalfCoordinate_not_walley_width_complement (reserve-half
;   reconstructs evidence but fails the bridge — so "can reconstruct" != "is PLN confidence").
; Portable: atan-math is available on BOTH CeTTa and PeTTa; pi is written as a
; numeric literal because PeTTa treats PI as an atom, not an arithmetic constant.
; ============================================================================

(= (pi) 3.141592653589793)
(= (pln-c $w $k)        (/ $w (+ $w $k)))
(= (reservehalf-c $w $k) (/ $w (+ (* 2.0 $w) $k)))
(= (arctan-c $w $k)     (* (/ 2.0 (pi)) (atan-math (/ $w $k))))

; Same weight w=5.0, scale k=1.0, three charts -> three displayed confidences:
!(pln-c 5.0 1.0)         ; 0.8333   PLN odds
!(reservehalf-c 5.0 1.0) ; 0.4545   reconstructive but not width-complement
!(arctan-c 5.0 1.0)      ; ~0.8743  compressed display

; POSITIVE: a dashboard may legitimately show arctan-c for visual compression.
; NEGATIVE: if you revise (combine evidence) in any chart other than the weight
;   space, you double-damp — the charts above disagree, so the chart is a real choice.
