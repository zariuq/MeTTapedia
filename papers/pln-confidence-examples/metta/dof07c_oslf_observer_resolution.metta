; ============================================================================
; DoF 7c — OSLF observer resolution shadow  (coarse observer -> width, sharp observer -> collapse)
; ----------------------------------------------------------------------------
; TIER: STRUCTURAL.  This is the concrete intuition-shadow for the generic and
; OSLF distinction/credal bridge:
;   - PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
;   - PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
;   - PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_has_strict_width
;   - PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_collapses_of_class_subsingleton
;
; THE KNOB.  Observational resolution: does the observer still identify a
; distinct pattern q with the target pattern p, or has that class collapsed?
;
; WHY KEEP IT.  A coarse observer can leave a truth query honestly interval-
; valued even when a sharper observer would collapse it to a point. This is a
; real source of width coming from indistinguishability, not from evidence total.
;
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

; Same target pattern p, two observation regimes:
;   coarse observer: {p, q} still look the same -> admissible point masses disagree
;   sharp observer : only p remains live       -> the singleton query collapses
;
; Read this as a toy OSLF scene: the observer is querying the truth of pattern p.
; In the coarse regime, p is still observationally identified with a distinct q.
; In the sharp regime, the live class has shrunk to {p}. The numbers below are
; exactly the width story the OSLF bridge theorem formalizes.

(= (coarse-lower) 0.0)
(= (coarse-upper) 1.0)
(= (coarse-width) (- (coarse-upper) (coarse-lower)))

(= (sharp-lower) 1.0)
(= (sharp-upper) 1.0)
(= (sharp-width) (- (sharp-upper) (sharp-lower)))

!(coarse-lower)   ; 0.0
!(coarse-upper)   ; 1.0
!(coarse-width)   ; 1.0
!(sharp-lower)    ; 1.0
!(sharp-upper)    ; 1.0
!(sharp-width)    ; 0.0

; POSITIVE: preserve observer resolution when width comes from not-yet-made
;   distinctions among patterns.
; NEGATIVE: if we collapse coarse and sharp observation into one surface number,
;   we hide whether the width is evidence-limited or distinction-limited.
