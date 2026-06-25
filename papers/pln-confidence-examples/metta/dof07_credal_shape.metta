; ============================================================================
; DoF 7 — Credal shape beyond one interval  (why <s,c> is a COMPRESSION)
; ----------------------------------------------------------------------------
; TIER: STRUCTURAL.  A single query interval loses the SHAPE of the credal set.
;   Two credal sets can agree on [L,U] for one gamble yet differ on another
;   gamble, on correlations, or under composition.
;
; THE KNOB.  Preserve the joint/credal shape, not just per-marginal intervals.
;
; WHY KEEP IT.  Two drug hypotheses can share the same marginal response
;   interval but differ in adverse-event dependence; an STV per marginal hides
;   the incompatible joint structure.
;
; Lean oracles: PLNTruthTower.CredalProjectionTower (credal envelope vs projective
;   width-complement vs lower-prevision bounds — four distinct semantics of "shape"),
;   plus the generic observation bridge
;   PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
;   / observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
;   and the OSLF specialization
;   PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_has_strict_width
;   / indistObs_indicatorGamble_collapses_of_class_subsingleton.
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

; Two worlds with IDENTICAL marginals P(A)=P(B)=0.5, different joints:
(= (and-positive)  0.5)   ; A,B perfectly dependent  -> P(A and B) = 0.5
(= (and-exclusive) 0.0)   ; A,B mutually exclusive    -> P(A and B) = 0.0

!(and-positive)    ; 0.5
!(and-exclusive)   ; 0.0

; The marginal STV on A is identical in both worlds (s=0.5), but the conjunction
;   differs by the full Frechet range [0, 0.5]. The two-number summary on A cannot
;   distinguish them -- the credal SHAPE is the lost degree of freedom.
; POSITIVE: keep the joint when composition/correlation matters.
; NEGATIVE: reporting only marginal STVs can certify two incompatible joint models as "the same."
