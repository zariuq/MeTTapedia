; ============================================================================
; DoF 7b — Distinction / credal shadow  (same marginal STV, different hidden joint)
; ----------------------------------------------------------------------------
; TIER: STRUCTURAL.  This is the intuition-shadow for the generic and OSLF
;   distinction/credal bridge.
;
; THE KNOB.  Limited observational resolution can leave multiple admissible
;   worlds live. They can agree on the same marginal STV-style surface while
;   disagreeing on a hidden joint or distinction-sensitive query.
;
; WHY KEEP IT.  Two models can both show the same marginal belief about A while
;   disagreeing sharply about whether A co-occurs with B. If we compress to a
;   single marginal STV, that hidden structure disappears.
;
; Lean oracles:
;   - PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_has_strict_width_of_related_ne
;   - PLNDistinctionCredalBridge.observationCredalSet_indicatorGamble_collapses_of_class_subsingleton
;   - PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_has_strict_width
;   - PLNDistinctionCredalOSLFBridge.indistObs_indicatorGamble_collapses_of_class_subsingleton
;   together with DoF 7's CredalProjectionTower oracle.
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (marginal-A $world) (stv 0.5 1.0))
(= (joint-A-and-B dependent) 0.5)
(= (joint-A-and-B exclusive) 0.0)
(= (distinction-gap) (- (joint-A-and-B dependent) (joint-A-and-B exclusive)))

!(marginal-A dependent)         ; (stv 0.5 1.0)
!(marginal-A exclusive)         ; (stv 0.5 1.0)
!(joint-A-and-B dependent)      ; 0.5
!(joint-A-and-B exclusive)      ; 0.0
!(distinction-gap)              ; 0.5

; POSITIVE: preserve the hidden joint / observational structure when later
;   rules or decisions depend on it.
; NEGATIVE: a marginal STV alone can make two incompatible admissible worlds
;   look identical.
