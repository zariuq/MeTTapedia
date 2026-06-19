; ============================================================================
; DoF 18 — Provenance / route semantics
; ----------------------------------------------------------------------------
; THE KNOB.  Two derivations with the SAME final counts can have different
;   provenance: direct observation vs pathway-mediated transfer vs long chain.
;   Carry a route tag and give each route its own kappa (or discount), so the
;   same raw evidence yields route-appropriate confidence.
;
; WHY KEEP IT.  Biomedical drug support should not flatten direct disease
;   evidence and pathway-mediated support into one number; the route matters for
;   audit and for how fast confidence should accrue.
;
; Lean oracle: PLNConfidenceDoFCanary  route_kappa_changes_confidence_not_strength
;   (same counts, route-specific kappa -> equal strength, different confidence).
; Portable: route as a DATA TAG (no collapse/bc/unique) -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (route-kappa direct)  1.0)   ; direct disease evidence: trusted, small kappa
(= (route-kappa pathway) 8.0)   ; pathway-mediated: model-dependent, large kappa

(= (route-strength $pos $neg) (/ $pos (+ $pos $neg)))
(= (route-conf $route $pos $neg)
   (/ (+ $pos $neg) (+ (+ $pos $neg) (route-kappa $route))))

; Same evidence (3 positive, 0 negative) on two routes:
!(route-strength 3.0 0.0)        ; 1.0   strength is route-INDEPENDENT
!(route-conf direct 3.0 0.0)     ; 0.75  direct route: confidence accrues fast
!(route-conf pathway 3.0 0.0)    ; 0.2727 pathway route: same counts, discounted confidence

; POSITIVE: a supported-drug hypothesis distinguishes direct vs pathway support.
; NEGATIVE: merging routes before applying route-kappa makes audit and discount impossible.
