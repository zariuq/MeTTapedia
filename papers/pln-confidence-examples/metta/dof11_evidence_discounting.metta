; ============================================================================
; DoF 11 — Feature / evidence discounting (source quality, IDF, dependence)
; ----------------------------------------------------------------------------
; THE KNOB.  Evidence can be reweighted before it enters the count tower:
;   evidence-power (Evidence p n) w  =  (evidence p^w n^w).
;     w < 1  discounts (e.g. duplicate / near-duplicate text-mined hits)
;     w = 1  unchanged
;     w > 1  amplifies (e.g. independent, curated replications)
;     w = 0  ignores the feature entirely.
;   Discounting lowers total weight, hence confidence; amplifying raises it.
;
; WHY KEEP IT.  Ten correlated text-mined positives should not count as ten
;   independent ones; two curated independent confirmations may count for more.
;
; Lean oracle: PLNConfidenceDoFCanary  power_discount_scales_logodds (new canary).
; Portable: imports the shared evidence API (co-located ./pln_evidence.metta).
; ============================================================================

!(import! &self ./pln_evidence.metta)

; Regraduated counts:
!(evidence-power (Evidence 10.0 2.0) 0.5)   ; (evidence 3.16.. 1.41..)  sqrt discount
!(evidence-power (Evidence 10.0 2.0) 1.0)   ; (evidence 10 2)           unchanged
!(evidence-power (Evidence 10.0 2.0) 2.0)   ; (evidence 100 4)          amplified

; Confidence at kappa=1 moves with the discount (lower for w<1, higher for w>1):
!(evidence-toConfidence (evidence-power (Evidence 10.0 2.0) 0.5) 1.0)  ; ~0.821  discounted
!(evidence-toConfidence (evidence-power (Evidence 10.0 2.0) 1.0) 1.0)  ; ~0.923  baseline
!(evidence-toConfidence (evidence-power (Evidence 10.0 2.0) 2.0) 1.0)  ; ~0.990  amplified

; POSITIVE: independent curated hits use w>1; duplicate text-mined hits use w<1.
; NEGATIVE: treating correlated pathway hits as independent (w=1 each) overstates confidence.
