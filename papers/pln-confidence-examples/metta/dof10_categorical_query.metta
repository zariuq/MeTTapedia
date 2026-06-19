; ============================================================================
; DoF 10 — Categorical query choice
; ----------------------------------------------------------------------------
; THE KNOB.  In multinomial / categorical evidence, the TOTAL concentration is
;   shared across categories, but each queried category has its own strength,
;   width, and confidence.  High total evidence does NOT mean high confidence
;   for a rare category.
;
; WHY KEEP IT.  A phenotype classifier may be very sure overall yet uncertain
;   about a rare subclass; forcing a single binary query erases that.
;
; Lean oracle: PLNTruthTower  TypedCategoricalTruth /
;   categoricalSurface_idmEnvelope_forced_by_aggregate (the IDM envelope is
;   forced category-wise by the aggregate concentration).
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

; A 3-category classifier; total N = 1000, but per-category evidence differs.
(= (cat-strength $count $total) (/ $count $total))
; Category-specific confidence uses the category's OWN observed count as evidence:
(= (cat-conf $count $kappa) (/ $count (+ $count $kappa)))

; Common class: 900 of 1000 observations
!(cat-strength 900.0 1000.0)   ; 0.90   high strength
!(cat-conf 900.0 1.0)          ; 0.9989 high confidence (lots of category evidence)

; Rare class: 2 of 1000 observations
!(cat-strength 2.0 1000.0)     ; 0.002  low strength
!(cat-conf 2.0 10.0)           ; 0.1667 low confidence despite high TOTAL evidence

; POSITIVE: per-category confidence flags the rare subclass as uncertain.
; NEGATIVE: a single aggregate "the classifier is 99.9% confident" hides that the
;   rare class rests on 2 observations.
