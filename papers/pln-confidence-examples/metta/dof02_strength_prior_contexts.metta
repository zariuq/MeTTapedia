; ============================================================================
; DoF 2 — Strength projection / prior context
; ----------------------------------------------------------------------------
; THE KNOB.  The SAME +/- counts read out a different "strength" depending on
;   the projection: maximum likelihood, a uniform Beta(1,1) posterior mean,
;   Jeffreys Beta(1/2,1/2), or any explicit prior.  Strength is NOT context-free.
;     beta-strength(pos,neg,alpha,beta) = (pos+alpha) / (pos+neg+alpha+beta)
;
; WHY KEEP IT.  Sparse data needs shrinkage toward a baseline; mature data can
;   safely use near-MLE.  Pretending strength is canonical hides this choice.
;
; Lean oracle: PLNTruthTower  posteriorMeanStrength / posteriorMeanStrength_improper_eq_mle
;   (MLE = the improper-prior limit) and BinaryContext.uniform.
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (beta-strength $pos $neg $alpha $beta)
   (/ (+ $pos $alpha) (+ (+ $pos $neg) (+ $alpha $beta))))

; Sparse single positive (1,0) under three contexts:
!(beta-strength 1.0 0.0 0.0 0.0)    ; 1.0    MLE / Haldane edge (overconfident on 1 datum)
!(beta-strength 1.0 0.0 1.0 1.0)    ; 0.6667 uniform Beta(1,1) — shrinks toward 0.5
!(beta-strength 1.0 0.0 0.5 0.5)    ; 0.75   Jeffreys Beta(1/2,1/2)

; Mature data (1000,0): the prior washes out, all projections ~ MLE:
!(beta-strength 1000.0 0.0 1.0 1.0)  ; 0.9990  (near 1.0)

; POSITIVE: sparse medical counts use a shrinkage prior so 1/0 is not read as certain.
; NEGATIVE: a thousand-observation benchmark forced through a strong prior would be needlessly damped.
