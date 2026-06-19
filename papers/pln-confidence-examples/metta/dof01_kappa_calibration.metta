; ============================================================================
; DoF 1 — Evidence scale / prior strength (kappa)
; ----------------------------------------------------------------------------
; THE KNOB.  PLN confidence in the evidence view is  c = N / (N + kappa),
;   where N = n+ + n-  is the total retained evidence, and kappa > 0 is the
;   effective prior / context size: "how much evidence counts as a lot."
;
; WHY KEEP IT FREE.  kappa does NOT change strength s = n+/(n+ + n-); it sets
;   the *rate* at which confidence accrues.  A hand-curated clinical fact and a
;   single noisy high-throughput hit can have the SAME +/- ratio yet should not
;   earn confidence at the same speed.  The Walley width-complement bridge forces
;   the *odds form* c = N/(N+kappa) once you pick the chart (see DoF 4/5), but it
;   never picks kappa.  So kappa stays a domain calibration knob.
;
; Lean oracle: PLNTruthTower (posteriorMeanStrength family) + EvidenceBeta;
;   the forcing of the odds *shape* is walley_width_complement_forces_plnOdds
;   (PLNConfidenceWeight.lean) which leaves kappa free.
;
; Portable: self-contained, float literals only -> runs on CeTTa(HE) and PeTTa.
; ============================================================================

(= (conf $total $kappa) (/ $total (+ $total $kappa)))

; Same total evidence N = 5.0, three context sizes:
!(conf 5.0 1.0)    ; -> 0.8333...  curated/trusted source : a little evidence already convinces
!(conf 5.0 10.0)   ; -> 0.3333...  ordinary noisy evidence : the same 5 counts mean much less
!(conf 5.0 50.0)   ; -> 0.0909...  indirect / pathway-mediated : 5 counts barely move confidence

; POSITIVE example (keep kappa small): a curated contraindication earns high
;   confidence from few confirmations.
; NEGATIVE example (do not fix kappa=1 globally): a lone weak omics hit would
;   then claim 0.83 confidence it has not earned.
