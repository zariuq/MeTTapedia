; ============================================================================
; DoF 8 — Backend for uncertainty (Bayesian Beta vs Walley IDM)
; ----------------------------------------------------------------------------
; THE KNOB.  The SAME counts can be summarized by different uncertainty
;   backends, each with different provenance:
;     Bayesian Beta posterior MEAN (a precise point):  (p+1)/(N+2)
;     Walley IDM predictive INTERVAL (robust bounds):  [p/(N+s), (p+s)/(N+s)]
;   A point estimate and a robust interval are NOT interchangeable.
;
; WHY KEEP IT.  A posterior mean is right for a parametric lab assay; a robust
;   safety envelope should not be silently collapsed to a single Bayesian point.
;
; Lean oracle: PLNConfidenceDoFCanary  beta_mean_strictly_inside_walley_idm_interval
;   (NEW canary, axiom-clean: the Beta posterior mean 3/7 lies strictly inside the
;   IDM interval [2/7,4/7], which has strictly positive width), built on
;   EvidenceBeta.lean + WalleyBinaryIDM.lean.
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (beta-mean  $p $n)    (/ (+ $p 1.0) (+ (+ $p $n) 2.0)))
(= (idm-lower  $p $n $s) (/ $p (+ (+ $p $n) $s)))
(= (idm-upper  $p $n $s) (/ (+ $p $s) (+ (+ $p $n) $s)))

; Counts (2 positive, 3 negative), IDM strength s = 2:
!(beta-mean 2.0 3.0)      ; 0.4286   Bayesian point estimate
!(idm-lower 2.0 3.0 2.0)  ; 0.2857   robust lower bound
!(idm-upper 2.0 3.0 2.0)  ; 0.5714   robust upper bound

; POSITIVE: report the Beta mean when a single parametric estimate is wanted.
; NEGATIVE: a safety decision needs the IDM interval [0.29, 0.57]; collapsing it to
;   the point 0.43 hides the genuine imprecision the same counts carry.
