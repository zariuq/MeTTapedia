; ============================================================================
; DoF 13 — Compatible completion / natural extension  (F2 finite shadow)
; ----------------------------------------------------------------------------
; TIER: STRUCTURAL REFERENCE.  This .metta shows only the FINITE-PREFIX shadow.
;   The real F2 statement is the infinite Lean crown; do not mistake the finite
;   read-off below for the full process law.
;
; THE KNOB.  In an exchangeable (i.i.d./de Finetti) stream, the external
;   sigma-additive mixing-family read-off ALWAYS exists from a finite prefix
;   (here: the Laplace/posterior-predictive next-success probability).  The
;   STRONGER "raw all-gambles process-law crown" holds EXACTLY at the
;   lower-prevision compatibility boundary -- which a finite .metta cannot decide.
;     laplace-pred k n = (k+1)/(n+2)   = external predictive readout
;
; WHY IT MATTERS.  A patient-response / defect / fraud stream can give useful
;   finite-prefix forecasts before any global compatibility witness exists.
;   Calling those a full process law without compatibility is assumption laundering.
;
; Lean oracle (the REAL claim): DeFinettiProjectiveCredalBridge
;   impreciseDeFinetti_analyticMixingFamily_sharpCompatibilityCrown
;   (raw crown <-> exists respecting lower prevision), and the counterexample
;   exists_..._not_pointwiseZeroInterior (pointwise zero-interior is NOT necessary).
; Portable: self-contained, float literals -> CeTTa(HE) + PeTTa.
; ============================================================================

(= (laplace-pred $k $n) (/ (+ $k 1.0) (+ $n 2.0)))

; External predictive readout from finite prefixes (always available):
!(laplace-pred 3.0 5.0)    ; 0.5714  3 successes in 5 trials -> next-success estimate
!(laplace-pred 30.0 50.0)  ; 0.5961  longer prefix, same exchangeable family

; The "raw all-gambles crown" is intentionally ABSENT here: it is not a function
;   of the finite counts -- it is the infinite compatibility boundary proved in Lean.
; POSITIVE: report the external predictive read-off for finite decisions.
; NEGATIVE: do NOT claim a full process law from finite prefixes alone (see Lean crown).
