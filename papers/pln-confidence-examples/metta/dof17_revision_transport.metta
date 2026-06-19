; ============================================================================
; DoF 17 — Rule-level confidence transport (revision is ADDITION in weight space)
; ----------------------------------------------------------------------------
; THE KNOB.  A PLN rule must decide how confidence combines: add in weight
;   space, take a minimum, multiply, or use a rule-specific effective evidence.
;   Revision of independent evidence is decode -> ADD WEIGHTS -> re-encode:
;     evidence-revision (Evidence p1 n1) (Evidence p2 n2) = (evidence p1+p2 n1+n2)
;   then read the STV back off the combined counts.
;
; WHY KEEP IT.  Doing the algebra in the wrong space silently double-damps:
;   feeding an already-decoded confidence through w2c as if it were a weight is
;   the classic bug.
;
; Lean oracle: PLNConfidenceWeightRevision  transportedConfidenceRevision /
;   plnConfidenceRevision / expConfidenceRevision / tanhConfidenceRevision
;   (one decode-add-reencode pattern, three charts).
; Portable: imports the shared evidence API (co-located ./pln_evidence.metta).
; ============================================================================

!(import! &self ./pln_evidence.metta)

; Two independent bodies of evidence, revised by adding counts:
!(evidence-revision (Evidence 4.0 2.0) (Evidence 3.0 1.0))  ; (evidence 7 3)

; Read the STV off the revised evidence (strength 0.7, confidence 10/11):
!(evidence-toSTV (evidence-revision (Evidence 4.0 2.0) (Evidence 3.0 1.0)) 1.0)  ; (stv 0.7 0.909..)

; Each source alone, for contrast:
!(evidence-toSTV (Evidence 4.0 2.0) 1.0)   ; (stv 0.667 0.857)
!(evidence-toSTV (Evidence 3.0 1.0) 1.0)   ; (stv 0.75  0.800)

; POSITIVE: revision in weight space gives the correct combined confidence 0.909
;   (higher than either source, because evidence accumulated).
; NEGATIVE: averaging the two displayed confidences (0.857, 0.800) would LOWER
;   confidence after seeing MORE evidence — the wrong-space double-damp.
