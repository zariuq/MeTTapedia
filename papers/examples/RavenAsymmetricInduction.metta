;; RavenAsymmetricInduction.metta
;; ----------------------------------------------------------------------------
;; PLN induction as evidence revision — the directional asymmetry of inductive
;; inheritance (Hempel's raven paradox, dissolved dynamically).
;;
;; Runnable on Hyperon Experimental:   metta RavenAsymmetricInduction.metta
;; (uses only grounded float arithmetic; integers floor-divide, so use floats.)
;;
;; Mirrors  Mettapedia/Logic/RavenAsymmetricInduction.lean
;;   evidence  = (Ev pos neg)          (BinaryEvidence ⟨pos, neg⟩)
;;   strength  = pos / (pos + neg)      (toStrength)
;;   revision  = componentwise add      (revision = (+))
;;
;; The SAME observations feed both links; the asymmetry is base-rate dilution:
;;   raven -> black : every raven is black     -> (Ev R 0),  strength = 1
;;   black -> raven : R ravens + M other black -> (Ev R M),  strength = R/(R+M)
;;
;; This file now mirrors the Lean story in a more parametric way:
;;   - observation kinds are explicit
;;   - evidence can be aggregated by iterated `revise`
;;   - a fast count-level view is provided for larger numeric canaries
;;   - concrete `5/95` and `5/995` examples are just instances
;;
;; In PeTTa's rule library, induction and abduction are tightly related at the
;; truth-function layer (`Truth_Induction T1 T2 = Truth_Abduction T2 T1`), but
;; this file studies the evidence-aggregation side of raven asymmetry rather
;; than a full derivation trace from repeated atomic abduction.
;; ----------------------------------------------------------------------------

;; --- evidence algebra ---
(= (strength (Ev $p $n))
   (if (== (+ $p $n) 0.0)
       0.0
       (/ $p (+ $p $n))))
(= (revise (Ev $p1 $n1) (Ev $p2 $n2)) (Ev (+ $p1 $p2) (+ $n1 $n2)))

;; --- observation kinds and their per-link contributions ---
(= (obs-evidence raven->black black-raven)     (Ev 1.0 0.0))
(= (obs-evidence raven->black black-non-raven) (Ev 0.0 0.0))
(= (obs-evidence black->raven black-raven)     (Ev 1.0 0.0))
(= (obs-evidence black->raven black-non-raven) (Ev 0.0 1.0))

;; --- iterated revision over finite datasets ---
(= (repeat-observation $n $link $obs $acc)
   (if (== $n 0.0)
       $acc
       (repeat-observation (- $n 1.0)
                           $link
                           $obs
                           (revise $acc (obs-evidence $link $obs)))))

(= (raven-dataset-evidence-iter $ravens $other-black $link)
   (repeat-observation $other-black
                       $link
                       black-non-raven
                       (repeat-observation $ravens
                                           $link
                                           black-raven
                                           (Ev 0.0 0.0))))

;; Fast count view: same dataset semantics, but without replaying every step.
(= (raven-dataset-evidence $ravens $other-black raven->black) (Ev $ravens 0.0))
(= (raven-dataset-evidence $ravens $other-black black->raven) (Ev $ravens $other-black))

(= (raven->black-evidence $ravens $other-black)
   (raven-dataset-evidence $ravens $other-black raven->black))

(= (black->raven-evidence $ravens $other-black)
   (raven-dataset-evidence $ravens $other-black black->raven))

;; ============================================================================
;; The asymmetry
;; ============================================================================

!(raven->black-evidence 5.0 95.0)    ; -> (Ev 5.0 0.0)
!(black->raven-evidence 5.0 95.0)    ; -> (Ev 5.0 95.0)

!(strength (raven->black-evidence 5.0 95.0))    ; -> 1.0
!(strength (black->raven-evidence 5.0 95.0))    ; -> 0.05
!(strength (black->raven-evidence 5.0 995.0))   ; -> 0.005

;; Induction = one revision step per observation.  One more black non-raven
;; pushes black->raven strength down further; one more black raven keeps
;; raven->black at 1.
!(strength (revise (raven-dataset-evidence-iter 5.0 95.0 black->raven)
                   (obs-evidence black->raven black-non-raven))) ; -> 5/101 ≈ 0.0495
!(strength (revise (raven-dataset-evidence-iter 5.0 95.0 raven->black)
                   (obs-evidence raven->black black-raven)))     ; -> 6/6 = 1.0
