; =============================================================================
; ocoherence_hm_adequacy_v1.metta
;
; <>-COHERENCE / HM-ADEQUACY SHADOW v1 — a bounded operational shadow of
; knotted-topoi's keystone "the subobject classifier classifies bisimilarity":
; OSLF-generated Hennessy-Milner modalities <F>phi are tested against context
; bisimulation by adequacy positives plus explicit separating witnesses.  This
; finite probe closes the conv/~/<> triangle on the examples below:
;   imp_coherence_exp1     did the <>/cert side (search emits cert <=> checker accepts);
;   conv_soundness_shadow_v1 did the conv/~ side (conv subset of ~, with the LTS+bisim);
;   THIS file              probes bounded adequacy + separation for modal-equivalence.
;
; HONEST SCOPE (v1 seed): the LTS + bounded bisim + structural-congruence conv are
; COPIED VERBATIM from conv_soundness_shadow_v1.metta (CeTTa import is fragile;
; self-contained is stable; both files are kept green together by the parity gate).
; "~" is bounded bisimulation; modal-equivalence is checked SOUNDLY two ways:
;   * ADEQUACY positives: bisimilar pairs AGREE on probe formulae (~ => modal-eq);
;   * SEPARATING WITNESS: for each listed ~/~ pair we EXHIBIT the distinguishing <F>phi that
;     one satisfies and the other refutes (the ~/~ => exists separating formula
;     direction -- the constructive teeth).  Bound = 8, modal depth <= 3.
;   * The dT label set is ONE object read two ways: the action `a` in a transition
;     (Tr a P') (Firing) IS the index `a` in a modality (FDia a phi) (Witnessing).
; run_ocoherence_gate.sh injects modal/~ breaks and confirms adequacy/witness reddens.
; =============================================================================

; ---------- process syntax + LTS (verbatim from conv_soundness_shadow_v1) ------
(= (lapp LNil $ys) $ys)
(= (lapp (LCons $x $xs) $ys) (LCons $x (lapp $xs $ys)))
(= (trans Nil) LNil)
(= (trans (Pre $a $P)) (LCons (Tr $a $P) LNil))
(= (trans (Sum $P $Q)) (lapp (trans $P) (trans $Q)))
(= (trans (Par $P $Q)) (lapp (par-l (trans $P) $Q) (par-r $P (trans $Q))))
(= (par-l LNil $Q) LNil)
(= (par-l (LCons (Tr $a $P1) $r) $Q) (LCons (Tr $a (Par $P1 $Q)) (par-l $r $Q)))
(= (par-r $P LNil) LNil)
(= (par-r $P (LCons (Tr $a $Q1) $r)) (LCons (Tr $a (Par $P $Q1)) (par-r $P $r)))

; ---------- bounded bisimulation ~_n (verbatim) -------------------------------
(= (bisim $n $P $Q)
   (if (== $n 0) True
     (if (matches $n (trans $P) $Q) (matches $n (trans $Q) $P) False)))
(= (matches $n LNil $Q) True)
(= (matches $n (LCons (Tr $a $P1) $rest) $Q)
   (if (has-match $n $a $P1 (trans $Q)) (matches $n $rest $Q) False))
(= (has-match $n $a $P1 LNil) False)
(= (has-match $n $a $P1 (LCons (Tr $b $Q1) $rest))
   (if (== $a $b)
       (if (bisim (- $n 1) $P1 $Q1) True (has-match $n $a $P1 $rest))
       (has-match $n $a $P1 $rest)))

; ---------- conv: decidable structural congruence (verbatim) ------------------
(= (cnf Nil) Nil)
(= (cnf (Pre $a $P)) (Pre $a (cnf $P)))
(= (cnf (Par $P $Q)) (mk-par (cnf $P) (cnf $Q)))
(= (cnf (Sum $P $Q)) (mk-sum (cnf $P) (cnf $Q)))
(= (mk-par $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Par $P $Q))))
(= (mk-sum $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Sum $P $Q))))
(= (conv-p $P $Q) (== (cnf $P) (cnf $Q)))

; ---------- OSLF Hennessy-Milner modal logic (NEW) ----------------------------
; phi ::= FTop | (FNeg phi) | (FAnd phi psi) | (FDia a phi)    <a>phi = "some
;   a-labelled transition reaches a phi-state".  bounded satisfaction (depth $n).
(= (not-b True) False)
(= (not-b False) True)
(= (sat $n $P FTop) True)
(= (sat $n $P (FNeg $phi)) (not-b (sat $n $P $phi)))
(= (sat $n $P (FAnd $phi $psi)) (if (sat $n $P $phi) (sat $n $P $psi) False))
(= (sat $n $P (FDia $a $phi))
   (if (== $n 0) False (dia-search (- $n 1) $a $phi (trans $P))))
(= (dia-search $n $a $phi LNil) False)
(= (dia-search $n $a $phi (LCons (Tr $b $P1) $rest))
   (if (== $a $b)
       (if (sat $n $P1 $phi) True (dia-search $n $a $phi $rest))
       (dia-search $n $a $phi $rest)))
; agreement on a formula, and the separating-witness predicate (the teeth)
(= (agree $n $P $Q $phi) (== (sat $n $P $phi) (sat $n $Q $phi)))
(= (separates $n $P $Q $phi) (not-b (agree $n $P $Q $phi)))

; ---------- example processes (verbatim discriminators) -----------------------
(= (PA)     (Pre a Nil))
(= (PAA)    (Sum (Pre a Nil) (Pre a Nil)))
(= (PAB)    (Sum (Pre a Nil) (Pre b Nil)))
(= (PBA)    (Sum (Pre b Nil) (Pre a Nil)))
(= (PpAB)   (Par (Pre a Nil) (Pre b Nil)))
(= (Pexp)   (Sum (Pre a (Pre b Nil)) (Pre b (Pre a Nil))))
(= (Pdiscm) (Sum (Pre a (Pre b Nil)) (Pre a (Pre c Nil))))
(= (Pdistr) (Pre a (Sum (Pre b Nil) (Pre c Nil))))
(= (PparA)  (Par (Pre a Nil) (Pre a Nil)))
(= (Pab)    (Pre a (Pre b Nil)))
(= (Pac)    (Pre a (Pre c Nil)))

; =============================================================================
; (i) ADEQUACY: bisimilar processes agree on modal formulae (~ => modal-eq).
;     The bisimilar (but non-conv) pairs of conv_soundness_shadow_v1, now agreeing
;     on probe formulae -- so conv (XS) ~ subset of modal-eq.
; =============================================================================
!(assertEqual (bisim 8 (PAA) (PA)) True)                                      ; a+a ~ a
!(assertEqual (agree 8 (PAA) (PA) (FDia a FTop)) True)                        ; both can do a
!(assertEqual (agree 8 (PAA) (PA) (FDia b FTop)) True)                        ; neither can do b
!(assertEqual (agree 8 (PAA) (PA) (FDia a (FDia a FTop))) True)               ; neither can do a.a
!(assertEqual (bisim 8 (PpAB) (Pexp)) True)                                   ; a|b ~ a.b+b.a
!(assertEqual (agree 8 (PpAB) (Pexp) (FDia a (FDia b FTop))) True)            ; both can do a.b
!(assertEqual (agree 8 (PpAB) (Pexp) (FDia b (FDia a FTop))) True)            ; both can do b.a
!(assertEqual (bisim 8 (PAB) (PBA)) True)                                     ; a+b ~ b+a
!(assertEqual (agree 8 (PAB) (PBA) (FAnd (FDia a FTop) (FDia b FTop))) True)  ; both can do a and b

; =============================================================================
; (ii) SEPARATING WITNESS: each listed ~/~ pair is split by an EXPLICIT <F>phi -- the
;      ~/~ => exists-separating-formula direction (constructive HM-adequacy teeth).
; =============================================================================
; a.b+a.c  ~/~  a.(b+c): only a.(b+c) reaches a state doing BOTH b and c.
!(assertEqual (bisim 8 (Pdiscm) (Pdistr)) False)
!(assertEqual (sat 8 (Pdistr) (FDia a (FAnd (FDia b FTop) (FDia c FTop)))) True)
!(assertEqual (sat 8 (Pdiscm) (FDia a (FAnd (FDia b FTop) (FDia c FTop)))) False)
!(assertEqual (separates 8 (Pdiscm) (Pdistr) (FDia a (FAnd (FDia b FTop) (FDia c FTop)))) True)
; a|a  ~/~  a: only a|a can do a TWICE.
!(assertEqual (bisim 8 (PparA) (PA)) False)
!(assertEqual (sat 8 (PparA) (FDia a (FDia a FTop))) True)
!(assertEqual (sat 8 (PA) (FDia a (FDia a FTop))) False)
!(assertEqual (separates 8 (PparA) (PA) (FDia a (FDia a FTop))) True)
; a.b  ~/~  a.c: only a.b reaches a b-doer.
!(assertEqual (bisim 8 (Pab) (Pac)) False)
!(assertEqual (separates 8 (Pab) (Pac) (FDia a (FDia b FTop))) True)

; =============================================================================
; (iii) TRIANGLE TIE: conv subset of ~ subset of modal-eq, on the 0-unit pair;
;       and the dT label `a` is both the LTS label (Tr a) and the modal index (FDia a).
; =============================================================================
!(assertEqual (conv-p (Par (PA) Nil) (PA)) True)                              ; a|0 == a (conv)
!(assertEqual (bisim 8 (Par (PA) Nil) (PA)) True)                             ; a|0 ~ a
!(assertEqual (agree 8 (Par (PA) Nil) (PA) (FDia a FTop)) True)               ; ... and modal-equal
; the witness formulae do NOT separate bisimilar pairs (adequacy soundness check)
!(assertEqual (separates 8 (PAA) (PA) (FDia a (FDia a FTop))) False)
!(assertEqual (separates 8 (PpAB) (Pexp) (FDia a (FDia b FTop))) False)
