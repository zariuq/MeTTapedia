; =============================================================================
; conv_soundness_shadow_v1.metta
;
; CONV-SOUNDNESS SHADOW v1 — the operational complement to the knot-rho /
; knotted-topoi denotational full abstraction.  knot-rho/knotted-topoi give the
; denotational truth ~ (context bisimulation = final-coalgebra equality;
; coinductive, undecidable in general).  The MIK is the DECIDABLE conv face.
; Web Claude's external criterion: conv (XS) ~ strictly is CORRECT (decidable !=
; undecidable); the only FAILURE is conv identifying a ~-distinct pair
; (unsoundness).  This file makes that executable on the FINITARY core, where ~
; IS decidable (finite, acyclic synchronisation trees -> the final coalgebra is
; literal/set-sized, knot-rho section "risk ledger").  It is the conv-side
; sibling of imp_coherence_exp1 (the <>-side).
;
; HONEST SCOPE (v1 seed, smallest meaningful instance, like exp1's =>-fragment):
;   * Object: a tiny CCS/rho equivariant fragment (the colour-respecting shadow
;     knot-rho recovers as Aczel's CCS model) with action-prefix, choice, and
;     interleaving parallel.  Actions a,b,c are opaque (the equivariant grading).
;   * "conv" is modelled as the decidable STRUCTURAL CONGRUENCE with 0 a unit for
;     | and + (sound: P|0 ~ P, P+0 ~ P) -- the decidable shadow.  It deliberately
;     does NOT have +-idempotence, +/|-commutativity, or the expansion law: those
;     are bisimulation-only, and their absence is exactly the strict gap conv (XS) ~.
;   * "~" is bounded bisimulation ~_n over the context-/action-labelled LTS;
;     BOUND=8 with all examples finite + acyclic of depth <= 3, so ~_8 = ~ here.
;   * The bridge to the kernel's lambda-Pi conv via the MeTTa2rho desugaring (the
;     scaling step) is FUTURE work and couples to Codex's rhometta lane; v1 pins
;     the relationship in the smallest setting where the gap is real (concurrency).
;
; Three oracle properties (positives AND negatives):
;   (i)   SOUNDNESS          conv P Q  =>  P ~ Q              (conv subset of ~)
;   (ii)  STRICT GAP         exists P,Q.  P ~ Q  AND  NOT conv P Q   (conv (XS) ~)
;   (iii) NO FALSE ID        no conv-equal pair is ~-distinct  (the unsoundness probe)
; run_conv_soundness_gate.sh injects unsound conv coarsenings / ~ over-matches and
; confirms property (i)/(iii) turns red -- the binding-mutation-gate pattern.
; =============================================================================

; ---------- process syntax (CCS/rho equivariant fragment) --------------------
; P ::= Nil | (Pre a P) | (Sum P Q) | (Par P Q)        a,b,c opaque actions
; transition lists use LNil/LCons (Nil is a process, kept distinct).

(= (lapp LNil $ys) $ys)
(= (lapp (LCons $x $xs) $ys) (LCons $x (lapp $xs $ys)))

; ---------- the context-/action-labelled transition system (the dT labels) ----
(= (trans Nil) LNil)
(= (trans (Pre $a $P)) (LCons (Tr $a $P) LNil))
(= (trans (Sum $P $Q)) (lapp (trans $P) (trans $Q)))
(= (trans (Par $P $Q)) (lapp (par-l (trans $P) $Q) (par-r $P (trans $Q))))
(= (par-l LNil $Q) LNil)
(= (par-l (LCons (Tr $a $P1) $r) $Q) (LCons (Tr $a (Par $P1 $Q)) (par-l $r $Q)))
(= (par-r $P LNil) LNil)
(= (par-r $P (LCons (Tr $a $Q1) $r)) (LCons (Tr $a (Par $P $Q1)) (par-r $P $r)))

; ---------- bounded bisimulation ~_n (decidable on the finitary core) ---------
(= (bisim $n $P $Q)
   (if (== $n 0) True
     (if (matches $n (trans $P) $Q)
         (matches $n (trans $Q) $P)
         False)))
(= (matches $n LNil $Q) True)
(= (matches $n (LCons (Tr $a $P1) $rest) $Q)
   (if (has-match $n $a $P1 (trans $Q))
       (matches $n $rest $Q)
       False))
(= (has-match $n $a $P1 LNil) False)
(= (has-match $n $a $P1 (LCons (Tr $b $Q1) $rest))
   (if (== $a $b)
       (if (bisim (- $n 1) $P1 $Q1) True (has-match $n $a $P1 $rest))
       (has-match $n $a $P1 $rest)))

; ---------- conv: the decidable structural congruence (0 a unit) --------------
; nested-if (non-overlapping) per the CeTTa equation-overlap discipline.
(= (cnf Nil) Nil)
(= (cnf (Pre $a $P)) (Pre $a (cnf $P)))
(= (cnf (Par $P $Q)) (mk-par (cnf $P) (cnf $Q)))
(= (cnf (Sum $P $Q)) (mk-sum (cnf $P) (cnf $Q)))
(= (mk-par $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Par $P $Q))))
(= (mk-sum $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Sum $P $Q))))
(= (conv-p $P $Q) (== (cnf $P) (cnf $Q)))

; the runnable soundness property (i)/(iii): conv P Q => P ~ Q
(= (conv-implies-bisim $P $Q) (if (conv-p $P $Q) (bisim 8 $P $Q) True))

; ---------- example processes (canonical CCS/rho discriminators) --------------
(= (PA)     (Pre a Nil))                                          ; a.0
(= (PAA)    (Sum (Pre a Nil) (Pre a Nil)))                        ; a.0 + a.0
(= (PAB)    (Sum (Pre a Nil) (Pre b Nil)))                        ; a.0 + b.0
(= (PBA)    (Sum (Pre b Nil) (Pre a Nil)))                        ; b.0 + a.0
(= (PpAB)   (Par (Pre a Nil) (Pre b Nil)))                        ; a.0 | b.0
(= (Pexp)   (Sum (Pre a (Pre b Nil)) (Pre b (Pre a Nil))))        ; a.b.0 + b.a.0
(= (Pdiscm) (Sum (Pre a (Pre b Nil)) (Pre a (Pre c Nil))))        ; a.b.0 + a.c.0
(= (Pdistr) (Pre a (Sum (Pre b Nil) (Pre c Nil))))                ; a.(b.0 + c.0)
(= (PparA)  (Par (Pre a Nil) (Pre a Nil)))                        ; a.0 | a.0
(= (Pab)    (Pre a (Pre b Nil)))                                  ; a.b.0
(= (Pac)    (Pre a (Pre c Nil)))                                  ; a.c.0

; =============================================================================
; (i) SOUNDNESS: conv P Q => P ~ Q.  The structural-congruence (0-unit) pairs
;     are convertible AND bisimilar -- conv is sound here.
; =============================================================================
!(assertEqual (conv-p (Par (PA) Nil) (PA)) True)            ; a|0 == a (conv)
!(assertEqual (bisim 8 (Par (PA) Nil) (PA)) True)           ; a|0 ~ a
!(assertEqual (conv-p (Sum (PA) Nil) (PA)) True)            ; a+0 == a (conv)
!(assertEqual (bisim 8 (Sum (PA) Nil) (PA)) True)           ; a+0 ~ a
!(assertEqual (conv-p (Par Nil (PA)) (PA)) True)            ; 0|a == a (conv)
!(assertEqual (bisim 8 (Par Nil (PA)) (PA)) True)           ; 0|a ~ a
; reflexivity: conv P P and P ~ P
!(assertEqual (conv-p (Pdiscm) (Pdiscm)) True)
!(assertEqual (bisim 8 (Pdiscm) (Pdiscm)) True)

; =============================================================================
; (ii) STRICT GAP: P ~ Q but NOT conv P Q.  ~ identifies idempotence,
;      commutativity, and the expansion law -- which the decidable conv refuses.
;      This is conv (XS) ~, the CORRECT divergence (Web Claude's external criterion).
; =============================================================================
; + idempotence: a+a ~ a, but NOT convertible
!(assertEqual (bisim 8 (PAA) (PA)) True)
!(assertEqual (conv-p (PAA) (PA)) False)
; + commutativity: a+b ~ b+a, but NOT convertible (cnf does not reorder)
!(assertEqual (bisim 8 (PAB) (PBA)) True)
!(assertEqual (conv-p (PAB) (PBA)) False)
; expansion law: a|b ~ a.b + b.a, but NOT convertible
!(assertEqual (bisim 8 (PpAB) (Pexp)) True)
!(assertEqual (conv-p (PpAB) (Pexp)) False)

; =============================================================================
; (iii) NO FALSE IDENTIFICATION: no conv-equal pair is ~-distinct, and the
;       genuine discriminators are refused by BOTH conv and ~.
; =============================================================================
; the canonical discriminator: a.b + a.c  ~/~  a.(b+c) -- AND not convertible
!(assertEqual (bisim 8 (Pdiscm) (Pdistr)) False)
!(assertEqual (conv-p (Pdiscm) (Pdistr)) False)
; knot-rho's parallel-not-union: a|a  ~/~  a -- AND not convertible
!(assertEqual (bisim 8 (PparA) (PA)) False)
!(assertEqual (conv-p (PparA) (PA)) False)
; distinct prefix continuations: a.b ~/~ a.c -- AND not convertible
!(assertEqual (bisim 8 (Pab) (Pac)) False)
!(assertEqual (conv-p (Pab) (Pac)) False)

; the runnable conv-subset-of-~ property over the whole suite: every pair
; satisfies conv P Q => P ~ Q.  Vacuously true where conv is False today; these
; become the TEETH under an unsound conv coarsening (run_conv_soundness_gate.sh).
!(assertEqual (conv-implies-bisim (PAB) (PA)) True)
!(assertEqual (conv-implies-bisim (PpAB) (PA)) True)
!(assertEqual (conv-implies-bisim (Pdiscm) (Pdistr)) True)
!(assertEqual (conv-implies-bisim (PparA) (PA)) True)
!(assertEqual (conv-implies-bisim (PAA) (PA)) True)
!(assertEqual (conv-implies-bisim (Pab) (Pac)) True)
!(assertEqual (conv-implies-bisim (Par (PA) Nil) (PA)) True)
!(assertEqual (conv-implies-bisim (Sum (PA) Nil) (PA)) True)
