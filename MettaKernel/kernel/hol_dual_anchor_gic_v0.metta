; =============================================================================
; hol_dual_anchor_gic_v0.metta
;
; Proof-relevant HOL4 and HOL Light anchors checked by the same generic MIK
; inference checker used for Metamath.
;
; The rules mirror the primitive/derived distinction exercised by the actual
; HOL4 HOL06_lcf_kernel and HOL Light SELF_IMP smoke programs.  Source-system
; execution is an independent gate; full source adequacy remains separate.
; =============================================================================

!(import! &self generic_inference_checker_v0)

; ---------- Shared abstract HOL carrier -------------------------------------
(= (hol-a) (PApp "A" LNil))
(= (hol-b) (PApp "B" LNil))
(= (hol-and-aa) (PApp "AndAA" LNil))
(= (hol-empty) (PApp "EmptyHyps" LNil))
(= (hol-hyp $p) (PApp "Hyp" (LCons $p LNil)))
(= (hol-remove $p $h)
   (PApp "RemoveHyp" (LCons $p (LCons $h LNil))))
(= (hol-union $left $right)
   (PApp "UnionHyps" (LCons $left (LCons $right LNil))))
(= (hol-seq $hyps $conclusion)
   (PApp "Seq" (LCons $hyps (LCons $conclusion LNil))))
(= (hol-eq $left $right)
   (PApp "Eq" (LCons $left (LCons $right LNil))))
(= (hol-imp $left $right)
   (PApp "Imp" (LCons $left (LCons $right LNil))))
(= (hol-bool $term) (PApp "Bool" (LCons $term LNil)))
(= (hol-thm $sequent) (PApp "Thm" (LCons $sequent LNil)))

(= (hol-constructors)
   (LCons (CDecl "A" 0)
     (LCons (CDecl "B" 0)
       (LCons (CDecl "AndAA" 0)
         (LCons (CDecl "EmptyHyps" 0)
           (LCons (CDecl "Hyp" 1)
             (LCons (CDecl "RemoveHyp" 2)
               (LCons (CDecl "UnionHyps" 2)
                 (LCons (CDecl "Seq" 2)
                   (LCons (CDecl "Eq" 2)
                     (LCons (CDecl "Imp" 2) LNil)))))))))))

(= (hol-judgments)
   (LCons (JDecl "Bool" 1) (LCons (JDecl "Thm" 1) LNil)))

; ---------- HOL4: ASSUME and DISCH are primitive ----------------------------
(= (h4-rules)
   (LCons
     (GRuleV1 "H4_BOOL_A" LNil LNil (hol-bool (hol-a)) LNil)
     (LCons
       (GRuleV1 "H4_BOOL_B" LNil LNil (hol-bool (hol-b)) LNil)
       (LCons
         (GRuleV1 "H4_ASSUME"
           (LCons (Formal "P" 0) LNil)
           (LCons (hol-bool (FVar "P")) LNil)
           (hol-thm (hol-seq (hol-hyp (FVar "P")) (FVar "P")))
           LNil)
         (LCons
           (GRuleV1 "H4_DISCH"
             (LCons (Formal "P" 0)
               (LCons (Formal "H" 0)
                 (LCons (Formal "Q" 0) LNil)))
             (LCons (hol-bool (FVar "P"))
               (LCons
                 (hol-thm (hol-seq (FVar "H") (FVar "Q")))
                 LNil))
             (hol-thm
               (hol-seq
                 (hol-remove (FVar "P") (FVar "H"))
                 (hol-imp (FVar "P") (FVar "Q"))))
             LNil)
           LNil)))))

(= (h4-language)
   (GInferenceLanguageV1 1
     (hol-constructors) (hol-judgments) (h4-rules) GNoConversion))

(= (h4-bool-a-proof)
   (GProof (GRuleInst "H4_BOOL_A" LNil) PrNil))
(= (h4-bool-b-proof)
   (GProof (GRuleInst "H4_BOOL_B" LNil) PrNil))
(= (h4-assume-a-proof)
   (GProof
     (GRuleInst "H4_ASSUME" (LCons (hol-a) LNil))
     (PrCons (h4-bool-a-proof) PrNil)))
(= (h4-assume-b-proof)
   (GProof
     (GRuleInst "H4_ASSUME" (LCons (hol-b) LNil))
     (PrCons (h4-bool-b-proof) PrNil)))
(= (h4-imp-id-goal)
   (hol-thm
     (hol-seq
       (hol-remove (hol-a) (hol-hyp (hol-a)))
       (hol-imp (hol-a) (hol-a)))))
(= (h4-imp-id-proof)
   (GProof
     (GRuleInst "H4_DISCH"
       (LCons (hol-a)
         (LCons (hol-hyp (hol-a)) (LCons (hol-a) LNil))))
     (PrCons (h4-bool-a-proof)
       (PrCons (h4-assume-a-proof) PrNil))))

; ---------- HOL Light: implication introduction is derived -----------------
(= (hl-rules)
   (LCons
     (GRuleV1 "HL_BOOL_A" LNil LNil (hol-bool (hol-a)) LNil)
     (LCons
       (GRuleV1 "HL_BOOL_ANDAA" LNil LNil (hol-bool (hol-and-aa)) LNil)
       (LCons
         (GRuleV1 "HL_ASSUME"
           (LCons (Formal "P" 0) LNil)
           (LCons (hol-bool (FVar "P")) LNil)
           (hol-thm (hol-seq (hol-hyp (FVar "P")) (FVar "P")))
           LNil)
         (LCons
           (GRuleV1 "HL_CONJ_AA_REPLAY" LNil
             (LCons
               (hol-thm (hol-seq (hol-hyp (hol-a)) (hol-a)))
               (LCons
                 (hol-thm (hol-seq (hol-hyp (hol-a)) (hol-a)))
                 LNil))
             (hol-thm (hol-seq (hol-hyp (hol-a)) (hol-and-aa)))
             LNil)
           (LCons
             (GRuleV1 "HL_CONJUNCT1_AA_REPLAY" LNil
               (LCons
                 (hol-thm
                   (hol-seq (hol-hyp (hol-and-aa)) (hol-and-aa)))
                 LNil)
               (hol-thm (hol-seq (hol-hyp (hol-and-aa)) (hol-a)))
               LNil)
             (LCons
               (GRuleV1 "HL_DEDUCT_ANTISYM_SINGLETON" LNil
                 (LCons
                   (hol-thm (hol-seq (hol-hyp (hol-a)) (hol-and-aa)))
                   (LCons
                     (hol-thm
                       (hol-seq (hol-hyp (hol-and-aa)) (hol-a)))
                     LNil))
                 (hol-thm
                   (hol-seq (hol-empty) (hol-eq (hol-and-aa) (hol-a))))
                 LNil)
               (LCons
                 (GRuleV1 "HL_IMP_DEF_AA" LNil LNil
                   (hol-thm
                     (hol-seq (hol-empty)
                       (hol-eq
                         (hol-eq (hol-and-aa) (hol-a))
                         (hol-imp (hol-a) (hol-a)))))
                   LNil)
                 (LCons
                   (GRuleV1 "HL_EQ_MP_EMPTY"
                     (LCons (Formal "P" 0)
                       (LCons (Formal "Q" 0) LNil))
                     (LCons
                       (hol-thm
                         (hol-seq (hol-empty)
                           (hol-eq (FVar "P") (FVar "Q"))))
                       (LCons
                         (hol-thm (hol-seq (hol-empty) (FVar "P")))
                         LNil))
                     (hol-thm (hol-seq (hol-empty) (FVar "Q")))
                     LNil)
                   LNil)))))))))

(= (hl-language)
   (GInferenceLanguageV1 1
     (hol-constructors) (hol-judgments) (hl-rules) GNoConversion))

(= (hl-bool-a-proof)
   (GProof (GRuleInst "HL_BOOL_A" LNil) PrNil))
(= (hl-bool-and-proof)
   (GProof (GRuleInst "HL_BOOL_ANDAA" LNil) PrNil))
(= (hl-assume-a-proof)
   (GProof
     (GRuleInst "HL_ASSUME" (LCons (hol-a) LNil))
     (PrCons (hl-bool-a-proof) PrNil)))
(= (hl-assume-and-proof)
   (GProof
     (GRuleInst "HL_ASSUME" (LCons (hol-and-aa) LNil))
     (PrCons (hl-bool-and-proof) PrNil)))
(= (hl-conj-aa-proof)
   (GProof
     (GRuleInst "HL_CONJ_AA_REPLAY" LNil)
     (PrCons (hl-assume-a-proof)
       (PrCons (hl-assume-a-proof) PrNil))))
(= (hl-conjunct1-proof)
   (GProof
     (GRuleInst "HL_CONJUNCT1_AA_REPLAY" LNil)
     (PrCons (hl-assume-and-proof) PrNil)))
(= (hl-deduct-proof)
   (GProof
     (GRuleInst "HL_DEDUCT_ANTISYM_SINGLETON" LNil)
     (PrCons (hl-conj-aa-proof)
       (PrCons (hl-conjunct1-proof) PrNil))))
(= (hl-imp-def-proof)
   (GProof (GRuleInst "HL_IMP_DEF_AA" LNil) PrNil))
(= (hl-self-imp-goal)
   (hol-thm (hol-seq (hol-empty) (hol-imp (hol-a) (hol-a)))))
(= (hl-self-imp-proof)
   (GProof
     (GRuleInst "HL_EQ_MP_EMPTY"
       (LCons (hol-eq (hol-and-aa) (hol-a))
         (LCons (hol-imp (hol-a) (hol-a)) LNil)))
     (PrCons (hl-imp-def-proof)
       (PrCons (hl-deduct-proof) PrNil))))

; ---------- Exact acceptance and mutation teeth -----------------------------
!(assertEqual (gic-language-valid (h4-language)) True)
!(assertEqual
  (gic-check (h4-language) (h4-imp-id-goal) (h4-imp-id-proof))
  True)
!(assertEqual
  (gic-check (h4-language) (h4-imp-id-goal)
    (GProof
      (GRuleInst "H4_DISCH"
        (LCons (hol-a)
          (LCons (hol-hyp (hol-a)) (LCons (hol-a) LNil))))
      (PrCons (h4-bool-a-proof) PrNil)))
  False)
!(assertEqual
  (gic-check (h4-language) (h4-imp-id-goal)
    (GProof
      (GRuleInst "H4_DISCH"
        (LCons (hol-a)
          (LCons (hol-hyp (hol-a)) (LCons (hol-a) LNil))))
      (PrCons (h4-assume-a-proof)
        (PrCons (h4-bool-a-proof) PrNil))))
  False)
!(assertEqual
  (gic-check (h4-language) (h4-imp-id-goal)
    (GProof
      (GRuleInst "H4_DISCH"
        (LCons (hol-a)
          (LCons (hol-hyp (hol-a)) (LCons (hol-a) LNil))))
      (PrCons (h4-bool-a-proof)
        (PrCons (h4-assume-b-proof) PrNil))))
  False)

!(assertEqual (gic-language-valid (hl-language)) True)
!(assertEqual
  (gic-check (hl-language) (hl-self-imp-goal) (hl-self-imp-proof))
  True)
!(assertEqual
  (gic-check (hl-language) (hl-self-imp-goal)
    (GProof
      (GRuleInst "H4_DISCH"
        (LCons (hol-a)
          (LCons (hol-hyp (hol-a)) (LCons (hol-a) LNil))))
      (PrCons (hl-assume-a-proof) PrNil)))
  False)
!(assertEqual
  (gic-check (hl-language) (hl-self-imp-goal)
    (GProof
      (GRuleInst "HL_EQ_MP_EMPTY"
        (LCons (hol-eq (hol-and-aa) (hol-a))
          (LCons (hol-imp (hol-a) (hol-a)) LNil)))
      (PrCons (hl-deduct-proof)
        (PrCons (hl-imp-def-proof) PrNil))))
  False)
!(assertEqual
  (gic-check (hl-language) (hl-self-imp-goal)
    (GProof
      (GRuleInst "HL_EQ_MP_EMPTY"
        (LCons (hol-eq (hol-and-aa) (hol-a))
          (LCons (hol-imp (hol-a) (hol-a)) LNil)))
      (PrCons (hl-imp-def-proof) PrNil)))
  False)

; Each profile rejects the other profile's proof object at the rule boundary.
!(assertEqual
  (gic-check (hl-language) (hl-self-imp-goal) (h4-imp-id-proof))
  False)
!(assertEqual
  (gic-check (h4-language) (hl-self-imp-goal) (hl-self-imp-proof))
  False)

!(HOLGICSummary 2 12 12 0)
