; ============================================================================
; HOL-Light equality-kernel LanguageDef concrete syntax, v0.
;
; This is the faithful direction for HOL hosting: object rules are the actual
; HOL-Light equality-kernel spine from fusion.ml, represented as LF constants
; and checked by the imported MeTTaKernel boundary.  The older 08 file remains
; a natural-deduction regression oracle until MP/DISCH are derived here through
; EQ_MP / DEDUCT_ANTISYM and the old primitive path can be retired.
;
; Sources:
;   repos/itp-curriculum-sources/hol_light/fusion.ml
;   repos/itp-curriculum-sources/hol_light/bool.ml
;   repos/itp-curriculum-sources/hol_light/Help/{REFL,TRANS,MK_COMB,ABS,
;     BETA,ASSUME,EQ_MP,IMP_ANTISYM_RULE}.hlp
; ============================================================================

!(import! &self ../../kernel/kernel_signature_lf_v0.metta)
!(import! &self ../../kernel/kernel_binding_decl_v1.metta)

; ---------- small LF term helpers -------------------------------------------
(= (hl-prf $P) (App (Con prf) $P))
(= (hl-eq $P $Q) (App (App (Con hl_eq) $P) $Q))
(= (hl-eqf $F $G) (App (App (Con hl_eqf) $F) $G))
(= (hl-eq2 $F $G) (App (App (Con hl_eq2) $F) $G))
(= (hl-eqpred2 $F $G) (App (App (Con hl_eqpred2) $F) $G))
(= (hl-bin-ty) (Pi (Con o) (Pi (Con o) (Con o))))
(= (hl-pred2-ty) (Pi (hl-bin-ty) (Con o)))
(= (hl-id) (Lam (Con o) (Var 0)))
(= (hl-sel1) (Lam (Con o) (Lam (Con o) (Var 1))))
(= (hl-sel2) (Lam (Con o) (Lam (Con o) (Var 0))))
(= (hl-and-pred $P $Q)
   (Lam (hl-bin-ty) (App (App (Var 0) $P) $Q)))
(= (hl-T-body) (hl-eqf (hl-id) (hl-id)))
(= (hl-and-body)
   (Lam (Con o)
     (Lam (Con o)
       (hl-eqpred2
         (Lam (Pi (Con o) (Pi (Con o) (Con o)))
           (App (App (Var 0) (Var 2)) (Var 1)))
         (Lam (Pi (Con o) (Pi (Con o) (Con o)))
           (App (App (Var 0) (Con hl_T)) (Con hl_T)))))))
(= (hl-imp-body)
   (Lam (Con o)
     (Lam (Con o)
       (hl-eq (App (App (Con hl_and) (Var 1)) (Var 0)) (Var 1)))))
(= (hl-and $P $Q) (App (App (Con hl_and) $P) $Q))
(= (hl-imp $P $Q) (App (App (Con hl_imp) $P) $Q))
(= (hl-imp-def-eq $P $Q)
   (hl-eq (hl-eq (hl-and $P $Q) $P) (hl-imp $P $Q)))

; ---------- hosted HOL-Light equality-kernel signature -----------------------
; Bounded to bool/proposition objects and bool -> bool functions.  This is not
; full polymorphic HOL-Light; it is the first faithful spine through the actual
; primitive rules.
(= (hol-light-eq-sig)
   (SCons (DConst o (Srt type))
   (SCons (DConst prf (Pi (Con o) (Srt type)))
   (SCons (DConst hl_eq (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst hl_eqf
             (Pi (Pi (Con o) (Con o))
                  (Pi (Pi (Con o) (Con o)) (Con o))))
   (SCons (DConst hl_eq2
             (Pi (Pi (Con o) (Pi (Con o) (Con o)))
                  (Pi (Pi (Con o) (Pi (Con o) (Con o))) (Con o))))
   (SCons (DConst hl_eqpred2
             (Pi (Pi (Pi (Con o) (Pi (Con o) (Con o))) (Con o))
                  (Pi (Pi (Pi (Con o) (Pi (Con o) (Con o))) (Con o))
                      (Con o))))
   (SCons (DConst A (Con o))
   (SCons (DConst B (Con o))
   (SCons (DConst hl_T (Con o))
   (SCons (DConst hl_and (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst hl_imp (Pi (Con o) (Pi (Con o) (Con o))))
   (SCons (DConst hl_T_DEF
             (hl-prf (hl-eq (Con hl_T) (hl-T-body))))
   (SCons (DConst hl_AND_DEF
             (hl-prf (hl-eq2 (Con hl_and) (hl-and-body))))
   (SCons (DConst hl_IMP_DEF
             (Pi (Con o)
               (Pi (Con o)
                 (hl-prf (hl-imp-def-eq (Var 1) (Var 0))))))

   ; REFL: |- t = t
   (SCons (DConst hl_REFL
             (Pi (Con o)
               (hl-prf (App (App (Con hl_eq) (Var 0)) (Var 0)))))
   (SCons (DConst hl_REFL2
             (Pi (hl-bin-ty)
               (hl-prf (App (App (Con hl_eq2) (Var 0)) (Var 0)))))
   (SCons (DConst hl_REFLPRED2
             (Pi (hl-pred2-ty)
               (hl-prf (App (App (Con hl_eqpred2) (Var 0)) (Var 0)))))

   ; TRANS: A |- p = q, B |- q = r  ==>  A u B |- p = r
   (SCons (DConst hl_TRANS
             (Pi (Con o)
               (Pi (Con o)
                 (Pi (Con o)
                   (Pi (hl-prf (App (App (Con hl_eq) (Var 2)) (Var 1)))
                     (Pi (hl-prf (App (App (Con hl_eq) (Var 2)) (Var 1)))
                       (hl-prf (App (App (Con hl_eq) (Var 4)) (Var 2)))))))))

   ; MK_COMB: f = g, x = y  ==>  f x = g y
   (SCons (DConst hl_MK_COMB
             (Pi (Pi (Con o) (Con o))
               (Pi (Pi (Con o) (Con o))
                 (Pi (Con o)
                   (Pi (Con o)
                     (Pi (hl-prf (App (App (Con hl_eqf) (Var 3)) (Var 2)))
                       (Pi (hl-prf (App (App (Con hl_eq) (Var 2)) (Var 1)))
                         (hl-prf
                           (App
                             (App (Con hl_eq) (App (Var 5) (Var 3)))
                             (App (Var 4) (Var 2)))))))))))
   (SCons (DConst hl_MK_COMB2
             (Pi (hl-bin-ty)
               (Pi (hl-bin-ty)
                 (Pi (Con o)
                   (Pi (Con o)
                     (Pi (hl-prf (App (App (Con hl_eq2) (Var 3)) (Var 2)))
                       (Pi (hl-prf (App (App (Con hl_eq) (Var 2)) (Var 1)))
                         (hl-prf
                           (App
                             (App (Con hl_eqf) (App (Var 5) (Var 3)))
                             (App (Var 4) (Var 2)))))))))))
   (SCons (DConst hl_MK_COMB_PRED2
             (Pi (hl-pred2-ty)
               (Pi (hl-pred2-ty)
                 (Pi (hl-bin-ty)
                   (Pi (hl-bin-ty)
                     (Pi (hl-prf (App (App (Con hl_eqpred2) (Var 3)) (Var 2)))
                       (Pi (hl-prf (App (App (Con hl_eq2) (Var 2)) (Var 1)))
                         (hl-prf
                           (App
                             (App (Con hl_eq) (App (Var 5) (Var 3)))
                             (App (Var 4) (Var 2)))))))))))

   ; ABS: (under a binder) f x = g x  ==>  (\x. f x) = (\x. g x)
   (SCons (DConst hl_ABS
             (Pi (Pi (Con o) (Con o))
               (Pi (Pi (Con o) (Con o))
                 (Pi
                   (Pi (Con o)
                     (hl-prf
                       (App
                         (App (Con hl_eq) (App (Var 2) (Var 0)))
                         (App (Var 1) (Var 0)))))
                   (hl-prf (App (App (Con hl_eqf) (Var 2)) (Var 1)))))))
   ; Bounded ABS instance at ((bool -> bool -> bool) -> bool), needed by
   ; bool.ml's AND_DEF derivation.
   (SCons (DConst hl_ABS_PRED2
             (Pi (hl-pred2-ty)
               (Pi (hl-pred2-ty)
                 (Pi
                   (Pi (hl-bin-ty)
                     (hl-prf
                       (App
                         (App (Con hl_eq) (App (Var 2) (Var 0)))
                         (App (Var 1) (Var 0)))))
                   (hl-prf (App (App (Con hl_eqpred2) (Var 2)) (Var 1)))))))

   ; BETA: |- (\x. x) x = x, the HOL-Light primitive trivial beta case.
   (SCons (DConst hl_BETA
             (Pi (Con o)
               (hl-prf
                 (App
                   (App (Con hl_eq) (App (Lam (Con o) (Var 0)) (Var 0)))
                   (Var 0)))))

   ; EQ_MP: |- p = q, |- p  ==>  |- q
   (SCons (DConst hl_EQ_MP
             (Pi (Con o)
               (Pi (Con o)
                 (Pi (hl-prf (App (App (Con hl_eq) (Var 1)) (Var 0)))
                   (Pi (hl-prf (Var 2))
                     (hl-prf (Var 2)))))))

   ; DEDUCT_ANTISYM: from p |- q and q |- p derive |- p = q.
	   (SCons (DConst hl_DEDUCT_ANTISYM
	             (Pi (Con o)
	               (Pi (Con o)
	                 (Pi
	                   (Pi (hl-prf (Var 1)) (hl-prf (Var 1)))
	                   (Pi
	                     (Pi (hl-prf (Var 1)) (hl-prf (Var 3)))
	                     (hl-prf (App (App (Con hl_eq) (Var 3)) (Var 2))))))))

	   SNil)))))))))))))))))))))))))))

; Derived-rule library shards.  Each local DThm chain admits one large derived
; theorem and then uses it opaquely by name in its local batch.  This keeps
; admission lexical without exposing a checked-signature token or retaining the
; whole derived-rule tower in one CeTTa run.
(= (hl-aa-thm-chain)
   (SCons (DThm hl_DISCH_AA_CORE
             (hl-prf (hl-eq (hl-and-AA) (Con A)))
             (hl-disch-AA-core))
   (SCons (DThm hl_SELF_IMP_A
             (hl-prf (hl-imp (Con A) (Con A)))
             (hl-self-imp-derived))
          SNil)))

(= (hl-mp-ab-thm-chain)
   (SCons (DThm hl_MP_AB
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B))))
             (hl-mp-AB))
          SNil))

(= (hl-expanded-ab-thm-chain)
   (SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-and-expanded-PQ-from-proofs (Con A) (Con B)))
          SNil))

(= (hl-conj-ab-thm-chain)
   (SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-and-expanded-PQ-from-proofs (Con A) (Con B)))
   (SCons (DThm hl_CONJ_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB))))
             (hl-conj-AB-from-proofs-sharded))
          SNil)))

(= (hl-conjunct1-ab-thm-chain)
   (SCons (DThm hl_CONJUNCT1_AB
             (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A)))
             (hl-conjunct1-PQ (Con A) (Con B)))
          SNil))

(= (hl-disch-ab-thm-chain)
   (SCons (DThm hl_MP_AB
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B))))
             (hl-mp-AB))
   (SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-and-expanded-PQ-from-proofs (Con A) (Con B)))
   (SCons (DThm hl_CONJ_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB))))
             (hl-conj-AB-from-proofs-sharded))
   (SCons (DThm hl_CONJUNCT1_AB
             (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A)))
             (hl-conjunct1-PQ (Con A) (Con B)))
   (SCons (DThm hl_DISCH_AB_UNDER_IMPAB
	             (Pi (hl-prf (hl-impAB)) (hl-prf (hl-impAB)))
	             (hl-disch-AB-under-impAB-sharded))
	          SNil))))))

(= (hl-old-mp-thm-chain)
   (SCons (DThm hl_MP_AB
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B))))
             (hl-mp-AB))
   (SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-and-expanded-PQ-from-proofs (Con A) (Con B)))
   (SCons (DThm hl_CONJ_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB))))
             (hl-conj-AB-from-proofs-sharded))
   (SCons (DThm hl_CONJUNCT1_AB
             (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A)))
             (hl-conjunct1-PQ (Con A) (Con B)))
   (SCons (DThm hl_DISCH_AB_UNDER_IMPAB
             (Pi (hl-prf (hl-impAB)) (hl-prf (hl-impAB)))
             (hl-disch-AB-under-impAB-sharded))
   (SCons (DThm hl_CONJ_IMPAB_FROM_PROOFS
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (hl-impAB)) (hl-prf (hl-and-impAB-impAB))))
             (hl-conj-PQ-from-proofs (hl-impAB) (hl-impAB)))
   (SCons (DThm hl_CONJUNCT1_IMPAB
             (Pi (hl-prf (hl-and-impAB-impAB)) (hl-prf (hl-impAB)))
             (hl-conjunct1-PQ (hl-impAB) (hl-impAB)))
   (SCons (DThm hl_OLD_MP_REPLAY
             (hl-prf (hl-impAB-self))
             (hl-old-mp-replay-sharded))
          SNil)))))))))

; ---------- rule certificates / spine terms ---------------------------------
(= (hl-refl-A)
   (App (Con hl_REFL) (Con A)))

(= (hl-refl-eqAA)
   (App (Con hl_REFL) (hl-eq (Con A) (Con A))))

(= (hl-trans-AAA)
   (App
     (App
       (App
         (App
           (App (Con hl_TRANS) (Con A))
           (Con A))
         (Con A))
       (hl-refl-A))
     (hl-refl-A)))

(= (hl-abs-id)
   (App
     (App
       (App (Con hl_ABS) (hl-id))
       (hl-id))
     (Lam (Con o) (App (Con hl_REFL) (Var 0)))))

(= (hl-mk-comb-id-A)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB) (hl-id))
             (hl-id))
           (Con A))
         (Con A))
       (hl-abs-id))
     (hl-refl-A)))

(= (hl-beta-A)
   (App (Con hl_BETA) (Con A)))

; ASSUME is represented by LF variables.  This is the identity derivation
; p |- p, used by DEDUCT_ANTISYM below.
(= (hl-assume-id-A)
   (Lam (hl-prf (Con A)) (Var 0)))

(= (hl-deduct-AA)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) (Con A))
         (Con A))
       (hl-assume-id-A))
     (hl-assume-id-A)))

(= (hl-eq-mp-eqAA)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-eq (Con A) (Con A)))
         (hl-eq (Con A) (Con A)))
       (hl-refl-eqAA))
     (hl-refl-A)))

(= (hl-refl-hl-eq)
   (App (Con hl_REFL2) (Con hl_eq)))

(= (hl-ap-term-eq-from $P $Q $h)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB2) (Con hl_eq))
             (Con hl_eq))
           $P)
         $Q)
       (hl-refl-hl-eq))
     $h))

(= (hl-sym-from $P $Q $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-eq $P $P))
         (hl-eq $Q $P))
       (App
         (App
           (App
             (App
               (App
                 (App (Con hl_MK_COMB) (App (Con hl_eq) $P))
                 (App (Con hl_eq) $Q))
               $P)
             $P)
           (hl-ap-term-eq-from $P $Q $h))
         (App (Con hl_REFL) $P)))
     (App (Con hl_REFL) $P)))

(= (hl-truth)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-T-body))
         (Con hl_T))
       (hl-sym-from (Con hl_T) (hl-T-body) (Con hl_T_DEF)))
     (hl-abs-id)))

(= (hl-eqt-intro-A)
   (Lam (hl-prf (Con A))
     (App
       (App
         (App
           (App (Con hl_DEDUCT_ANTISYM) (Con A))
           (Con hl_T))
         (Lam (hl-prf (Con A)) (hl-truth)))
       (Lam (hl-prf (Con hl_T)) (Var 1)))))

(= (hl-eqt-elim-A-from $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (Con hl_T))
         (Con A))
       (hl-sym-from (Con A) (Con hl_T) $h))
     (hl-truth)))

(= (hl-refl-prop $P) (App (Con hl_REFL) $P))

(= (hl-eqt-elim-from $P $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (Con hl_T))
         $P)
       (hl-sym-from $P (Con hl_T) $h))
     (hl-truth)))

(= (hl-eqt-intro-at-depth1 $P)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) $P)
         (Con hl_T))
       (Lam (hl-prf $P) (hl-truth)))
     (Lam (hl-prf (Con hl_T)) (Var 2))))

(= (hl-eqt-intro-at-depth2 $P)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) $P)
         (Con hl_T))
       (Lam (hl-prf $P) (hl-truth)))
     (Lam (hl-prf (Con hl_T)) (Var 3))))

(= (hl-and-PQ $P $Q) (hl-and $P $Q))
(= (hl-and-expanded-PQ $P $Q)
   (hl-eqpred2 (hl-and-pred $P $Q) (hl-and-pred (Con hl_T) (Con hl_T))))

(= (hl-and-def-P $P)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB2) (Con hl_and))
             (hl-and-body))
           $P)
         $P)
       (hl-and-def))
     (hl-refl-prop $P)))

(= (hl-and-def-PQ $P $Q)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB) (App (Con hl_and) $P))
             (App (hl-and-body) $P))
           $Q)
         $Q)
       (hl-and-def-P $P))
     (hl-refl-prop $Q)))

(= (hl-expand-and-PQ-from $P $Q $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-and-PQ $P $Q))
         (hl-and-expanded-PQ $P $Q))
       (hl-and-def-PQ $P $Q))
     $h))

(= (hl-select-conj1-eq-from $P $Q $h)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB_PRED2) (hl-and-pred $P $Q))
             (hl-and-pred (Con hl_T) (Con hl_T)))
           (hl-sel1))
         (hl-sel1))
       (hl-expand-and-PQ-from $P $Q $h))
     (App (Con hl_REFL2) (hl-sel1))))

(= (hl-select-conj2-eq-from $P $Q $h)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB_PRED2) (hl-and-pred $P $Q))
             (hl-and-pred (Con hl_T) (Con hl_T)))
           (hl-sel2))
         (hl-sel2))
       (hl-expand-and-PQ-from $P $Q $h))
     (App (Con hl_REFL2) (hl-sel2))))

(= (hl-conjunct1-PQ $P $Q)
   (Lam (hl-prf (hl-and-PQ $P $Q))
     (hl-eqt-elim-from $P (hl-select-conj1-eq-from $P $Q (Var 0)))))

(= (hl-conjunct2-PQ $P $Q)
   (Lam (hl-prf (hl-and-PQ $P $Q))
     (hl-eqt-elim-from $Q (hl-select-conj2-eq-from $P $Q (Var 0)))))

(= (hl-pointwise-PQ-eq $P $Q $eqP $eqQ)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB) (App (Var 0) $P))
             (App (Var 0) (Con hl_T)))
           $Q)
         (Con hl_T))
       (App
         (App
           (App
             (App
               (App
                 (App (Con hl_MK_COMB2) (Var 0))
                 (Var 0))
               $P)
             (Con hl_T))
           (App (Con hl_REFL2) (Var 0)))
         $eqP))
     $eqQ))

(= (hl-and-expanded-PQ-from-proofs $P $Q)
   (Lam (hl-prf $P)
     (Lam (hl-prf $Q)
       (App
         (App
           (App (Con hl_ABS_PRED2) (hl-and-pred $P $Q))
           (hl-and-pred (Con hl_T) (Con hl_T)))
         (Lam (hl-bin-ty)
           (hl-pointwise-PQ-eq
             $P
             $Q
             (hl-eqt-intro-at-depth2 $P)
             (hl-eqt-intro-at-depth1 $Q)))))))

(= (hl-conj-PQ-from-proofs $P $Q)
   (Lam (hl-prf $P)
     (Lam (hl-prf $Q)
       (App
         (App
           (App
             (App (Con hl_EQ_MP) (hl-and-expanded-PQ $P $Q))
             (hl-and-PQ $P $Q))
           (hl-sym-from
             (hl-and-PQ $P $Q)
             (hl-and-expanded-PQ $P $Q)
             (hl-and-def-PQ $P $Q)))
         (App (App (hl-and-expanded-PQ-from-proofs $P $Q) (Var 1)) (Var 0))))))

(= (hl-conj-AB-from-proofs-sharded)
   (Lam (hl-prf (Con A))
     (Lam (hl-prf (Con B))
       (App
         (App
           (App
             (App (Con hl_EQ_MP) (hl-and-expanded-PQ (Con A) (Con B)))
             (hl-and-PQ (Con A) (Con B)))
           (hl-sym-from
             (hl-and-PQ (Con A) (Con B))
             (hl-and-expanded-PQ (Con A) (Con B))
             (hl-and-def-PQ (Con A) (Con B))))
         (App (App (Con hl_AND_EXPANDED_AB_FROM_PROOFS) (Var 1)) (Var 0))))))

(= (hl-and-AA) (hl-and (Con A) (Con A)))
(= (hl-and-expanded-AA)
   (hl-eqpred2 (hl-and-pred (Con A) (Con A)) (hl-and-pred (Con hl_T) (Con hl_T))))

(= (hl-and-def)
   (Con hl_AND_DEF))

(= (hl-and-def-A)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB2) (Con hl_and))
             (hl-and-body))
           (Con A))
         (Con A))
       (hl-and-def))
     (hl-refl-A)))

(= (hl-and-def-AA)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB) (App (Con hl_and) (Con A)))
             (App (hl-and-body) (Con A)))
           (Con A))
         (Con A))
       (hl-and-def-A))
     (hl-refl-A)))

(= (hl-expand-and-AA-from $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-and-AA))
         (hl-and-expanded-AA))
       (hl-and-def-AA))
     $h))

(= (hl-select-conj1-eq-AT-from $h)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB_PRED2) (hl-and-pred (Con A) (Con A)))
             (hl-and-pred (Con hl_T) (Con hl_T)))
           (hl-sel1))
         (hl-sel1))
       (hl-expand-and-AA-from $h))
     (App (Con hl_REFL2) (hl-sel1))))

(= (hl-eqt-intro-A-at-depth1)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) (Con A))
         (Con hl_T))
       (Lam (hl-prf (Con A)) (hl-truth)))
     (Lam (hl-prf (Con hl_T)) (Var 2))))

(= (hl-pointwise-AA-eq)
   (App
     (App
       (App
         (App
           (App
             (App (Con hl_MK_COMB) (App (Var 0) (Con A)))
             (App (Var 0) (Con hl_T)))
           (Con A))
         (Con hl_T))
       (App
         (App
           (App
             (App
               (App
                 (App (Con hl_MK_COMB2) (Var 0))
                 (Var 0))
               (Con A))
             (Con hl_T))
           (App (Con hl_REFL2) (Var 0)))
         (hl-eqt-intro-A-at-depth1)))
     (hl-eqt-intro-A-at-depth1)))

(= (hl-and-expanded-AA-from-A)
   (Lam (hl-prf (Con A))
     (App
       (App
         (App (Con hl_ABS_PRED2) (hl-and-pred (Con A) (Con A)))
         (hl-and-pred (Con hl_T) (Con hl_T)))
       (Lam (hl-bin-ty) (hl-pointwise-AA-eq)))))

(= (hl-conj-AA-from-A)
   (Lam (hl-prf (Con A))
     (App
       (App
         (App
           (App (Con hl_EQ_MP) (hl-and-expanded-AA))
           (hl-and-AA))
         (hl-sym-from (hl-and-AA) (hl-and-expanded-AA) (hl-and-def-AA)))
       (App (hl-and-expanded-AA-from-A) (Var 0)))))

(= (hl-conjunct1-AA)
   (Lam (hl-prf (hl-and-AA))
     (hl-eqt-elim-A-from (hl-select-conj1-eq-AT-from (Var 0)))))

(= (hl-disch-AA-core)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) (hl-and-AA))
         (Con A))
       (hl-conjunct1-AA))
     (hl-conj-AA-from-A)))

(= (hl-imp-def-AA)
   (App (App (Con hl_IMP_DEF) (Con A)) (Con A)))

(= (hl-self-imp-derived-expected)
	       (App
	         (App
	           (App
	             (App (Con hl_EQ_MP) (hl-eq (hl-and-AA) (Con A)))
	             (hl-imp (Con A) (Con A)))
	           (hl-imp-def-AA))
	     (Con hl_DISCH_AA_CORE)))
(= (hl-self-imp-derived) (hl-self-imp-derived-expected))

(= (hl-impAB) (hl-imp (Con A) (Con B)))
(= (hl-and-AB) (hl-and (Con A) (Con B)))
(= (hl-imp-def-AB)
   (App (App (Con hl_IMP_DEF) (Con A)) (Con B)))

(= (hl-impAB-eq-from $h)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-impAB))
         (hl-eq (hl-and-AB) (Con A)))
       (hl-sym-from
         (hl-eq (hl-and-AB) (Con A))
         (hl-impAB)
         (hl-imp-def-AB)))
     $h))

(= (hl-mp-AB)
   (Lam (hl-prf (hl-impAB))
     (Lam (hl-prf (Con A))
       (App
         (hl-conjunct2-PQ (Con A) (Con B))
           (App
             (App
               (App
                 (App (Con hl_EQ_MP) (Con A))
                 (hl-and-AB))
             (hl-sym-from (hl-and-AB) (Con A) (hl-impAB-eq-from (Var 1))))
           (Var 0))))))

(= (hl-disch-AB-under-impAB)
	   (Lam (hl-prf (hl-impAB))
	     (App
	       (App
         (App
           (App (Con hl_EQ_MP) (hl-eq (hl-and-AB) (Con A)))
           (hl-impAB))
         (hl-imp-def-AB))
       (App
         (App
           (App
             (App (Con hl_DEDUCT_ANTISYM) (hl-and-AB))
             (Con A))
	           (hl-conjunct1-PQ (Con A) (Con B)))
	         (Lam (hl-prf (Con A))
	       (App
	               (App (hl-conj-PQ-from-proofs (Con A) (Con B)) (Var 0))
	             (App (App (Con hl_MP_AB) (Var 1)) (Var 0))))))))

(= (hl-disch-AB-under-impAB-sharded)
   (Lam (hl-prf (hl-impAB))
     (App
       (App
         (App
           (App (Con hl_EQ_MP) (hl-eq (hl-and-AB) (Con A)))
           (hl-impAB))
         (hl-imp-def-AB))
       (App
         (App
           (App
             (App (Con hl_DEDUCT_ANTISYM) (hl-and-AB))
             (Con A))
           (Con hl_CONJUNCT1_AB))
         (Lam (hl-prf (Con A))
           (App
             (App (Con hl_CONJ_AB_FROM_PROOFS) (Var 0))
             (App (App (Con hl_MP_AB) (Var 1)) (Var 0))))))))

(= (hl-impAB-self) (hl-imp (hl-impAB) (hl-impAB)))
(= (hl-and-impAB-impAB) (hl-and (hl-impAB) (hl-impAB)))
(= (hl-imp-def-impAB-impAB)
   (App (App (Con hl_IMP_DEF) (hl-impAB)) (hl-impAB)))

(= (hl-old-mp-replay-core)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) (hl-and-impAB-impAB))
         (hl-impAB))
       (hl-conjunct1-PQ (hl-impAB) (hl-impAB)))
     (Lam (hl-prf (hl-impAB))
       (App
         (App (hl-conj-PQ-from-proofs (hl-impAB) (hl-impAB)) (Var 0))
         (App (hl-disch-AB-under-impAB) (Var 0))))))

(= (hl-old-mp-replay)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-eq (hl-and-impAB-impAB) (hl-impAB)))
         (hl-impAB-self))
         (hl-imp-def-impAB-impAB))
     (hl-old-mp-replay-core)))

(= (hl-old-mp-replay-core-sharded)
   (App
     (App
       (App
         (App (Con hl_DEDUCT_ANTISYM) (hl-and-impAB-impAB))
         (hl-impAB))
       (Con hl_CONJUNCT1_IMPAB))
     (Lam (hl-prf (hl-impAB))
       (App
         (App (Con hl_CONJ_IMPAB_FROM_PROOFS) (Var 0))
         (App (Con hl_DISCH_AB_UNDER_IMPAB) (Var 0))))))

(= (hl-old-mp-replay-sharded)
   (App
     (App
       (App
         (App (Con hl_EQ_MP) (hl-eq (hl-and-impAB-impAB) (hl-impAB)))
         (hl-impAB-self))
       (hl-imp-def-impAB-impAB))
     (hl-old-mp-replay-core-sharded)))

(= (hl-core-prim-batch-jobs)
   (Cons (Accept
            (hl-refl-A)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-trans-AAA)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-abs-id)
            (hl-prf (hl-eqf (hl-id) (hl-id))))
   (Cons (Accept
            (hl-mk-comb-id-A)
            (hl-prf (hl-eq (App (hl-id) (Con A)) (App (hl-id) (Con A)))))
   (Cons (Accept
            (hl-beta-A)
            (hl-prf (hl-eq (App (hl-id) (Con A)) (Con A))))
   (Cons (Accept
            (hl-deduct-AA)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-eq-mp-eqAA)
            (hl-prf (hl-eq (Con A) (Con A))))
         Nil))))))))

(= (hl-core-def-batch-jobs)
   (Cons (Accept
            (hl-and-def-AA)
            (hl-prf (hl-eq (hl-and-AA) (hl-and-expanded-AA))))
   (Cons (Accept
            (hl-sym-from (Con A) (Con A) (hl-refl-A))
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-eqt-intro-A)
            (Pi (hl-prf (Con A)) (hl-prf (hl-eq (Con A) (Con hl_T)))))
         Nil))))

(= (hl-core-prim-def-batch-jobs)
   (Cons (Accept
            (hl-refl-A)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-trans-AAA)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-abs-id)
            (hl-prf (hl-eqf (hl-id) (hl-id))))
   (Cons (Accept
            (hl-mk-comb-id-A)
            (hl-prf (hl-eq (App (hl-id) (Con A)) (App (hl-id) (Con A)))))
   (Cons (Accept
            (hl-beta-A)
            (hl-prf (hl-eq (App (hl-id) (Con A)) (Con A))))
   (Cons (Accept
            (hl-deduct-AA)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-eq-mp-eqAA)
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-and-def-AA)
            (hl-prf (hl-eq (hl-and-AA) (hl-and-expanded-AA))))
   (Cons (Accept
            (hl-sym-from (Con A) (Con A) (hl-refl-A))
            (hl-prf (hl-eq (Con A) (Con A))))
   (Cons (Accept
            (hl-eqt-intro-A)
            (Pi (hl-prf (Con A)) (hl-prf (hl-eq (Con A) (Con hl_T)))))
         Nil)))))))))))

(= (hl-core-and-from-A-job)
   (Cons (Accept
            (hl-and-expanded-AA-from-A)
            (Pi (hl-prf (Con A)) (hl-prf (hl-and-expanded-AA))))
         Nil))

(= (hl-core-imp-def-job)
   (Cons (Accept
            (hl-imp-def-AA)
            (hl-prf (hl-imp-def-eq (Con A) (Con A))))
         Nil))

(= (hl-core-abs-T-job)
   (Cons (Accept
            (hl-truth)
            (hl-prf (Con hl_T)))
         Nil))

(= (hl-core-negative-jobs)
   (Cons (Reject
            (hl-refl-A)
            (hl-prf (hl-eq (Con A) (Con B))))
   (Cons (Reject
            (hl-beta-A)
            (hl-prf (hl-eq (Con A) (Con B))))
         Nil)))

(= (hl-conj-batch-jobs)
   (Cons (Accept
            (hl-conjunct1-AA)
            (Pi (hl-prf (hl-and-AA)) (hl-prf (Con A))))
   (Cons (Accept
            (hl-conjunct2-PQ (Con A) (Con B))
            (Pi (hl-prf (hl-and-AB)) (hl-prf (Con B))))
         Nil)))

(= (hl-aa-chain-jobs)
   (Cons (Accept
            (Con hl_DISCH_AA_CORE)
            (hl-prf (hl-eq (hl-and-AA) (Con A))))
   (Cons (Accept
            (Con hl_SELF_IMP_A)
            (hl-prf (hl-imp (Con A) (Con A))))
         Nil)))

(= (hl-mp-batch-jobs)
   (Cons (Accept
            (Con hl_MP_AB)
            (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B)))))
         Nil))

(= (hl-expanded-ab-batch-jobs)
   (Cons (Accept
            (Con hl_AND_EXPANDED_AB_FROM_PROOFS)
            (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B))))))
         Nil))

(= (hl-conj-ab-batch-jobs)
   (Cons (Accept
            (Con hl_CONJ_AB_FROM_PROOFS)
            (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB)))))
         Nil))

(= (hl-conjunct1-ab-batch-jobs)
   (Cons (Accept
            (Con hl_CONJUNCT1_AB)
            (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A))))
         Nil))

(= (hl-disch-ab-batch-jobs)
   (Cons (Accept
            (Con hl_DISCH_AB_UNDER_IMPAB)
            (Pi (hl-prf (hl-impAB)) (hl-prf (hl-impAB))))
         Nil))

(= (hl-old-mp-batch-jobs)
   (Cons (Accept
            (Con hl_CONJ_IMPAB_FROM_PROOFS)
            (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (hl-impAB)) (hl-prf (hl-and-impAB-impAB)))))
   (Cons (Accept
            (Con hl_CONJUNCT1_IMPAB)
            (Pi (hl-prf (hl-and-impAB-impAB)) (hl-prf (hl-impAB))))
   (Cons (Accept
            (Con hl_OLD_MP_REPLAY)
            (hl-prf (hl-impAB-self)))
         Nil))))

(= (hl-def-theorem-jobs)
   (Cons (Accept
            (Con hl_T_DEF)
            (hl-prf (hl-eq (Con hl_T) (hl-T-body))))
   (Cons (Accept
            (Con hl_AND_DEF)
            (hl-prf (hl-eq2 (Con hl_and) (hl-and-body))))
   (Cons (Accept
            (App (App (Con hl_IMP_DEF) (Con A)) (Con B))
            (hl-prf (hl-imp-def-eq (Con A) (Con B))))
         Nil))))

(= (hl-check-core-prim-def-batch) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-core-prim-def-batch-jobs)))
(= (hl-check-def-theorems) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-def-theorem-jobs)))
(= (hl-check-core-and-from-A) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-core-and-from-A-job)))
(= (hl-check-core-imp-def) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-core-imp-def-job)))
(= (hl-check-core-abs-T) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-core-abs-T-job)))
(= (hl-check-core-negatives) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-core-negative-jobs)))
(= (hl-check-conj-batch) (kernel-check-batch-judgments (hol-light-eq-sig) (hl-conj-batch-jobs)))
(= (hl-check-aa-chain)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-aa-thm-chain)
     (hl-aa-chain-jobs)))
(= (hl-check-mp-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-mp-ab-thm-chain)
     (hl-mp-batch-jobs)))
(= (hl-check-expanded-ab-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-expanded-ab-thm-chain)
     (hl-expanded-ab-batch-jobs)))
(= (hl-check-conj-ab-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-conj-ab-thm-chain)
     (hl-conj-ab-batch-jobs)))
(= (hl-check-conjunct1-ab-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-conjunct1-ab-thm-chain)
     (hl-conjunct1-ab-batch-jobs)))
(= (hl-check-disch-ab-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-disch-ab-thm-chain)
     (hl-disch-ab-batch-jobs)))
(= (hl-check-old-mp-batch)
   (kernel-check-batch-judgments-with-thms
     (hol-light-eq-sig)
     (hl-old-mp-thm-chain)
     (hl-old-mp-batch-jobs)))
; ---------- checks -----------------------------------------------------------
; HOL-Light-style definitions are object-level theorem constants over opaque
; constants, matching HOL-Light's definition discipline rather than LF unfolding.
!(assertEqual (hl-check-def-theorems) True)

; Scoped batch admission covers theorem groups without exposing any public
; checked-signature token.  Large derived rules are sharded; the curriculum gate
; runs this file with eval-arena hash-consing so repeated proof subterms share.
!(assertEqual (hl-check-core-prim-def-batch) True)
!(assertEqual (hl-check-core-and-from-A) True)
!(assertEqual (hl-check-core-imp-def) True)
!(assertEqual (hl-check-core-abs-T) True)
!(assertEqual (hl-check-core-negatives) True)
!(assertEqual (hl-check-conj-batch) True)
!(assertEqual (hl-check-aa-chain) True)
!(assertEqual (hl-check-mp-batch) True)
!(assertEqual (hl-check-expanded-ab-batch) True)
!(assertEqual (hl-check-conj-ab-batch) True)
!(assertEqual (hl-check-conjunct1-ab-batch) True)
!(assertEqual (hl-check-disch-ab-batch) True)
!(assertEqual (hl-check-old-mp-batch) True)

!(assertEqual
  (binding-decl-depth (BindPi domain codomain) codomain)
  1)
