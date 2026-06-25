; ============================================================================
; HOL side-by-side showcase: HOL4 kernel facts and MIK checked certificates.
;
; Run the source HOL side:
;   cd /home/aimama/aihub/Mettapedia/MettaKernel/Curriculum/HOL
;   Holmake HOL06_lcf_kernelTheory.uo
;
; Run the MIK side:
;   cd /home/aimama/aihub/Mettapedia/MettaKernel/Curriculum/Notation
;   /home/aimama/aihub/hyperon/CeTTa/cetta --eval-hashcons 09_hol_light_eq_kernel.metta
;   /home/aimama/aihub/hyperon/CeTTa/cetta --eval-hashcons 11_hol_side_by_side_showcase.metta
;
; This is an untrusted concrete-syntax frontend.  Parser success never proves a
; theorem; each readable MIK form below must map to a certificate shard checked
; by 09_hol_light_eq_kernel.metta.  This file intentionally does not import 09:
; 09 is the real proof check, while 11 is the light readable correspondence map.
; ============================================================================

!(import! &self ../../kernel/kernel_binding_decl_v1.metta)

; ---------- tiny mirror of the LF term shapes used by 09 ---------------------
; These definitions mirror the term constructors in 09 so the side-by-side file
; can show exact lowered judgments without re-running the heavy proof shards.
(= (hl-prf $P) (App (Con prf) $P))
(= (hl-eq $P $Q) (App (App (Con hl_eq) $P) $Q))
(= (hl-id) (Lam (Con o) (Var 0)))
(= (hl-and $P $Q) (App (App (Con hl_and) $P) $Q))
(= (hl-imp $P $Q) (App (App (Con hl_imp) $P) $Q))

; ---------- readable MIK forms, beside HOL4 source ---------------------------

; HOL4, Curriculum/HOL/HOL06_lcf_kernelScript.sml:
;   Theorem refl_ex = REFL “x:num”;
; MIK/HOL bounded bool/proposition analogue:
;   (|- (= p p)) by REFL
(= (hshow-refl-form) (by (|- (= p p)) REFL))

; HOL4:
;   Theorem imp_id_kernel = DISCH “p:bool” (ASSUME “p:bool”);
; MIK/HOL:
;   (|- (==> p p)) by (DISCH p (ASSUME p))
(= (hshow-imp-id-form) (by (|- (==> p p)) (DISCH p (ASSUME p))))

; HOL4:
;   Theorem beta_ex = BETA_CONV “(\x:num. x) y”;
; MIK/HOL bounded bool/proposition analogue:
;   (|- (= ((\ x x) p) p)) by BETA
(= (hshow-beta-form) (by (|- (= ((\\ x x) p) p)) BETA))

; Binding integration demo using the same readable lambda marker, with two
; nested binders.  This is a syntax/binder check, not a 09 theorem shard yet.
;   \x. \y. x
(= (hshow-nested-k-form) (\\ x (\\ y x)))

; Other tiny checked HOL-Light equality-kernel facts already covered by 09.
(= (hshow-truth-form) (by (|- T) TRUTH))
(= (hshow-conjunct1-form) (by ((/\\ p q) |- p) CONJUNCT1))

; Negatives: these parse as readable HOL-shaped text, but the proof tags do not
; match the statements and must not become checked certificates.
(= (hshow-bad-refl-for-imp-form) (by (|- (==> p p)) REFL))
(= (hshow-bad-beta-for-refl-form) (by (|- (= p p)) BETA))

; ---------- parser to small abstract judgments/certificate tags --------------

(= (hshow-prs $form)
   (if (== $form (hshow-refl-form)) (Ok (HShow REFL (HThm (= HP HP))))
   (if (== $form (hshow-imp-id-form)) (Ok (HShow DISCH_ASSUME (HThm (==> HP HP))))
   (if (== $form (hshow-beta-form)) (Ok (HShow BETA (HThm (= ((\\ x x) HP) HP))))
   (if (== $form (hshow-truth-form)) (Ok (HShow TRUTH (HThm HT)))
   (if (== $form (hshow-conjunct1-form)) (Ok (HShow CONJUNCT1 (HSeq (/\\ HP HQ) HP)))
   (if (== $form (hshow-bad-refl-for-imp-form)) (Ok (HShow REFL (HThm (==> HP HP))))
   (if (== $form (hshow-bad-beta-for-refl-form)) (Ok (HShow BETA (HThm (= HP HP))))
      (Err unknown-hol-showcase-syntax)))))))))

; ---------- lowering to 09's HOL-Light LF encoding ---------------------------

(= (hshow-lower-prop HP) (Con A))
(= (hshow-lower-prop HQ) (Con B))
(= (hshow-lower-prop HT) (Con hl_T))
(= (hshow-lower-prop (==> $P $Q)) (hl-imp (hshow-lower-prop $P) (hshow-lower-prop $Q)))
(= (hshow-lower-prop (/\\ $P $Q)) (hl-and (hshow-lower-prop $P) (hshow-lower-prop $Q)))
(= (hshow-lower-prop (= $P $Q)) (hl-eq (hshow-lower-term $P) (hshow-lower-term $Q)))

(= (hshow-lower-term HP) (Con A))
(= (hshow-lower-term HQ) (Con B))
(= (hshow-lower-term p) (Con A))
(= (hshow-lower-term q) (Con B))
(= (hshow-lower-term ((\\ $x $body) $arg)) (App (hshow-lower-lambda-id) (hshow-lower-term $arg)))

(= (hshow-lower-judgment (HThm $P)) (hl-prf (hshow-lower-prop $P)))
(= (hshow-lower-judgment (HSeq $H $P))
   (Pi (hl-prf (hshow-lower-prop $H)) (hl-prf (hshow-lower-prop $P))))

; ---------- BindingDecl integration for the beta/lambda showcase -------------

(= (hshow-lambda-decl) (Bind1 body))
(= (hshow-lambda-body-depth) (binding-decl-depth (hshow-lambda-decl) body))
(= (hshow-lower-lambda-id-with-decl $decl)
   (if (== (binding-decl-depth $decl body) 1)
     (Lam (Con o) (Var 0))
     (Bad bad-showcase-lambda-binding-decl)))
(= (hshow-lower-lambda-id) (hshow-lower-lambda-id-with-decl (hshow-lambda-decl)))
(= (hshow-shift-lambda-body $t)
   (binding-shift-under-depth 1 0 (hshow-lambda-body-depth) $t))

(= (hshow-nested-lambda-decl)
   (BindFields (BCons (BField body 2) BNil)))
(= (hshow-nested-lambda-body-depth)
   (binding-decl-depth (hshow-nested-lambda-decl) body))
(= (hshow-lower-nested-k-with-decl $decl)
   (if (== (binding-decl-depth $decl body) 2)
     (Lam (Con o) (Lam (Con o) (Var 1)))
     (Bad bad-showcase-nested-lambda-binding-decl)))
(= (hshow-lower-nested-k) (hshow-lower-nested-k-with-decl (hshow-nested-lambda-decl)))
(= (hshow-shift-nested-lambda-body $t)
   (binding-shift-under-depth 1 0 (hshow-nested-lambda-body-depth) $t))

; ---------- checked 09 certificate references --------------------------------

(= (hshow-cert $shard $cert $judg) (CheckedBy $shard $cert $judg))
(= (hshow-checked-parsed $parsed)
   (if (== $parsed (HShow REFL (HThm (= HP HP))))
     (Ok (hshow-cert hl-check-core-prim-def-batch hl_REFL_A (HThm (= HP HP))))
   (if (== $parsed (HShow DISCH_ASSUME (HThm (==> HP HP))))
     (Ok (hshow-cert hl-check-aa-chain hl_SELF_IMP_A (HThm (==> HP HP))))
   (if (== $parsed (HShow BETA (HThm (= ((\\ x x) HP) HP))))
     (Ok (hshow-cert hl-check-core-prim-def-batch hl_BETA_A (HThm (= ((\\ x x) HP) HP))))
   (if (== $parsed (HShow TRUTH (HThm HT)))
     (Ok (hshow-cert hl-check-core-abs-T hl_TRUTH (HThm HT)))
   (if (== $parsed (HShow CONJUNCT1 (HSeq (/\\ HP HQ) HP)))
     (Ok (hshow-cert hl-check-conjunct1-ab-batch hl_CONJUNCT1_AB (HSeq (/\\ HP HQ) HP)))
     (Err certificate-statement-mismatch)))))))
(= (hshow-corresponds (Ok $parsed)) (hshow-checked-parsed $parsed))
(= (hshow-corresponds (Err $e)) (Err $e))
(= (hshow-correspondence $form) (hshow-corresponds (hshow-prs $form)))

; ---------- checks -----------------------------------------------------------

!(assertEqual (hshow-prs (hshow-refl-form)) (Ok (HShow REFL (HThm (= HP HP)))))
!(assertEqual (hshow-prs (hshow-imp-id-form)) (Ok (HShow DISCH_ASSUME (HThm (==> HP HP)))))
!(assertEqual (hshow-prs (hshow-beta-form)) (Ok (HShow BETA (HThm (= ((\\ x x) HP) HP)))))
!(assertEqual (hshow-prs (hshow-conjunct1-form)) (Ok (HShow CONJUNCT1 (HSeq (/\\ HP HQ) HP))))

!(assertEqual (hshow-lower-prop (==> HP HP)) (hl-imp (Con A) (Con A)))
!(assertEqual (hshow-lower-prop (= HP HP)) (hl-eq (Con A) (Con A)))
!(assertEqual
  (hshow-lower-prop (= ((\\ x x) HP) HP))
  (hl-eq (App (hl-id) (Con A)) (Con A)))
!(assertEqual
  (hshow-lower-judgment (HSeq (/\\ HP HQ) HP))
  (Pi (hl-prf (hl-and (Con A) (Con B))) (hl-prf (Con A))))

!(assertEqual (hshow-lambda-body-depth) 1)
!(assertEqual (hshow-lower-lambda-id) (hl-id))
!(assertEqual (hshow-lower-lambda-id-with-decl Bind0) (Bad bad-showcase-lambda-binding-decl))
!(assertEqual (hshow-shift-lambda-body (Var 0)) (Var 0))
!(assertEqual (hshow-shift-lambda-body (Var 1)) (Var 2))
!(assertEqual (hshow-nested-k-form) (\\ x (\\ y x)))
!(assertEqual (hshow-nested-lambda-body-depth) 2)
!(assertEqual (hshow-lower-nested-k) (Lam (Con o) (Lam (Con o) (Var 1))))
!(assertEqual
  (hshow-lower-nested-k-with-decl (BindFields (BCons (BField body 1) BNil)))
  (Bad bad-showcase-nested-lambda-binding-decl))
!(assertEqual (hshow-shift-nested-lambda-body (Var 1)) (Var 1))
!(assertEqual (hshow-shift-nested-lambda-body (Var 2)) (Var 3))

!(assertEqual
  (hshow-correspondence (hshow-refl-form))
  (Ok (hshow-cert hl-check-core-prim-def-batch hl_REFL_A (HThm (= HP HP)))))
!(assertEqual
  (hshow-correspondence (hshow-imp-id-form))
  (Ok (hshow-cert hl-check-aa-chain hl_SELF_IMP_A (HThm (==> HP HP)))))
!(assertEqual
  (hshow-correspondence (hshow-beta-form))
  (Ok (hshow-cert hl-check-core-prim-def-batch hl_BETA_A (HThm (= ((\\ x x) HP) HP)))))
!(assertEqual
  (hshow-correspondence (hshow-truth-form))
  (Ok (hshow-cert hl-check-core-abs-T hl_TRUTH (HThm HT))))
!(assertEqual
  (hshow-correspondence (hshow-conjunct1-form))
  (Ok (hshow-cert hl-check-conjunct1-ab-batch hl_CONJUNCT1_AB (HSeq (/\\ HP HQ) HP))))

!(assertEqual (hshow-prs (by (|- bogus) REFL)) (Err unknown-hol-showcase-syntax))
!(assertEqual (hshow-prs (hshow-bad-refl-for-imp-form)) (Ok (HShow REFL (HThm (==> HP HP)))))
!(assertEqual (hshow-correspondence (hshow-bad-refl-for-imp-form)) (Err certificate-statement-mismatch))
!(assertEqual (hshow-correspondence (hshow-bad-beta-for-refl-form)) (Err certificate-statement-mismatch))
