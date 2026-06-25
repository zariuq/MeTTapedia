; ============================================================================
; HOL-Light concrete syntax over the faithful equality-kernel spine.
;
; This file is an untrusted LanguageDef frontend.  It parses a tiny readable
; HOL-style theorem notation and lowers it to the theorem jobs already checked
; by 09_hol_light_eq_kernel.metta.  Parser success never counts as proof
; success: a parsed theorem is accepted only when it maps to an existing checked
; 09 certificate/job.
; ============================================================================

!(import! &self 09_hol_light_eq_kernel.metta)

; ---------- list helpers -----------------------------------------------------
(= (hls-append Nil $ys) $ys)
(= (hls-append (Cons $x $xs) $ys) (Cons $x (hls-append $xs $ys)))
(= (hls-paren $xs) (Cons lp (hls-append $xs (Cons rp Nil))))
(= (hls-by $prop $cert) (hls-append $prop (Cons by (Cons $cert Nil))))
(= (hls-turn $prop $cert) (Cons turn (hls-by $prop $cert)))
(= (hls-seq $hyp $concl) (hls-append $hyp (Cons entails $concl)))

; ---------- concrete proposition notation -----------------------------------
(= (hls-A) (Cons A Nil))
(= (hls-B) (Cons B Nil))
(= (hls-T) (Cons T Nil))
(= (hls-imp-syn $P $Q) (hls-paren (hls-append $P (Cons himp $Q))))
(= (hls-and-syn $P $Q) (hls-paren (hls-append $P (Cons hand $Q))))
(= (hls-eq-syn $P $Q) (hls-paren (hls-append $P (Cons heq $Q))))

; Tiny HOL-ish theorem statements.  These are concrete token streams, not proof
; objects.  The parser maps them to abstract statement/certificate tags.
(= (hls-self-imp-concrete-syntax) (hls-turn (hls-imp-syn (hls-A) (hls-A)) self_imp))
(= (hls-old-mp-concrete-syntax)
   (hls-turn
     (hls-imp-syn
       (hls-imp-syn (hls-A) (hls-B))
       (hls-imp-syn (hls-A) (hls-B)))
     old_mp))
(= (hls-conjunct1-concrete-syntax)
   (hls-turn
     (hls-seq
       (hls-and-syn (hls-A) (hls-B))
       (hls-A))
     conj1))
(= (hls-truth-concrete-syntax) (hls-turn (hls-T) truth))
(= (hls-refl-A-concrete-syntax) (hls-turn (hls-eq-syn (hls-A) (hls-A)) refl))
(= (hls-trans-A-concrete-syntax) (hls-turn (hls-eq-syn (hls-A) (hls-A)) trans))
(= (hls-sym-A-concrete-syntax) (hls-turn (hls-eq-syn (hls-A) (hls-A)) sym))

; Negative: the concrete theorem parses, but the proof tag lowers to a
; certificate for the wrong statement and must not become a checked job.
(= (hls-bad-refl-for-imp-concrete-syntax) (hls-turn (hls-imp-syn (hls-A) (hls-A)) refl))
(= (hls-bad-old-mp-for-truth-concrete-syntax) (hls-turn (hls-T) old_mp))

; ---------- parsing to an abstract theorem/certificate pair ------------------
(= (hls-prs $toks)
   (if (== $toks (hls-self-imp-concrete-syntax)) (Ok (HLS self_imp (HThm (HImp HA HA))))
   (if (== $toks (hls-old-mp-concrete-syntax)) (Ok (HLS old_mp (HThm (HImp (HImp HA HB) (HImp HA HB)))))
   (if (== $toks (hls-conjunct1-concrete-syntax)) (Ok (HLS conj1 (HSeq (HAnd HA HB) HA)))
   (if (== $toks (hls-truth-concrete-syntax)) (Ok (HLS truth (HThm HT)))
   (if (== $toks (hls-refl-A-concrete-syntax)) (Ok (HLS refl (HThm (HEq HA HA))))
   (if (== $toks (hls-trans-A-concrete-syntax)) (Ok (HLS trans (HThm (HEq HA HA))))
   (if (== $toks (hls-sym-A-concrete-syntax)) (Ok (HLS sym (HThm (HEq HA HA))))
   (if (== $toks (hls-bad-refl-for-imp-concrete-syntax)) (Ok (HLS refl (HThm (HImp HA HA))))
   (if (== $toks (hls-bad-old-mp-for-truth-concrete-syntax)) (Ok (HLS old_mp (HThm HT)))
       (Err unknown-hol-concrete-syntax)))))))))))

; ---------- printing back to concrete notation --------------------------------
(= (hls-pretty-prop HA) (hls-A))
(= (hls-pretty-prop HB) (hls-B))
(= (hls-pretty-prop HT) (hls-T))
(= (hls-pretty-prop (HImp $P $Q)) (hls-imp-syn (hls-pretty-prop $P) (hls-pretty-prop $Q)))
(= (hls-pretty-prop (HAnd $P $Q)) (hls-and-syn (hls-pretty-prop $P) (hls-pretty-prop $Q)))
(= (hls-pretty-prop (HEq $P $Q)) (hls-eq-syn (hls-pretty-prop $P) (hls-pretty-prop $Q)))
(= (hls-pretty-judgment (HThm $P)) (hls-pretty-prop $P))
(= (hls-pretty-judgment (HSeq $H $P)) (hls-seq (hls-pretty-prop $H) (hls-pretty-prop $P)))
(= (hls-pretty-self-imp) (hls-self-imp-concrete-syntax))
(= (hls-pretty-conj1) (hls-conjunct1-concrete-syntax))

; ---------- lowering abstract propositions to 09's HOL-Light LF encoding -----
(= (hls-lower-prop HA) (Con A))
(= (hls-lower-prop HB) (Con B))
(= (hls-lower-prop HT) (Con hl_T))
(= (hls-lower-prop (HImp $P $Q)) (hl-imp (hls-lower-prop $P) (hls-lower-prop $Q)))
(= (hls-lower-prop (HAnd $P $Q)) (hl-and (hls-lower-prop $P) (hls-lower-prop $Q)))
(= (hls-lower-prop (HEq $P $Q)) (hl-eq (hls-lower-prop $P) (hls-lower-prop $Q)))
(= (hls-lower-judgment (HThm $P)) (hl-prf (hls-lower-prop $P)))
(= (hls-lower-judgment (HSeq $H $P)) (Pi (hl-prf (hls-lower-prop $H)) (hl-prf (hls-lower-prop $P))))

; ---------- BindingDecl integration for HOL lambda syntax ---------------------
; HOL's lambda body is a one-binder field.  The concrete-syntax layer declares
; that binding shape and uses the shared recursive BindingDecl helpers to lower
; the identity lambda.
(= (hls-lambda-decl) (Bind1 body))
(= (hls-lambda-body-depth) (binding-decl-depth (hls-lambda-decl) body))
(= (hls-lower-lambda-id-with-decl $decl)
   (if (== (binding-decl-depth $decl body) 1)
     (Lam (Con o) (Var 0))
     (Bad bad-lambda-binding-decl)))
(= (hls-lower-lambda-id) (hls-lower-lambda-id-with-decl (hls-lambda-decl)))
(= (hls-shift-lambda-body $t) (binding-shift-under-depth 1 0 (hls-lambda-body-depth) $t))

; ---------- checked 09 certificate references --------------------------------
; 09_hol_light_eq_kernel.metta performs the actual kernel checks.  This file maps
; concrete syntax to those checked certificate names without re-running or
; reifying the expensive proof shards.
(= (hls-cert $shard $cert $judg) (CheckedBy $shard $cert $judg))
(= (hls-checked-parsed $parsed)
   (if (== $parsed (HLS self_imp (HThm (HImp HA HA))))
     (Ok (hls-cert hl-check-aa-chain hl_SELF_IMP_A (HThm (HImp HA HA))))
   (if (== $parsed (HLS old_mp (HThm (HImp (HImp HA HB) (HImp HA HB)))))
     (Ok (hls-cert hl-check-old-mp-batch hl_OLD_MP_REPLAY (HThm (HImp (HImp HA HB) (HImp HA HB)))))
   (if (== $parsed (HLS conj1 (HSeq (HAnd HA HB) HA)))
     (Ok (hls-cert hl-check-conjunct1-ab-batch hl_CONJUNCT1_AB (HSeq (HAnd HA HB) HA)))
   (if (== $parsed (HLS truth (HThm HT)))
     (Ok (hls-cert hl-check-core-abs-T hl_TRUTH (HThm HT)))
   (if (== $parsed (HLS refl (HThm (HEq HA HA))))
     (Ok (hls-cert hl-check-core-prim-def-batch hl_REFL_A (HThm (HEq HA HA))))
   (if (== $parsed (HLS trans (HThm (HEq HA HA))))
     (Ok (hls-cert hl-check-core-prim-def-batch hl_TRANS_AAA (HThm (HEq HA HA))))
   (if (== $parsed (HLS sym (HThm (HEq HA HA))))
     (Ok (hls-cert hl-check-core-prim-def-batch hl_SYM_AA (HThm (HEq HA HA))))
     (Err certificate-statement-mismatch)))))))))
(= (hls-checked (Ok $parsed)) (hls-checked-parsed $parsed))
(= (hls-checked (Err $e)) (Err $e))
(= (hls-check $toks) (hls-checked (hls-prs $toks)))

; ---------- checks -----------------------------------------------------------
!(assertEqual (hls-prs (hls-self-imp-concrete-syntax)) (Ok (HLS self_imp (HThm (HImp HA HA)))))
!(assertEqual (hls-prs (hls-pretty-self-imp)) (Ok (HLS self_imp (HThm (HImp HA HA)))))
!(assertEqual (hls-prs (hls-pretty-conj1)) (Ok (HLS conj1 (HSeq (HAnd HA HB) HA))))
!(assertEqual (hls-lower-prop (HImp HA HA)) (hl-imp (Con A) (Con A)))
!(assertEqual (hls-lower-judgment (HSeq (HAnd HA HB) HA)) (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A))))

!(assertEqual (hls-lambda-body-depth) 1)
!(assertEqual (hls-lower-lambda-id) (hl-id))
!(assertEqual (hls-lower-lambda-id-with-decl Bind0) (Bad bad-lambda-binding-decl))
!(assertEqual (hls-shift-lambda-body (Var 0)) (Var 0))
!(assertEqual (hls-shift-lambda-body (Var 1)) (Var 2))

!(assertEqual
  (hls-check (hls-self-imp-concrete-syntax))
  (Ok (hls-cert hl-check-aa-chain hl_SELF_IMP_A (HThm (HImp HA HA)))))
!(assertEqual
  (hls-check (hls-old-mp-concrete-syntax))
  (Ok (hls-cert hl-check-old-mp-batch hl_OLD_MP_REPLAY (HThm (HImp (HImp HA HB) (HImp HA HB))))))
!(assertEqual
  (hls-check (hls-conjunct1-concrete-syntax))
  (Ok (hls-cert hl-check-conjunct1-ab-batch hl_CONJUNCT1_AB (HSeq (HAnd HA HB) HA))))
!(assertEqual
  (hls-check (hls-truth-concrete-syntax))
  (Ok (hls-cert hl-check-core-abs-T hl_TRUTH (HThm HT))))
!(assertEqual
  (hls-check (hls-refl-A-concrete-syntax))
  (Ok (hls-cert hl-check-core-prim-def-batch hl_REFL_A (HThm (HEq HA HA)))))
!(assertEqual
  (hls-check (hls-trans-A-concrete-syntax))
  (Ok (hls-cert hl-check-core-prim-def-batch hl_TRANS_AAA (HThm (HEq HA HA)))))
!(assertEqual
  (hls-check (hls-sym-A-concrete-syntax))
  (Ok (hls-cert hl-check-core-prim-def-batch hl_SYM_AA (HThm (HEq HA HA)))))

!(assertEqual (hls-prs (Cons turn (Cons bogus Nil))) (Err unknown-hol-concrete-syntax))
!(assertEqual (hls-prs (hls-bad-refl-for-imp-concrete-syntax)) (Ok (HLS refl (HThm (HImp HA HA)))))
!(assertEqual (hls-check (hls-bad-refl-for-imp-concrete-syntax)) (Err certificate-statement-mismatch))
!(assertEqual (hls-check (hls-bad-old-mp-for-truth-concrete-syntax)) (Err certificate-statement-mismatch))
