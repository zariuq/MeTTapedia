; ============================================================================
; kernel_signature_lf_frontend_bridge_lib_v0.metta
;
; Reusable LF frontend bridge helpers.
;
; One shared kernel-facing ABI:
;   KWCheck sig term type
;
; Frontends may keep their own untrusted search/parsing/evidence layers, but
; they should lower exported witnesses through the helpers here instead of
; rebuilding LF proof-term assembly in parallel.
; ============================================================================

!(import! &self ../Curriculum/Notation/03_lf_concrete_syntax_hook.metta)

; ---------- signature / LF proof helpers ------------------------------------
(= (kw-sig-append SNil $ys) $ys)
(= (kw-sig-append (SCons $d $rest) $ys) (SCons $d (kw-sig-append $rest $ys)))

(= (kw-prop-term $prop) (Con $prop))
(= (kw-imp $prem $concl)
   (App (App (Con imp) (kw-prop-term $prem)) $concl))
(= (kw-arrow LNil $concl) (Con $concl))
(= (kw-arrow (LCons $prem $rest) $concl)
   (kw-imp $prem (kw-arrow $rest $concl)))
(= (kw-prf-type $prop-term) (App (Con prf) $prop-term))

; ---------- canonical kernel witness ABI ------------------------------------
(= (kw-kernel-check $w)
   (case $w
     (((KWCheck $sig $term $type) (kernel-check $sig $term $type))
      ($_ (Err bad-kernel-witness)))))

; ---------- generic FWChainer skeleton lowering -----------------------------
; Shared declarative certificate skeleton:
;   FwFact pf prop
;   FwRule pf premises conclusion kids
;
; Frontends provide only this metadata-level tree. The LF proof-term assembly
; and the kernel verdict both live here.
(= (fw-cert-goal-prop $skel)
   (case $skel
     (((FwFact $pf $prop) (OkProp (kw-prop-term $prop)))
      ((FwRule $pf $prems $concl $kids) (OkProp (kw-prop-term $concl)))
      ($_ (Err bad-fw-cert-skeleton)))))

(= (fw-cert-terms LNil) (OkTerms LNil))
(= (fw-cert-terms (LCons $kid $kids))
   (case (fw-cert-term $kid)
     (((OkTerm $term)
        (case (fw-cert-terms $kids)
          (((OkTerms $rest) (OkTerms (LCons $term $rest)))
           ($e $e))))
      ($e $e))))

; Partial application is left to the kernel to reject via the claimed type;
; over-applied imports fail closed here.
(= (kw-apply-proof $prems $concl $pf LNil) (OkTerm $pf))
(= (kw-apply-proof LNil $concl $pf (LCons $kid $kids))
   (Err too-many-fw-kids))
(= (kw-apply-proof (LCons $prem $rest) $concl $pf (LCons $kid $kids))
   (kw-apply-proof
     $rest
     $concl
     (App (App (App (App (Con impE) (Con $prem)) (kw-arrow $rest $concl)) $pf) $kid)
     $kids))

(= (fw-cert-term $skel)
   (case $skel
     (((FwFact $pf $prop) (OkTerm (Con $pf)))
      ((FwRule $pf $prems $concl $kids)
        (case (fw-cert-terms $kids)
          (((OkTerms $terms) (kw-apply-proof $prems $concl (Con $pf) $terms))
           ($e $e))))
      ($_ (Err bad-fw-cert-skeleton)))))

(= (fw-cert-lower $sig $skel)
   (case (fw-cert-goal-prop $skel)
     (((OkProp $prop)
        (case (fw-cert-term $skel)
          (((OkTerm $term) (Ok (KWCheck $sig $term (kw-prf-type $prop))))
           ($e $e))))
      ($e $e))))

(= (fw-cert-kernel-check $sig $skel)
   (case (fw-cert-lower $sig $skel)
     (((Ok (KWCheck $sig0 $term $type))
        (kw-kernel-check (KWCheck $sig0 $term $type)))
      ($e $e))))

; ---------- parser witness importer -----------------------------------------
(= (parser-lower-lf $toks $ast $type)
   (case (lfn-prsT $toks)
     (((Err $e) (Err (parser-lower-failed $e)))
      ($ast0 (if (== $ast0 $ast)
               (Ok (KWCheck (good-sig) $ast $type))
               (Err parser-cert-mismatch))))))
