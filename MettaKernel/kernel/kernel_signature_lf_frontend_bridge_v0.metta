; ============================================================================
; kernel_signature_lf_frontend_bridge_v0.metta
;
; Shared frontend -> kernel witness seam for kernel_signature_lf_v0.
;
; Frontends stay untrusted. This file defines one small canonical kernel-facing
; witness (`KWCheck`) plus two witness importers:
;   * chainer witnesses using the MIKFact/MIKRule certificate shape
;   * parser-produced LF concrete syntax lowering from the notation lane
;
; The only acceptance verdict comes from the real imported `kernel-check`.
; ============================================================================

!(import! &self kernel_signature_lf_frontend_bridge_lib_v0.metta)

; ---------- chainer witness metadata ----------------------------------------
; We re-check the same witness shape exported by the CeTTaChainer line:
;   MIKFact id
;   MIKRule label kids
; The frontend metadata names the ground propositions and proof constants; the
; kernel still checks the assembled LF proof term itself.

(= (ch-fact-meta $id)
   (case $id
     ((f-socr-human (ChFactMeta ax_f_socr_human ch_socr_human))
      (f-human-mortal (ChFactMeta ax_f_human_mortal ch_human_mortal))
      ($_ (Err unknown-chainer-fact)))))

(= (ch-rule-meta $label)
   (case $label
     ((trans-inh
        (ChRuleMeta ax_trans_inh
          (LCons ch_socr_human (LCons ch_human_mortal LNil))
          ch_socr_mortal))
      ($_ (Err unknown-chainer-rule)))))

(= (ch-cert-skels LNil) (OkSkels LNil))
(= (ch-cert-skels (LCons $kid $kids))
   (case (ch-cert-skel $kid)
     (((OkSkel $skel)
        (case (ch-cert-skels $kids)
          (((OkSkels $rest) (OkSkels (LCons $skel $rest)))
           ($e $e))))
      ($e $e))))

(= (ch-cert-skel $cert)
   (case $cert
     (((MIKFact $id)
        (case (ch-fact-meta $id)
          (((ChFactMeta $pf $prop) (OkSkel (FwFact $pf $prop)))
           ($e $e))))
      ((MIKRule $label $kids)
        (case (ch-rule-meta $label)
          (((ChRuleMeta $pf $prems $concl)
             (case (ch-cert-skels $kids)
               (((OkSkels $skels) (OkSkel (FwRule $pf $prems $concl $skels)))
                ($e $e))))
           ($e $e))))
      ($_ (Err bad-chainer-witness)))))

(= (chainer-prop-decls)
   (SCons (DConst ch_socr_human (Con o))
   (SCons (DConst ch_human_mortal (Con o))
   (SCons (DConst ch_socr_mortal (Con o))
          SNil))))

(= (chainer-proof-decls)
   (SCons (DAxiom ax_f_socr_human (kw-prf-type (kw-prop-term ch_socr_human)))
   (SCons (DAxiom ax_f_human_mortal (kw-prf-type (kw-prop-term ch_human_mortal)))
   (SCons (DAxiom ax_trans_inh
            (kw-prf-type
              (App (App (Con imp) (Con ch_socr_human))
                   (App (App (Con imp) (Con ch_human_mortal))
                        (Con ch_socr_mortal)))))
          SNil))))

(= (chainer-kernel-sig)
   (kw-sig-append (good-sig)
     (kw-sig-append (chainer-prop-decls) (chainer-proof-decls))))

(= (chainer-lower $cert)
   (case (ch-cert-skel $cert)
     (((OkSkel $skel) (fw-cert-lower (chainer-kernel-sig) $skel))
      ($e $e))))

; ---------- shared frontend entry point -------------------------------------
; Accepted external witness shapes:
;   * KWCheck sig term type        -- canonical kernel witness
;   * FWChainer cert               -- chainer certificate import
;   * FWParserLF tokens ast type   -- LF concrete-syntax lowering import
(= (frontend-lower $w)
   (case $w
     (((KWCheck $sig $term $type) (Ok $w))
      ((FWChainer $cert) (chainer-lower $cert))
      ((FWParserLF $toks $ast $type) (parser-lower-lf $toks $ast $type))
      ($_ (Err bad-frontend-witness)))))

(= (frontend-kernel-check $w)
   (case (frontend-lower $w)
     (((Ok (KWCheck $sig $term $type)) (kw-kernel-check (KWCheck $sig $term $type)))
      ($e $e))))

; ---------- concrete witnesses ----------------------------------------------
(= (front-chainer-pos)
   (FWChainer (MIKRule trans-inh
     (LCons (MIKFact f-socr-human) (LCons (MIKFact f-human-mortal) LNil)))))
(= (front-chainer-neg)
   (FWChainer (MIKRule trans-inh
     (LCons (MIKFact f-human-mortal) (LCons (MIKFact f-socr-human) LNil)))))
(= (front-parser-pos)
   (FWParserLF
     (lfn-idnat-app-z-concrete-syntax)
     (App (Lam (Con nat) (Var 0)) (Con z))
     (Con nat)))
(= (front-parser-neg)
   (FWParserLF
     (lfn-rfl-z-concrete-syntax)
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (App (Con s) (Con z)))))
(= (front-parser-wrong-cert)
   (FWParserLF
     (lfn-idnat-app-z-concrete-syntax)
     (Con z)
     (Con nat)))
(= (front-parser-malformed)
   (FWParserLF (Cons lp (Cons bogus Nil)) (Con z) (Con nat)))

; ---------- checks -----------------------------------------------------------
!(assertEqual (sig-admitted (chainer-kernel-sig)) True)

; Canonical kernel witness stays tiny and fail-closed.
!(assertEqual
   (kw-kernel-check (KWCheck (good-sig) (App (Con rfl) (Con z))
                     (App (App (Con eqn) (Con z)) (Con z))))
   (Ok (CheckedPrf ANil
     (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))))
!(assertEqual (kw-kernel-check bogus) (Err bad-kernel-witness))

; Chainer line -> shared kernel witness -> real kernel verdict.
!(assertEqual
   (frontend-lower (front-chainer-pos))
   (Ok (KWCheck
     (chainer-kernel-sig)
     (App
       (App
         (App
           (App (Con impE) (Con ch_human_mortal))
           (Con ch_socr_mortal))
         (App
           (App
             (App
               (App (Con impE) (Con ch_socr_human))
               (App (App (Con imp) (Con ch_human_mortal)) (Con ch_socr_mortal)))
             (Con ax_trans_inh))
           (Con ax_f_socr_human)))
       (Con ax_f_human_mortal))
     (kw-prf-type (Con ch_socr_mortal)))))
!(assertEqual
   (frontend-kernel-check (front-chainer-pos))
   (Ok (CheckedPrf
     (ACons ax_trans_inh (ACons ax_f_socr_human (ACons ax_f_human_mortal ANil)))
     (App
       (App
         (App
           (App (Con impE) (Con ch_human_mortal))
           (Con ch_socr_mortal))
         (App
           (App
             (App
               (App (Con impE) (Con ch_socr_human))
               (App (App (Con imp) (Con ch_human_mortal)) (Con ch_socr_mortal)))
             (Con ax_trans_inh))
           (Con ax_f_socr_human)))
       (Con ax_f_human_mortal))
     (kw-prf-type (Con ch_socr_mortal)))))
!(assertEqual (frontend-kernel-check (front-chainer-neg)) (Err check-failed))

; Parser line -> same kernel witness -> same real kernel verdict.
!(assertEqual
   (frontend-lower (front-parser-pos))
   (Ok (KWCheck (good-sig) (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))
!(assertEqual
   (frontend-kernel-check (front-parser-pos))
   (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))
!(assertEqual (frontend-kernel-check (front-parser-neg)) (Err check-failed))
!(assertEqual (frontend-kernel-check (front-parser-wrong-cert)) (Err parser-cert-mismatch))
!(assertEqual
   (frontend-kernel-check (front-parser-malformed))
   (Err (parser-lower-failed bad-head)))

; Malformed frontend witness is rejected before any shadow-checking can happen.
!(assertEqual (frontend-kernel-check (FWChainer (MIKRule bogus LNil))) (Err unknown-chainer-rule))
!(assertEqual (frontend-kernel-check bogus) (Err bad-frontend-witness))
