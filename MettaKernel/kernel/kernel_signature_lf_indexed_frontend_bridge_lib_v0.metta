; ============================================================================
; kernel_signature_lf_indexed_frontend_bridge_lib_v0.metta
;
; Generic frontend boundary for the indexed LF kernel.
;
; The payload is deliberately the same small witness used by the basic LF
; frontend:
;   KWCheck signature term type
;
; This file changes only which existing kernel checks that witness.  In
; particular, it adds no benchmark rule and no alternate acceptance path.
; The indexed kernel supplies the broader PTS product profile and the generic
; indexed-family declarations; `kernel-check` remains the sole authority.
; ============================================================================

!(import! &self kernel_signature_lf_indexed_lib_v0.metta)

(= (kw-kernel-check $witness)
   (case $witness
     (((KWCheck $signature $term $type)
        (kernel-check $signature $term $type))
      ($_ (Err bad-kernel-witness)))))

; The indexed PTS admits a type parameter and checks its identity function.
!(assertEqual
   (kw-kernel-check
     (KWCheck SNil
       (Lam (Srt type) (Var 0))
       (Pi (Srt type) (Srt type))))
   (Ok
     (CheckedPrf ANil
       (Lam (Srt type) (Var 0))
       (Pi (Srt type) (Srt type)))))

; A term with the wrong dependent body type still fails at the same boundary.
!(assertEqual
   (kw-kernel-check
     (KWCheck SNil
       (Lam (Srt type) (Srt type))
       (Pi (Srt type) (Srt type))))
   (Err check-failed))

!(assertEqual (kw-kernel-check malformed) (Err bad-kernel-witness))
