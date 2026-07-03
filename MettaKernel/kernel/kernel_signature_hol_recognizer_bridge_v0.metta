; ============================================================================
; kernel_signature_hol_recognizer_bridge_v0.metta
;
; HOL/STT `hol-core-g` surface -> verified recognizer twin -> LF kernel-check.
;
; Source anchors: HOL is an object logic encoded as an LF signature in the HHP
; methodology, with Assaf-Burel HOL-to-Dedukti as the translation comparison.
; The checked fragment is classical/STT-shaped only at the signature layer; the
; trusted verdict remains the imported lambda-Pi kernel-check.
;
; Implementation notes, not source claims: finite corpus proof elaboration,
; explicit parser/elaborator Err values, and no parser-success-as-proof shortcut.
;
; The parser/lowerer is the trusted front end because it mirrors the Lean M2
; recognizer (`Mettapedia/GSLT/LanguageDef/HOL.lean`) and is differentially
; checked here on the finite corpus.  The proof-fragment elaborator only inserts
; the LF proof-domain annotation forced by `impI A B`; final acceptance is still
; exclusively the imported `kernel-check`.
;
; Only token streams enter this bridge; parse failures and elaboration failures
; never reach the kernel.
; ============================================================================

!(import! &self hol_recognizer_v0)
!(import! &self kernel_signature_lf_v0)

(= (hol-prf-type $prop) (App (Con prf) $prop))

(= (hol-prove $proof-toks $prop-toks)
   (case (hol-recognize-proof $proof-toks)
     (((Ok $proof)
        (case (hol-recognize $prop-toks)
          (((Ok $prop) (kernel-check (good-sig) $proof (hol-prf-type $prop)))
           ((Err $e) (Err (prop-parse-failed $e))))))
      ((Err $e) (Err (proof-parse-failed $e))))))

(= (hol-check-prop $prop-toks)
   (case (hol-recognize $prop-toks)
     (((Ok $prop) (kernel-check (good-sig) $prop (Con o)))
      ((Err $e) (Err (prop-parse-failed $e))))))

; ---------- parse -> kernel-check: implication proofs through HOL surface ----
!(assertEqual
  (hol-prove (ht-self-imp-proof) (ht-self-imp))
  (Ok (CheckedPrf ANil
    (App (App (App (Con impI) (Con A)) (Con A))
         (Lam (App (Con prf) (Con A)) (Var 0)))
    (App (Con prf) (App (App (Con imp) (Con A)) (Con A))))))

!(assertEqual
  (hol-prove (ht-k-proof) (ht-k-theorem))
  (Ok (CheckedPrf ANil
    (App (App (App (Con impI) (Con A)) (App (App (Con imp) (Con B)) (Con A)))
      (Lam (App (Con prf) (Con A))
        (App (App (App (Con impI) (Con B)) (Con A))
          (Lam (App (Con prf) (Con B)) (Var 1)))))
    (App (Con prf)
      (App (App (Con imp) (Con A))
        (App (App (Con imp) (Con B)) (Con A)))))))

!(assertEqual
  (hol-prove (ht-mp-theorem-proof) (ht-mp-theorem))
  (Ok (CheckedPrf ANil
    (App (App (App (Con impI) (App (App (Con imp) (Con A)) (Con B)))
                    (App (App (Con imp) (Con A)) (Con B)))
      (Lam (App (Con prf) (App (App (Con imp) (Con A)) (Con B)))
        (App (App (App (Con impI) (Con A)) (Con B))
          (Lam (App (Con prf) (Con A))
            (App (App (App (App (Con impE) (Con A)) (Con B)) (Var 1)) (Var 0))))))
    (App (Con prf)
      (App (App (Con imp) (App (App (Con imp) (Con A)) (Con B)))
        (App (App (Con imp) (Con A)) (Con B)))))))

; Negative: parser and elaborator can succeed while the imported kernel rejects.
!(assertEqual (hol-prove (ht-bad-a-imp-b-proof) (ht-a-imp-b)) (Err check-failed))
!(assertEqual (hol-prove (ht-malformed) (ht-self-imp)) (Err (proof-parse-failed paren-malformed)))
