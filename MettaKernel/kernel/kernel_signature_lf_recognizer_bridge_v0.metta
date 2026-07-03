; ============================================================================
; kernel_signature_lf_recognizer_bridge_v0.metta
;
; The verified parse -> kernel bridge for kernel_signature_lf_v0.
;
; Source anchors: HHP LF terms and Dedukti/Lambdapi concrete conventions supply
; the parser vocabulary; the final proof verdict is the finite lambda-Pi kernel
; check in kernel_signature_lf_v0.  The trust split follows logical-framework
; front-end methodology: recognized syntax is still checked by the kernel.
;
; Implementation notes, not source claims: parser failures are explicit Err
; values and never reach kernel-check.
;
; The recognizer itself lives in `lf_recognizer_v0.metta` (self-contained, runs
; identically on CeTTa and the Lean-verified LeaTTa engine); this file only wires
; its output into the imported `kernel-check`.
;
; Trust architecture:
;   * the recognizer is the trusted front end -- its algorithm is proved correct
;     in the Lean spec (recognize_sound / sound_all: recognize ts = some t only for
;     WellScoped t), and its runnable twin is `lf-recognize`.  No producer-supplied
;     AST, no re-check: the parser is trusted because it is verified.
;   * the only acceptance verdict comes from the imported `kernel-check`.
;   * a parse failure never reaches the kernel (fail-closed).
;   * the fast generalized GLL/GLR engine is an oracle-checked performance sibling
;     that stays outside this trusted surface.
; ============================================================================

!(import! &self lf_recognizer_v0)
!(import! &self kernel_signature_lf_v0)

; ---------- parse -> kernel bridge (fail-closed) ----------------------------
; Parse the proof term and its claimed type from surface tokens; the kernel gives
; the only verdict.  A parse failure never reaches the kernel.
(= (lf-prove $term-toks $type-toks)
   (case (lf-recognize $term-toks)
     (((Ok $term)
        (case (lf-recognize $type-toks)
          (((Ok $type) (kernel-check (good-sig) $term $type))
           ((Err $e) (Err (type-parse-failed $e))))))
      ((Err $e) (Err (term-parse-failed $e))))))

; Convenience: proof term parsed from surface, type supplied as kernel AST.
(= (lf-check $term-toks $type)
   (case (lf-recognize $term-toks)
     (((Ok $term) (kernel-check (good-sig) $term $type))
      ((Err $e) (Err (term-parse-failed $e))))))

; ---------- parse -> kernel-check: the real verdicts -------------------------
; rfl z : eqn z z            -- accepted
!(assertEqual
   (lf-prove (tk-rfl-z) (tk-eqn-z-z))
   (Ok (CheckedPrf ANil (App (Con rfl) (Con z))
     (App (App (Con eqn) (Con z)) (Con z)))))
; (LAM x : nat . x) z : nat  -- accepted (beta target)
!(assertEqual
   (lf-check (tk-idapp-z) (Con nat))
   (Ok (CheckedPrf ANil (App (Lam (Con nat) (Var 0)) (Con z)) (Con nat))))
; LAM x : nat . x : nat -> nat  -- accepted
!(assertEqual
   (lf-prove (tk-id-nat) (tk-nat-arr-nat))
   (Ok (CheckedPrf ANil (Lam (Con nat) (Var 0)) (Pi (Con nat) (Con nat)))))
; rfl z : eqn z (s z)        -- well-parsed but ill-typed: kernel rejects
!(assertEqual (lf-prove (tk-rfl-z) (tk-eqn-z-sz)) (Err check-failed))
; malformed proof term never reaches the kernel
!(assertEqual (lf-check (tk-malformed) (Con nat)) (Err (term-parse-failed paren-malformed)))
