; =============================================================================
; vec_indexed_family_ntt_target.metta
;
; Executable target contract for the post-upgrade Lean OSLF/NTT lane.
;
; This does not run OSLF itself.  It records, in checkable MeTTa data, what the
; Lean LanguageDef/NTT diagnostic for kernel_signature_lf_vec_v0.metta must cover.
; The important guard is that Vec A n is indexed and multi-argument, so a
; unaryCrossings-only readout is not sufficient evidence.
; =============================================================================

(= (m-member $x TNil) False)
(= (m-member $x (TCons $h $t))
   (if (== $x $h) True (m-member $x $t)))

(= (target-has $target $item) (m-member $item $target))

(= (vec-ntt-target)
   (TCons
     (source kernel_signature_lf_vec_v0.metta)
   (TCons
       (required-constructors
        (
         (vec (Pi Type (Pi nat Type)))
         (vnil (Pi A Type (Vec A z)))
         (vcons (Pi A Type (Pi n nat (Pi x A (Pi xs (Vec A n) (Vec A (s n)))))))
        ))
   (TCons
       (required-positive-checks
        (
         (vec-nat-z-has-type Type)
         (vnil-nat-has-type (Vec nat z))
         (vcons-nat-z-z-vnil-has-type (Vec nat (s z)))
         (kernel-check-vcons-exact-index-ok)
        ))
   (TCons
       (required-negative-checks
        (
         (vnil-nat-rejects (Vec nat (s z)))
         (vcons-one-rejects (Vec nat z))
         (vcons-wrong-tail-index-rejects)
         (vcons-wrong-element-type-rejects)
         (kernel-check-vcons-wrong-index-rejects)
        ))
   (TCons
       (oslf-ntt-requirements
        (
         (languageDef-must-represent-dependent-telescopes)
         (ntt-readout-must-handle-multi-argument-constructors)
         (ntt-readout-must-handle-indexed-family-targets)
         (diamond-witness-must-correspond-to-kernel-check)
         (unaryCrossings-only-is-insufficient)
        ))
     TNil))))))

!(assertEqual
   (target-has (vec-ntt-target)
     (
       required-constructors
       (
         (vec (Pi Type (Pi nat Type)))
         (vnil (Pi A Type (Vec A z)))
         (vcons (Pi A Type (Pi n nat (Pi x A (Pi xs (Vec A n) (Vec A (s n)))))))
       )
     ))
   True)

!(assertEqual
   (target-has (vec-ntt-target)
     (
       required-negative-checks
       (
         (vnil-nat-rejects (Vec nat (s z)))
         (vcons-one-rejects (Vec nat z))
         (vcons-wrong-tail-index-rejects)
         (vcons-wrong-element-type-rejects)
         (kernel-check-vcons-wrong-index-rejects)
       )
     ))
   True)

!(assertEqual
   (target-has (vec-ntt-target)
     (
       oslf-ntt-requirements
       (
         (languageDef-must-represent-dependent-telescopes)
         (ntt-readout-must-handle-multi-argument-constructors)
         (ntt-readout-must-handle-indexed-family-targets)
         (diamond-witness-must-correspond-to-kernel-check)
         (unaryCrossings-only-is-insufficient)
       )
     ))
   True)

; Regression guard: do not accept the older unary-crossings-only diagnostic as
; enough for indexed families.
!(assertEqual
   (target-has (vec-ntt-target) (unaryCrossings-only-is-sufficient))
   False)
