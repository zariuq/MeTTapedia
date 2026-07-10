; =============================================================================
; kernel_signature_metta_rev_involution_v0.metta
;
; Classification: derived.
;
; Fast target contract for the longer generated MeTTaRev involution theorem.
; The imported stage checks the base reverse/append proof terms.  The full
; rev (rev [0,1,2]) = [0,1,2] proof lives in the optional slow fixture
; kernel_signature_metta_rev_involution_slow_v0.metta, outside the 240s parity
; gate.
;
; Run:
;   cetta kernel_signature_metta_rev_involution_v0.metta
; =============================================================================

!(import! &self kernel_signature_metta_rev_v0)

(= (mrv-rev-involution-012-type)
   (mrv-reduces (mrv-prev (mrv-prev (mrv-list-012))) (mrv-list-012)))

!(assertEqual (sig-has-name MeTTaRev:thm:rev-involution-list0 (mrv-metta-rev-stage-sig)) True)
!(assertEqual (sig-has-name MeTTaRev:thm:rev-involution-012 (mrv-metta-rev-stage-sig)) False)
