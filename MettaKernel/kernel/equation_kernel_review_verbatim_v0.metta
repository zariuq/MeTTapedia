; =============================================================================
; equation_kernel_review_verbatim_v0.metta
;
; The reviewed theory-mixing probe in its original call shapes, which the
; repaired interface no longer has. Load after equation_kernel_registry_v0,
; equation_kernel_v0 and equation_kernel_space_v0. HE and CeTTa read the old
; calls as inert data, so no theorem results; PeTTa refuses the file when it
; loads, because ek:lcf-step is called with five arguments.
; =============================================================================

(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))

!(ek:control ctl-review-lcf-cross-theory-verbatim (let $t (ek:lcf-step (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:lcf-refl (ek:sym "A")) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) (ek:lcf-claim (ek:lcf-step (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) ek:nil) $t (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) 0) ek:nil ek:nil))) ek:none)
