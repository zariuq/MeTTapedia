; =============================================================================
; kernel_binding_abt_engine_v1.metta
;
; ABT Binding Engine v1, compatibility wrapper.
;
; The real import-stable waist lives in `kernel_binding_waist_v1.metta` and has
; no dependency on the indexed checker.  This wrapper preserves the older module
; name for existing replay/parity rows while importing ONLY the waist.  The live
; indexed kernel is now itself a waist client, so importing it here would either
; duplicate binding answers or trigger deep imported-assertion fragility.  Indexed
; routing is proven by `run_binding_mutation_gate.sh`, which rewrites the indexed
; import to a mutated waist and requires the indexed suite to go red.
; =============================================================================

!(import! &self kernel_binding_waist_v1)
