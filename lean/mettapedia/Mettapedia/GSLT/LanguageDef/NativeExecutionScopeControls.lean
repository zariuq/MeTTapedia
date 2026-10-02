import Mettapedia.GSLT.LanguageDef.NativeExecutionScope

/-! Ownership and byte-comparison controls. No machine code is executed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionScope

private def handle : NativeOps.Address := ⟨1, 0, []⟩
private def other : NativeOps.Address := ⟨2, 0, []⟩
private def request : Request := ⟨⟨[195], [], []⟩, ⟨1, by decide +kernel⟩⟩
private def observed : Observation := ⟨request, [7]⟩
private def replacement : Observation := ⟨request, [9]⟩
private def scope : Scope := complete [] handle observed

theorem completed_output_readable : targetOutput scope (some handle) = some [7] := by
  decide +kernel

theorem completed_receipt_matches :
    targetMatches scope (some handle) request.inputs [7] = true := by decide +kernel

theorem null_handle_refuses_zero_output :
    targetMatches scope none request.inputs [] = false := rfl

theorem foreign_handle_refuses :
    targetMatches scope (some other) request.inputs [7] = false := by decide +kernel

theorem empty_scope_refuses : targetMatches [] (some handle) request.inputs [7] = false := rfl

theorem caller_output_substitution_refuses :
    targetMatches scope (some handle) request.inputs [9] = false := by decide +kernel

theorem changed_code_refuses :
    targetMatches scope (some handle) ⟨[194], [], []⟩ [7] = false := by decide +kernel

theorem changed_first_input_refuses :
    targetMatches scope (some handle) ⟨[195], [1], []⟩ [7] = false := by decide +kernel

theorem changed_second_input_refuses :
    targetMatches scope (some handle) ⟨[195], [], [1]⟩ [7] = false := by decide +kernel

theorem released_observation_refuses :
    targetMatches (targetRelease scope (some handle)) (some handle) request.inputs [7] = false := by
  decide +kernel

theorem foreign_release_preserves_observation :
    targetRelease scope (some other) = scope := by decide +kernel

theorem released_handle_can_be_reused :
    targetMatches (complete (targetRelease scope (some handle)) handle replacement)
      (some handle) request.inputs [9] = true := by decide +kernel

theorem reused_handle_refuses_old_output :
    targetMatches (complete (targetRelease scope (some handle)) handle replacement)
      (some handle) request.inputs [7] = false := by decide +kernel

private def emptyObserved : Observation :=
  ⟨⟨request.inputs, ⟨0, by decide +kernel⟩⟩, []⟩

theorem completed_empty_output_is_present :
    targetOutput (complete [] handle emptyObserved) (some handle) = some [] := by decide +kernel

theorem absent_output_is_distinct : targetOutput [] (some handle) = none := rfl

theorem completed_empty_output_matches :
    targetMatches (complete [] handle emptyObserved) (some handle) request.inputs [] = true := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeExecutionScope
