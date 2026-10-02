import Mettapedia.Languages.VibeITP.Native.TermRetainSource
import Mettapedia.Languages.VibeITP.Native.HeapArrayDisciplineControls

/-! Actual source invocation, null, prior faults and wrapping reference counts. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermRetainControls

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeWord64 HeapCells TermHeap TermHeapControls TermRetainSource

def state : SourceState Unit := ⟨memory, none, true, true, (), ⟨0, 0, 0, 0, 0⟩⟩

theorem fresh_parameter_frame : sourceFreshFrame state.memory 200 := ⟨fun _ => rfl, rfl⟩

theorem actual_root_retain_runs (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some rootAddress)] state
      ⟨.reference (some rootAddress), retained state 101 0 rootCell⟩ :=
  (function_exact state 101 0 rootCell rfl rfl rfl _).mpr ⟨⟨200, fresh_parameter_frame⟩, rfl⟩

theorem actual_retain_preserves_shared_graph (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    ∃ out, SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some rootAddress)] state out ∧
      out.value = .reference (some rootAddress) ∧
      At out.state.memory signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  refine ⟨_, actual_root_retain_runs heap calls, ?_⟩
  exact function_preserves_meaning state 101 0 rootCell rfl
    HeapArrayDisciplineControls.ordinary_memory_has_discipline rfl rfl _
    (actual_root_retain_runs heap calls) shared_application_represented

theorem root_count_is_two :
    sourceRead (retained state 101 0 rootCell).memory ⟨101, 0, [6]⟩ = some (.word 2) := rfl

theorem child_count_stays_two :
    sourceRead (retained state 101 0 rootCell).memory ⟨100, 0, [6]⟩ = some (.word 2) := rfl

theorem wrong_return_pointer_refused (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    ¬ SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some rootAddress)] state
      ⟨.reference none, retained state 101 0 rootCell⟩ :=
  function_wrong_pointer_refused state 101 0 rootCell rfl rfl rfl _ (by intro bad; cases bad)

theorem missing_count_update_refused (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    ¬ SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some rootAddress)] state
      ⟨.reference (some rootAddress), state⟩ := by
  intro ran
  have same := ((function_exact state 101 0 rootCell rfl rfl rfl _).mp ran).2
  have impossible := congrArg (fun out : SourceRawResult Unit =>
    sourceRead out.state.memory ⟨101, 0, [6]⟩) same
  have different : (some (SourceValue.word 1)) ≠ some (.word 2) := by
    intro same
    have numbers : (1 : Nat) = 2 := congrArg Fin.val (SourceValue.word.inj (Option.some.inj same))
    contradiction
  exact different impossible

theorem null_retain_ignores_unneeded_capabilities (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    let unavailable := { state with allocatorAvailable := false, releaseAvailable := false }
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference none] unavailable ⟨.reference none, unavailable⟩ := by
  exact (null_function_exact _ rfl _).mpr ⟨⟨200, fresh_parameter_frame⟩, rfl⟩

theorem prior_fault_returns_null_without_touching_heap (heap : SourceHeapSemantics Unit)
    (calls : SourceCalls Unit) :
    let failed := { state with fault := some .invalidRequest }
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some rootAddress)] failed ⟨.reference none, failed⟩ :=
  (entry_fault_exact _ _ .invalidRequest rfl _).mpr rfl

def overflowCell : TermCell := { childCell with references := bounded 64 (2^64 - 1) }
def overflowState : SourceState Unit :=
  { state with memory := sourceStoreCell memory 100 0 overflowCell.sourceValue }

theorem overflowing_retain_runs (heap : SourceHeapSemantics Unit) (calls : SourceCalls Unit) :
    SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls
      NativeOpsSourceGuestSnapshot.function_026 [.reference (some childAddress)] overflowState
      ⟨.reference (some childAddress), retained overflowState 100 0 overflowCell⟩ :=
  (function_exact overflowState 100 0 overflowCell rfl rfl rfl _).mpr ⟨⟨200, ⟨fun _ => rfl, rfl⟩⟩, rfl⟩

theorem overflow_count_is_zero :
    sourceRead (retained overflowState 100 0 overflowCell).memory ⟨100, 0, [6]⟩ = some (.word 0) := rfl

theorem overflowing_retain_preserves_mathematical_term :
    At (retained overflowState 100 0 overflowCell).memory signature markers rootAddress
      (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  have initial : At overflowState.memory signature markers rootAddress
      (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
    term_count_store_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
      100 0 childCell (bounded 64 (2^64 - 1)) rfl shared_application_represented
  have valid : ArrayBaseDiscipline.Memory overflowState.memory :=
    reference_count_write_keeps_array_discipline HeapArrayDisciplineControls.ordinary_memory_has_discipline
      ⟨100, 0, [6]⟩ (bounded 64 (2^64 - 1)) rfl
  exact retained_meaning 100 0 overflowCell valid rfl initial

end Mettapedia.Languages.VibeITP.Native.TermRetainControls
