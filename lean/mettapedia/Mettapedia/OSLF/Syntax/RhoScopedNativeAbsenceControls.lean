import Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence
import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessorControls
import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveControls

/-!
# Original reactive controls for permitted and unrestricted futures

An open process variable has no original core reaction. Replacing it by a
supplied communicating process enables an actual original event, so its
current negative guard is not full native absence. That substitution is
excluded by the earned retraction condition. Fresh-variable extensions are
positive admitted futures and preserve the exact availability verdict.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedNativeAbsenceControls

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedEventPresheaf RhoScopedNativeAbsence
open RhoScopedParallelInventory RhoIntrinsicCanonicalBag RhoScopedConstructorInventory
open RhoScopedReactionReadout RhoScopedParallelReactiveControls SyntacticRetractionContexts

def processVariable : Process [Srt.pr] := project (.var .zero)

theorem process_variable_components : components processVariable = { .bvar 0 } := by
  rw [components_bagContents]
  rfl

theorem process_variable_quiet : ¬ Enabled core processVariable := by
  rintro ⟨result, step⟩
  obtain ⟨root, surrounding, sourceReadout, _⟩ :=
    (step_iff_root_surrounding _ _).mp step
  have included : read root.source ≤ read processVariable := by
    rw [sourceReadout, read_join]
    exact Multiset.le_add_right _ _
  have bound := components_le included
  rw [← rootReading_source root] at bound
  cases reading : rootReading root with
  | communication channel payload continuation =>
    rw [reading] at bound
    change components (join (RhoIntrinsicReadback.outputClass channel payload)
      (RhoIntrinsicReadback.inputClass channel continuation)) ≤ _ at bound
    rw [join_components, output_components, input_components, process_variable_components] at bound
    have counts := Multiset.card_le_card bound
    simp only [Multiset.card_add, Multiset.card_singleton] at counts
    omega
  | reflection payload =>
    have same : root.1.val = .reflection := by
      have readout := rootReading_rule root
      rw [reading] at readout
      exact readout.symm
    have excluded := root.1.property
    rw [same] at excluded
    exact excluded

theorem supplied_communication_enabled : Enabled core commRoot.source := by
  refine ⟨commRoot.target, (step_iff_root_surrounding _ _).mpr ?_⟩
  exact ⟨commRoot, zero [], (join_zero_right _).symm, (join_zero_right _).symm⟩

def activatingSubstitution : Sub sig [Srt.pr] [] := extend commRoot.2.source

theorem activating_readout : bindQ activatingSubstitution processVariable = commRoot.source := rfl

theorem current_quiet_future_active :
    ¬ Enabled core processVariable ∧ Enabled core (bindQ activatingSubstitution processVariable) :=
  ⟨process_variable_quiet, activating_readout.symm ▸ supplied_communication_enabled⟩

def sourceWorld : (Syntactic.Ctxt sig)ᵒᵖ := Opposite.op ⟨[Srt.pr]⟩

def activatedWorld : (Syntactic.Ctxt sig)ᵒᵖ := Opposite.op ⟨[]⟩

def actualFuture : sourceWorld ⟶ activatedWorld :=
  (show (⟨[]⟩ : Syntactic.Ctxt sig) ⟶ ⟨[Srt.pr]⟩ from activatingSubstitution).op

theorem current_guard_is_not_full_native_absence :
    ¬ processVariable ∈ (absentAtAllFutures core).obj sourceWorld := by
  intro absent
  have blocked := (full_absence_iff_future core sourceWorld processVariable).mp absent
    activatedWorld actualFuture
  exact blocked current_quiet_future_active.2

theorem activating_substitution_has_no_section :
    ¬ IsSplitEpi (show (⟨[]⟩ : Syntactic.Ctxt sig) ⟶ ⟨[Srt.pr]⟩ from activatingSubstitution) := by
  intro splitting
  let change : world (S := sig) [] ⟶ world (S := sig) [Srt.pr] :=
    ⟨activatingSubstitution, splitting⟩
  exact process_variable_quiet
    ((permitted_enabled_iff core change.op processVariable).mp current_quiet_future_active.2)

theorem fresh_name_keeps_quiet :
    ¬ Enabled core (bindQ (fresh (S := sig) [Srt.pr] Srt.nm (quoteRaw null)).val processVariable) :=
  fun active => process_variable_quiet
    ((permitted_enabled_iff core (fresh (S := sig) [Srt.pr] Srt.nm (quoteRaw null)).op processVariable).mp active)

theorem fresh_name_keeps_native_guard :
    bindQ (fresh (S := sig) [Srt.pr] Srt.nm (quoteRaw null)).val processVariable ∈
      (permittedAbsent core).obj (Opposite.op (world [Srt.nm, Srt.pr])) :=
  (permitted_absence_iff_current core _ _).mpr fresh_name_keeps_quiet

theorem fresh_name_keeps_actual_communication :
    Enabled core (bindQ (fresh (S := sig) [] Srt.nm (quoteRaw null)).val commRoot.source) :=
  (permitted_enabled_iff core (fresh (S := sig) [] Srt.nm (quoteRaw null)).op commRoot.source).mpr
    supplied_communication_enabled

end Mettapedia.OSLF.Binding.RhoScopedNativeAbsenceControls
