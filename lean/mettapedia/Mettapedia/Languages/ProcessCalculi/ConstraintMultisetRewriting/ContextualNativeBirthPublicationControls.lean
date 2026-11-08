import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleControls

/-!
# An earlier native birth keeps answers that a later caller binding excludes

The source first publishes box(X) as an ordinary reusable row, then tells
X=1. Native input binding preserves the birth's box(2) instance. The same
box(X) read through the current caller has only box(1), so replacing the
birth block by the current block loses an observable answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublicationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualSourceSchedules ContextualPrefixPublicationControls
open ContextualConjunctiveQueries
open ContextualScheduleControls.EarlierSchema (body admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

def birth : body.BirthIndex := ⟨0, by decide +kernel⟩

theorem the_original_birth_has_two :
    ContextualPublication.SourceInstances (body.births.get birth).problem (body.births.get birth).value none (box (symbol 2)) := by
  refine ⟨ContextualGuardMatching.Extension.identity none, firstModel none 2, ?_, rfl⟩
  change ContextualResidual.Models (firstModel none 2) []
  intro equation member
  cases member

theorem the_actual_native_information_keeps_two (occupied : Finset Nat) :
    ContextualPublication.SourceInstances (body.native.nativeBindingInformation occupied [] [])
      (body.nativeBirthValue birth) none (box (symbol 2)) := by
  have parts := body.admitted_characterization.mp admitted
  exact (body.native_birth_instances parts.1 parts.2.1 parts.2.2.1 occupied [] [] birth _).mpr
    the_original_birth_has_two

theorem replacing_birth_by_current_would_lose_two (occupied : Finset Nat) :
    ¬ ContextualPublication.SourceInstances (body.native.nativeBindingInformation occupied [] [])
      (body.native.nativeBindingValue (instantiate body.native.bindingCurrent (box secondX))) none (box (symbol 2)) := by
  have parts := body.admitted_characterization.mp admitted
  intro native
  obtain ⟨extension, candidate, model, same⟩ :=
    (body.native.native_current_instances parts.1 parts.2.1 parts.2.2.1 occupied [] [] (box secondX) _).mp native
  have one := the_callers_variable_is_one extension.declarations candidate model
  change box (instantiate candidate secondX) = box (symbol (decl := extension.declarations) 2) at same
  rw [one] at same
  have arguments := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments.1).1)
  omega

def physical : Option (OccurrenceAllocationRenaming.Name Nat) := some (.inr (0, 0))

theorem actual_selection : body.native.bindingSelection = ⟨[Option.none], [], [physical]⟩ := by
  have taken : body.native.net.effect.taken = ∅ := by decide +kernel
  have kept : body.native.net.effect.kept = ∅ := by decide +kernel
  have made : body.native.net.effect.made = {Sum.inr (0, 0)} := by decide +kernel
  simp only [ContextualNativeBodies.Body.bindingSelection, taken, kept, made, Finset.toList_empty, Finset.toList_singleton,
    List.map_nil, List.map_cons]
  rfl

def savedValue : Term (signature base body.native.guardFamily) [] () :=
  instantiate (ContextualIndependentProblems.inclusion body.native.guardVariables body.native.guardDeclarations (.inl (some birth)))
    (body.births.get birth).value

def lowerValue (value : Term (signature base body.native.guardFamily) [] ()) :
    List (Term (signature base (queryFamily body.native.bindingLocals body.native.guardFamily)) [] ()) :=
  [instantiate (ContextualSelectionViews.capturedSource body.native.bindingLocals body.native.guardFamily) value]

def produced := lowerValue savedValue

def output (_ : Option (OccurrenceAllocationRenaming.Name Nat)) := body.nativeBirthValue birth

theorem native_value_producer_admitted (value : Term (signature base body.native.guardFamily) [] ()) :
    ContextualConditionalExecution.Admitted (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
      (body.native.nativeBindingState ∅) (body.native.nativeBindingRule (lowerValue value) []) body.native.bindingSelection
      (fun _ => body.native.nativeBindingValue value) := by
  have parts := body.admitted_characterization.mp admitted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [actual_selection]
    exact List.nodup_singleton _
  · rw [actual_selection]
    exact List.nodup_singleton _
  · change ((body.native.bindingSelection.taken.map body.native.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor body.native.bindingLocals body.native.bindingLocals body.native.guardFamily))).length =
        body.native.bindingSelection.taken.length
    simp only [List.length_map]
  · change ((body.native.bindingSelection.read.map body.native.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor body.native.bindingLocals body.native.bindingLocals body.native.guardFamily))).length =
        body.native.bindingSelection.read.length
    simp only [List.length_map]
  · erw [ContextualConditionalSourceAdmission.prepared_rule]
    rw [actual_selection]
    change [body.native.nativeBindingValue value] =
      [instantiate (ContextualClauseFrames.frame body.native.bindingLocals body.native.bindingLocals body.native.guardFamily ∅).assignment
        (queryView body.native.bindingLocals body.native.bindingLocals body.native.guardFamily
          (instantiate (ContextualSelectionViews.capturedSource body.native.bindingLocals body.native.guardFamily) value))]
    congr 1
    unfold ContextualNativeBodies.Body.nativeBindingValue queryView
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
    apply congrArg (fun assignment => instantiate assignment value)
    funext name
    simp only [Assignment.compose, ContextualSelectionViews.capturedSource]
    erw [instantiate_generator]
    change ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
      body.native.guardFamily name =
      instantiate (ContextualClauseFrames.frame body.native.bindingLocals body.native.bindingLocals body.native.guardFamily ∅).assignment
        (generator (family body.native.bindingLocals body.native.bindingLocals body.native.guardFamily) (.inr (.inr name)))
    erw [instantiate_generator]
    rfl
  · rw [actual_selection]
    change ({Option.none} : Finset (Option (OccurrenceAllocationRenaming.Name Nat))) ⊆ insert Option.none ∅
    exact Finset.Subset.rfl
  · rw [actual_selection]
    exact Finset.empty_subset _
  · rw [actual_selection]
    exact Finset.disjoint_empty_right _
  · rw [actual_selection]
    change Disjoint ({physical} : Finset (Option (OccurrenceAllocationRenaming.Name Nat))) {Option.none}
    decide +kernel
  · exact (body.native.native_binding_solvable_iff parts.1 parts.2.1 ∅ (lowerValue value) []).mpr parts.2.2.1
  · intro check member
    erw [ContextualConditionalSourceAdmission.prepared_rule] at member
    change check ∈ [] at member
    cases member

theorem the_compiled_producer_is_admitted :
    ContextualConditionalExecution.Admitted (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
      (body.native.nativeBindingState ∅) (body.native.nativeBindingRule produced []) body.native.bindingSelection output :=
  native_value_producer_admitted savedValue

/-- The source-derived native rule really runs and its published schema
retains 2 at every worklist budget. The caller remains separately fixed. -/
theorem an_actual_producer_keeps_the_earlier_answer (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) (body.native.nativeBindingState ∅),
      firing.rule = body.native.nativeBindingRule produced [] ∧ firing.selection = body.native.bindingSelection ∧
        firing.outputs = output ∧ firing.reusable = (fun _ => true) ∧ firing.fuel = fuel ∧
        firing.target.present = {physical} ∧
        ∀ (Future : Type) (future : Future → MetaArity base) (candidate : Assignment firing.target.declarations future),
          Matches
            (ContextualPublication.privateFamily (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
              firing.update.declaration)
            firing.target.declarations candidate (box (symbol 2)) (firing.target.rows physical) := by
  obtain ⟨firing, rule, selection, values, reusable, budget⟩ := ContextualConditionalExecution.realize_at_fuel
    (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) (body.native.nativeBindingState ∅)
    (body.native.nativeBindingRule produced []) body.native.bindingSelection output (fun _ => true) the_compiled_producer_is_admitted fuel
  refine ⟨firing, rule, selection, values, reusable, budget, ?_, ?_⟩
  · rw [firing.physical_result, selection, actual_selection]
    decide +kernel
  · intro Future future candidate
    have parts := body.admitted_characterization.mp admitted
    apply (body.ordinary_native_row_matches_birth parts.1 parts.2.1 parts.2.2.1 ∅ produced []
      firing rule selection physical (by rw [selection, actual_selection]; exact List.mem_singleton_self _)
      (by rw [reusable]) birth (by rw [values]; rfl) candidate (box (symbol 2))).mpr
    refine ⟨ContextualGuardMatching.Extension.identity future, firstModel future 2, ?_, rfl⟩
    change ContextualResidual.Models (firstModel future 2) []
    intro equation member
    cases member

theorem the_actual_returned_caller_is_one
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) (body.native.nativeBindingState ∅))
    (rule : firing.rule = body.native.nativeBindingRule produced []) (selection : firing.selection = body.native.bindingSelection)
    {Future : Type} (future : Future → MetaArity base) (candidate : Assignment firing.target.declarations future)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    instantiate candidate
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
        (body.native.nativeBindingValue (instantiate body.native.bindingCurrent secondX))) = symbol 1 := by
  have one := the_callers_variable_is_one future _
    (body.native.native_returned_current_model ∅ produced [] firing rule selection candidate model)
  unfold ContextualNativeBodies.Body.nativeBindingValue
  erw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  exact one

def sharedValue : Term (signature base body.native.guardFamily) [] () :=
  instantiate body.native.bindingCurrent (box secondX)

/-- The same native producer with a shared output follows the current
caller instead of opening an independent creation-time schema. -/
theorem an_actual_shared_producer_keeps_one (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) (body.native.nativeBindingState ∅),
      firing.rule = body.native.nativeBindingRule (lowerValue sharedValue) [] ∧ firing.selection = body.native.bindingSelection ∧
        firing.outputs = (fun _ => body.native.nativeBindingValue sharedValue) ∧ firing.reusable = (fun _ => false) ∧
        firing.fuel = fuel ∧ ContextualConditionalExecution.Solvable firing.target.equations ∧
        ∀ (Future : Type) (future : Future → MetaArity base) (candidate : Assignment firing.target.declarations future),
          ContextualResidual.Models candidate firing.target.equations →
          Matches
            (ContextualPublication.privateFamily (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
              firing.update.declaration)
            firing.target.declarations candidate (box (symbol 1)) (firing.target.rows physical) ∧
          ¬ Matches
            (ContextualPublication.privateFamily (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
              firing.update.declaration)
            firing.target.declarations candidate (box (symbol 2)) (firing.target.rows physical) := by
  obtain ⟨firing, rule, selection, values, reusable, budget⟩ := ContextualConditionalExecution.realize_at_fuel
    (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals) (body.native.nativeBindingState ∅)
    (body.native.nativeBindingRule (lowerValue sharedValue) []) body.native.bindingSelection
    (fun _ => body.native.nativeBindingValue sharedValue) (fun _ => false) (native_value_producer_admitted sharedValue) fuel
  refine ⟨firing, rule, selection, values, reusable, budget, body.native.native_target_solvable ∅ firing, ?_⟩
  intro Future future candidate model
  have current := body.native.native_returned_current_model ∅ (lowerValue sharedValue) [] firing rule selection candidate model
  have one := the_callers_variable_is_one future _ current
  have exactRow (pattern : Term (signature base future) [] ()) :
      Matches
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank body.native.bindingLocals body.native.bindingLocals)
          firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows physical) ↔ pattern = box (symbol 1) := by
    rw [body.native.shared_native_row_matches_current ∅ firing physical
      (by rw [selection, actual_selection]; exact List.mem_singleton_self _) (by rw [reusable])
      (box secondX) (by rw [values]; rfl) candidate pattern]
    change pattern = box (instantiate _ secondX) ↔ _
    rw [one]
  refine ⟨(exactRow (box (symbol 1))).mpr rfl, ?_⟩
  intro matched
  have same := (exactRow (box (symbol 2))).mp matched
  have arguments := Args.cons.inj (eq_of_heq (Term.op.inj same).2)
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments.1).1)
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublicationControls
