import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels

/-!
# Prepared all-future asks reflect injective capture-interface extensions

The active extension keeps every private scope identity and injectively
renames captures with their parameter contexts and sorts. Reflection uses
that actual extension, not an arbitrary binding assignment. Per-use scopes
remain fixed; changing their allocation is handled by scope relocation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching

variable {S : Signature} {Local Shared O : Type}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S}

def activeExtension (extension : Extension captures) : Extension (ContextualActivatedStep.target locals captures) where
  Names := ScopedVar Local ⊕ extension.Names
  declarations := ContextualActivatedStep.target locals extension.declarations
  name := Sum.map id extension.name
  injective := by
    intro first second same
    cases first with
    | inl first =>
        cases second with
        | inl second => exact congrArg Sum.inl (Sum.inl.inj same)
        | inr second => cases same
    | inr first =>
        cases second with
        | inl second => cases same
        | inr second => exact congrArg Sum.inr (extension.injective (Sum.inr.inj same))
  preserves name := by
    cases name with
    | inl name => rfl
    | inr name => exact extension.preserves name

theorem activeExtension_assignment (extension : Extension captures) :
    (activeExtension locals extension).assignment = activeLift locals extension.assignment := by
  funext name
  cases name with
  | inl name => rfl
  | inr name =>
      change castMetaBody (V := signature S (ContextualActivatedStep.target locals extension.declarations))
          (extension.preserves name)
          (generator (ContextualActivatedStep.target locals extension.declarations) (.inr (extension.name name))) =
        instantiate (ContextualSelectionViews.capturedTarget locals extension.declarations)
          (castMetaBody (V := signature S extension.declarations) (extension.preserves name)
            (generator extension.declarations (extension.name name)))
      rw [instantiate_castMetaBody, instantiate_generator]
      rfl

theorem prepared_ask_extension_iff (extension : Extension captures) (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals extension.declarations occupied selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals extension.assignment)))
          (fun occurrence => (rows occurrence).map locals extension.assignment)
          (ContextualTransportedActivation.configurationMap extension.assignment before))
        (ContextualGuardedStep.guardRows locals extension.declarations
          (fun occurrence => (rows occurrence).map locals extension.assignment)) before.present
        (check.map (instantiate (activeLift locals extension.assignment))) ↔
      ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present check := by
  have reflected := ContextualGuardSemantics.Ask.extension_iff locals (activeExtension locals extension)
    (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
    (ContextualGuardedStep.guardRows locals captures rows) before.present check
  rw [activeExtension_assignment] at reflected
  change ContextualGuardSemantics.Ask locals
      (ContextualFrameUnifier.mapProblem (activeLift locals extension.assignment)
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before))
      (fun occurrence => (ContextualGuardedStep.guardRows locals captures rows occurrence).map locals
        (activeLift locals extension.assignment)) before.present
      (check.map (instantiate (activeLift locals extension.assignment))) ↔
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
      (ContextualGuardedStep.guardRows locals captures rows) before.present check at reflected
  rw [ContextualPreparationNaturality.problem_transport locals extension.assignment occupied selection rule rows before,
    guardRows_transport] at reflected
  exact reflected

/-- Pure capture-interface extension preserves and reflects the complete
semantic admission, including output shape and future-family solvability.
The ledger, physical world and original guard cuts are fixed explicitly. -/
theorem semantic_admission_extension_iff [DecidableEq O]
    (extension : Extension captures) (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort) :
    ContextualGuardedStep.Valid locals extension.declarations occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals extension.assignment)))
        (fun occurrence => (rows occurrence).map locals extension.assignment)
        (ContextualTransportedActivation.configurationMap extension.assignment before)
        (fun occurrence => instantiate (activeLift locals extension.assignment) (outputs occurrence)) ↔
      ContextualGuardedStep.Valid locals captures occupied selection rule rows before outputs := by
  have prepared := ContextualPreparationNaturality.prepared_rule_transport locals extension.assignment
    occupied selection rule rows
  have produced := congrArg RuleInstance.produce prepared
  have checked := congrArg RuleInstance.checks prepared
  have solutions :
      ContextualFrameUnifier.Solvable
        (ContextualActivatedStep.problem locals extension.declarations occupied selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals extension.assignment)))
          (fun occurrence => (rows occurrence).map locals extension.assignment)
          (ContextualTransportedActivation.configurationMap extension.assignment before)) ↔
      ContextualFrameUnifier.Solvable
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before) := by
    have preserved := (activeExtension locals extension).exists_model_iff
      (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
    change ContextualFrameUnifier.Solvable (source := ContextualActivatedStep.target locals extension.declarations)
      (ContextualFrameUnifier.mapProblem (activeExtension locals extension).assignment
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before)) ↔
      ContextualFrameUnifier.Solvable
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before) at preserved
    rw [activeExtension_assignment,
      ContextualPreparationNaturality.problem_transport locals extension.assignment occupied selection rule rows before] at preserved
    exact preserved
  have injective : Function.Injective
      (instantiate (Γ := Γ) (sort := sort) (activeLift locals extension.assignment)) := by
    have preserved := (activeExtension locals extension).instantiate_injective (Γ := Γ) (sort := sort)
    rw [activeExtension_assignment] at preserved
    exact preserved
  constructor
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, ?_, ?_, ?_, ?_, ?_⟩,
      solutions.mp admitted.solvable⟩
    · simpa only [RuleInstance.map, List.length_map] using admitted.take_length
    · simpa only [RuleInstance.map, List.length_map] using admitted.read_length
    · apply List.map_injective_iff.mpr injective
      exact (List.map_map ..).trans (admitted.outputs.trans produced.symm)
    · exact ⟨admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
        admitted.occurrences.apart, admitted.occurrences.fresh, fun _ member => by cases member⟩
    · intro check member
      apply (prepared_ask_extension_iff locals extension occupied selection rule rows before check).mp
      apply admitted.checks
      rw [← checked]
      exact List.mem_map.mpr ⟨check, member, rfl⟩
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, ?_, ?_, ?_, ?_, ?_⟩,
      solutions.mpr admitted.solvable⟩
    · simpa only [RuleInstance.map, List.length_map] using admitted.take_length
    · simpa only [RuleInstance.map, List.length_map] using admitted.read_length
    · exact (List.map_map ..).symm.trans
        ((congrArg (List.map (instantiate (activeLift locals extension.assignment))) admitted.outputs).trans produced)
    · exact ⟨admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
        admitted.occurrences.apart, admitted.occurrences.fresh, fun _ member => by cases member⟩
    · intro check member
      rw [← checked] at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (prepared_ask_extension_iff locals extension occupied selection rule rows before original).mpr
        (admitted.checks original present)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality
