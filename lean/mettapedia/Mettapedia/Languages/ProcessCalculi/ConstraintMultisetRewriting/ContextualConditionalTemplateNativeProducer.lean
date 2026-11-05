import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeBinding

/-!
# Native producer expressions come from saved conditional births

Output-private variables have a separate declaration block without global
equations. Value and local conditions are lowered through the same role
assignment. Captures use the current caller and the saved birth transport.
The producer does not read final source rows or assume source admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}


def outputEnvironment (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Assignment (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) after.declarations) schedule.guardFamily
  | .inl name => generator schedule.guardFamily ⟨.inr occurrence, name⟩
  | .inr name => schedule.bindingCurrent name

abbrev producerLocals (schedule : Schedule S O Γ sort before after) :=
  ContextualConditionalRowPacking.family schedule.outputVariables schedule.outputDeclarations

def producerDecoder (schedule : Schedule S O Γ sort before after) :
    Assignment schedule.guardFamily (ContextualSelectionViews.source schedule.producerLocals schedule.guardFamily)
  | ⟨.inr occurrence, name⟩ => generator (ContextualSelectionViews.source schedule.producerLocals schedule.guardFamily)
      (.inl ⟨occurrence, name⟩)
  | ⟨.inl index, name⟩ => generator (ContextualSelectionViews.source schedule.producerLocals schedule.guardFamily)
      (.inr ⟨.inl index, name⟩)

def storedOutputRow (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (Row schedule.producerLocals schedule.guardFamily Γ sort) :=
  (schedule.outputRow occurrence).map fun row =>
    ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence
      (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent)

theorem output_decoding_square (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Assignment.compose schedule.producerDecoder (schedule.outputEnvironment occurrence) =
      Assignment.compose
        (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence)
        (ContextualStoredRows.liftCaptures (schedule.outputDeclarations occurrence) schedule.bindingCurrent) := by
  funext name
  cases name with
  | inl name =>
      change instantiate schedule.producerDecoder (generator schedule.guardFamily ⟨.inr occurrence, name⟩) =
        instantiate (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence)
          (generator (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) schedule.guardFamily) (.inl name))
      simp only [instantiate_generator]
      rfl
  | inr name =>
      change instantiate schedule.producerDecoder (generator schedule.guardFamily ⟨.inl none, name⟩) =
        instantiate (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence)
          (instantiate (ContextualSelectionViews.capturedSource (schedule.outputDeclarations occurrence) schedule.guardFamily)
            (generator schedule.guardFamily ⟨.inl none, name⟩))
      simp only [instantiate_generator]
      change _ = instantiate
        (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence)
        (generator (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) schedule.guardFamily)
          (.inr ⟨.inl none, name⟩))
      erw [instantiate_generator]
      rfl

theorem output_body_decodes (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (row : Row (schedule.outputDeclarations occurrence) after.declarations Γ sort) :
    instantiate schedule.producerDecoder (instantiate (schedule.outputEnvironment occurrence)
        (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value)) =
      ContextualStoredRows.asTemplate schedule.producerLocals schedule.guardFamily
        (ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence
          (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent)).value := by
  rw [ContextualConditionalRowPacking.template]
  change _ = instantiate _ (ContextualStoredRows.asTemplate _ _ (row.value.map _ schedule.bindingCurrent))
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    output_decoding_square]

theorem output_conditions_decode (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (row : Row (schedule.outputDeclarations occurrence) after.declarations Γ sort) :
    ContextualResidual.mapProblem schedule.producerDecoder
        (ContextualResidual.mapProblem (schedule.outputEnvironment occurrence) row.obligations) =
      (ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence
        (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent)).obligations := by
  change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _) =
    ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)
  rw [ContextualConditionalNaturality.map_problem_compose, ContextualConditionalNaturality.map_problem_compose,
    output_decoding_square]

def outputBody (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (Term (signature S schedule.guardFamily) Γ sort) :=
  (schedule.outputRow occurrence).map fun row => instantiate (schedule.outputEnvironment occurrence)
    (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value)

/-- These equations are output metadata, not a summand of guardProblem. -/
def outputConditions (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (ContextualResidual.Problem schedule.guardFamily) :=
  (schedule.outputRow occurrence).map fun row => ContextualResidual.mapProblem (schedule.outputEnvironment occurrence) row.obligations

def producerCode (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort :=
  match physical with
  | none => schedule.bindingPattern none
  | some name =>
      ((schedule.outputBody (OccurrenceAllocationRenaming.erase name)).map
        (instantiate (ContextualSelectionViews.capturedSource schedule.bindingLocals schedule.guardFamily))).getD
          (schedule.bindingPattern physical)

noncomputable def producerValues (schedule : Schedule S O Γ sort before after) :=
  schedule.bindingSelection.made.map schedule.producerCode

noncomputable def producerRule (schedule : Schedule S O Γ sort before after) :=
  schedule.nativeBindingRule schedule.producerValues []

noncomputable def producerOutputs (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :=
  ContextualConditionalSourceAdmission.outputs schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
    occupied schedule.bindingSelection (schedule.bindingRule schedule.producerValues []) schedule.bindingRows


theorem produced_body_has_authored_origin (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (value : Term (signature S schedule.guardFamily) Γ sort) (selected : schedule.outputBody occurrence = some value) :
    ∃ row, schedule.outputRow occurrence = some row ∧
      value = instantiate (schedule.outputEnvironment occurrence)
        (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value) := by
  obtain ⟨row, source, same⟩ := Option.map_eq_some_iff.mp selected
  exact ⟨row, source, same.symm⟩

theorem stored_output_instances (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (candidate : Assignment schedule.guardFamily next) (pattern : Term (signature S next) Γ sort) :
    (∃ row, schedule.storedOutputRow occurrence = some row ∧
      Matches schedule.producerLocals schedule.guardFamily candidate pattern row) ↔
      ∃ birth, schedule.outputBirth occurrence = some birth ∧
        birth.origin.Instances (Assignment.compose candidate schedule.bindingCurrent) pattern := by
  rw [← schedule.output_row_instances occurrence (Assignment.compose candidate schedule.bindingCurrent) pattern]
  constructor
  · rintro ⟨stored, selected, matched⟩
    obtain ⟨row, source, same⟩ := Option.map_eq_some_iff.mp selected
    subst stored
    refine ⟨row, source, ?_⟩
    have unpacked := (ContextualConditionalRowPacking.matches_iff schedule.outputVariables schedule.outputDeclarations
      schedule.guardFamily occurrence _ candidate pattern).mp matched
    exact (matches_map_iff (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent candidate pattern row).mp unpacked
  · rintro ⟨row, source, matched⟩
    refine ⟨ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.guardFamily occurrence
      (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent), ?_, ?_⟩
    · exact Option.map_eq_some_iff.mpr ⟨row, source, rfl⟩
    · apply (ContextualConditionalRowPacking.matches_iff schedule.outputVariables schedule.outputDeclarations
        schedule.guardFamily occurrence _ candidate pattern).mpr
      exact (matches_map_iff (schedule.outputDeclarations occurrence) after.declarations schedule.bindingCurrent candidate pattern row).mpr matched

def producerReusable (_schedule : Schedule S O Γ sort before after)
    (_physical : Option (OccurrenceAllocationRenaming.Name O)) : Bool := false

theorem producer_made_distinct (schedule : Schedule S O Γ sort before after) : schedule.bindingSelection.made.Nodup :=
  (Finset.nodup_toList _).map (fun _ _ same => Option.some.inj same)

theorem producer_outputs_at (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.bindingSelection.made) :
    schedule.producerOutputs occupied physical =
      instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode physical)) := by
  let values := (ContextualActivatedStep.prepared
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily occupied
    schedule.bindingSelection schedule.producerRule
    (fun occurrence => (schedule.nativeBindingState occupied).rows occurrence |>.value)).rule.produce
  have compiled : values = schedule.bindingSelection.made.map (fun occurrence =>
      instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode occurrence))) := by
    dsimp only [values, producerRule, nativeBindingRule]
    erw [ContextualConditionalSourceAdmission.prepared_rule]
    change (schedule.producerValues.map _).map _ = _
    simp only [producerValues, List.map_map, Function.comp_def]
  obtain ⟨port, equal⟩ := List.mem_iff_get.mp made
  have lengths : schedule.bindingSelection.made.length = values.length := by rw [compiled, List.length_map]
  have assigned := ContextualTemplateSource.assign_get schedule.bindingSelection.made values schedule.producer_made_distinct lengths port
  rw [equal] at assigned
  change (ContextualTemplateSource.assign schedule.bindingSelection.made values physical).getD _ = _
  rw [assigned]
  change values[port.val]'(by omega) = _
  have indexed := congrArg (fun list => list[port.val]?) compiled
  have bound : port.val < values.length := by omega
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem port.isLt, Option.map_some] at indexed
  exact (Option.some.inj indexed).trans (congrArg (fun occurrence =>
    instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
      (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode occurrence))) equal)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
