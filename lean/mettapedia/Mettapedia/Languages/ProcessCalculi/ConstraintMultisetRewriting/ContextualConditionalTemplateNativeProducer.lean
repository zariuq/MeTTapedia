import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerAdmission

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

local instance : DecidableEq (OccurrenceAllocationRenaming.Name O) :=
  inferInstanceAs (DecidableEq (O ⊕ (Nat × O)))
local instance : DecidableEq (Option (OccurrenceAllocationRenaming.Name O)) := inferInstance
local instance : BEq (Option (OccurrenceAllocationRenaming.Name O)) where
  beq left right := decide (left = right)
local instance : LawfulBEq (Option (OccurrenceAllocationRenaming.Name O)) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def outputEnvironment (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Assignment (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) after.declarations) schedule.native.guardFamily
  | .inl name => generator schedule.native.guardFamily ⟨.inl (some occurrence), name⟩
  | .inr name => schedule.native.bindingCurrent name

abbrev producerLocals (schedule : Schedule S O Γ sort before after) :=
  ContextualConditionalRowPacking.family schedule.outputVariables schedule.outputDeclarations

def producerDecoder (schedule : Schedule S O Γ sort before after) :
    Assignment schedule.native.guardFamily (ContextualSelectionViews.source schedule.producerLocals schedule.native.guardFamily)
  | ⟨.inl (some occurrence), name⟩ => generator (ContextualSelectionViews.source schedule.producerLocals schedule.native.guardFamily)
      (.inl ⟨occurrence, name⟩)
  | ⟨.inl none, name⟩ => generator (ContextualSelectionViews.source schedule.producerLocals schedule.native.guardFamily)
      (.inr ⟨.inl none, name⟩)
  | ⟨.inr cut, name⟩ => generator (ContextualSelectionViews.source schedule.producerLocals schedule.native.guardFamily)
      (.inr ⟨.inr cut, name⟩)

def storedOutputRow (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (Row schedule.producerLocals schedule.native.guardFamily Γ sort) :=
  (schedule.outputRow occurrence).map fun row =>
    ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence
      (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent)

theorem output_decoding_square (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Assignment.compose schedule.producerDecoder (schedule.outputEnvironment occurrence) =
      Assignment.compose
        (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence)
        (ContextualStoredRows.liftCaptures (schedule.outputDeclarations occurrence) schedule.native.bindingCurrent) := by
  funext name
  cases name with
  | inl name =>
      change instantiate schedule.producerDecoder (generator schedule.native.guardFamily ⟨.inl (some occurrence), name⟩) =
        instantiate (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence)
          (generator (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) schedule.native.guardFamily) (.inl name))
      simp only [instantiate_generator]
      rfl
  | inr name =>
      change instantiate schedule.producerDecoder (generator schedule.native.guardFamily ⟨.inl none, name⟩) =
        instantiate (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence)
          (instantiate (ContextualSelectionViews.capturedSource (schedule.outputDeclarations occurrence) schedule.native.guardFamily)
            (generator schedule.native.guardFamily ⟨.inl none, name⟩))
      simp only [instantiate_generator]
      change _ = instantiate
        (ContextualConditionalRowPacking.inclusion schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence)
        (generator (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) schedule.native.guardFamily)
          (.inr ⟨.inl none, name⟩))
      erw [instantiate_generator]
      rfl

theorem output_body_decodes (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (row : Row (schedule.outputDeclarations occurrence) after.declarations Γ sort) :
    instantiate schedule.producerDecoder (instantiate (schedule.outputEnvironment occurrence)
        (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value)) =
      ContextualStoredRows.asTemplate schedule.producerLocals schedule.native.guardFamily
        (ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence
          (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent)).value := by
  rw [ContextualConditionalRowPacking.template]
  change _ = instantiate _ (ContextualStoredRows.asTemplate _ _ (row.value.map _ schedule.native.bindingCurrent))
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    output_decoding_square]

theorem output_conditions_decode (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (row : Row (schedule.outputDeclarations occurrence) after.declarations Γ sort) :
    ContextualResidual.mapProblem schedule.producerDecoder
        (ContextualResidual.mapProblem (schedule.outputEnvironment occurrence) row.obligations) =
      (ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence
        (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent)).obligations := by
  change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _) =
    ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ _)
  rw [ContextualConditionalNaturality.map_problem_compose, ContextualConditionalNaturality.map_problem_compose,
    output_decoding_square]

def outputBody (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (Term (signature S schedule.native.guardFamily) Γ sort) :=
  (schedule.outputRow occurrence).map fun row => instantiate (schedule.outputEnvironment occurrence)
    (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value)

/-- These equations are output metadata, not a summand of guardProblem. -/
def outputConditions (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (ContextualResidual.Problem schedule.native.guardFamily) :=
  (schedule.outputRow occurrence).map fun row => ContextualResidual.mapProblem (schedule.outputEnvironment occurrence) row.obligations

/-- The native recipe is fixed before execution. Dedicated output-hole
declarations become private; current, cut and opened input declarations
remain captures. The saved row constructor is retained. -/
def producerRecipe (schedule : Schedule S O Γ sort before after) (isSchema : Bool)
    (conditions : ContextualResidual.Problem schedule.native.guardFamily) :
    ContextualConditionalPublication.Recipe schedule.producerLocals
      (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
        schedule.native.bindingLocals schedule.native.guardFamily) where
  role
    | .inr ⟨.inl (some occurrence), name⟩ => .inl ⟨occurrence, name⟩
    | identity => .inr identity
  preserves := by
    intro identity
    cases identity with
    | inl identity => rfl
    | inr identity =>
        rcases identity with ⟨block, name⟩
        cases block with
        | inl output => cases output <;> rfl
        | inr cut => rfl
  conditions := ContextualResidual.mapProblem
    (ContextualSelectionViews.capturedTarget
      (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      schedule.native.guardFamily) conditions
  isSchema := isSchema

/-- Per-port publication data, computed from saved births rather than the
final source row table or a native solver return. -/
noncomputable def producerRecipes (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Option (ContextualConditionalPublication.Recipe schedule.producerLocals
      (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
        schedule.native.bindingLocals schedule.native.guardFamily)) :=
  if physical ∈ schedule.native.bindingSelection.made then
    match physical with
    | none => none
    | some name => (schedule.outputRow (OccurrenceAllocationRenaming.erase name)).map fun row =>
        schedule.producerRecipe (match row.value with | .schema _ => true | .shared _ => false)
          (ContextualResidual.mapProblem (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase name))
            row.obligations)
  else none

theorem producerRecipes_none_of_not_made (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O))
    (missing : physical ∉ schedule.native.bindingSelection.made) :
    schedule.producerRecipes physical = none := by
  simp only [producerRecipes, if_neg missing]

def producerCode (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort :=
  match physical with
  | none => schedule.native.bindingPattern none
  | some name =>
      ((schedule.outputBody (OccurrenceAllocationRenaming.erase name)).map
        (instantiate (ContextualSelectionViews.capturedSource schedule.native.bindingLocals schedule.native.guardFamily))).getD
          (schedule.native.bindingPattern physical)

theorem produced_body_has_authored_origin (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (value : Term (signature S schedule.native.guardFamily) Γ sort) (selected : schedule.outputBody occurrence = some value) :
    ∃ row, schedule.outputRow occurrence = some row ∧
      value = instantiate (schedule.outputEnvironment occurrence)
        (ContextualStoredRows.asTemplate (schedule.outputDeclarations occurrence) after.declarations row.value) := by
  obtain ⟨row, source, same⟩ := Option.map_eq_some_iff.mp selected
  exact ⟨row, source, same.symm⟩

theorem stored_output_instances (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (candidate : Assignment schedule.native.guardFamily next) (pattern : Term (signature S next) Γ sort) :
    (∃ row, schedule.storedOutputRow occurrence = some row ∧
      Matches schedule.producerLocals schedule.native.guardFamily candidate pattern row) ↔
      ∃ birth, schedule.outputBirth occurrence = some birth ∧
        birth.origin.Instances (Assignment.compose candidate schedule.native.bindingCurrent) pattern := by
  rw [← schedule.output_row_instances occurrence (Assignment.compose candidate schedule.native.bindingCurrent) pattern]
  constructor
  · rintro ⟨stored, selected, matched⟩
    obtain ⟨row, source, same⟩ := Option.map_eq_some_iff.mp selected
    subst stored
    refine ⟨row, source, ?_⟩
    have unpacked := (ContextualConditionalRowPacking.matches_iff schedule.outputVariables schedule.outputDeclarations
      schedule.native.guardFamily occurrence _ candidate pattern).mp matched
    exact (matches_map_iff (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent candidate pattern row).mp unpacked
  · rintro ⟨row, source, matched⟩
    refine ⟨ContextualConditionalRowPacking.pack schedule.outputVariables schedule.outputDeclarations schedule.native.guardFamily occurrence
      (row.map (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent), ?_, ?_⟩
    · exact Option.map_eq_some_iff.mpr ⟨row, source, rfl⟩
    · apply (ContextualConditionalRowPacking.matches_iff schedule.outputVariables schedule.outputDeclarations
        schedule.native.guardFamily occurrence _ candidate pattern).mpr
      exact (matches_map_iff (schedule.outputDeclarations occurrence) after.declarations schedule.native.bindingCurrent candidate pattern row).mpr matched

def producerReusable (_schedule : Schedule S O Γ sort before after)
    (_physical : Option (OccurrenceAllocationRenaming.Name O)) : Bool := false

/-- The captured-template producer of the compiled mixed body. -/
def producer (schedule : Schedule S O Γ sort before after) : schedule.native.Producer :=
  ⟨schedule.producerCode, schedule.producerReusable⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
