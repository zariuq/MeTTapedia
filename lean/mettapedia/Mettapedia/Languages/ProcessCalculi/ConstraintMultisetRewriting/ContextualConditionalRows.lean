import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality

/-!
# Stored values with latent equations in the same private frame

The value retains the existing schema/shared representation. Latent equations
use that same row-local declaration family and its declared captures. A use
opens the value and equations with one assignment. Ordinary stored rows are
the empty-equation fragment. Equations may live under different object
binders; their observation contexts and sorts remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {Local Shared Next Later Future : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {later : Later → MetaArity S} {future : Future → MetaArity S}

structure Row (context : Ctx S) (sort : S.Srt) where
  value : ContextualStoredRows.Row locals captures context sort
  obligations : ContextualResidual.Problem (ContextualSelectionViews.source locals captures)

def ofStored {Γ : Ctx S} {sort : S.Srt} (value : ContextualStoredRows.Row locals captures Γ sort) : Row locals captures Γ sort :=
  ⟨value, []⟩

def Row.map (assignment : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (row : Row locals captures Γ sort) : Row locals next Γ sort :=
  ⟨row.value.map locals assignment, ContextualResidual.mapProblem (ContextualStoredRows.liftCaptures locals assignment) row.obligations⟩

def Row.viewAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :=
  ContextualStoredRows.viewAt locals captures scope row.value

def Row.obligationsAt (scope : Nat) {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :=
  ContextualResidual.mapProblem (ContextualFreshening.assignment locals captures scope) row.obligations

def Matches (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) : Prop :=
  ∃ extension : Extension next, ∃ images : Assignment locals extension.declarations,
    ContextualResidual.Models (instanceAssignment locals images extension.assignment candidate) row.obligations ∧
      instantiate (instanceAssignment locals images extension.assignment candidate)
        (ContextualStoredRows.asTemplate locals captures row.value) = instantiate extension.assignment pattern

theorem ofStored_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (value : ContextualStoredRows.Row locals captures Γ sort) :
    Matches locals captures candidate pattern (ofStored locals captures value) ↔
      ContextualGuardMatching.Matches locals candidate pattern value := by
  cases value with
  | schema body =>
      constructor
      · rintro ⟨extension, images, _, same⟩
        exact ⟨extension, images, same⟩
      · rintro ⟨extension, images, same⟩
        exact ⟨extension, images, (by intro equation member; cases member), same⟩
  | shared value =>
      constructor
      · rintro ⟨extension, images, _, same⟩
        have fixed := instance_on_shared_value locals images extension.assignment candidate value
        exact (extension.instantiate_injective (fixed.symm.trans same)).symm
      · intro same
        let extension := Extension.withLocals locals next
        refine ⟨extension, (fun name => generator extension.declarations (.inl name)),
          (by intro equation member; cases member), ?_⟩
        change instantiate (instanceAssignment locals _ extension.assignment candidate)
          (instantiate (ContextualSelectionViews.capturedSource locals captures) value) = _
        exact (instance_on_shared_value locals _ extension.assignment candidate value).trans
          (congrArg (instantiate extension.assignment) same).symm

theorem matches_map_iff (change : Assignment captures later) (candidate : Assignment later next)
    {Γ : Ctx S} {sort : S.Srt} (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) :
    Matches locals later candidate pattern (row.map locals captures change) ↔
      Matches locals captures (Assignment.compose candidate change) pattern row := by
  have fixed : ∀ (extension : Extension next) (images : Assignment locals extension.declarations),
      ContextualResidual.Models (instanceAssignment locals images extension.assignment candidate)
        (ContextualResidual.mapProblem (ContextualStoredRows.liftCaptures locals change) row.obligations) ↔
      ContextualResidual.Models (instanceAssignment locals images extension.assignment (Assignment.compose candidate change)) row.obligations := by
    intro extension images
    rw [ContextualResidual.models_mapProblem, instance_after_capture_transport]
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, (fixed extension images).mp obligations, ?_⟩
    change instantiate (instanceAssignment locals images extension.assignment candidate)
      (ContextualStoredRows.asTemplate locals later (row.value.map locals change)) = _ at same
    rw [ContextualStoredRows.asTemplate_map] at same
    exact (instantiated_transported_body locals images extension.assignment candidate change
      (ContextualStoredRows.asTemplate locals captures row.value)).symm.trans same
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, (fixed extension images).mpr obligations, ?_⟩
    change instantiate (instanceAssignment locals images extension.assignment candidate)
      (ContextualStoredRows.asTemplate locals later (row.value.map locals change)) = _
    rw [ContextualStoredRows.asTemplate_map]
    exact (instantiated_transported_body locals images extension.assignment candidate change
      (ContextualStoredRows.asTemplate locals captures row.value)).trans same

theorem ofStored_map (change : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    (ofStored locals captures row).map locals captures change = ofStored locals next (row.map locals change) := rfl

theorem view_transport (change : Assignment captures next) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    instantiate (ContextualViewNaturality.activeLift locals change) (row.viewAt locals captures scope) =
      (row.map locals captures change).viewAt locals next scope :=
  ContextualViewNaturality.viewAt_transport locals change scope row.value

theorem obligations_transport (change : Assignment captures next) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    ContextualResidual.mapProblem (ContextualViewNaturality.activeLift locals change) (row.obligationsAt locals captures scope) =
      (row.map locals captures change).obligationsAt locals next scope := by
  change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ row.obligations) =
    ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ row.obligations)
  simp only [ContextualResidual.mapProblem, List.map_map]
  congr 1
  funext equation
  dsimp only [Function.comp_def]
  simp only [instantiateObservation_comp]
  exact congrArg (fun assignment => (instantiateObservation assignment equation.1, instantiateObservation assignment equation.2))
    (ContextualViewNaturality.freshening_square locals change scope)

theorem opening_assignment (scope : Nat)
    (candidate : Assignment (ContextualSelectionViews.target locals captures) next) :
    Assignment.compose candidate (ContextualFreshening.assignment locals captures scope) =
      instanceAssignment locals (fun name => candidate (.inl (Mettapedia.Logic.LP.ScopedVar.at scope name)))
        (generator next) (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) := by
  funext name
  cases name with
  | inl name => exact instantiate_generator _ _
  | inr name =>
      change instantiate candidate (generator _ (.inr name)) =
        instantiate (generator next) (instantiate candidate (generator _ (.inr name)))
      exact (instantiate_identity _).symm

/-- Actual opened value equations and latent conditions give one semantic
row match under the same caller interpretation. -/
theorem matches_of_open (scope : Nat)
    (candidate : Assignment (ContextualSelectionViews.target locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort)
    (pattern : Term (signature S next) Γ sort)
    (conditions : ContextualResidual.Models candidate (row.obligationsAt locals captures scope))
    (same : instantiate candidate (row.viewAt locals captures scope) = pattern) :
    Matches locals captures (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) pattern row := by
  refine ⟨Extension.identity next, (fun name => candidate (.inl (Mettapedia.Logic.LP.ScopedVar.at scope name))), ?_, ?_⟩
  · have source := (ContextualResidual.models_mapProblem _ _ _).mp conditions
    rw [opening_assignment] at source
    exact source
  · have source := same
    rw [Row.viewAt, ContextualStoredRows.viewAt_eq_freshening] at source
    change instantiate candidate (instantiate (ContextualFreshening.assignment locals captures scope)
      (ContextualStoredRows.asTemplate locals captures row.value)) = pattern at source
    rw [← Assignment.instantiate_compose, opening_assignment] at source
    exact source.trans (instantiate_identity pattern).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
