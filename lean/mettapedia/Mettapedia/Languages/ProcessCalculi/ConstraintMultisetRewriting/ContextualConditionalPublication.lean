import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationInventory

/-!
# Conditional answers become independently reusable stored rows

The actual returned value and its residual equations use the same private
names in the stored row. Opening a row can therefore neither forget a
condition nor constrain another use's private variables. Extending the
private bank retains all previous row matching, including latent equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Local Added Shared Next Future : Type}
    (locals : Local → MetaArity S) (added : Added → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {future : Future → MetaArity S}

theorem private_square (images : Assignment locals future) (embedding : Assignment next future)
    (candidate : Assignment captures next) :
    Assignment.compose (instanceAssignment locals images embedding candidate)
      (ContextualStoredRows.privateSource locals captures) = images := by
  funext name
  exact instantiate_generator _ _

def store {Γ : Ctx S} {sort : S.Srt} (answer : ContextualResidualAnswers.Answer locals Γ sort) : Row locals captures Γ sort :=
  ⟨ContextualStoredRows.store locals captures answer.value,
    ContextualResidual.mapProblem (ContextualStoredRows.privateSource locals captures) answer.obligations⟩

theorem store_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (answer : ContextualResidualAnswers.Answer locals Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches locals captures candidate pattern (store locals captures answer) ↔ answer.Instances next pattern := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      rw [private_square locals captures images extension.assignment candidate] at original
      exact original
    · exact (ContextualPublication.instantiate_store locals images extension.assignment candidate answer.value).symm.trans same
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [private_square]
      exact obligations
    · exact (ContextualPublication.instantiate_store locals images extension.assignment candidate answer.value).trans same

def extendPrivate {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    Row (ContextualPublication.privateFamily locals added) captures Γ sort :=
  ⟨ContextualPublication.extendPrivate locals added row.value,
    ContextualResidual.mapProblem (ContextualPublication.includePrivate locals added) row.obligations⟩

theorem extended_template {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    ContextualStoredRows.asTemplate (ContextualPublication.privateFamily locals added) captures
      (extendPrivate locals added captures row).value =
    instantiate (ContextualPublication.includePrivate locals added)
      (ContextualStoredRows.asTemplate locals captures row.value) := by
  change ContextualStoredRows.asTemplate (ContextualPublication.privateFamily locals added) captures
      (ContextualPublication.extendPrivate locals added row.value) = _
  cases row.value with
  | schema body => rfl
  | live value =>
      change instantiate (ContextualSelectionViews.capturedSource (ContextualPublication.privateFamily locals added) captures) value =
        instantiate (ContextualPublication.includePrivate locals added)
          (instantiate (ContextualSelectionViews.capturedSource locals captures) value)
      rw [← Assignment.instantiate_compose]
      apply congrArg (fun assignment => instantiate assignment value)
      funext name
      change generator (ContextualSelectionViews.source (ContextualPublication.privateFamily locals added) captures)
        (.inr name) = instantiate (ContextualPublication.includePrivate locals added)
          (generator (ContextualSelectionViews.source locals captures) (.inr name))
      exact (instantiate_generator (ContextualPublication.includePrivate locals added) (Sum.inr name)).symm

theorem extendPrivate_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (row : Row locals captures Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals added) captures candidate pattern
      (extendPrivate locals added captures row) ↔ Matches locals captures candidate pattern row := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, (fun name => images (.inl name)), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      rw [ContextualPublication.instance_includePrivate] at original
      exact original
    · rw [extended_template] at same
      rw [← Assignment.instantiate_compose, ContextualPublication.instance_includePrivate] at same
      exact same
  · rintro ⟨extension, images, obligations, same⟩
    let extra := Extension.withLocals added extension.declarations
    let images' : Assignment (ContextualPublication.privateFamily locals added) extra.declarations
      | .inl name => instantiate extra.assignment (images name)
      | .inr name => generator extra.declarations (.inl name)
    have square : Assignment.compose extra.assignment (instanceAssignment locals images extension.assignment candidate) =
        instanceAssignment locals (fun name => images' (.inl name)) (extension.trans extra).assignment candidate := by
      erw [Extension.trans_assignment]
      funext name
      cases name with
      | inl name => rfl
      | inr name => exact instantiate_comp extension.assignment extra.assignment (candidate name)
    refine ⟨extension.trans extra, images', ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [ContextualPublication.instance_includePrivate, ← square]
      exact ContextualResidual.models_compose obligations extra.assignment
    · rw [extended_template, ← Assignment.instantiate_compose]
      erw [ContextualPublication.instance_includePrivate, ← square]
      erw [Extension.trans_assignment]
      exact (Assignment.instantiate_compose extra.assignment _ _).trans
        ((congrArg (instantiate extra.assignment) same).trans
          (Assignment.instantiate_compose extra.assignment extension.assignment pattern).symm)

def ordinary {Γ : Ctx S} {sort : S.Srt} (answer : ContextualResidualAnswers.Answer added Γ sort) :
    Row (ContextualPublication.privateFamily locals added) captures Γ sort :=
  ⟨ContextualPublication.ordinary locals added answer.value,
    ContextualResidual.mapProblem
      (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
        (ContextualPublication.newPrivate locals added)) answer.obligations⟩

theorem ordinary_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (answer : ContextualResidualAnswers.Answer added Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals added) captures candidate pattern
      (ordinary locals added captures answer) ↔ answer.Instances next pattern := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, (fun name => images (.inr name)), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      have square : Assignment.compose
          (instanceAssignment (ContextualPublication.privateFamily locals added) images extension.assignment candidate)
          (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
            (ContextualPublication.newPrivate locals added)) = (fun name => images (.inr name)) := by
        rw [Assignment.compose_associative, private_square]
        funext name
        exact instantiate_generator images (.inr name)
      exact square ▸ original
    · change instantiate (instanceAssignment (ContextualPublication.privateFamily locals added) images extension.assignment candidate)
        (instantiate (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (instantiate (ContextualPublication.newPrivate locals added) answer.value)) = _ at same
      rw [ContextualPublication.instantiate_store, ContextualPublication.instantiate_newPrivate] at same
      exact same
  · rintro ⟨extension, images, obligations, same⟩
    let extra := Extension.withLocals locals extension.declarations
    let images' : Assignment (ContextualPublication.privateFamily locals added) extra.declarations
      | .inl name => generator extra.declarations (.inl name)
      | .inr name => instantiate extra.assignment (images name)
    have square : Assignment.compose
        (instanceAssignment (ContextualPublication.privateFamily locals added) images' (extension.trans extra).assignment candidate)
        (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (ContextualPublication.newPrivate locals added)) = Assignment.compose extra.assignment images := by
      erw [Assignment.compose_associative, private_square]
      funext name
      exact instantiate_generator images' (.inr name)
    refine ⟨extension.trans extra, images', ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [square]
      exact ContextualResidual.models_compose obligations extra.assignment
    · change instantiate (instanceAssignment (ContextualPublication.privateFamily locals added) images'
        (extension.trans extra).assignment candidate)
        (instantiate (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (instantiate (ContextualPublication.newPrivate locals added) answer.value)) = _
      erw [ContextualPublication.instantiate_store, ContextualPublication.instantiate_newPrivate, Extension.trans_assignment]
      exact (Assignment.instantiate_compose extra.assignment images answer.value).trans
        ((congrArg (instantiate extra.assignment) same).trans
          (Assignment.instantiate_compose extra.assignment extension.assignment pattern).symm)

theorem update_matches_source {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source}
    (update : ContextualFrameUpdate.Update problem) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals update.declaration) captures candidate pattern
      (ordinary locals update.declaration captures (ContextualResidualAnswers.ofUpdate update value)) ↔
    ContextualPublication.SourceInstances problem value next pattern :=
  (ordinary_matches_iff locals update.declaration captures candidate _ pattern).trans
    (ContextualResidualAnswers.ofUpdate_exact update value next pattern)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
