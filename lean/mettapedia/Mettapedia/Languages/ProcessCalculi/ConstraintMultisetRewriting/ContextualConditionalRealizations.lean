import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality

/-!
# Conditional row realizations in a fixed future family

A realization supplies private images in the same family as the caller.
It is the joint-model witness needed when several source ports share query
bindings. Ordinary matching may first extend that family. The distinction
keeps unrelated future extensions from being silently conjoined.

Unused private arities are supplied explicitly. No inhabitant at an
arbitrary interface is assumed. These witnesses are logical assignments,
not an additional source-language operation or runtime allocation policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Local Added Shared Next Later : Type}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {later : Later → MetaArity S}

def valuation (images : Assignment locals next) (candidate : Assignment captures next) :
    Assignment (ContextualSelectionViews.source locals captures) next
  | .inl name => images name
  | .inr name => candidate name

theorem instance_valuation (images : Assignment locals later) (embedding : Assignment next later)
    (candidate : Assignment captures next) :
    instanceAssignment locals images embedding candidate =
      valuation locals captures images (Assignment.compose embedding candidate) := rfl

theorem valuation_captures (images : Assignment locals next) (candidate : Assignment captures next) :
    Assignment.compose (valuation locals captures images candidate)
      (ContextualSelectionViews.capturedSource locals captures) = candidate := by
  funext name
  exact instantiate_generator _ _

theorem valuation_private (images : Assignment locals next) (candidate : Assignment captures next) :
    Assignment.compose (valuation locals captures images candidate)
      (ContextualStoredRows.privateSource locals captures) = images := by
  funext name
  exact instantiate_generator _ _

theorem valuation_future (images : Assignment locals next) (candidate : Assignment captures next)
    (change : Assignment next later) :
    valuation locals captures (Assignment.compose change images) (Assignment.compose change candidate) =
      Assignment.compose change (valuation locals captures images candidate) := by
  funext name
  cases name <;> rfl

theorem valuation_capture_map (images : Assignment locals later) (candidate : Assignment next later)
    (change : Assignment captures next) :
    Assignment.compose (valuation locals next images candidate) (ContextualStoredRows.liftCaptures locals change) =
      valuation locals captures images (Assignment.compose candidate change) := by
  funext name
  cases name with
  | inl name => exact instantiate_generator _ _
  | inr name =>
      change instantiate (valuation locals next images candidate)
        (instantiate (ContextualSelectionViews.capturedSource locals next) (change name)) = _
      rw [← Assignment.instantiate_compose, valuation_captures]
      rfl

def Realizes (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) : Prop :=
  ∃ images : Assignment locals next,
    ContextualResidual.Models (valuation locals captures images candidate) row.obligations ∧
      instantiate (valuation locals captures images candidate)
        (ContextualStoredRows.asTemplate locals captures row.value) = pattern

theorem matches_iff {Γ : Ctx S} {sort : S.Srt} (candidate : Assignment captures next)
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) :
    Matches locals captures candidate pattern row ↔
      ∃ extension : Extension next, Realizes locals captures
        (Assignment.compose extension.assignment candidate) (instantiate extension.assignment pattern) row := by
  constructor <;> rintro ⟨extension, images, model, same⟩ <;> exact ⟨extension, images, model, same⟩

theorem Realizes.future {Γ : Ctx S} {sort : S.Srt} {candidate : Assignment captures next}
    {pattern : Term (signature S next) Γ sort} {row : Row locals captures Γ sort}
    (realized : Realizes locals captures candidate pattern row) (change : Assignment next later) :
    Realizes locals captures (Assignment.compose change candidate) (instantiate change pattern) row := by
  obtain ⟨images, model, same⟩ := realized
  refine ⟨Assignment.compose change images, ?_, ?_⟩
  · rw [valuation_future]
    exact ContextualResidual.models_compose model change
  · rw [valuation_future, Assignment.instantiate_compose, same]

theorem realizes_map_iff {Γ : Ctx S} {sort : S.Srt} (change : Assignment captures next)
    (candidate : Assignment next later) (pattern : Term (signature S later) Γ sort)
    (row : Row locals captures Γ sort) :
    Realizes locals next candidate pattern (row.map locals captures change) ↔
      Realizes locals captures (Assignment.compose candidate change) pattern row := by
  constructor <;> rintro ⟨images, model, same⟩ <;> refine ⟨images, ?_, ?_⟩
  · exact valuation_capture_map locals captures images candidate change ▸
      (ContextualResidual.models_mapProblem _ _ _).mp model
  · change instantiate (valuation locals next images candidate)
      (ContextualStoredRows.asTemplate locals next (row.value.map locals change)) = pattern at same
    rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose,
      valuation_capture_map] at same
    exact same
  · apply (ContextualResidual.models_mapProblem _ _ _).mpr
    rw [valuation_capture_map]
    exact model
  · change instantiate (valuation locals next images candidate)
      (ContextualStoredRows.asTemplate locals next (row.value.map locals change)) = pattern
    rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, valuation_capture_map]
    exact same

theorem realizes_shared_iff {Γ : Ctx S} {sort : S.Srt} (candidate : Assignment captures next)
    (filler : Assignment locals next) (value : Term (signature S captures) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    Realizes locals captures candidate pattern (ofStored locals captures (.shared value)) ↔
      instantiate candidate value = pattern := by
  constructor
  · rintro ⟨images, _, same⟩
    change instantiate (valuation locals captures images candidate)
      (instantiate (ContextualSelectionViews.capturedSource locals captures) value) = pattern at same
    rwa [← Assignment.instantiate_compose, valuation_captures] at same
  · intro same
    refine ⟨filler, (by intro equation member; cases member), ?_⟩
    change instantiate (valuation locals captures filler candidate)
      (instantiate (ContextualSelectionViews.capturedSource locals captures) value) = pattern
    rw [← Assignment.instantiate_compose, valuation_captures, same]

variable (added : Added → MetaArity S)

theorem valuation_includePrivate
    (images : Assignment (ContextualPublication.privateFamily locals added) next) (candidate : Assignment captures next) :
    Assignment.compose (valuation (ContextualPublication.privateFamily locals added) captures images candidate)
      (ContextualPublication.includePrivate locals added) =
      valuation locals captures (fun name => images (.inl name)) candidate := by
  funext name
  cases name <;> exact instantiate_generator _ _

theorem realizes_extendPrivate_iff {Γ : Ctx S} {sort : S.Srt}
    (candidate : Assignment captures next) (filler : Assignment added next)
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) :
    Realizes (ContextualPublication.privateFamily locals added) captures candidate pattern
      (ContextualConditionalPublication.extendPrivate locals added captures row) ↔
      Realizes locals captures candidate pattern row := by
  constructor
  · rintro ⟨images, model, same⟩
    refine ⟨fun name => images (.inl name), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp model
      rwa [valuation_includePrivate] at original
    · rw [ContextualConditionalPublication.extended_template, ← Assignment.instantiate_compose,
        valuation_includePrivate] at same
      exact same
  · rintro ⟨images, model, same⟩
    let combined : Assignment (ContextualPublication.privateFamily locals added) next
      | .inl name => images name
      | .inr name => filler name
    refine ⟨combined, ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [valuation_includePrivate]
      exact model
    · rw [ContextualConditionalPublication.extended_template, ← Assignment.instantiate_compose,
        valuation_includePrivate]
      exact same

def AnswerRealizes {V : Type} {declaration : V → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (answer : ContextualConditionalAnswers.Answer declaration Γ sort) (next : Next → MetaArity S)
    (pattern : Term (signature S next) Γ sort) : Prop :=
  ∃ images : Assignment declaration next,
    ContextualResidual.Models images answer.obligations ∧ instantiate images answer.value = pattern

theorem valuation_newPrivate
    (images : Assignment (ContextualPublication.privateFamily locals added) next) (candidate : Assignment captures next) :
    Assignment.compose (valuation (ContextualPublication.privateFamily locals added) captures images candidate)
      (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
        (ContextualPublication.newPrivate locals added)) = (fun name => images (.inr name)) := by
  rw [Assignment.compose_associative, valuation_private]
  funext name
  exact instantiate_generator _ _

private theorem ordinary_value {Γ : Ctx S} {sort : S.Srt}
    (images : Assignment (ContextualPublication.privateFamily locals added) next) (candidate : Assignment captures next)
    (answer : ContextualConditionalAnswers.Answer added Γ sort) :
    instantiate (valuation (ContextualPublication.privateFamily locals added) captures images candidate)
      (ContextualStoredRows.asTemplate _ _ (ContextualConditionalPublication.ordinary locals added captures answer).value) =
      instantiate (fun name => images (.inr name)) answer.value := by
  change instantiate (valuation _ _ images candidate)
    (instantiate (ContextualStoredRows.privateSource _ _)
      (instantiate (ContextualPublication.newPrivate locals added) answer.value)) = _
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    ← Assignment.compose_associative, valuation_newPrivate]
  rfl

theorem realizes_ordinary_iff {Γ : Ctx S} {sort : S.Srt}
    (candidate : Assignment captures next) (filler : Assignment locals next)
    (answer : ContextualConditionalAnswers.Answer added Γ sort) (pattern : Term (signature S next) Γ sort) :
    Realizes (ContextualPublication.privateFamily locals added) captures candidate pattern
      (ContextualConditionalPublication.ordinary locals added captures answer) ↔ AnswerRealizes answer next pattern := by
  constructor
  · rintro ⟨images, model, same⟩
    refine ⟨fun name => images (.inr name), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp model
      rwa [valuation_newPrivate] at original
    · exact (ordinary_value locals captures added images candidate answer).symm.trans same
  · rintro ⟨images, model, same⟩
    let combined : Assignment (ContextualPublication.privateFamily locals added) next
      | .inl name => filler name
      | .inr name => images name
    refine ⟨combined, ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [valuation_newPrivate]
      exact model
    · exact (ordinary_value locals captures added combined candidate answer).trans same

theorem answer_ofUpdate_iff {V : Type} {declaration : V → MetaArity S}
    {problem : ContextualResidual.Problem declaration} (update : ContextualFrameUpdate.Update problem)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    AnswerRealizes (ContextualConditionalAnswers.ofUpdate update value) next pattern ↔
      AnswerRealizes ⟨problem, value⟩ next pattern := by
  constructor
  · rintro ⟨images, model, same⟩
    exact ⟨Assignment.compose images update.answer, update.valid.sound next images model,
      (Assignment.instantiate_compose images update.answer value).trans same⟩
  · rintro ⟨images, model, same⟩
    obtain ⟨residual, residualModel, agrees⟩ := update.factors next images model
    exact ⟨residual, residualModel,
      (ContextualFrameUnifier.factor_terms images update.answer residual agrees value).symm.trans same⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations
