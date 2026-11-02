import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate

/-!
# Actual completed updates form consistent helper-active frames

The active family contains disjoint copies of the original declarations and
the complete declaration family returned by the solver. Its endomorphic
answer is the existing fresh-frame construction applied to that actual
answer. Helper identities are retained and fixed. No ambient name supply or
inhabited collection of terms at every sort is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate

variable {S : Signature} {V W Next : Type} {source : V → MetaArity S} {returned : W → MetaArity S}

def noDeclarations : Empty → MetaArity S := fun impossible => nomatch impossible

abbrev old (source : V → MetaArity S) := ContextualFreshFrame.old source (noDeclarations (S := S))
abbrev target (returned : W → MetaArity S) := ContextualFreshFrame.target returned (noDeclarations (S := S))
abbrev active (source : V → MetaArity S) (returned : W → MetaArity S) :=
  ContextualFreshFrame.active source returned (noDeclarations (S := S))

def sourceIntoOld (source : V → MetaArity S) : Assignment source (old source) :=
  fun identity => generator (old source) (.inl identity)

def returnedIntoTarget (returned : W → MetaArity S) : Assignment returned (target returned) :=
  fun identity => generator (target returned) (.inl identity)

def frameAnswer {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment (old source) (target update.declaration)
  | .inl identity => instantiate (returnedIntoTarget update.declaration) (update.answer identity)
  | .inr impossible => nomatch impossible

def includeSource {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment source (active source update.declaration) :=
  Assignment.compose (ContextualFreshFrame.includeOld source update.declaration noDeclarations) (sourceIntoOld source)

def includeReturned {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment update.declaration (active source update.declaration) :=
  Assignment.compose (ContextualFreshFrame.includeTarget source update.declaration noDeclarations)
    (returnedIntoTarget update.declaration)

def answer {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment (active source update.declaration) (active source update.declaration) :=
  ContextualFreshFrame.answer source update.declaration noDeclarations (frameAnswer update)

theorem preserves_others {problem : ContextualResidual.Problem source} (update : Update problem) :
    ∀ identity : Empty, frameAnswer update (.inr identity) = generator (target update.declaration) (.inr identity) := by
  intro impossible
  exact nomatch impossible

theorem frameAnswer_on_source {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment.compose (frameAnswer update) (sourceIntoOld source) =
      Assignment.compose (returnedIntoTarget update.declaration) update.answer := by
  funext identity
  rw [Assignment.compose, sourceIntoOld, instantiate_generator]
  rfl

theorem answer_on_source {problem : ContextualResidual.Problem source} (update : Update problem) :
    Assignment.compose (answer update) (includeSource update) =
      Assignment.compose (includeReturned update) update.answer := by
  unfold answer includeSource includeReturned
  rw [Assignment.compose_associative,
    ContextualFreshFrame.answer_includeOld source update.declaration noDeclarations (frameAnswer update) (preserves_others update),
    ← Assignment.compose_associative, frameAnswer_on_source, Assignment.compose_associative]

theorem answer_on_source_term {problem : ContextualResidual.Problem source} (update : Update problem)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    instantiate (answer update) (instantiate (includeSource update) term) =
      instantiate (includeReturned update) (instantiate update.answer term) := by
  rw [← Assignment.instantiate_compose, answer_on_source, Assignment.instantiate_compose]

theorem helper_declaration {problem : ContextualResidual.Problem source} (update : Update problem)
    (identity : update.Variables) : active source update.declaration (.inr (.inl identity)) = update.declaration identity := rfl

theorem helper_is_fixed {problem : ContextualResidual.Problem source} (update : Update problem)
    (identity : update.Variables) :
    answer update (.inr (.inl identity)) = generator (active source update.declaration) (.inr (.inl identity)) := rfl

theorem old_and_returned_are_disjoint {problem : ContextualResidual.Problem source} (update : Update problem)
    (original : V) (helper : update.Variables) :
    (Sum.inl original : V ⊕ (update.Variables ⊕ Empty)) ≠ .inr (.inl helper) := by
  intro same
  cases same

theorem completed_is_principal {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : Update (ContextualResidual.observeProblem problem)) (empty : update.remaining = []) :
    ContextualFrameUnifier.Principal problem update.answer := by
  constructor
  · exact (ContextualResidual.models_observeProblem update.answer problem).mp (update.completed empty)
  · intro Variables declaration candidate solved
    obtain ⟨residual, _, components⟩ := update.valid.complete declaration candidate
      ((ContextualResidual.models_observeProblem candidate problem).mpr solved)
    exact ⟨residual, components⟩

theorem frameAnswer_is_principal {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : Update (ContextualResidual.observeProblem problem)) (empty : update.remaining = []) :
    ContextualFrameUnifier.Principal (ContextualFrameUnifier.mapProblem (sourceIntoOld source) problem) (frameAnswer update) := by
  have original := completed_is_principal problem update empty
  constructor
  · apply (ContextualFrameUnifier.models_mapProblem (sourceIntoOld source) (frameAnswer update) problem).mpr
    rw [frameAnswer_on_source]
    exact ContextualFrameUnifier.models_compose original.sound (returnedIntoTarget update.declaration)
  · intro Variables declaration candidate solved
    have oldSolved := (ContextualFrameUnifier.models_mapProblem (sourceIntoOld source) candidate problem).mp solved
    obtain ⟨residual, components⟩ := original.factors declaration (Assignment.compose candidate (sourceIntoOld source)) oldSolved
    let through : Assignment (target update.declaration) declaration := fun identity => match identity with
      | .inl name => residual name
      | .inr impossible => nomatch impossible
    have throughReturned : Assignment.compose through (returnedIntoTarget update.declaration) = residual := by
      funext identity
      rw [Assignment.compose, returnedIntoTarget, instantiate_generator]
    refine ⟨through, ?_⟩
    intro identity
    cases identity with
    | inl name =>
        change candidate (.inl name) = instantiate through (instantiate (returnedIntoTarget update.declaration) (update.answer name))
        rw [← Assignment.instantiate_compose, throughReturned]
        simpa only [Assignment.compose, sourceIntoOld, instantiate_generator] using components name
    | inr impossible => exact nomatch impossible

theorem map_compose {X : Type} {next : Next → MetaArity S} {last : X → MetaArity S}
    (first : Assignment source next) (second : Assignment next last) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.mapProblem second (ContextualFrameUnifier.mapProblem first problem) =
      ContextualFrameUnifier.mapProblem (Assignment.compose second first) problem := by
  simp only [ContextualFrameUnifier.mapProblem, List.map_map]
  congr 1
  funext equation
  exact congrArg₂ Prod.mk (instantiate_comp first second equation.1) (instantiate_comp first second equation.2)

theorem principal_on {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : Update (ContextualResidual.observeProblem problem)) (empty : update.remaining = [])
    (observed : List (Term (signature S source) Γ sort)) :
    (ContextualFamilies.action (active source update.declaration) Γ sort).PrincipalOn
      (ContextualFrameUnifier.mapProblem (includeSource update) problem) (answer update)
      (observed.map (instantiate (includeSource update))) := by
  have original := ContextualFreshFrame.principal_on source update.declaration noDeclarations
    (ContextualFrameUnifier.mapProblem (sourceIntoOld source) problem) (frameAnswer update)
    (frameAnswer_is_principal problem update empty) (preserves_others update)
    (observed.map (instantiate (sourceIntoOld source)))
  have observations : (observed.map (instantiate (sourceIntoOld source))).map
      (instantiate (ContextualFreshFrame.includeOld source update.declaration noDeclarations)) =
        observed.map (instantiate (includeSource update)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro term _
    exact (Assignment.instantiate_compose _ _ term).symm
  rw [map_compose, observations] at original
  exact original

theorem consistent {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : Update (ContextualResidual.observeProblem problem)) (empty : update.remaining = []) :
    (ContextualFamilies.action (active source update.declaration) Γ sort).Consistent
      (ContextualFrameUnifier.mapProblem (includeSource update) problem) :=
  ⟨answer update, (principal_on problem update empty []).sound⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
