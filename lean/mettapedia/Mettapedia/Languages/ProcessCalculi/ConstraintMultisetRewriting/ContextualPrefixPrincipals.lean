import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame

/-!
# Unused declarations preserve prefix-model existence and principality

New declaration bodies remain unconstrained generators in the answer.
Every candidate supplies its own bodies for those declarations when it
factors. No whole execution, globally inhabited term family or off-image
inverse is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Extra V W X : Type}
  (unused : Extra → MetaArity S) {source : V → MetaArity S} {target : W → MetaArity S}
  {later : X → MetaArity S}

theorem exists_prefix_model_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem : EquationStore (Term (signature S source) Γ sort)) :
    (∃ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment (extended unused source) future),
      ContextualFrameUnifier.Models candidate
        (ContextualFrameUnifier.mapProblem (inclusion unused source) prefixProblem)) ↔
    ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      ContextualFrameUnifier.Models candidate prefixProblem := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, Assignment.compose candidate (inclusion unused source),
      (ContextualFrameUnifier.models_mapProblem _ _ _).mp model⟩
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Extra ⊕ Future, extended unused future, ContextualStoredRows.liftCaptures unused candidate,
      (lifted_prefix_models_iff unused candidate prefixProblem).mpr model⟩

def factorWithUnused (candidate : Assignment (extended unused source) later)
    (residual : Assignment target later) : Assignment (extended unused target) later
  | .inl name => candidate (.inl name)
  | .inr name => residual name

theorem factor_restricts (candidate : Assignment (extended unused source) later)
    (residual : Assignment target later) :
    Assignment.compose (factorWithUnused unused candidate residual) (inclusion unused target) = residual := by
  funext name
  exact instantiate_generator (factorWithUnused unused candidate residual) (Sum.inr name)

theorem principal_with_unused {Γ : Ctx S} {sort : S.Srt}
    {prefixProblem : EquationStore (Term (signature S source) Γ sort)} {answer : Assignment source target}
    (principal : ContextualFrameUnifier.Principal prefixProblem answer) :
    ContextualFrameUnifier.Principal
      (ContextualFrameUnifier.mapProblem (inclusion unused source) prefixProblem)
      (ContextualStoredRows.liftCaptures unused answer) := by
  refine ⟨(lifted_prefix_models_iff unused answer prefixProblem).mpr principal.sound, ?_⟩
  intro Future future candidate model
  let restricted := Assignment.compose candidate (inclusion unused source)
  have prefixModel : ContextualFrameUnifier.Models restricted prefixProblem :=
    (ContextualFrameUnifier.models_mapProblem _ _ _).mp model
  obtain ⟨residual, components⟩ := principal.factors future restricted prefixModel
  refine ⟨factorWithUnused unused candidate residual, ?_⟩
  intro name
  cases name with
  | inl name =>
      exact (instantiate_generator (factorWithUnused unused candidate residual) (Sum.inl name)).symm
  | inr name =>
      have oldComponent : candidate (.inr name) = instantiate residual (answer name) :=
        (instantiate_generator candidate (Sum.inr name)).symm.trans (components name)
      change candidate (.inr name) = instantiate (factorWithUnused unused candidate residual)
        (instantiate (inclusion unused target) (answer name))
      rw [← Assignment.instantiate_compose, factor_restricts]
      exact oldComponent

/-- Extend a completed saved update by genuinely unused declarations. Its
computed old assignment is retained; the new declarations remain free.
The certificate still concerns the transported original prefix, not an
empty input store. Later equations must be passed to the worklist. -/
def completedUpdateWithUnused [DecidableEq Extra] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (empty : update.remaining = []) :
    ContextualFrameUpdate.Update
      (ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem (inclusion unused source) problem)) where
  Variables := Extra ⊕ update.Variables
  equality := by letI := update.equality; infer_instance
  declaration := extended unused update.declaration
  answer := ContextualStoredRows.liftCaptures unused update.answer
  remaining := []
  valid := by
    have principal := principal_with_unused unused
      (ContextualComputedFreshFrame.completed_is_principal problem update empty)
    simpa only [List.append_nil, ContextualResidual.mapProblem, List.map_nil] using
      ContextualResidual.of_principal_prefix principal []

theorem completedUpdateWithUnused_preserves_old_term [DecidableEq Extra]
    {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem problem))
    (empty : update.remaining = []) {Δ : Ctx S} {result : S.Srt}
    (value : Term (signature S source) Δ result) :
    instantiate (completedUpdateWithUnused unused problem update empty).answer
        (instantiate (inclusion unused source) value) =
      instantiate (inclusion unused update.declaration) (instantiate update.answer value) :=
  ContextualStoredRows.liftCaptures_on_shared_value unused update.answer value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModels
