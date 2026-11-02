import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A flexible pair decreases the finite active model potential

Factoring two contextual images through their common parameter interface
replaces two equally sized trees by one tree. Its positive size makes this
strict progress, even when the common image still has unresolved holes.
Unrelated active declarations are preserved, and their carrier may be
infinite. The selected equation supplies the factorization for the entire
retained problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFlexPair
open scoped BigOperators

variable {S : Signature} {Other Variables : Type} {next : Variables → MetaArity S}
  {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}

def sourcePotential (L R : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations L R result others) next) (active : Finset Other) : Nat :=
  termSize (candidate (.inl false)) + termSize (candidate (.inl true)) +
    ∑ identity ∈ active, termSize (candidate (.inr identity))

def targetPotential (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (targetDeclarations common result others) next) (active : Finset Other) : Nat :=
  termSize (candidate (.inl ())) + ∑ identity ∈ active, termSize (candidate (.inr identity))

theorem decreases_of_factors (pullback : ScopePullback left right) (result : S.Srt)
    (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations L R result others) next)
    (remaining : Assignment (targetDeclarations pullback.context result others) next)
    (components : ∀ identity, candidate identity = instantiate remaining (answer pullback result others identity))
    (active : Finset Other) :
    targetPotential pullback.context result others remaining active <
      sourcePotential L R result others candidate active := by
  have first := congrArg termSize (components (.inl false))
  have second := congrArg termSize (components (.inl true))
  simp only [answer, ContextualFamily.instantiate_rename, instantiate_generator, termSize_rename] at first second
  have rest : (∑ identity ∈ active, termSize (candidate (.inr identity))) =
      ∑ identity ∈ active, termSize (remaining (.inr identity)) := by
    apply Finset.sum_congr rfl
    intro identity _
    rw [components (.inr identity), answer, instantiate_generator]
  have positive := termSize_pos (remaining (.inl ()))
  unfold sourcePotential targetPotential
  omega

theorem model_progress (pullback : ScopePullback left right) (result : S.Srt)
    (others : Other → MetaArity S)
    (problem : ContextualResidual.Problem (sourceDeclarations L R result others))
    (selected :
      (observe (rename (S := signature S (sourceDeclarations L R result others)) left
        (generator (sourceDeclarations L R result others) (.inl false))),
       observe (rename (S := signature S (sourceDeclarations L R result others)) right
        (generator (sourceDeclarations L R result others) (.inl true)))) ∈ problem)
    (candidate : Assignment (sourceDeclarations L R result others) next)
    (solved : ContextualResidual.Models candidate problem) (active : Finset Other) :
    ∃ remaining : Assignment (targetDeclarations pullback.context result others) next,
      ContextualResidual.Models remaining (ContextualResidual.mapProblem (answer pullback result others) problem) ∧
      (∀ identity, candidate identity = instantiate remaining (answer pullback result others identity)) ∧
      targetPotential pullback.context result others remaining active <
        sourcePotential L R result others candidate active := by
  obtain ⟨remaining, components⟩ := factors pullback result others next candidate
    (observe_injective (solved _ selected))
  exact ⟨remaining,
    (ContextualResidual.models_of_components candidate _ remaining components problem).mp solved,
    components, decreases_of_factors pullback result others candidate remaining components active⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress
