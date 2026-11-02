import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairRoster

/-!
# Flexible-pair progress on the actual residual roster

Factoring the two selected holes through their common parameter interface
introduces one helper and no previously inactive unselected declaration.
Every model factors through the retained queue with a strict decrease of its
active-image potential, even when the common image remains open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairActive

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFlexPair
open ContextualActiveSupport

variable {S : Signature} {Other Next : Type} [DecidableEq Other] {next : Next → MetaArity S}
  {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}

def targetRoster (before : Finset (Bool ⊕ Other)) : Finset (Unit ⊕ Other) :=
  ({()} : Finset Unit).disjSum before.toRight

omit [DecidableEq Other] in
theorem answer_is_bounded (pullback : ScopePullback left right) (result : S.Srt)
    (others : Other → MetaArity S) (before : Finset (Bool ⊕ Other)) :
    ∀ identity ∈ before, Bounded (fun name => name ∈ targetRoster before)
      (answer pullback result others identity) := by
  intro identity present name named
  cases identity with
  | inl marker =>
      cases marker <;> simp only [answer, support_rename, support_generator, List.mem_singleton] at named
      all_goals subst name; exact Finset.inl_mem_disjSum.mpr (Finset.mem_singleton_self _)
  | inr identity =>
      rw [answer, support_generator, List.mem_singleton] at named
      subst name
      exact Finset.inr_mem_disjSum.mpr (Finset.mem_toRight.mpr present)

theorem active_is_bounded (pullback : ScopePullback left right) (result : S.Srt)
    (others : Other → MetaArity S) (problem : Problem (sourceDeclarations L R result others)) :
    active (mapProblem (answer pullback result others) problem) ⊆ targetRoster (active problem) :=
  map_active_subset _ problem (active problem) _ (fun _ member => member)
    (answer_is_bounded pullback result others (active problem))

omit [DecidableEq Other] in
theorem roster_potential (common : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (before : Finset (Bool ⊕ Other)) (candidate : Assignment (targetDeclarations common result others) next) :
    potential candidate (targetRoster before) =
      ContextualFlexPairProgress.targetPotential common result others candidate before.toRight := by
  unfold targetRoster potential
  rw [Finset.sum_disjSum, Finset.sum_singleton]
  rfl

theorem model_progress (pullback : ScopePullback left right) (result : S.Srt)
    (others : Other → MetaArity S) (problem : Problem (sourceDeclarations L R result others))
    (selected :
      (observe (rename (S := signature S (sourceDeclarations L R result others)) left
        (generator (sourceDeclarations L R result others) (.inl false))),
       observe (rename (S := signature S (sourceDeclarations L R result others)) right
        (generator (sourceDeclarations L R result others) (.inl true)))) ∈ problem)
    (candidate : Assignment (sourceDeclarations L R result others) next) (solved : Models candidate problem) :
    ∃ remaining : Assignment (targetDeclarations pullback.context result others) next,
      Models remaining (mapProblem (answer pullback result others) problem) ∧
      (∀ identity, candidate identity = instantiate remaining (answer pullback result others identity)) ∧
      potential remaining (active (mapProblem (answer pullback result others) problem)) <
        potential candidate (active problem) := by
  obtain ⟨remaining, models, components, decrease⟩ := ContextualFlexPairProgress.model_progress pullback result
    others problem selected candidate solved (active problem).toRight
  have first : .inl false ∈ active problem := by
    apply (mem_active _ _).mpr
    refine ⟨_, selected, .inl ?_⟩
    change .inl false ∈ support (rename (S := signature S (sourceDeclarations L R result others)) left
      (generator (sourceDeclarations L R result others) (.inl false)))
    rw [support_rename, support_generator]
    exact List.mem_singleton_self _
  have second : .inl true ∈ active problem := by
    apply (mem_active _ _).mpr
    refine ⟨_, selected, .inr ?_⟩
    change .inl true ∈ support (rename (S := signature S (sourceDeclarations L R result others)) right
      (generator (sourceDeclarations L R result others) (.inl true)))
    rw [support_rename, support_generator]
    exact List.mem_singleton_self _
  have start := (ContextualPairRoster.pair_potential candidate (active problem) first second).symm
  have finish := potential_monotone remaining (active_is_bounded pullback result others problem)
  rw [roster_potential] at finish
  change ContextualFlexPairProgress.sourcePotential L R result others candidate (active problem).toRight =
    potential candidate (active problem) at start
  exact ⟨remaining, models, components, lt_of_le_of_lt finish (start ▸ decrease)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairActive
