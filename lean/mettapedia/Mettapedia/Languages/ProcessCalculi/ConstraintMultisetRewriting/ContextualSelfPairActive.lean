import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInterfacePotential

/-!
# Same-hole pruning decreases the actual active interface cost

Pruning two different parameter maps need not reduce model-image size.
It cannot increase that primary potential, and strictly decreases the sum
of active parameter counts. Bounds on the actual residual roster retain
unselected declarations without assuming the ambient family finite.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairActive

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualSelfPair

variable {S : Signature} {Other Next : Type} [DecidableEq Other] {next : Next → MetaArity S}
  {Δ Γ : Ctx S} {left right : Ren S Δ Γ}

def targetRoster (before : Finset (Unit ⊕ Other)) : Finset (Unit ⊕ Other) :=
  ({()} : Finset Unit).disjSum before.toRight

omit [DecidableEq Other] in
theorem answer_is_bounded (equalizer : ScopeEqualizer left right) (result : S.Srt)
    (others : Other → MetaArity S) (before : Finset (Unit ⊕ Other)) :
    ∀ identity ∈ before, Bounded (fun name => name ∈ targetRoster before)
      (answer equalizer result others identity) := by
  intro identity present name named
  cases identity with
  | inl marker =>
      rw [answer, support_rename, support_generator, List.mem_singleton] at named
      subst name
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_singleton_self _)
  | inr identity =>
      rw [answer, support_generator, List.mem_singleton] at named
      subst name
      exact Finset.inr_mem_disjSum.mpr (Finset.mem_toRight.mpr present)

theorem active_is_bounded (equalizer : ScopeEqualizer left right) (result : S.Srt)
    (others : Other → MetaArity S) (problem : Problem (declarations Δ result others)) :
    active (mapProblem (answer equalizer result others) problem) ⊆ targetRoster (active problem) :=
  map_active_subset _ problem (active problem) _ (fun _ member => member)
    (answer_is_bounded equalizer result others (active problem))

omit [DecidableEq Other] in
theorem roster_image_potential (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (before : Finset (Unit ⊕ Other)) (candidate : Assignment (declarations parameters result others) next) :
    potential candidate (targetRoster before) =
      ContextualSelfPairProgress.imagePotential parameters result others candidate before.toRight := by
  unfold potential targetRoster
  rw [Finset.sum_disjSum, Finset.sum_singleton]
  rfl

theorem model_progress (different : left ≠ right) (result : S.Srt) (others : Other → MetaArity S)
    (problem : Problem (declarations Δ result others))
    (selected :
      (observe (rename (S := signature S (declarations Δ result others)) left
        (generator (declarations Δ result others) (.inl ()))),
       observe (rename (S := signature S (declarations Δ result others)) right
        (generator (declarations Δ result others) (.inl ())))) ∈ problem)
    (candidate : Assignment (declarations Δ result others) next) (solved : Models candidate problem) :
    ∃ remaining : Assignment (declarations (ScopeEqualizer.Finite.build left right).context result others) next,
      Models remaining (mapProblem (answer (ScopeEqualizer.Finite.build left right) result others) problem) ∧
      (∀ identity, candidate identity =
        instantiate remaining (answer (ScopeEqualizer.Finite.build left right) result others identity)) ∧
      potential remaining (active (mapProblem (answer (ScopeEqualizer.Finite.build left right) result others) problem)) ≤
        potential candidate (active problem) ∧
      ContextualInterfacePotential.cost (declarations (ScopeEqualizer.Finite.build left right).context result others)
        (active (mapProblem (answer (ScopeEqualizer.Finite.build left right) result others) problem)) <
      ContextualInterfacePotential.cost (declarations Δ result others) (active problem) := by
  let equalizer := ScopeEqualizer.Finite.build left right
  obtain ⟨remaining, models, components, images, parameters⟩ := ContextualSelfPairProgress.model_progress
    different result others problem selected candidate solved (active problem).toRight
  have root : .inl () ∈ active problem := by
    apply (mem_active _ _).mpr
    refine ⟨_, selected, .inl ?_⟩
    change .inl () ∈ support (rename (S := signature S (declarations Δ result others)) left
      (generator (declarations Δ result others) (.inl ())))
    rw [support_rename, support_generator]
    exact List.mem_singleton_self _
  have sourceImages := ContextualSumRoster.unit_potential candidate (active problem) root
  have targetImages := potential_monotone remaining (active_is_bounded equalizer result others problem)
  rw [roster_image_potential, images] at targetImages
  have sourceParameters := ContextualInterfacePotential.selected_unit_cost Δ result others (active problem) root
  have targetParameters := ContextualInterfacePotential.monotone
    (declarations equalizer.context result others) (active_is_bounded equalizer result others problem)
  rw [targetRoster, ContextualInterfacePotential.unit_roster_cost] at targetParameters
  refine ⟨remaining, models, components, ?_, ?_⟩
  · exact targetImages.trans_eq sourceImages.symm
  · change _ ≤ ContextualSelfPairProgress.parameterPotential equalizer.context others (active problem).toRight at targetParameters
    change _ = ContextualSelfPairProgress.parameterPotential Δ others (active problem).toRight at sourceParameters
    exact (lt_of_le_of_lt targetParameters parameters).trans_eq sourceParameters.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairActive
