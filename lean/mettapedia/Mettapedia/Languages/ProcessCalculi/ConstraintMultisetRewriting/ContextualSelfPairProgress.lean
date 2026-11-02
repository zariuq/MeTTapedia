import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.BindingScopeEqualizerSizes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Same-hole pruning preserves model size and decreases parameter size

The common image of a same-hole equation has exactly the original tree
size: positional renaming does not add nodes. When the two maps differ,
their computed equalizer removes a parameter. This supplies the secondary
component of a lexicographic solver measure without falsely claiming that
tree size decreases. The active interface is finite, not the declaration
carrier or the signature's sorts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSelfPair
open scoped BigOperators

variable {S : Signature} {Other Variables : Type} {next : Variables → MetaArity S}
  {Δ Γ : Ctx S} {left right : Ren S Δ Γ}

def imagePotential (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (candidate : Assignment (declarations parameters result others) next) (active : Finset Other) : Nat :=
  termSize (candidate (.inl ())) + ∑ identity ∈ active, termSize (candidate (.inr identity))

def parameterPotential (parameters : Ctx S) (others : Other → MetaArity S) (active : Finset Other) : Nat :=
  parameters.length + ∑ identity ∈ active, (others identity).1.length

theorem image_size_preserved_of_factors (equalizer : ScopeEqualizer left right) (result : S.Srt)
    (others : Other → MetaArity S)
    (candidate : Assignment (declarations Δ result others) next)
    (remaining : Assignment (declarations equalizer.context result others) next)
    (components : ∀ identity, candidate identity = instantiate remaining (answer equalizer result others identity))
    (active : Finset Other) :
    imagePotential equalizer.context result others remaining active = imagePotential Δ result others candidate active := by
  have selected := congrArg termSize (components (.inl ()))
  simp only [answer, ContextualFamily.instantiate_rename, instantiate_generator, termSize_rename] at selected
  have rest : (∑ identity ∈ active, termSize (candidate (.inr identity))) =
      ∑ identity ∈ active, termSize (remaining (.inr identity)) := by
    apply Finset.sum_congr rfl
    intro identity _
    rw [components (.inr identity), answer, instantiate_generator]
  unfold imagePotential
  omega

theorem parameter_size_decreases (different : left ≠ right) (others : Other → MetaArity S)
    (active : Finset Other) :
    parameterPotential (ScopeEqualizer.Finite.build left right).context others active <
      parameterPotential Δ others active := by
  have strict := ScopeEqualizer.Finite.context_length_lt left right different
  change (ScopeEqualizer.Finite.context left right).length + _ < Δ.length + _
  omega

theorem model_progress (different : left ≠ right) (result : S.Srt) (others : Other → MetaArity S)
    (problem : ContextualResidual.Problem (declarations Δ result others))
    (selected :
      (observe (rename (S := signature S (declarations Δ result others)) left
        (generator (declarations Δ result others) (.inl ()))),
       observe (rename (S := signature S (declarations Δ result others)) right
        (generator (declarations Δ result others) (.inl ())))) ∈ problem)
    (candidate : Assignment (declarations Δ result others) next)
    (solved : ContextualResidual.Models candidate problem) (active : Finset Other) :
    ∃ remaining : Assignment (declarations (ScopeEqualizer.Finite.build left right).context result others) next,
      ContextualResidual.Models remaining
        (ContextualResidual.mapProblem (answer (ScopeEqualizer.Finite.build left right) result others) problem) ∧
      (∀ identity, candidate identity =
        instantiate remaining (answer (ScopeEqualizer.Finite.build left right) result others identity)) ∧
      imagePotential (ScopeEqualizer.Finite.build left right).context result others remaining active =
        imagePotential Δ result others candidate active ∧
      parameterPotential (ScopeEqualizer.Finite.build left right).context others active <
        parameterPotential Δ others active := by
  obtain ⟨remaining, components⟩ := factors (ScopeEqualizer.Finite.build left right) result others next candidate
    (observe_injective (solved _ selected))
  exact ⟨remaining,
    (ContextualResidual.models_of_components candidate _ remaining components problem).mp solved,
    components, image_size_preserved_of_factors _ result others candidate remaining components active,
    parameter_size_decreases different others active⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress
