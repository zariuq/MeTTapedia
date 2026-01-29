/-
# MetaMo Appraisal Functor

The appraisal functor represents how an AGI system evaluates environmental
stimuli and modulates its motivational state accordingly.

## Mathematical Definition

Given a Q-module (Θ, •) over a commutative quantale Q, the appraisal functor
is defined by a sensitivity parameter q_sens ∈ Q:

  App_{q_sens}(θ) = q_sens • θ

This captures the idea that environmental signals modulate the intensity
of motivational states proportionally to the system's sensitivity.

## Key Properties

1. **Endomorphism**: Appraisal is a Q-module endomorphism
2. **Monotonicity**: Higher sensitivity means more intense appraisal
3. **Composition**: App_{q₁} ∘ App_{q₂} = App_{q₁ * q₂}

## References

- Goertzel & Lian, "Weakness and Its Quantale" (MetaMo Appendix)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Basic

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-! ## Appraisal Functor Definition -/

/-- The appraisal functor with sensitivity parameter q_sens.

In MetaMo, appraisal represents how the system evaluates environmental
stimuli. The sensitivity parameter controls the intensity of the response:
- High q_sens: Strong response to stimuli
- Low q_sens: Muted response
- q_sens = 1: No modulation (identity) -/
def appraisalFunctor (q_sens : Q) : Θ → Θ := fun θ => q_sens • θ

/-- Alternative name emphasizing the sensitivity parameter -/
abbrev App (q_sens : Q) : Θ → Θ := appraisalFunctor q_sens

/-! ### Basic Properties -/

@[simp]
theorem appraisalFunctor_apply (q_sens : Q) (θ : Θ) :
    appraisalFunctor q_sens θ = q_sens • θ := rfl

/-- Appraisal with unit sensitivity is the identity -/
@[simp]
theorem appraisalFunctor_one : appraisalFunctor (1 : Q) = (id : Θ → Θ) := by
  ext θ
  simp only [appraisalFunctor_apply, one_smul, id_eq]

/-- Appraisal preserves the Q-module structure -/
theorem appraisalFunctor_map_smul (q_sens q : Q) (θ : Θ) :
    appraisalFunctor q_sens (q • θ) = q • appraisalFunctor q_sens θ := by
  simp only [appraisalFunctor_apply]
  exact smul_smul_comm q_sens q θ

/-- Appraisal is a Q-module endomorphism -/
def appraisalEndo (q_sens : Q) : QModuleEndo Q Θ :=
  smulEndo q_sens

@[simp]
theorem appraisalEndo_apply (q_sens : Q) (θ : Θ) :
    appraisalEndo q_sens θ = q_sens • θ := rfl

/-! ### Composition Laws -/

/-- Composition of appraisals corresponds to multiplication of sensitivities -/
theorem appraisalFunctor_comp (q₁ q₂ : Q) :
    appraisalFunctor (Θ := Θ) q₁ ∘ appraisalFunctor q₂ = appraisalFunctor (q₁ * q₂) := by
  ext θ
  simp only [Function.comp_apply, appraisalFunctor_apply]
  exact (mul_smul q₁ q₂ θ).symm

/-- Appraisal functors commute (since Q is commutative) -/
theorem appraisalFunctor_comm (q₁ q₂ : Q) :
    appraisalFunctor (Θ := Θ) q₁ ∘ appraisalFunctor q₂ =
    appraisalFunctor q₂ ∘ appraisalFunctor q₁ := by
  rw [appraisalFunctor_comp, appraisalFunctor_comp, mul_comm]

/-- Appraisal endomorphisms compose correctly -/
theorem appraisalEndo_comp (q₁ q₂ : Q) :
    (appraisalEndo (Θ := Θ) q₁).comp (appraisalEndo q₂) =
    appraisalEndo (q₁ * q₂) :=
  smulEndo_comp q₁ q₂

/-! ### Monotonicity Properties -/

/-- Appraisal is monotone in the motivational state -/
theorem appraisalFunctor_mono_state (q_sens : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    appraisalFunctor q_sens θ₁ ≤ appraisalFunctor q_sens θ₂ := by
  simp only [appraisalFunctor_apply]
  exact smul_mono_right q_sens h

/-- Appraisal distributes over joins -/
theorem appraisalFunctor_sup (q_sens : Q) (θ₁ θ₂ : Θ) :
    appraisalFunctor q_sens (θ₁ ⊔ θ₂) =
    appraisalFunctor q_sens θ₁ ⊔ appraisalFunctor q_sens θ₂ := by
  simp only [appraisalFunctor_apply]
  exact smul_sup q_sens θ₁ θ₂

/-! ### Sensitivity Ordering

When we have an ordering on Q, higher sensitivity means more intense responses.
-/

section SensitivityOrdering

variable [LE Q]

/-- If the quantale has a notion of "stronger" elements affecting states more,
    this would give monotonicity in sensitivity. This requires additional
    structure: q₁ ≤ q₂ → q₁ • θ ≤ q₂ • θ for θ ≥ ⊥.

    This is NOT automatic from the QModule axioms and would require either:
    1. Assuming the module is "positive" (θ ≥ ⊥ implies q • θ ≥ ⊥)
    2. Adding smul_mono_left as an axiom

    For now, we state this as a separate condition.
-/
class PositiveQModule (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] [LE Q] where
  smul_mono_left : ∀ {q₁ q₂ : Q}, q₁ ≤ q₂ → ∀ θ : Θ, q₁ • θ ≤ q₂ • θ

variable [PositiveQModule Q Θ]

/-- For positive modules, appraisal is monotone in sensitivity -/
theorem appraisalFunctor_mono_sens {q₁ q₂ : Q} (h : q₁ ≤ q₂) (θ : Θ) :
    appraisalFunctor q₁ θ ≤ appraisalFunctor q₂ θ := by
  simp only [appraisalFunctor_apply]
  exact PositiveQModule.smul_mono_left h θ

end SensitivityOrdering

end Mettapedia.CognitiveArchitecture.MetaMo
