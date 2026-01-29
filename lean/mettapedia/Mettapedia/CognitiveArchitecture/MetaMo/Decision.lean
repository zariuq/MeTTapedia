/-
# MetaMo Decision Functor

The decision functor represents how an AGI system selects actions based on
its current motivational state and goal priorities.

## Mathematical Definition

Given a Q-module (Θ, •) over a commutative quantale Q, the decision functor
is defined by a decision weight parameter q_dec ∈ Q:

  Dec_{q_dec}(θ) = q_dec • θ

This captures the idea that action selection modulates motivational states
based on goal priorities and decision thresholds.

## Interpretation

- **q_dec close to 1**: Conservative decisions, preserve current motivation
- **q_dec close to 0**: Aggressive filtering, focus on high-priority goals
- **Intermediate q_dec**: Balanced decision-making

## References

- Goertzel & Lian, "Weakness and Its Quantale" (MetaMo Appendix)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Basic

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-! ## Decision Functor Definition -/

/-- The decision functor with decision weight parameter q_dec.

In MetaMo, the decision functor represents goal-driven action selection.
The decision weight controls how motivational states are filtered:
- High q_dec: Preserve more of the motivational state
- Low q_dec: Aggressive filtering toward high-priority goals
- q_dec = 1: No filtering (identity) -/
def decisionFunctor (q_dec : Q) : Θ → Θ := fun θ => q_dec • θ

/-- Alternative name emphasizing the decision parameter -/
abbrev Dec (q_dec : Q) : Θ → Θ := decisionFunctor q_dec

/-! ### Basic Properties -/

@[simp]
theorem decisionFunctor_apply (q_dec : Q) (θ : Θ) :
    decisionFunctor q_dec θ = q_dec • θ := rfl

/-- Decision with unit weight is the identity -/
@[simp]
theorem decisionFunctor_one : decisionFunctor (1 : Q) = (id : Θ → Θ) := by
  ext θ
  simp only [decisionFunctor_apply, one_smul, id_eq]

/-- Decision preserves the Q-module structure -/
theorem decisionFunctor_map_smul (q_dec q : Q) (θ : Θ) :
    decisionFunctor q_dec (q • θ) = q • decisionFunctor q_dec θ := by
  simp only [decisionFunctor_apply]
  exact smul_smul_comm q_dec q θ

/-- Decision is a Q-module endomorphism -/
def decisionEndo (q_dec : Q) : QModuleEndo Q Θ :=
  smulEndo q_dec

@[simp]
theorem decisionEndo_apply (q_dec : Q) (θ : Θ) :
    decisionEndo q_dec θ = q_dec • θ := rfl

/-! ### Composition Laws -/

/-- Composition of decisions corresponds to multiplication of weights -/
theorem decisionFunctor_comp (q₁ q₂ : Q) :
    decisionFunctor (Θ := Θ) q₁ ∘ decisionFunctor q₂ = decisionFunctor (q₁ * q₂) := by
  ext θ
  simp only [Function.comp_apply, decisionFunctor_apply]
  exact (mul_smul q₁ q₂ θ).symm

/-- Decision functors commute (since Q is commutative) -/
theorem decisionFunctor_comm (q₁ q₂ : Q) :
    decisionFunctor (Θ := Θ) q₁ ∘ decisionFunctor q₂ =
    decisionFunctor q₂ ∘ decisionFunctor q₁ := by
  rw [decisionFunctor_comp, decisionFunctor_comp, mul_comm]

/-- Decision endomorphisms compose correctly -/
theorem decisionEndo_comp (q₁ q₂ : Q) :
    (decisionEndo (Θ := Θ) q₁).comp (decisionEndo q₂) =
    decisionEndo (q₁ * q₂) :=
  smulEndo_comp q₁ q₂

/-! ### Monotonicity Properties -/

/-- Decision is monotone in the motivational state -/
theorem decisionFunctor_mono_state (q_dec : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    decisionFunctor q_dec θ₁ ≤ decisionFunctor q_dec θ₂ := by
  simp only [decisionFunctor_apply]
  exact smul_mono_right q_dec h

/-- Decision distributes over joins -/
theorem decisionFunctor_sup (q_dec : Q) (θ₁ θ₂ : Θ) :
    decisionFunctor q_dec (θ₁ ⊔ θ₂) =
    decisionFunctor q_dec θ₁ ⊔ decisionFunctor q_dec θ₂ := by
  simp only [decisionFunctor_apply]
  exact smul_sup q_dec θ₁ θ₂

/-! ### Relationship with Appraisal

The key insight of MetaMo is that appraisal and decision have the same
algebraic structure - they are both scalar multiplication endomorphisms.
The distinction between them is semantic (environmental sensitivity vs
goal-driven selection), not structural.
-/

end Mettapedia.CognitiveArchitecture.MetaMo
