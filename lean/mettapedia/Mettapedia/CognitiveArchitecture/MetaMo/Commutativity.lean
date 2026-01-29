/-
# MetaMo Commutativity Theorem

The central theorem of MetaMo: when the underlying quantale elements commute,
the appraisal and decision functors commute as well.

## Mathematical Statement

For a Q-module Θ over a commutative quantale Q, and elements q_sens, q_dec ∈ Q:

  q_sens * q_dec = q_dec * q_sens  →  App_{q_sens} ∘ Dec_{q_dec} = Dec_{q_dec} ∘ App_{q_sens}

Since Q is commutative, the premise is always satisfied, giving us:

  App_{q_sens} ∘ Dec_{q_dec} = Dec_{q_dec} ∘ App_{q_sens}

## Interpretation

This theorem guarantees that in MetaMo:
- The order of appraisal and decision doesn't matter
- Environmental evaluation and goal-based selection can be interleaved freely
- The system exhibits compositional modularity

## References

- Goertzel & Lian, "Weakness and Its Quantale" (MetaMo Appendix)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Appraisal
import Mettapedia.CognitiveArchitecture.MetaMo.Decision

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

/-! ## The Main Commutativity Theorem -/

/-- **Core MetaMo Theorem**: Appraisal and decision commute when their parameters commute.

For a Q-module over a commutative quantale Q, and any q_sens, q_dec ∈ Q:
if q_sens * q_dec = q_dec * q_sens, then the appraisal and decision functors commute.

This follows from the associativity of module action and commutativity of Q. -/
theorem appraisal_decision_commute_of_comm (q_sens q_dec : Q)
    (h_comm : q_sens * q_dec = q_dec * q_sens) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  -- q_sens • (q_dec • θ) = q_dec • (q_sens • θ)
  -- Use the explicit commutativity hypothesis
  rw [← mul_smul, ← mul_smul, h_comm]

/-- **Core MetaMo Theorem (Strong Form)**: In a commutative quantale,
appraisal and decision ALWAYS commute.

Since Q is commutative, q_sens * q_dec = q_dec * q_sens is automatic. -/
theorem appraisal_decision_commute (q_sens q_dec : Q) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  appraisal_decision_commute_of_comm q_sens q_dec (mul_comm q_sens q_dec) θ

/-- Commutativity as function composition -/
theorem appraisal_decision_commute_comp (q_sens q_dec : Q) :
    appraisalFunctor (Θ := Θ) q_sens ∘ decisionFunctor q_dec =
    decisionFunctor q_dec ∘ appraisalFunctor q_sens := by
  ext θ
  exact appraisal_decision_commute q_sens q_dec θ

/-- Commutativity of the Q-module endomorphisms -/
theorem appraisalEndo_decisionEndo_commute (q_sens q_dec : Q) :
    (appraisalEndo (Θ := Θ) q_sens).comp (decisionEndo q_dec) =
    (decisionEndo q_dec).comp (appraisalEndo q_sens) := by
  ext θ
  simp only [QModuleEndo.comp_apply, appraisalEndo_apply, decisionEndo_apply]
  exact appraisal_decision_commute q_sens q_dec θ

/-! ## Composition Relationships -/

/-- The composition of appraisal and decision is another scalar multiplication -/
theorem appraisal_comp_decision (q_sens q_dec : Q) :
    appraisalFunctor (Θ := Θ) q_sens ∘ decisionFunctor q_dec =
    (fun θ => QModule.smul (q_sens * q_dec) θ) := by
  ext θ
  simp only [Function.comp_apply, appraisalFunctor_apply, decisionFunctor_apply]
  exact (mul_smul q_sens q_dec θ).symm

/-- The composition equals scalar multiplication by the product -/
theorem appraisal_decision_product (q_sens q_dec : Q) (θ : Θ) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) = QModule.smul (Q := Q) (q_sens * q_dec) θ := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  exact (mul_smul q_sens q_dec θ).symm

/-! ## Associativity of Motivational Dynamics -/

/-- Triple composition: three successive operations can be reordered arbitrarily -/
theorem triple_dynamics_assoc (q₁ q₂ q₃ : Q) (θ : Θ) :
    (q₁ • (q₂ • (q₃ • θ))) = ((q₁ * q₂ * q₃) • θ) := by
  rw [mul_smul, mul_smul]

/-- Any permutation of three operations gives the same result -/
theorem triple_dynamics_perm (q₁ q₂ q₃ : Q) (θ : Θ) :
    q₁ • (q₂ • (q₃ • θ)) = q₂ • (q₃ • (q₁ • θ)) := by
  rw [triple_dynamics_assoc, triple_dynamics_assoc]
  congr 1
  -- q₁ * q₂ * q₃ = q₂ * q₃ * q₁ in a commutative monoid
  simp only [mul_comm, mul_left_comm]

/-! ## Application: Motivational Dynamics Iteration

When appraisal and decision are applied repeatedly, the order doesn't matter.
-/

/-- Two iterations of appraisal-decision cycles commute with each other -/
theorem double_cycle_commute (q_s₁ q_d₁ q_s₂ q_d₂ : Q) (θ : Θ) :
    appraisalFunctor q_s₁ (decisionFunctor q_d₁
      (appraisalFunctor q_s₂ (decisionFunctor q_d₂ θ))) =
    appraisalFunctor q_s₂ (decisionFunctor q_d₂
      (appraisalFunctor q_s₁ (decisionFunctor q_d₁ θ))) := by
  simp only [appraisalFunctor_apply, decisionFunctor_apply]
  -- Both sides equal (q_s₁ * q_d₁ * q_s₂ * q_d₂) • θ by associativity
  rw [← mul_smul, ← mul_smul, ← mul_smul]
  rw [← mul_smul, ← mul_smul, ← mul_smul]
  congr 1
  -- In a commutative monoid, any permutation is equal
  -- q_s₁ * (q_d₁ * (q_s₂ * q_d₂)) = q_s₂ * (q_d₂ * (q_s₁ * q_d₁))
  simp only [mul_comm, mul_left_comm]

end Mettapedia.CognitiveArchitecture.MetaMo
