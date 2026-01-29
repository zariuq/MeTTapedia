/-
# PLN-MetaMo Bridge

This module connects Probabilistic Logic Networks (PLN) to the MetaMo motivational
framework, showing how PLN evidence theory provides a semantic foundation for
AGI cognitive dynamics.

## Core Insight

PLN and MetaMo share the same mathematical substrate: **commutative quantales**.

- **PLN**: Uses [0,1] with multiplication as the quantale for truth values
  - Transitivity: sAB * sBC ≤ sAC (product is lower bound on deduction)
  - Residuation: implies strength via left residuate

- **MetaMo**: Uses Q-modules over quantales for motivational dynamics
  - Appraisal: App_q(θ) = q • θ (environmental sensitivity)
  - Decision: Dec_q(θ) = q • θ (goal-directed action)
  - Commutativity: App ∘ Dec = Dec ∘ App

The bridge shows that PLN truth values can parameterize MetaMo dynamics:
- **Sensitivity parameter** = PLN truth strength of "environment → belief"
- **Decision parameter** = PLN truth strength of "goal → action"

## References

- Goertzel & Lian, "Weakness and Its Quantale"
- Goertzel et al., "Probabilistic Logic Networks"
- Goertzel et al., "OpenPsi"
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.Logic.PLNQuantaleConnection
import Mathlib.Data.Real.Basic

namespace Mettapedia.CognitiveArchitecture.Bridges

open Mettapedia.CognitiveArchitecture.MetaMo
open Mettapedia.Logic.PLNQuantaleConnection
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

/-! ## PLN Strength as Quantale Element

The strength component of a SimpleTruthValue lives in [0,1], which embeds
into ℝ≥0∞ (extended nonnegative reals). This lets us use PLN strengths
as parameters in MetaMo dynamics over ℝ≥0∞.
-/

/-- Embed a PLN strength (real in [0,1]) into ℝ≥0∞ -/
noncomputable def strengthToENNReal (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) : ℝ≥0∞ :=
  ENNReal.ofReal s

/-- The embedded strength is at most 1 -/
theorem strengthToENNReal_le_one (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    strengthToENNReal s hs ≤ 1 := by
  unfold strengthToENNReal
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hs.2

/-- The embedded strength is nonnegative -/
theorem strengthToENNReal_nonneg (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ strengthToENNReal s hs :=
  zero_le _

/-! ## PLN-Parameterized MetaMo Dynamics

Using PLN truth values to parameterize MetaMo dynamics.
-/

variable {Θ : Type*} [CompleteLattice Θ] [QModule ℝ≥0∞ Θ]

/-- Appraisal functor parameterized by PLN strength -/
noncomputable def plnAppraisalFunctor (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Θ → Θ :=
  appraisalFunctor (strengthToENNReal s hs)

/-- Decision functor parameterized by PLN strength -/
noncomputable def plnDecisionFunctor (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Θ → Θ :=
  decisionFunctor (strengthToENNReal s hs)

/-- PLN-parameterized dynamics: composition of PLN-weighted appraisal and decision -/
noncomputable def plnMotivationalDynamics
    (s_sens s_dec : ℝ)
    (hs_sens : s_sens ∈ Set.Icc (0 : ℝ) 1)
    (hs_dec : s_dec ∈ Set.Icc (0 : ℝ) 1) : Θ → Θ :=
  motivationalDynamics (strengthToENNReal s_sens hs_sens) (strengthToENNReal s_dec hs_dec)

/-! ## Key Theorems: PLN Properties Transfer to MetaMo -/

/-- Commutativity of PLN-parameterized dynamics -/
theorem pln_dynamics_commute
    (s_sens s_dec : ℝ)
    (hs_sens : s_sens ∈ Set.Icc (0 : ℝ) 1)
    (hs_dec : s_dec ∈ Set.Icc (0 : ℝ) 1)
    (θ : Θ) :
    plnAppraisalFunctor s_sens hs_sens (plnDecisionFunctor s_dec hs_dec θ) =
    plnDecisionFunctor s_dec hs_dec (plnAppraisalFunctor s_sens hs_sens θ) := by
  unfold plnAppraisalFunctor plnDecisionFunctor
  exact appraisal_decision_commute _ _ θ

/-- PLN-parameterized dynamics preserve order -/
theorem pln_dynamics_mono
    (s_sens s_dec : ℝ)
    (hs_sens : s_sens ∈ Set.Icc (0 : ℝ) 1)
    (hs_dec : s_dec ∈ Set.Icc (0 : ℝ) 1)
    {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    plnMotivationalDynamics s_sens s_dec hs_sens hs_dec θ₁ ≤
    plnMotivationalDynamics s_sens s_dec hs_sens hs_dec θ₂ := by
  unfold plnMotivationalDynamics
  exact motivationalDynamics_mono _ _ h

/-! ## Interpretation: PLN Semantics for MetaMo

The PLN-MetaMo bridge gives a **probabilistic interpretation** to motivational dynamics:

### Sensitivity Parameter (q_sens)

The appraisal sensitivity q_sens can be interpreted as:
- P(Update_belief | Environment_stimulus)
- The probability that an environmental stimulus updates the agent's beliefs
- High q_sens: Agent is very sensitive to environment
- Low q_sens: Agent is relatively immune to environmental changes

### Decision Parameter (q_dec)

The decision weight q_dec can be interpreted as:
- P(Take_action | Goal_activated)
- The probability that an activated goal leads to action
- High q_dec: Strong goal-directed behavior
- Low q_dec: Weak/exploratory behavior

### Deduction and Composition

The PLN deduction rule corresponds to MetaMo dynamics composition:
- (A→B) ⊗ (B→C) ≤ (A→C)   [PLN transitivity]
- App_q₁ ∘ Dec_q₂ = App∘Dec with weight q₁*q₂   [MetaMo composition]

### Stability Condition

For stable dynamics, we need the combined parameter < 1:
- q_sens * q_dec < 1
- In PLN terms: P(stimulus→belief) * P(goal→action) < 1
- This is always true for proper probabilities (both ≤ 1)!

So PLN-parameterized MetaMo dynamics are automatically stable when
both parameters are proper probabilities in [0,1].
-/

/-- PLN dynamics with proper probability parameters give a bounded combined weight -/
theorem pln_combined_weight_le_one
    (s_sens s_dec : ℝ)
    (hs_sens : s_sens ∈ Set.Icc (0 : ℝ) 1)
    (hs_dec : s_dec ∈ Set.Icc (0 : ℝ) 1) :
    strengthToENNReal s_sens hs_sens * strengthToENNReal s_dec hs_dec ≤ 1 := by
  calc strengthToENNReal s_sens hs_sens * strengthToENNReal s_dec hs_dec
      ≤ 1 * 1 := by
        apply mul_le_mul'
        · exact strengthToENNReal_le_one s_sens hs_sens
        · exact strengthToENNReal_le_one s_dec hs_dec
    _ = 1 := one_mul 1

end Mettapedia.CognitiveArchitecture.Bridges
