/-
# OpenPsi as MetaMo Instance (Corrected)

This module bridges the corrected OpenPsi to the MetaMo framework by:
1. Using ℝ≥0∞ as the commutative quantale (already proven in QuantaleWeakness)
2. Defining a 10-dimensional motivational state space
3. Proving OpenPsi motivational states form a QModule over ℝ≥0∞

## Mathematical Structure

The key insight is that ℝ≥0∞ (extended nonnegative reals) with multiplication forms
a commutative quantale, and we can use this as the "intensity/confidence" space for
motivational dynamics.

## Corrected State Vector (10 dimensions)

Previous incorrect implementation: 9 dimensions (3 PAD + 6 wrong demands)
Correct implementation: 10 dimensions:
- 4 modulators (Activation, Resolution, SecuringThreshold, SelectionThreshold)
- 6 demand satisfactions (Energy, Water, Integrity, Affiliation, Certainty, Competence)

## References

- Goertzel & Lian, "Weakness and Its Quantale"
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (AGI 2011)
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.CognitiveArchitecture.OpenPsi.Basic

namespace Mettapedia.CognitiveArchitecture.OpenPsi

open Mettapedia.CognitiveArchitecture.MetaMo
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

/-! ## OpenPsi State Vector (Corrected)

For the QModule instance, we use a 10-dimensional vector of ℝ≥0∞ values.
This allows us to use the product lattice structure.

The state vector has components for:
- 4 modulator dimensions
- 6 demand satisfaction levels

Total: 10 components
-/

/-- The dimension of the corrected OpenPsi state vector -/
def stateDim : ℕ := 10

/-- Indices for modulator components (0-3) -/
def activationIdx : Fin stateDim := ⟨0, by norm_num [stateDim]⟩
def resolutionIdx : Fin stateDim := ⟨1, by norm_num [stateDim]⟩
def securingThresholdIdx : Fin stateDim := ⟨2, by norm_num [stateDim]⟩
def selectionThresholdIdx : Fin stateDim := ⟨3, by norm_num [stateDim]⟩

/-- Indices for demand satisfaction components (4-9) -/
def energySatIdx : Fin stateDim := ⟨4, by norm_num [stateDim]⟩
def waterSatIdx : Fin stateDim := ⟨5, by norm_num [stateDim]⟩
def integritySatIdx : Fin stateDim := ⟨6, by norm_num [stateDim]⟩
def affiliationSatIdx : Fin stateDim := ⟨7, by norm_num [stateDim]⟩
def certaintySatIdx : Fin stateDim := ⟨8, by norm_num [stateDim]⟩
def competenceSatIdx : Fin stateDim := ⟨9, by norm_num [stateDim]⟩

/-- Convert DemandType to its satisfaction index -/
def DemandType.toSatIdx : DemandType → Fin stateDim
  | .energy => energySatIdx
  | .water => waterSatIdx
  | .integrity => integritySatIdx
  | .affiliation => affiliationSatIdx
  | .certainty => certaintySatIdx
  | .competence => competenceSatIdx

/-- OpenPsi state vector: a function from indices to ℝ≥0∞ values -/
abbrev OpenPsiStateVec := Fin stateDim → ℝ≥0∞

/-! ## CompleteLattice Instance for OpenPsiStateVec

Function types to complete lattices inherit the complete lattice structure
via pointwise operations. This is already in Mathlib's Pi instances.
-/

-- Already available from Mathlib:
-- instance : CompleteLattice OpenPsiStateVec := Pi.completeLattice

/-! ## QModule Instance

We prove that OpenPsiStateVec forms a QModule over ℝ≥0∞.
Scalar multiplication is defined component-wise: (q • θ)(i) = q * θ(i)
-/

/-- Component-wise scalar multiplication for OpenPsi state vectors -/
noncomputable def stateVecSmul (q : ℝ≥0∞) (θ : OpenPsiStateVec) : OpenPsiStateVec :=
  fun i => q * θ i

/-- OpenPsi state vectors form a QModule over ℝ≥0∞ -/
noncomputable instance openPsiQModule : QModule ℝ≥0∞ OpenPsiStateVec where
  smul := stateVecSmul
  smul_one θ := by
    ext i
    simp only [stateVecSmul, one_mul]
  smul_assoc q₁ q₂ θ := by
    ext i
    simp only [stateVecSmul, mul_assoc]
  smul_sup q θ₁ θ₂ := by
    ext i
    simp only [stateVecSmul, Pi.sup_apply]
    -- Need: q * (θ₁ i ⊔ θ₂ i) = q * θ₁ i ⊔ q * θ₂ i
    -- This is exactly the quantale distributivity in ℝ≥0∞
    have hdist : q * sSup {θ₁ i, θ₂ i} = ⨆ y ∈ ({θ₁ i, θ₂ i} : Set ℝ≥0∞), q * y :=
      ENNReal.mul_sSup
    have hsup_pair : sSup ({θ₁ i, θ₂ i} : Set ℝ≥0∞) = θ₁ i ⊔ θ₂ i := sSup_pair
    rw [← hsup_pair, hdist]
    exact iSup_pair

/-! ## Key Properties

The MetaMo framework gives us important properties for free once we have
the QModule instance.
-/

/-- Appraisal and decision functors commute on OpenPsi states -/
theorem openPsi_appraisal_decision_commute (q_sens q_dec : ℝ≥0∞) (θ : OpenPsiStateVec) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  appraisal_decision_commute q_sens q_dec θ

/-- OpenPsi dynamics preserve the lattice order -/
theorem openPsi_dynamics_mono (q_sens q_dec : ℝ≥0∞) {θ₁ θ₂ : OpenPsiStateVec} (h : θ₁ ≤ θ₂) :
    motivationalDynamics q_sens q_dec θ₁ ≤ motivationalDynamics q_sens q_dec θ₂ :=
  motivationalDynamics_mono q_sens q_dec h

/-! ## Neutral State

A canonical neutral state with all components at a middle value.
-/

/-- The neutral OpenPsi state (all components at 1/2) -/
noncomputable def neutralStateVec : OpenPsiStateVec := fun _ => 1 / 2

/-! ## Interpretation

The QModule structure on OpenPsi states gives us:

1. **Scalar multiplication**: q • θ scales all motivational intensities by q
   - q = 1: No change (identity)
   - q < 1: Dampening (reducing arousal, satisfaction levels)
   - q > 1: Amplification (increasing motivational drive)

2. **Appraisal functor**: App_q(θ) = q • θ
   - Represents environmental sensitivity
   - High q_sens: Agent is very responsive to stimuli
   - Low q_sens: Agent is relatively inert

3. **Decision functor**: Dec_q(θ) = q • θ
   - Represents goal-directed action selection weight
   - High q_dec: Strong goal pursuit
   - Low q_dec: Exploratory/random behavior

4. **Commutativity**: The order of appraisal and decision doesn't matter!
   - This is a key MetaMo theorem, now proven for the corrected OpenPsi

5. **Stability**: Under contractive dynamics (q_sens * q_dec < 1), the system
   converges to a unique equilibrium state.

## Corrected Components (10-dimensional)

Modulators (indices 0-3):
- **Activation** (0): Overall system energy
- **Resolution** (1): Perception detail level
- **SecuringThreshold** (2): Information acceptance threshold
- **SelectionThreshold** (3): Action selection determinism

Demand Satisfactions (indices 4-9):
- **Energy** (4): Physiological energy satisfaction
- **Water** (5): Hydration satisfaction
- **Integrity** (6): System stability satisfaction
- **Affiliation** (7): Social connection satisfaction
- **Certainty** (8): Knowledge confidence satisfaction
- **Competence** (9): Problem-solving ability satisfaction

This matches the actual OpenPsi specification from the OpenCog Wiki and
Dörner's Psi theory, rather than the incorrect PAD-based model.
-/

end Mettapedia.CognitiveArchitecture.OpenPsi
