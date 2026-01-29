/-
# MicroPsi as MetaMo Instance

This module bridges MicroPsi to the MetaMo framework by:
1. Using ℝ≥0∞ as the commutative quantale
2. Defining a 10-dimensional motivational state space
3. Proving MicroPsi motivational states form a QModule over ℝ≥0∞

## State Vector (10 dimensions)

- 3 PAD dimensions (Pleasure, Arousal, Dominance)
- 7 demand satisfaction levels

Note: Same total dimension as OpenPsi (10) but different decomposition:
- OpenPsi: 4 modulators + 6 demands
- MicroPsi: 3 PAD + 7 demands

## References

- Bach, "MicroPsi 2: The Next Generation" (AGI 2012)
- Goertzel & Lian, "Weakness and Its Quantale"
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.CognitiveArchitecture.MicroPsi.Basic

namespace Mettapedia.CognitiveArchitecture.MicroPsi

open Mettapedia.CognitiveArchitecture.MetaMo
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

/-! ## MicroPsi State Vector

For the QModule instance, we use a 10-dimensional vector of ℝ≥0∞ values.

Components:
- 3 PAD emotional dimensions (indices 0-2)
- 7 demand satisfaction levels (indices 3-9)
-/

/-- The dimension of the MicroPsi state vector -/
def stateDim : ℕ := 10

/-- Indices for PAD emotional components (0-2) -/
def pleasureIdx : Fin stateDim := ⟨0, by norm_num [stateDim]⟩
def arousalIdx : Fin stateDim := ⟨1, by norm_num [stateDim]⟩
def dominanceIdx : Fin stateDim := ⟨2, by norm_num [stateDim]⟩

/-- Indices for demand satisfaction components (3-9) -/
def foodSatIdx : Fin stateDim := ⟨3, by norm_num [stateDim]⟩
def waterSatIdx : Fin stateDim := ⟨4, by norm_num [stateDim]⟩
def intactnessSatIdx : Fin stateDim := ⟨5, by norm_num [stateDim]⟩
def affiliationSatIdx : Fin stateDim := ⟨6, by norm_num [stateDim]⟩
def certaintySatIdx : Fin stateDim := ⟨7, by norm_num [stateDim]⟩
def competenceSatIdx : Fin stateDim := ⟨8, by norm_num [stateDim]⟩
def explorationSatIdx : Fin stateDim := ⟨9, by norm_num [stateDim]⟩

/-- Convert DemandType to its satisfaction index -/
def DemandType.toSatIdx : DemandType → Fin stateDim
  | .food => foodSatIdx
  | .water => waterSatIdx
  | .intactness => intactnessSatIdx
  | .affiliation => affiliationSatIdx
  | .certainty => certaintySatIdx
  | .competence => competenceSatIdx
  | .exploration => explorationSatIdx

/-- MicroPsi state vector: a function from indices to ℝ≥0∞ values -/
abbrev MicroPsiStateVec := Fin stateDim → ℝ≥0∞

/-! ## QModule Instance

MicroPsi state vectors form a QModule over ℝ≥0∞.
Scalar multiplication is component-wise: (q • θ)(i) = q * θ(i)
-/

/-- Component-wise scalar multiplication for MicroPsi state vectors -/
noncomputable def stateVecSmul (q : ℝ≥0∞) (θ : MicroPsiStateVec) : MicroPsiStateVec :=
  fun i => q * θ i

/-- MicroPsi state vectors form a QModule over ℝ≥0∞ -/
noncomputable instance microPsiQModule : QModule ℝ≥0∞ MicroPsiStateVec where
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
    have hdist : q * sSup {θ₁ i, θ₂ i} = ⨆ y ∈ ({θ₁ i, θ₂ i} : Set ℝ≥0∞), q * y :=
      ENNReal.mul_sSup
    have hsup_pair : sSup ({θ₁ i, θ₂ i} : Set ℝ≥0∞) = θ₁ i ⊔ θ₂ i := sSup_pair
    rw [← hsup_pair, hdist]
    exact iSup_pair

/-! ## Key Properties

MetaMo properties hold for MicroPsi.
-/

/-- Appraisal and decision functors commute on MicroPsi states -/
theorem microPsi_appraisal_decision_commute (q_sens q_dec : ℝ≥0∞) (θ : MicroPsiStateVec) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  appraisal_decision_commute q_sens q_dec θ

/-- MicroPsi dynamics preserve the lattice order -/
theorem microPsi_dynamics_mono (q_sens q_dec : ℝ≥0∞) {θ₁ θ₂ : MicroPsiStateVec} (h : θ₁ ≤ θ₂) :
    motivationalDynamics q_sens q_dec θ₁ ≤ motivationalDynamics q_sens q_dec θ₂ :=
  motivationalDynamics_mono q_sens q_dec h

/-! ## Neutral State -/

/-- The neutral MicroPsi state (all components at 1/2) -/
noncomputable def neutralStateVec : MicroPsiStateVec := fun _ => 1 / 2

/-! ## Interpretation

The QModule structure on MicroPsi states gives us:

1. **Scalar multiplication**: q • θ scales all values by q
2. **Appraisal functor**: Environmental sensitivity
3. **Decision functor**: Goal-directed action selection weight
4. **Commutativity**: Order of appraisal and decision doesn't matter
5. **Stability**: Contractive dynamics converge

## MicroPsi-Specific Components (10-dimensional)

PAD Emotional State (indices 0-2):
- **Pleasure** (0): Valence/hedonic tone
- **Arousal** (1): Activation/energy level
- **Dominance** (2): Control/submissiveness

Demand Satisfactions (indices 3-9):
- **Food** (3): Energy/sustenance satisfaction
- **Water** (4): Hydration satisfaction
- **Intactness** (5): Health/integrity satisfaction
- **Affiliation** (6): Social connection satisfaction
- **Certainty** (7): Predictability satisfaction
- **Competence** (8): Mastery/skill satisfaction
- **Exploration** (9): Novelty/curiosity satisfaction

This matches Bach's MicroPsi architecture with PAD emotional model.
-/

end Mettapedia.CognitiveArchitecture.MicroPsi
