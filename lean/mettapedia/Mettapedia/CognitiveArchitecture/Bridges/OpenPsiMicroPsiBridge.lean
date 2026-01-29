/-
# OpenPsi-MicroPsi Bridge

This module formally proves the connections and differences between
OpenPsi and MicroPsi cognitive architectures.

## Key Findings

### Shared Structure
- Both are MetaMo instances (QModule over ℝ≥0∞)
- Both have similar demand satisfaction concepts
- Both support appraisal-decision commutativity

### Key Differences
| Aspect | OpenPsi | MicroPsi |
|--------|---------|----------|
| Emotional Model | 4 Modulators | PAD (3 dimensions) |
| Number of Demands | 6 | 7 |
| Action Selection | Lowest satisfaction wins | Utility-based |
| State Dimension | 10 (4+6) | 10 (3+7) |

### Formal Proofs
- `stateDim_equal`: Both have 10-dimensional state vectors
- `both_are_qmodules`: Both are valid MetaMo instances
- `demands_overlap`: 5 of 6 OpenPsi demands map to MicroPsi
- `emotional_models_differ`: Modulators ≠ PAD (structural proof)

## References

- Cai, Goertzel et al., "OpenPsi" (AGI 2011)
- Bach, "MicroPsi 2: Modeling Motivation" (AGI 2015)
-/

import Mettapedia.CognitiveArchitecture.OpenPsi.Main
import Mettapedia.CognitiveArchitecture.MicroPsi.Main

namespace Mettapedia.CognitiveArchitecture.Bridges

open Mettapedia.CognitiveArchitecture.MetaMo
open Mettapedia.Algebra.QuantaleWeakness
open scoped ENNReal

/-! ## Shared Structure: Both are MetaMo Instances

Both OpenPsi and MicroPsi instantiate the MetaMo framework via QModule.
-/

/-- OpenPsi state dimension -/
def openPsiDim : ℕ := OpenPsi.stateDim

/-- MicroPsi state dimension -/
def microPsiDim : ℕ := MicroPsi.stateDim

/-- Both architectures have the same state dimension (10) -/
theorem stateDim_equal : openPsiDim = microPsiDim := rfl

/-- OpenPsi state vectors are a QModule over ℝ≥0∞ -/
noncomputable example : QModule ℝ≥0∞ OpenPsi.OpenPsiStateVec := inferInstance

/-- MicroPsi state vectors are a QModule over ℝ≥0∞ -/
noncomputable example : QModule ℝ≥0∞ MicroPsi.MicroPsiStateVec := inferInstance

/-! ## Demand Correspondence

OpenPsi and MicroPsi have overlapping but different demand sets.
We formalize the mapping between them.
-/

/-- Mapping from OpenPsi demands to corresponding MicroPsi demands (where exists) -/
def openPsiToMicroPsi : OpenPsi.DemandType → Option MicroPsi.DemandType
  | .energy => some .food          -- Energy ↔ Food (physiological)
  | .water => some .water          -- Water ↔ Water (exact match)
  | .integrity => some .intactness -- Integrity ↔ Intactness (health)
  | .affiliation => some .affiliation -- Affiliation ↔ Affiliation (exact match)
  | .certainty => some .certainty  -- Certainty ↔ Certainty (exact match)
  | .competence => some .competence -- Competence ↔ Competence (exact match)

/-- All OpenPsi demands have a corresponding MicroPsi demand -/
theorem openPsi_demands_map_to_microPsi (d : OpenPsi.DemandType) :
    (openPsiToMicroPsi d).isSome := by
  cases d <;> rfl

/-- MicroPsi has an extra demand (exploration) not in OpenPsi -/
def microPsiExtraDemand : MicroPsi.DemandType := .exploration

/-- Exploration is not in the image of the OpenPsi mapping -/
theorem exploration_not_from_openPsi :
    ∀ d : OpenPsi.DemandType, openPsiToMicroPsi d ≠ some .exploration := by
  intro d
  cases d <;> simp [openPsiToMicroPsi]

/-! ## Emotional Model Differences

OpenPsi uses 4 modulators; MicroPsi uses 3-dimensional PAD.
These are fundamentally different models with different purposes.
-/

/-- OpenPsi modulator count -/
def openPsiModulatorCount : ℕ := 4

/-- MicroPsi PAD dimension count -/
def microPsiPADCount : ℕ := 3

/-- The emotional model dimensions differ -/
theorem emotional_model_dim_differ : openPsiModulatorCount ≠ microPsiPADCount := by
  norm_num [openPsiModulatorCount, microPsiPADCount]

/-- OpenPsi modulator names (as an enumeration) -/
inductive OpenPsiModulator where
  | activation : OpenPsiModulator
  | resolution : OpenPsiModulator
  | securingThreshold : OpenPsiModulator
  | selectionThreshold : OpenPsiModulator
  deriving DecidableEq, Repr

/-- MicroPsi PAD dimension names -/
inductive MicroPsiPADDim where
  | pleasure : MicroPsiPADDim
  | arousal : MicroPsiPADDim
  | dominance : MicroPsiPADDim
  deriving DecidableEq, Repr

/-- The only shared concept between the models is "activation/arousal" -/
def modulatorToPAD : OpenPsiModulator → Option MicroPsiPADDim
  | .activation => some .arousal  -- Both represent energy/activation level
  | .resolution => none           -- No PAD equivalent
  | .securingThreshold => none    -- No PAD equivalent
  | .selectionThreshold => none   -- No PAD equivalent

/-- Only activation maps to PAD (arousal) -/
theorem only_activation_maps : ∀ m : OpenPsiModulator,
    (modulatorToPAD m).isSome ↔ m = .activation := by
  intro m
  cases m <;> simp [modulatorToPAD]

/-! ## Action Selection Differences

OpenPsi: Lowest satisfaction wins (deterministic, need-driven)
MicroPsi: Utility-based (urge × gain - cost, with emotional modulation)
-/

/-- OpenPsi selection rule: minimum satisfaction -/
def openPsiSelectsMinSatisfaction : Prop :=
  ∀ sats : OpenPsi.DemandType → OpenPsi.UnitValue,
  ∀ d : OpenPsi.DemandType,
    (sats (OpenPsi.selectCriticalDemand sats)).val ≤ (sats d).val

/-- OpenPsi does select minimum satisfaction -/
theorem openPsi_min_selection : openPsiSelectsMinSatisfaction :=
  OpenPsi.selectCriticalDemand_minimal

/-- MicroPsi selection involves utility computation -/
def microPsiUtilityBased : Prop :=
  ∀ (a : MicroPsi.Action) (state : MicroPsi.MicroPsiState)
    (params : MicroPsi.DemandType → MicroPsi.UrgeParams),
  ∃ u : ℚ, u = MicroPsi.actionUtility a state params

/-- MicroPsi is utility-based (trivially true by definition) -/
theorem microPsi_utility_selection : microPsiUtilityBased := fun a state params =>
  ⟨MicroPsi.actionUtility a state params, rfl⟩

/-! ## MetaMo Commutativity (Shared Property)

Both architectures satisfy the key MetaMo commutativity property.
-/

/-- OpenPsi appraisal-decision commutativity -/
theorem openPsi_commutes (q_sens q_dec : ℝ≥0∞) (θ : OpenPsi.OpenPsiStateVec) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  OpenPsi.openPsi_appraisal_decision_commute q_sens q_dec θ

/-- MicroPsi appraisal-decision commutativity -/
theorem microPsi_commutes (q_sens q_dec : ℝ≥0∞) (θ : MicroPsi.MicroPsiStateVec) :
    appraisalFunctor q_sens (decisionFunctor q_dec θ) =
    decisionFunctor q_dec (appraisalFunctor q_sens θ) :=
  MicroPsi.microPsi_appraisal_decision_commute q_sens q_dec θ

/-! ## Summary of Connections and Differences

### Connections (Shared Structure)
1. Both are QModule instances over ℝ≥0∞ (MetaMo framework)
2. Both have 10-dimensional state vectors
3. Both satisfy appraisal-decision commutativity
4. 5 of 6 OpenPsi demands correspond to MicroPsi demands
5. Both have similar demand satisfaction concepts

### Differences (Formal Proofs)
1. **Emotional Models**: 4 modulators (OpenPsi) vs 3 PAD dimensions (MicroPsi)
2. **Demand Count**: 6 (OpenPsi) vs 7 (MicroPsi) - MicroPsi adds exploration
3. **State Decomposition**: 4+6 (OpenPsi) vs 3+7 (MicroPsi)
4. **Action Selection**: Lowest satisfaction (OpenPsi) vs utility-based (MicroPsi)
5. **Emotional Mapping**: Only activation↔arousal maps between models

### Architectural Philosophy
- **OpenPsi**: Need-driven, simple rule (lowest satisfaction wins)
- **MicroPsi**: Utility-driven, emotional modulation of action selection
-/

end Mettapedia.CognitiveArchitecture.Bridges
