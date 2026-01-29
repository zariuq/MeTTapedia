/-
# OpenPsi: Correct Dörner's Psi Theory Implementation

This module provides a **correct** formalization of OpenPsi based on actual sources:
- OpenCog Wiki OpenPsi (2010)
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (AGI 2011)
- Dörner's Psi theory foundations

## Architecture

OpenPsi consists of:
1. **Demands** (6 types from Dörner): Energy, Water, Integrity, Affiliation, Certainty, Competence
2. **Modulators** (4 cognitive regulators): Activation, Resolution, SecuringThreshold, SelectionThreshold
3. **Fuzzy Satisfaction**: `fuzzy_within(level, min, max)` computation
4. **Action Selection**: Select demand with lowest satisfaction (most critical)

## Important Note on PAD Model

The PAD model (Pleasure-Arousal-Dominance from Mehrabian & Russell) is used by **MicroPsi**,
NOT by OpenPsi. The previous incorrect implementation confused these two systems.

## References

- https://wiki.opencog.org/w/OpenPsi_(2010)
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (2011)
- Dörner, "Bauplan für eine Seele" (1999)
- Bach, "MicroPsi 2: Modeling Motivation" (AGI 2015) - for MicroPsi differences
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.CognitiveArchitecture.OpenPsi.FuzzyLogic
import Mathlib.Tactic.FinCases

namespace Mettapedia.CognitiveArchitecture.OpenPsi

/-! ## Demand Types (Dörner's Psi Theory)

The six fundamental demands from Dörner's Psi theory.
These differ from the previously incorrect implementation.
-/

/-- The six demand types from Dörner's Psi theory.
    Reference: OpenCog Wiki OpenPsi (2010), Dörner "Bauplan für eine Seele" (1999) -/
inductive DemandType where
  /-- Physiological: energy/fuel level -/
  | energy : DemandType
  /-- Physiological: hydration (may be disabled in some implementations) -/
  | water : DemandType
  /-- Physical/system stability and health -/
  | integrity : DemandType
  /-- Social connection need -/
  | affiliation : DemandType
  /-- Confidence in knowledge/predictions -/
  | certainty : DemandType
  /-- Problem-solving ability and mastery -/
  | competence : DemandType
  deriving DecidableEq, Repr

/-- Number of demand types -/
def DemandType.count : ℕ := 6

/-- Convert demand type to index -/
def DemandType.toIndex : DemandType → Fin 6
  | .energy => 0
  | .water => 1
  | .integrity => 2
  | .affiliation => 3
  | .certainty => 4
  | .competence => 5

/-- Convert index to demand type -/
def DemandType.fromIndex : Fin 6 → DemandType
  | 0 => .energy
  | 1 => .water
  | 2 => .integrity
  | 3 => .affiliation
  | 4 => .certainty
  | 5 => .competence

theorem DemandType.fromIndex_toIndex (d : DemandType) :
    fromIndex (toIndex d) = d := by
  cases d <;> rfl

theorem DemandType.toIndex_fromIndex (i : Fin 6) :
    toIndex (fromIndex i) = i := by
  fin_cases i <;> rfl

/-- Enumeration of all demand types -/
def DemandType.all : List DemandType :=
  [.energy, .water, .integrity, .affiliation, .certainty, .competence]

theorem DemandType.mem_all (d : DemandType) : d ∈ DemandType.all := by
  cases d <;> simp [DemandType.all]

/-! ## Modulator State (NOT PAD!)

The four modulators from OpenPsi that regulate cognitive processing.
These are NOT the PAD emotional model - that's MicroPsi!

Reference: OpenCog Wiki OpenPsi (2010)
-/

/-- The four modulators from OpenPsi that regulate cognitive processing.
    This is NOT the PAD model (which is MicroPsi's emotional model).

    - **Activation**: Overall system energy level (high = active, low = sluggish)
    - **Resolution**: Perception detail level (high = fine-grained, low = coarse)
    - **SecuringThreshold**: Confidence required to accept information (high = skeptical)
    - **SelectionThreshold**: Action selection determinism (high = deterministic, low = exploratory)
-/
structure ModulatorState where
  /-- Overall system energy (high = active, low = sluggish) -/
  activation : UnitValue
  /-- Perception detail level (high = fine-grained, low = coarse) -/
  resolution : UnitValue
  /-- Confidence threshold for accepting information (high = skeptical) -/
  securingThreshold : UnitValue
  /-- Action selection variability (high = deterministic, low = exploratory) -/
  selectionThreshold : UnitValue
  deriving Repr

namespace ModulatorState

/-- Default modulator state (all at 0.5) -/
def default : ModulatorState :=
  ⟨UnitValue.half, UnitValue.half, UnitValue.half, UnitValue.half⟩

/-- High activation state (energetic, detailed perception, deterministic) -/
def highActivation : ModulatorState :=
  ⟨UnitValue.one, UnitValue.one, UnitValue.half, UnitValue.one⟩

/-- Low activation state (sluggish, coarse perception, exploratory) -/
def lowActivation : ModulatorState :=
  ⟨UnitValue.zero, UnitValue.zero, UnitValue.half, UnitValue.zero⟩

end ModulatorState

/-! ## Demand State

The current level and target range for each demand.
Satisfaction is computed using fuzzy_within.
-/

/-- Demand state: current level and target range for each demand type -/
structure DemandState where
  /-- Current level for each demand type -/
  levels : DemandType → UnitValue
  /-- Target range for each demand type -/
  targets : DemandType → DemandTarget

namespace DemandState

/-- Default demand state: all levels at 0.5, default targets [0.3, 0.7] -/
def default : DemandState :=
  ⟨fun _ => UnitValue.half, fun _ => DemandTarget.default⟩

/-- All demands fully satisfied (levels at 1.0) -/
def satisfied : DemandState :=
  ⟨fun _ => UnitValue.one, fun _ => DemandTarget.default⟩

/-- All demands unsatisfied (levels at 0.0) -/
def unsatisfied : DemandState :=
  ⟨fun _ => UnitValue.zero, fun _ => DemandTarget.default⟩

/-- Get the fuzzy satisfaction for a specific demand -/
noncomputable def satisfaction (state : DemandState) (d : DemandType) : UnitValue :=
  fuzzySatisfaction (state.levels d) (state.targets d)

/-- Get satisfactions for all demands -/
noncomputable def allSatisfactions (state : DemandState) : DemandType → UnitValue :=
  fun d => state.satisfaction d

end DemandState

/-! ## Combined OpenPsi State

The complete OpenPsi state combines modulators with demand levels.
-/

/-- The complete motivational state of an OpenPsi agent -/
structure OpenPsiState where
  /-- Current modulator state -/
  modulators : ModulatorState
  /-- Current demand state -/
  demands : DemandState

namespace OpenPsiState

/-- Default OpenPsi state -/
def default : OpenPsiState :=
  ⟨ModulatorState.default, DemandState.default⟩

/-- Get the satisfaction level for a specific demand -/
noncomputable def satisfaction (state : OpenPsiState) (d : DemandType) : UnitValue :=
  state.demands.satisfaction d

end OpenPsiState

/-! ## Deficit Computation

The deficit of a demand is 1 - satisfaction (inverse of satisfaction level).
Higher deficit = higher urgency to address the demand.
-/

/-- Deficit of a demand = 1 - satisfaction level -/
def deficit (level : UnitValue) : UnitValue :=
  ⟨1 - level.val, ⟨by linarith [level.property.2], by linarith [level.property.1]⟩⟩

/-- Deficit is inverse of satisfaction -/
theorem deficit_one : deficit UnitValue.one = UnitValue.zero := by
  simp [deficit, UnitValue.one, UnitValue.zero]

/-- Deficit of zero is one -/
theorem deficit_zero : deficit UnitValue.zero = UnitValue.one := by
  simp [deficit, UnitValue.one, UnitValue.zero]

end Mettapedia.CognitiveArchitecture.OpenPsi
