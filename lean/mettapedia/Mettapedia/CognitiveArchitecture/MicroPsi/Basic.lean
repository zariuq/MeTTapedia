/-
# MicroPsi: Bach's Cognitive Architecture

MicroPsi is Joscha Bach's cognitive architecture based on Dörner's Psi theory,
but with significant extensions including the PAD emotional model.

## Architecture

MicroPsi consists of:
1. **Demands**: Similar to Dörner but with different structure
2. **PAD Emotional Model**: Pleasure-Arousal-Dominance (Mehrabian & Russell 1974)
3. **Urges**: Priority computation based on demand satisfaction and modulators
4. **Action Selection**: Utility-based selection with emotional modulation

## Key Difference from OpenPsi

**MicroPsi uses PAD for emotions; OpenPsi uses 4 modulators!**

| MicroPsi | OpenPsi |
|----------|---------|
| PAD (Pleasure, Arousal, Dominance) | 4 Modulators (Activation, Resolution, SecuringThreshold, SelectionThreshold) |

## References

- Bach, "Principles of Synthetic Intelligence" (2009)
- Bach, "MicroPsi 2: The Next Generation of the MicroPsi Cognitive Architecture" (AGI 2012)
- Bach, "MicroPsi 2: Modeling Motivation" (AGI 2015)
- Mehrabian & Russell, "An Approach to Environmental Psychology" (1974) - PAD model
-/

import Mettapedia.CognitiveArchitecture.MetaMo.Main
import Mettapedia.CognitiveArchitecture.OpenPsi.FuzzyLogic
import Mathlib.Tactic.FinCases

namespace Mettapedia.CognitiveArchitecture.MicroPsi

-- Import UnitValue from OpenPsi.FuzzyLogic
open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## PAD Emotional Model

The PAD (Pleasure-Arousal-Dominance) model from Mehrabian & Russell (1974).
This is what MicroPsi uses for emotional state - NOT OpenPsi!

Each dimension is a continuous value in [0,1]:
- **Pleasure** (Valence): Positive vs negative affect
- **Arousal**: High vs low activation/energy
- **Dominance**: In control vs submissive
-/

/-- The PAD emotional state model (Mehrabian & Russell 1974).
    Used by MicroPsi, NOT by OpenPsi!

    - **Pleasure** (Valence): 0 = negative affect, 1 = positive affect
    - **Arousal**: 0 = calm/low energy, 1 = excited/high energy
    - **Dominance**: 0 = submissive/controlled, 1 = dominant/in control
-/
structure PADState where
  /-- Pleasure/Valence dimension (0 = negative, 1 = positive) -/
  pleasure : UnitValue
  /-- Arousal/Activation dimension (0 = calm, 1 = excited) -/
  arousal : UnitValue
  /-- Dominance/Control dimension (0 = submissive, 1 = dominant) -/
  dominance : UnitValue
  deriving Repr

namespace PADState

/-- Neutral PAD state (all dimensions at 0.5) -/
def neutral : PADState :=
  ⟨UnitValue.half, UnitValue.half, UnitValue.half⟩

/-- Happy/excited state (high pleasure, high arousal, high dominance) -/
def happy : PADState :=
  ⟨UnitValue.one, UnitValue.one, UnitValue.one⟩

/-- Sad/depressed state (low pleasure, low arousal, low dominance) -/
def sad : PADState :=
  ⟨UnitValue.zero, UnitValue.zero, UnitValue.zero⟩

/-- Angry state (low pleasure, high arousal, high dominance) -/
def angry : PADState :=
  ⟨UnitValue.zero, UnitValue.one, UnitValue.one⟩

/-- Fearful state (low pleasure, high arousal, low dominance) -/
def fearful : PADState :=
  ⟨UnitValue.zero, UnitValue.one, UnitValue.zero⟩

/-- Relaxed state (high pleasure, low arousal, high dominance) -/
def relaxed : PADState :=
  ⟨UnitValue.one, UnitValue.zero, UnitValue.one⟩

end PADState

/-! ## MicroPsi Demand Types

MicroPsi's demands are based on Dörner's Psi theory but with some variations.
Bach's implementation focuses on:
- Physiological needs (food/energy, water, intactness)
- Cognitive needs (certainty, competence)
- Social needs (affiliation)
- Plus additional exploratory drives
-/

/-- MicroPsi demand types based on Bach's cognitive architecture.
    Similar to Dörner's but with MicroPsi-specific organization. -/
inductive DemandType where
  /-- Physiological: food/energy need -/
  | food : DemandType
  /-- Physiological: water/hydration need -/
  | water : DemandType
  /-- Physiological: intactness/health (similar to Dörner's integrity) -/
  | intactness : DemandType
  /-- Social: affiliation/connection need -/
  | affiliation : DemandType
  /-- Cognitive: certainty/predictability need -/
  | certainty : DemandType
  /-- Cognitive: competence/mastery need -/
  | competence : DemandType
  /-- Exploration: novelty-seeking drive -/
  | exploration : DemandType
  deriving DecidableEq, Repr

/-- Number of MicroPsi demand types (7, vs OpenPsi's 6) -/
def DemandType.count : ℕ := 7

/-- Convert demand type to index -/
def DemandType.toIndex : DemandType → Fin 7
  | .food => 0
  | .water => 1
  | .intactness => 2
  | .affiliation => 3
  | .certainty => 4
  | .competence => 5
  | .exploration => 6

/-- Convert index to demand type -/
def DemandType.fromIndex : Fin 7 → DemandType
  | 0 => .food
  | 1 => .water
  | 2 => .intactness
  | 3 => .affiliation
  | 4 => .certainty
  | 5 => .competence
  | 6 => .exploration

theorem DemandType.fromIndex_toIndex (d : DemandType) :
    fromIndex (toIndex d) = d := by
  cases d <;> rfl

theorem DemandType.toIndex_fromIndex (i : Fin 7) :
    toIndex (fromIndex i) = i := by
  fin_cases i <;> rfl

/-- Enumeration of all MicroPsi demand types -/
def DemandType.all : List DemandType :=
  [.food, .water, .intactness, .affiliation, .certainty, .competence, .exploration]

theorem DemandType.mem_all (d : DemandType) : d ∈ DemandType.all := by
  cases d <;> simp [DemandType.all]

/-! ## Demand State

MicroPsi demand state with satisfaction levels.
-/

/-- MicroPsi demand state: satisfaction level for each demand -/
structure DemandState where
  /-- Current satisfaction level for each demand type -/
  levels : DemandType → UnitValue

namespace DemandState

/-- All demands fully satisfied -/
def satisfied : DemandState :=
  ⟨fun _ => UnitValue.one⟩

/-- All demands unsatisfied -/
def unsatisfied : DemandState :=
  ⟨fun _ => UnitValue.zero⟩

/-- Neutral demand state (all at 0.5) -/
def neutral : DemandState :=
  ⟨fun _ => UnitValue.half⟩

end DemandState

/-! ## Urge Computation

MicroPsi uses urge-based action selection, where urge combines:
- Demand deficit (1 - satisfaction)
- Demand importance weight
- Emotional modulation from PAD state
-/

/-- Deficit of a demand = 1 - satisfaction level -/
def deficit (level : UnitValue) : UnitValue :=
  ⟨1 - level.val, ⟨by linarith [level.property.2], by linarith [level.property.1]⟩⟩

/-- Urge parameters for a demand type -/
structure UrgeParams where
  /-- Base importance weight of this demand -/
  importance : UnitValue
  /-- Decay rate (how fast urge grows when unsatisfied) -/
  decayRate : UnitValue
  deriving Repr

/-- Default urge parameters -/
def UrgeParams.default : UrgeParams :=
  ⟨UnitValue.half, UnitValue.half⟩

/-- Compute urge for a demand given its level, parameters, and PAD state.

    In MicroPsi, arousal modulates urge strength:
    - High arousal → stronger urges
    - Low arousal → weaker urges

    urge = deficit × importance × (0.5 + 0.5 × arousal) -/
def urge (level : UnitValue) (params : UrgeParams) (pad : PADState) : ℚ :=
  let d := (deficit level).val
  let arousalMod := (1/2 : ℚ) + (1/2 : ℚ) * pad.arousal.val
  d * params.importance.val * arousalMod

/-! ## Combined MicroPsi State

The full MicroPsi motivational state combines PAD emotions with demand levels.
-/

/-- The complete motivational state of a MicroPsi agent -/
structure MicroPsiState where
  /-- Current PAD emotional state -/
  emotions : PADState
  /-- Current demand satisfaction levels -/
  demands : DemandState

namespace MicroPsiState

/-- Neutral MicroPsi state -/
def neutral : MicroPsiState :=
  ⟨PADState.neutral, DemandState.neutral⟩

/-- Compute urge for a specific demand in the current state -/
def demandUrge (state : MicroPsiState) (d : DemandType) (params : UrgeParams) : ℚ :=
  urge (state.demands.levels d) params state.emotions

end MicroPsiState

/-! ## Action Selection (Utility-Based)

MicroPsi uses utility-based action selection, unlike OpenPsi's
"lowest satisfaction wins" rule.
-/

/-- An action that can be selected by MicroPsi -/
structure Action where
  /-- Unique identifier -/
  id : ℕ
  /-- Which demand this action primarily serves -/
  targetDemand : DemandType
  /-- Expected satisfaction gain -/
  expectedGain : UnitValue
  /-- Action cost/effort -/
  cost : UnitValue
  deriving Repr

/-- Utility of an action = urge × expectedGain - cost

    This is different from OpenPsi's "lowest satisfaction wins" rule! -/
def actionUtility
    (a : Action)
    (state : MicroPsiState)
    (params : DemandType → UrgeParams) : ℚ :=
  let u := state.demandUrge a.targetDemand (params a.targetDemand)
  u * a.expectedGain.val - a.cost.val

/-! ## Key Theorems -/

/-- Deficit is inverse: deficit of 1 is 0 -/
theorem deficit_one : deficit UnitValue.one = UnitValue.zero := by
  simp [deficit, UnitValue.one, UnitValue.zero]

/-- Deficit of 0 is 1 -/
theorem deficit_zero : deficit UnitValue.zero = UnitValue.one := by
  simp [deficit, UnitValue.one, UnitValue.zero]

/-- Higher arousal increases urge (all else equal) -/
theorem urge_mono_arousal
    (level : UnitValue) (params : UrgeParams)
    (pad1 pad2 : PADState)
    (h : pad1.arousal.val ≤ pad2.arousal.val) :
    urge level params pad1 ≤ urge level params pad2 := by
  simp only [urge]
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add_left
    apply mul_le_mul_of_nonneg_left h
    norm_num
  · apply mul_nonneg
    · exact (deficit level).property.1
    · exact params.importance.property.1

end Mettapedia.CognitiveArchitecture.MicroPsi
