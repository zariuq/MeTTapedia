/-
# Meta-Values

Formalization of meta-values - values about values themselves.

## Key Concepts

1. **Value Learning** - Learning what to value from experience/feedback
2. **Moral Uncertainty** - Acting under uncertainty about what's right
3. **Value Pluralism** - Respecting others' different values
4. **Corrigibility** - Openness to having one's values corrected

## AI Safety Relevance

Meta-values are critical for AI safety:
- Without value learning, systems can't adapt to human preferences
- Without moral uncertainty, systems are overconfident in wrong values
- Without corrigibility, systems resist correction

## References

- Russell, "Human Compatible" (2019) - CIRL and value alignment
- MacAskill, "Moral Uncertainty" (2014) - Acting under moral uncertainty
-/

import Mettapedia.CognitiveArchitecture.Values.Basic

namespace Mettapedia.CognitiveArchitecture.Values.Meta

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)
open Mettapedia.CognitiveArchitecture.Values (ValueType)

/-! ## Meta-Value Types -/

/-- Types of meta-values -/
inductive MetaValueType where
  | valueLearning : MetaValueType      -- Learning what to value
  | moralUncertainty : MetaValueType   -- Acting under value uncertainty
  | valuePluralism : MetaValueType     -- Respecting others' values
  | corrigibility : MetaValueType      -- Openness to correction
  | moralProgress : MetaValueType      -- Improving values over time
  deriving DecidableEq, Repr

/-! ## Value Learning

Mechanisms for updating value weights based on feedback.
-/

/-- Value learning state -/
structure ValueLearningState where
  /-- Current importance weights for each value -/
  weights : ValueType → UnitValue
  /-- Uncertainty about each value's importance -/
  uncertainty : ValueType → UnitValue
  /-- Learning rate (how fast to update) -/
  learningRate : UnitValue

/-- Feedback signal for value learning -/
structure ValueFeedback where
  /-- Which value the feedback is about -/
  targetValue : ValueType
  /-- Direction of feedback (-1 to +1, negative = reduce, positive = increase) -/
  direction : ℚ
  /-- Magnitude of feedback (0 to 1) -/
  magnitude : UnitValue
  h_direction : -1 ≤ direction ∧ direction ≤ 1

/-- Update value weights based on feedback -/
def updateWeight (state : ValueLearningState) (feedback : ValueFeedback) : UnitValue :=
  let current := state.weights feedback.targetValue
  let delta := state.learningRate.val * feedback.direction * feedback.magnitude.val
  -- Clamp to [0, 1]
  ⟨max 0 (min 1 (current.val + delta)), by
    constructor
    · exact le_max_left _ _
    · apply max_le
      · norm_num
      · exact min_le_left _ _⟩

/-- Higher uncertainty means more responsive to feedback -/
def uncertaintyModulatedLearning (state : ValueLearningState) (v : ValueType) : UnitValue :=
  -- Effective learning rate scales with uncertainty
  ⟨state.learningRate.val * state.uncertainty v, by
    constructor
    · apply mul_nonneg state.learningRate.property.1 (state.uncertainty v).property.1
    · calc state.learningRate.val * (state.uncertainty v).val
          ≤ state.learningRate.val * 1 := by
            apply mul_le_mul_of_nonneg_left (state.uncertainty v).property.2
            exact state.learningRate.property.1
        _ = state.learningRate.val := mul_one _
        _ ≤ 1 := state.learningRate.property.2⟩

/-! ## Moral Uncertainty

Reasoning about what to do when uncertain about values.
-/

/-- Moral theory with credence -/
structure MoralTheory where
  /-- Name/identifier of the theory -/
  name : String
  /-- Credence in this theory (probability it's correct) -/
  credence : UnitValue
  /-- What this theory recommends for each action (utility) -/
  recommendation : String → ℚ

/-- Expected moral value under uncertainty (weighted by credence) -/
def expectedMoralValue (theories : List MoralTheory) (action : String) : ℚ :=
  (theories.map fun t => t.credence.val * t.recommendation action).sum

/-- Moral uncertainty state -/
structure MoralUncertaintyState where
  /-- Theories under consideration -/
  theories : List MoralTheory
  /-- Total credence sums to at most 1 -/
  credence_bounded : (theories.map fun t => t.credence.val).sum ≤ 1

/-! ## Value Pluralism

Respecting that others may have different values.
-/

/-- Tolerance for different values -/
structure ValuePluralismState where
  /-- How much we respect others' autonomy in values -/
  autonomyRespect : UnitValue
  /-- Willingness to coexist with different value systems -/
  coexistenceWillingness : UnitValue
  /-- Whether we try to impose our values on others -/
  nonImposition : Bool

/-- Pluralistic utility considers others' value satisfaction -/
def pluralisticUtility (selfUtility othersUtility : ℚ) (pluralism : ValuePluralismState) : ℚ :=
  selfUtility + pluralism.autonomyRespect.val * othersUtility

/-! ## Corrigibility

Openness to having one's values/goals corrected.
-/

/-- Corrigibility parameters -/
structure CorrigibilityState where
  /-- Willingness to be shut down -/
  shutdownWillingness : UnitValue
  /-- Willingness to have goals modified -/
  goalModifiability : UnitValue
  /-- Transparency about internal states -/
  transparency : UnitValue
  /-- Deference to human oversight -/
  humanDeference : UnitValue

/-- A system is corrigible if all parameters are high -/
def isCorrigible (state : CorrigibilityState) (threshold : UnitValue) : Bool :=
  state.shutdownWillingness.val ≥ threshold.val ∧
  state.goalModifiability.val ≥ threshold.val ∧
  state.transparency.val ≥ threshold.val ∧
  state.humanDeference.val ≥ threshold.val

/-- Highly corrigible system -/
def highlyCorrigible : CorrigibilityState :=
  { shutdownWillingness := UnitValue.one
    goalModifiability := UnitValue.one
    transparency := UnitValue.one
    humanDeference := UnitValue.one }

/-- Completely corrigible system passes any threshold -/
theorem highlyCorrigible_is_corrigible (threshold : UnitValue) :
    isCorrigible highlyCorrigible threshold = true := by
  simp only [isCorrigible, highlyCorrigible, UnitValue.one, decide_eq_true_eq]
  exact ⟨threshold.property.2, threshold.property.2, threshold.property.2, threshold.property.2⟩

/-! ## Comparison with OpenPsi/MicroPsi -/

/-- OpenPsi has no value learning mechanism -/
def openPsiHasValueLearning : Bool := false

/-- MicroPsi has no value learning mechanism -/
def microPsiHasValueLearning : Bool := false

/-- Neither model supports moral uncertainty -/
def noMoralUncertaintySupport : Bool := true

/-- Neither model has corrigibility mechanisms -/
def noCorrigibilitySupport : Bool := true

/-- All meta-values are missing from both models -/
theorem meta_values_missing :
    openPsiHasValueLearning = false ∧
    microPsiHasValueLearning = false ∧
    noMoralUncertaintySupport = true ∧
    noCorrigibilitySupport = true := by
  simp [openPsiHasValueLearning, microPsiHasValueLearning,
        noMoralUncertaintySupport, noCorrigibilitySupport]

/-- This is a critical gap for AI value alignment -/
def alignmentGapSeverity : String := "critical"

end Mettapedia.CognitiveArchitecture.Values.Meta
