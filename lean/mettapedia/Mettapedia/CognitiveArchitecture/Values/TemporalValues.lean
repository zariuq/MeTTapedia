/-
# Temporal Values

Formalization of temporal values - values about the future, legacy, and
intergenerational concerns. OpenPsi and MicroPsi are present-focused,
optimizing current satisfaction without regard for distant future.

## Key Concepts

1. **Legacy** - Impact after death, lasting contributions
2. **Future Generations** - Welfare of descendants
3. **Sustainability** - Long-term environmental/resource care
4. **Patience** - Willingness to delay gratification

## References

- Parfit, "Reasons and Persons" (1984) - Personal identity and future selves
- Jonas, "The Imperative of Responsibility" (1979) - Ethics for the technological age
-/

import Mettapedia.CognitiveArchitecture.Values.Basic

namespace Mettapedia.CognitiveArchitecture.Values.Temporal

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Temporal Value Types -/

/-- Types of temporal values -/
inductive TemporalValueType where
  | legacy : TemporalValueType           -- Impact after death
  | futureGenerations : TemporalValueType -- Welfare of descendants
  | sustainability : TemporalValueType    -- Long-term resource care
  | patience : TemporalValueType          -- Delayed gratification
  | tradition : TemporalValueType         -- Preserving past practices
  deriving DecidableEq, Repr

/-! ## Temporal Discounting

How much future outcomes are discounted relative to present.
-/

/-- Temporal discount parameters -/
structure DiscountParameters where
  /-- Discount rate per time unit (0 = no discounting, 1 = total discounting) -/
  rate : UnitValue
  /-- Time horizon considered (in abstract time units) -/
  horizon : ℕ

/-- Discount factor for a future time t -/
def discountFactor (params : DiscountParameters) (t : ℕ) : ℚ :=
  (1 - params.rate.val) ^ t

/-- Present value of a future utility -/
def presentValue (params : DiscountParameters) (futureUtility : ℚ) (t : ℕ) : ℚ :=
  futureUtility * discountFactor params t

/-- Discount factor decreases with time -/
theorem discount_decreases (params : DiscountParameters) (t1 t2 : ℕ) :
    t1 ≤ t2 → discountFactor params t2 ≤ discountFactor params t1 := by
  intro hle
  simp only [discountFactor]
  have h : 0 ≤ 1 - params.rate.val := by
    have hr := params.rate.property
    linarith
  have h2 : 1 - params.rate.val ≤ 1 := by
    have hr := params.rate.property
    linarith
  -- For 0 ≤ x ≤ 1 and t1 ≤ t2, we have x^t2 ≤ x^t1
  apply pow_le_pow_of_le_one h h2 hle

/-- No discounting means all times are equally valued -/
theorem no_discount_equal (t : ℕ) :
    discountFactor ⟨UnitValue.zero, 100⟩ t = 1 := by
  simp [discountFactor, UnitValue.zero]

/-! ## Legacy Concerns

Values about lasting impact beyond one's lifetime.
-/

/-- Legacy state -/
structure LegacyState where
  /-- Importance of leaving a legacy -/
  legacyWeight : UnitValue
  /-- Estimated lasting impact (0-1 scale) -/
  estimatedImpact : UnitValue
  /-- Satisfaction with legacy progress -/
  satisfaction : UnitValue

/-- Legacy-adjusted utility adds legacy consideration -/
def legacyAdjustedUtility (immediate : ℚ) (legacy : LegacyState) : ℚ :=
  immediate + legacy.legacyWeight.val * legacy.estimatedImpact.val

/-! ## Future Generations

Values concerning the welfare of descendants.
-/

/-- Concern for future generations -/
structure FutureGenConcern where
  /-- How much we care about future generations (0-1) -/
  concernLevel : UnitValue
  /-- Number of generations we consider -/
  generationsConsidered : ℕ
  /-- Discount per generation -/
  generationalDiscount : UnitValue

/-- Utility of an outcome considering future generations -/
def intergenerationalUtility
    (concern : FutureGenConcern)
    (presentUtility : ℚ)
    (futureUtility : ℕ → ℚ) : ℚ :=
  let generationWeights := List.range concern.generationsConsidered |>.map fun g =>
    concern.concernLevel.val * (1 - concern.generationalDiscount.val) ^ g
  let futureSum := (List.range concern.generationsConsidered).map (fun g =>
    generationWeights.getD g 0 * futureUtility g) |>.sum
  presentUtility + futureSum

/-! ## Sustainability

Long-term resource and environmental values.
-/

/-- Sustainability parameters -/
structure SustainabilityParams where
  /-- Importance of sustainability -/
  importance : UnitValue
  /-- Current resource depletion rate (0 = sustainable, 1 = depleting) -/
  depletionRate : UnitValue
  /-- Regeneration capacity -/
  regenerationRate : UnitValue

/-- Whether current practices are sustainable -/
def isSustainable (params : SustainabilityParams) : Bool :=
  params.depletionRate.val ≤ params.regenerationRate.val

/-- Sustainability-adjusted utility penalizes unsustainable practices -/
def sustainabilityAdjustedUtility (params : SustainabilityParams) (utility : ℚ) : ℚ :=
  if isSustainable params then
    utility
  else
    -- Penalty proportional to unsustainability
    utility - params.importance.val * (params.depletionRate.val - params.regenerationRate.val)

/-! ## Comparison with OpenPsi/MicroPsi -/

/-- OpenPsi is present-focused -/
def openPsiTimeHorizon : String := "present satisfaction only"

/-- MicroPsi is present-focused -/
def microPsiTimeHorizon : String := "present satisfaction only"

/-- Neither model has temporal values -/
def missingTemporalValues : List TemporalValueType :=
  [.legacy, .futureGenerations, .sustainability, .patience, .tradition]

/-- All temporal values are missing from both models -/
theorem all_temporal_missing : missingTemporalValues.length = 5 := by rfl

/-- Neither model considers future generations -/
theorem no_future_generations_support : True := trivial

end Mettapedia.CognitiveArchitecture.Values.Temporal
