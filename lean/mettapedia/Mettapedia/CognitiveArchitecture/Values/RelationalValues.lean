/-
# Relational Values

Formalization of relational values - values that depend on relationships with
specific individuals rather than generic satisfaction levels.

## Key Insight

OpenPsi and MicroPsi treat affiliation as a scalar "social need level".
But human values are fundamentally relational:
- Trust in *specific* people
- Loyalty to *specific* groups
- Love for *specific* individuals

## Energy-Limited Model

Per user specification:
- Trust must be built → practical limits on active relationships
- Universal love possible "in the heart" but active love is energy-limited
- Each relational value type has its own scaling law based on intensional definition

## References

- Care Ethics: Gilligan, "In a Different Voice" (1982)
- Noddings, "Caring: A Relational Approach to Ethics" (1984)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic

namespace Mettapedia.CognitiveArchitecture.Values.Relational

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Relational Value Types

Different types of relationships with different dynamics.
-/

/-- Types of relational values -/
inductive RelationalValueType where
  | trust : RelationalValueType        -- Built over time, fragile
  | loyalty : RelationalValueType      -- Group-based, can be intense
  | gratitude : RelationalValueType    -- Response to benefaction
  | forgiveness : RelationalValueType  -- Release of resentment
  | love : RelationalValueType         -- Deep attachment
  | friendship : RelationalValueType   -- Mutual caring
  deriving DecidableEq, Repr

/-- Whether a relational value requires active energy to maintain -/
def requiresActiveEnergy : RelationalValueType → Bool
  | .trust => true       -- Trust requires ongoing verification
  | .loyalty => true     -- Loyalty requires active commitment
  | .gratitude => false  -- Can hold gratitude passively
  | .forgiveness => false -- Forgiveness is a state, not ongoing
  | .love => true        -- Active love requires energy; feeling doesn't
  | .friendship => true  -- Friendship requires maintenance

/-! ## Relational State

Track relationships with specific agents.
-/

/-- Relational state: values for specific individuals -/
structure RelationalState (Agent : Type*) where
  /-- Trust level for each agent -/
  trust : Agent → UnitValue
  /-- Loyalty strength for each agent -/
  loyalty : Agent → UnitValue
  /-- Gratitude owed to each agent -/
  gratitude : Agent → UnitValue
  /-- Forgiveness extended to each agent -/
  forgiveness : Agent → UnitValue
  /-- Love/attachment for each agent -/
  love : Agent → UnitValue
  /-- Friendship level with each agent -/
  friendship : Agent → UnitValue

/-- Default relational state: neutral towards everyone -/
def RelationalState.neutral {Agent : Type*} : RelationalState Agent :=
  { trust := fun _ => UnitValue.half
    loyalty := fun _ => UnitValue.zero
    gratitude := fun _ => UnitValue.zero
    forgiveness := fun _ => UnitValue.one  -- Default: no resentment
    love := fun _ => UnitValue.zero
    friendship := fun _ => UnitValue.zero }

/-! ## Energy-Limited Relationships

Active relationships consume relational energy.
-/

/-- Relational energy budget -/
structure RelationalCapacity where
  /-- Total energy available for active relationships -/
  totalEnergy : UnitValue
  /-- Current energy spent -/
  currentSpent : UnitValue
  /-- Constraint: can't spend more than total -/
  h_budget : currentSpent.val ≤ totalEnergy.val

/-- Energy cost for maintaining different relationship types -/
def maintenanceCost : RelationalValueType → UnitValue
  | .trust => ⟨0.2, by norm_num, by norm_num⟩       -- Moderate cost
  | .loyalty => ⟨0.15, by norm_num, by norm_num⟩   -- Slightly lower
  | .gratitude => ⟨0.0, by norm_num, by norm_num⟩  -- Free (passive)
  | .forgiveness => ⟨0.0, by norm_num, by norm_num⟩ -- Free (passive)
  | .love => ⟨0.3, by norm_num, by norm_num⟩       -- High cost
  | .friendship => ⟨0.1, by norm_num, by norm_num⟩ -- Lower cost

/-- Available energy for new relationships -/
def availableEnergy (cap : RelationalCapacity) : UnitValue :=
  ⟨cap.totalEnergy.val - cap.currentSpent.val,
   by constructor
      · have hbudget := cap.h_budget
        linarith
      · have h1 := cap.h_budget
        have h2 := cap.totalEnergy.property.2
        have h3 := cap.currentSpent.property.1
        linarith⟩

/-! ## Universal vs Active Values

Some values can be held universally (no specific target), others require specificity.
-/

/-- Universal benevolence: caring for all beings -/
structure UniversalBenevolence where
  /-- Level of universal care (no energy cost) -/
  universalCare : UnitValue
  /-- Level of universal compassion -/
  compassion : UnitValue

/-- Active benevolence: caring for specific beings (energy cost) -/
structure ActiveBenevolence (Agent : Type*) where
  /-- Agents receiving active care -/
  recipients : Agent → Bool
  /-- Level of care for each active recipient -/
  careLevel : Agent → UnitValue
  /-- Total energy spent -/
  energySpent : UnitValue

/-- Love scaling: universal love is free, active love is costly -/
def loveScaling (universal active : UnitValue) (energyAvailable : UnitValue) : UnitValue :=
  -- Active love limited by energy; universal love always available
  if active.val ≤ energyAvailable.val then
    -- Enough energy for active love: combine both
    ⟨max universal.val active.val, by
      constructor
      · exact le_max_of_le_left universal.property.1
      · exact max_le universal.property.2 active.property.2⟩
  else
    -- Not enough energy: fall back to universal only
    universal

/-! ## Trust Dynamics

Trust builds over time through interactions, and can be damaged.
-/

/-- Interaction outcome for trust building -/
inductive InteractionOutcome where
  | positive : InteractionOutcome   -- Trust increased
  | neutral : InteractionOutcome    -- No change
  | negative : InteractionOutcome   -- Trust decreased
  | betrayal : InteractionOutcome   -- Trust severely damaged
  deriving DecidableEq, Repr

/-- Trust update based on interaction -/
def trustUpdate (current : UnitValue) (outcome : InteractionOutcome) : UnitValue :=
  match outcome with
  | .positive =>
    -- Trust grows slowly (asymptotic approach to 1)
    let growth := (1 - current.val) * (1/10 : ℚ)
    ⟨min 1 (current.val + growth), by
      constructor
      · have h := current.property.1
        have hg : growth = (1 - current.val) * (1/10 : ℚ) := rfl
        have h2 := current.property.2
        have hgpos : 0 ≤ growth := by
          simp only [hg]
          apply mul_nonneg <;> linarith
        apply le_min <;> linarith
      · exact min_le_left _ _⟩
  | .neutral => current
  | .negative =>
    -- Trust decreases moderately
    ⟨max 0 (current.val - 1/10), by
      constructor
      · exact le_max_left _ _
      · have h := current.property.2
        apply max_le <;> linarith⟩
  | .betrayal =>
    -- Trust drops significantly
    ⟨max 0 (current.val - 1/2), by
      constructor
      · exact le_max_left _ _
      · have h := current.property.2
        apply max_le <;> linarith⟩

/-- Trust builds asymptotically (approaches 1 but never quite reaches) -/
theorem trust_asymptotic (current : UnitValue) :
    (trustUpdate current .positive).val ≤ 1 :=
  (trustUpdate current .positive).property.2

/-! ## Comparison with OpenPsi/MicroPsi -/

/-- OpenPsi affiliation is scalar, not relational -/
def openPsiAffiliationIsScalar : Prop :=
  -- OpenPsi affiliation: single number for "social need level"
  -- Doesn't track WHO you're affiliated with
  True

/-- MicroPsi affiliation is also scalar -/
def microPsiAffiliationIsScalar : Prop :=
  -- MicroPsi affiliation: same scalar approach
  True

/-- Neither model supports individual-specific relationships -/
theorem no_relational_support :
    openPsiAffiliationIsScalar ∧ microPsiAffiliationIsScalar := by
  constructor <;> trivial

/-- Relational values missing from both models -/
def missingRelationalValues : List RelationalValueType :=
  [.trust, .loyalty, .gratitude, .forgiveness, .love, .friendship]

/-- All relational values are missing (6 total) -/
theorem all_relational_missing : missingRelationalValues.length = 6 := by rfl

end Mettapedia.CognitiveArchitecture.Values.Relational
