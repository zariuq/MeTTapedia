/-
# OpenPsi Fuzzy Logic Satisfaction

Formalization of OpenPsi's fuzzy satisfaction computation based on the
fuzzy_within function from the OpenCog implementation.

## Core Concept

In OpenPsi, demands have target ranges [min, max]. Satisfaction is computed as:
- 1.0 when the demand level is within the target range
- < 1.0 when outside the range, with smooth drop-off

This matches the fuzzy logic approach from:
- OpenCog Wiki OpenPsi (2010)
- Dörner's Psi theory demand satisfaction

## References

- https://wiki.opencog.org/w/OpenPsi_(2010)
- Cai, Goertzel et al., "OpenPsi: Realizing Dörner's 'Psi' Cognitive Model" (2011)
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

namespace Mettapedia.CognitiveArchitecture.OpenPsi

/-! ## Unit Value Type

Values bounded in [0, 1] using rationals for computability.
-/

/-- A value in the unit interval [0,1], represented as a subtype of ℚ -/
abbrev UnitValue := { x : ℚ // 0 ≤ x ∧ x ≤ 1 }

namespace UnitValue

/-- The zero unit value -/
def zero : UnitValue := ⟨0, by norm_num, by norm_num⟩

/-- The one unit value -/
def one : UnitValue := ⟨1, by norm_num, by norm_num⟩

/-- The half unit value -/
def half : UnitValue := ⟨1/2, by norm_num, by norm_num⟩

/-- Create a unit value from a rational, clamping to [0,1] -/
noncomputable def ofRat (q : ℚ) : UnitValue :=
  ⟨max 0 (min q 1), by
    constructor
    · exact le_max_left 0 _
    · exact max_le (by norm_num) (min_le_right q 1)⟩

/-- Partial order on UnitValue inherited from ℚ -/
instance : LE UnitValue := ⟨fun a b => a.val ≤ b.val⟩
instance : LT UnitValue := ⟨fun a b => a.val < b.val⟩

instance : DecidableRel (· ≤ · : UnitValue → UnitValue → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

instance : DecidableRel (· < · : UnitValue → UnitValue → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))

theorem val_le_refl (a : UnitValue) : a ≤ a := _root_.le_refl a.val

theorem val_le_trans {a b c : UnitValue} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  _root_.le_trans hab hbc

theorem val_le_antisymm {a b : UnitValue} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a; cases b
  simp only [Subtype.mk.injEq]
  exact _root_.le_antisymm hab hba

theorem zero_le_one : zero ≤ one := by
  show (0 : ℚ) ≤ 1
  norm_num

end UnitValue

/-! ## Demand Target Range

A target range specifies when a demand is considered satisfied.
-/

/-- A target range for a demand level.
    Satisfaction is 1.0 when level is within [minLevel, maxLevel]. -/
structure DemandTarget where
  /-- Minimum acceptable level -/
  minLevel : UnitValue
  /-- Maximum acceptable level -/
  maxLevel : UnitValue
  /-- The range is valid (min ≤ max) -/
  h_valid : minLevel.val ≤ maxLevel.val
  deriving Repr

namespace DemandTarget

/-- Default target range [0.3, 0.7] -/
def default : DemandTarget where
  minLevel := ⟨3/10, by norm_num, by norm_num⟩
  maxLevel := ⟨7/10, by norm_num, by norm_num⟩
  h_valid := by norm_num

/-- Full satisfaction range [0, 1] - always satisfied -/
def full : DemandTarget where
  minLevel := UnitValue.zero
  maxLevel := UnitValue.one
  h_valid := by show (0 : ℚ) ≤ 1; norm_num

end DemandTarget

/-! ## Fuzzy Satisfaction Computation

The core fuzzy logic function that computes demand satisfaction.
-/

/-- Check if a level is within the target range -/
def inTargetRange (level : UnitValue) (target : DemandTarget) : Prop :=
  target.minLevel.val ≤ level.val ∧ level.val ≤ target.maxLevel.val

instance : Decidable (inTargetRange level target) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Fuzzy satisfaction computation (matches OpenPsi's fuzzy_within).

When level is in [min, max]: satisfaction = 1.0
When level < min: satisfaction = level / min (linear drop-off)
When level > max: satisfaction = max / level (inverse drop-off)

Note: We handle edge cases (min = 0, level = 0) carefully. -/
noncomputable def fuzzySatisfaction (level : UnitValue) (target : DemandTarget) : UnitValue :=
  if h_in_range : target.minLevel.val ≤ level.val ∧ level.val ≤ target.maxLevel.val then
    -- In range: fully satisfied
    UnitValue.one
  else if h_below : level.val < target.minLevel.val then
    -- Below minimum: linear drop-off
    if h_min_pos : target.minLevel.val = 0 then
      -- Edge case: min = 0 but level < 0 is impossible for UnitValue
      UnitValue.one
    else
      -- level / min where 0 ≤ level < min, so 0 ≤ level/min < 1
      ⟨level.val / target.minLevel.val, by
        have h_min_pos' : 0 < target.minLevel.val :=
          lt_of_le_of_ne target.minLevel.property.1 (Ne.symm h_min_pos)
        constructor
        · exact div_nonneg level.property.1 (le_of_lt h_min_pos')
        · rw [div_le_one h_min_pos']
          exact le_of_lt h_below⟩
  else
    -- Above maximum: inverse drop-off (level > max)
    if h_level_pos : level.val = 0 then
      -- Edge case: level = 0 but we're in "above max" branch means max < 0, impossible
      UnitValue.one
    else
      -- max / level where max < level, so max/level < 1
      ⟨target.maxLevel.val / level.val, by
        have h_level_pos' : 0 < level.val :=
          lt_of_le_of_ne level.property.1 (Ne.symm h_level_pos)
        -- From ¬h_in_range and ¬h_below, we get level > max
        have h_above : target.maxLevel.val < level.val := by
          push_neg at h_in_range
          have h_not_below : level.val ≥ target.minLevel.val := le_of_not_gt h_below
          exact h_in_range h_not_below
        constructor
        · exact div_nonneg target.maxLevel.property.1 (le_of_lt h_level_pos')
        · rw [div_le_one h_level_pos']
          exact le_of_lt h_above⟩

/-! ## Key Theorems -/

/-- Satisfaction is 1 when level is within the target range -/
theorem fuzzySatisfaction_in_range (level : UnitValue) (target : DemandTarget)
    (h : inTargetRange level target) :
    fuzzySatisfaction level target = UnitValue.one := by
  unfold fuzzySatisfaction inTargetRange at *
  rw [dif_pos h]

/-- Satisfaction is at most 1 -/
theorem fuzzySatisfaction_le_one (level : UnitValue) (target : DemandTarget) :
    (fuzzySatisfaction level target).val ≤ 1 :=
  (fuzzySatisfaction level target).property.2

/-- Satisfaction is nonnegative -/
theorem fuzzySatisfaction_nonneg (level : UnitValue) (target : DemandTarget) :
    0 ≤ (fuzzySatisfaction level target).val :=
  (fuzzySatisfaction level target).property.1

/-- When level equals min, satisfaction is 1 (boundary case) -/
theorem fuzzySatisfaction_at_min (target : DemandTarget) :
    fuzzySatisfaction target.minLevel target = UnitValue.one := by
  apply fuzzySatisfaction_in_range
  unfold inTargetRange
  exact ⟨_root_.le_refl _, target.h_valid⟩

/-- When level equals max, satisfaction is 1 (boundary case) -/
theorem fuzzySatisfaction_at_max (target : DemandTarget) :
    fuzzySatisfaction target.maxLevel target = UnitValue.one := by
  apply fuzzySatisfaction_in_range
  unfold inTargetRange
  exact ⟨target.h_valid, _root_.le_refl _⟩

/-- With full range [0,1], any level gives satisfaction 1 -/
theorem fuzzySatisfaction_full_range (level : UnitValue) :
    fuzzySatisfaction level DemandTarget.full = UnitValue.one := by
  apply fuzzySatisfaction_in_range
  unfold inTargetRange DemandTarget.full
  simp only
  exact ⟨level.property.1, level.property.2⟩

end Mettapedia.CognitiveArchitecture.OpenPsi
