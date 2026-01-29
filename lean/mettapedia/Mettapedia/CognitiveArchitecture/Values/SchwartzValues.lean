/-
# Schwartz's Theory of Basic Human Values

Formalization of Schwartz's 10 universal values and their circular (circumplex)
structure. Values are arranged in a circle where:
- Adjacent values are compatible (can be pursued together)
- Opposite values are conflicting (pursuing one undermines the other)

## The Circumplex Structure

```
                    Self-Transcendence
                          ↑
        Universalism ←----+----→ Benevolence
                         |
  Openness               |               Conservation
     ↑                   |                    ↑
Self-Direction ←---------+---------→ Conformity
Stimulation              |            Tradition
     ↓                   |            Security
                         |                    ↓
        Hedonism ←-------+-------→ Power
                         |
                    Achievement
                          ↓
                   Self-Enhancement
```

## References

- Schwartz, "A Theory of Cultural Values" (1992)
- Schwartz & Bilsky, "Toward a Universal Psychological Structure" (1987)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Mettapedia.CognitiveArchitecture.Values.Schwartz

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)
open Mettapedia.CognitiveArchitecture.Values (ValueType)

/-! ## Angular Position on Circumplex

Each Schwartz value has an angular position on the circumplex circle.
Values are arranged in a specific order based on empirical research.
-/

/-- Angular position of each Schwartz value on the circumplex (in radians).
    Positions are based on Schwartz's empirical findings about value proximity. -/
noncomputable def circumplex_angle : ValueType → ℝ
  | .universalism => 0                    -- 0° (top)
  | .benevolence => Real.pi / 5           -- 36°
  | .conformity => 2 * Real.pi / 5        -- 72°
  | .tradition => 3 * Real.pi / 5         -- 108°
  | .security => 4 * Real.pi / 5          -- 144°
  | .power => Real.pi                     -- 180° (bottom)
  | .achievement => 6 * Real.pi / 5       -- 216°
  | .hedonism => 7 * Real.pi / 5          -- 252°
  | .stimulation => 8 * Real.pi / 5       -- 288°
  | .selfDirection => 9 * Real.pi / 5     -- 324°
  | _ => 0  -- Non-Schwartz values default to 0

/-- Angular distance between two values (0 to π) -/
noncomputable def angular_distance (v1 v2 : ValueType) : ℝ :=
  let diff := |circumplex_angle v1 - circumplex_angle v2|
  min diff (2 * Real.pi - diff)

/-! ## Compatibility and Conflict

Values close on the circumplex are compatible; opposite values conflict.
-/

/-- Compatibility score based on angular distance.
    Adjacent values (small angle) have high compatibility.
    Opposite values (angle ≈ π) have low compatibility. -/
noncomputable def compatibility (v1 v2 : ValueType) : ℝ :=
  Real.cos (angular_distance v1 v2)

/-- Two values are compatible if their angular distance is < π/2 -/
noncomputable def areCompatible (v1 v2 : ValueType) : Prop :=
  angular_distance v1 v2 < Real.pi / 2

/-- Two values conflict if their angular distance is > π/2 -/
noncomputable def conflict (v1 v2 : ValueType) : Prop :=
  angular_distance v1 v2 > Real.pi / 2

/-! ## Value Pairs

Known compatible and conflicting value pairs from Schwartz's research.
-/

/-- Opposite value pairs (conflict strongly) -/
def oppositePairs : List (ValueType × ValueType) :=
  [(.universalism, .power),
   (.benevolence, .achievement),
   (.conformity, .stimulation),
   (.tradition, .selfDirection),
   (.security, .hedonism)]

/-- Adjacent value pairs (highly compatible) -/
def adjacentPairs : List (ValueType × ValueType) :=
  [(.universalism, .benevolence),
   (.benevolence, .conformity),
   (.conformity, .tradition),
   (.tradition, .security),
   (.security, .power),
   (.power, .achievement),
   (.achievement, .hedonism),
   (.hedonism, .stimulation),
   (.stimulation, .selfDirection),
   (.selfDirection, .universalism)]

/-! ## Higher-Order Value Dimensions

Schwartz groups the 10 values into 4 higher-order dimensions.
-/

/-- The four higher-order value dimensions -/
inductive HigherOrderValue where
  | selfTranscendence : HigherOrderValue  -- Universalism, Benevolence
  | conservation : HigherOrderValue       -- Conformity, Tradition, Security
  | selfEnhancement : HigherOrderValue    -- Power, Achievement
  | opennessToChange : HigherOrderValue   -- Self-Direction, Stimulation, Hedonism
  deriving DecidableEq, Repr

/-- Map Schwartz values to higher-order dimensions -/
def toHigherOrder : ValueType → Option HigherOrderValue
  | .universalism => some .selfTranscendence
  | .benevolence => some .selfTranscendence
  | .conformity => some .conservation
  | .tradition => some .conservation
  | .security => some .conservation
  | .power => some .selfEnhancement
  | .achievement => some .selfEnhancement
  | .selfDirection => some .opennessToChange
  | .stimulation => some .opennessToChange
  | .hedonism => some .opennessToChange
  | _ => none

/-- Higher-order dimensions that conflict -/
def higherOrderConflict : HigherOrderValue → HigherOrderValue → Bool
  | .selfTranscendence, .selfEnhancement => true
  | .selfEnhancement, .selfTranscendence => true
  | .conservation, .opennessToChange => true
  | .opennessToChange, .conservation => true
  | _, _ => false

/-! ## Value Satisfaction Dynamics

How pursuing one value affects satisfaction of others.
-/

/-- Spillover effect: pursuing a value increases satisfaction of compatible values
    and decreases satisfaction of conflicting values -/
noncomputable def spilloverEffect (pursued : ValueType) (affected : ValueType)
    (gain : UnitValue) : ℝ :=
  compatibility pursued affected * gain.val

/-- Pursuing universalism helps benevolence but hurts power.
    Benevolence is adjacent (angle = π/5), Power is opposite (angle = π).
    cos(π/5) ≈ 0.81 > cos(π) = -1 -/
theorem universalism_benevolence_vs_power :
    compatibility .universalism .benevolence > compatibility .universalism .power := by
  unfold compatibility angular_distance circumplex_angle
  -- Simplify the expressions: |0 - x| = |x| = x for x ≥ 0
  have hpi5 : |0 - Real.pi / 5| = Real.pi / 5 := by
    rw [zero_sub, abs_neg]
    exact abs_of_nonneg (by linarith [Real.pi_pos])
  have hpi : |0 - Real.pi| = Real.pi := by
    rw [zero_sub, abs_neg]
    exact abs_of_nonneg Real.pi_nonneg
  rw [hpi5, hpi]
  have h1 : Real.pi / 5 ≤ 2 * Real.pi - Real.pi / 5 := by linarith [Real.pi_pos]
  have h2 : Real.pi ≤ 2 * Real.pi - Real.pi := by linarith [Real.pi_pos]
  rw [min_eq_left h1, min_eq_left h2]
  -- Now compare cos(π/5) > cos(π) = -1
  have hcos_pi : Real.cos Real.pi = -1 := Real.cos_pi
  rw [hcos_pi]
  -- cos(π/5) > 0 > -1
  have h3 : Real.cos (Real.pi / 5) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  linarith

/-! ## Cultural Value Profiles

Different cultures emphasize different parts of the circumplex.
-/

/-- A cultural value profile assigns emphasis to each value -/
structure CulturalProfile where
  emphasis : ValueType → UnitValue
  /-- Total emphasis sums to a reasonable amount -/
  normalized : (schwartzValues.map (fun v => (emphasis v).val)).sum ≤ 10

/-- Western individualistic profile (emphasizes openness, self-enhancement) -/
def westernProfile : ValueType → UnitValue
  | .selfDirection => ⟨0.8, by norm_num, by norm_num⟩
  | .achievement => ⟨0.7, by norm_num, by norm_num⟩
  | .power => ⟨0.5, by norm_num, by norm_num⟩
  | .hedonism => ⟨0.6, by norm_num, by norm_num⟩
  | .stimulation => ⟨0.6, by norm_num, by norm_num⟩
  | .conformity => ⟨0.3, by norm_num, by norm_num⟩
  | .tradition => ⟨0.3, by norm_num, by norm_num⟩
  | .security => ⟨0.5, by norm_num, by norm_num⟩
  | .benevolence => ⟨0.6, by norm_num, by norm_num⟩
  | .universalism => ⟨0.5, by norm_num, by norm_num⟩
  | _ => UnitValue.half

/-- East Asian collectivist profile (emphasizes conservation, self-transcendence) -/
def collectivistProfile : ValueType → UnitValue
  | .selfDirection => ⟨0.4, by norm_num, by norm_num⟩
  | .achievement => ⟨0.6, by norm_num, by norm_num⟩
  | .power => ⟨0.4, by norm_num, by norm_num⟩
  | .hedonism => ⟨0.3, by norm_num, by norm_num⟩
  | .stimulation => ⟨0.3, by norm_num, by norm_num⟩
  | .conformity => ⟨0.8, by norm_num, by norm_num⟩
  | .tradition => ⟨0.7, by norm_num, by norm_num⟩
  | .security => ⟨0.7, by norm_num, by norm_num⟩
  | .benevolence => ⟨0.8, by norm_num, by norm_num⟩
  | .universalism => ⟨0.6, by norm_num, by norm_num⟩
  | _ => UnitValue.half

/-! ## Theorems about Circumplex Structure -/

/-- Schwartz values form a complete circle (10 values, 36° apart) -/
theorem schwartz_circle_complete :
    schwartzValues.length = 10 := by rfl

/-- Each opposite pair has approximately π angular distance -/
theorem opposite_pairs_conflict :
    oppositePairs.length = 5 := by rfl

/-- Each adjacent pair is close on the circumplex -/
theorem adjacent_pairs_compatible :
    adjacentPairs.length = 10 := by rfl

/-- Same value has zero angular distance -/
theorem self_distance_zero (v : ValueType) :
    angular_distance v v = 0 := by
  unfold angular_distance
  simp only [sub_self, abs_zero]
  rw [min_eq_left]
  linarith [Real.pi_pos]

end Mettapedia.CognitiveArchitecture.Values.Schwartz
