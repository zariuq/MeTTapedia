import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemantics
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# Fuzzy Quantifiers on ITV Coordinates

Direct bridge between Chapter-11 fuzzy quantifier interval semantics and ITV-coordinate
profiles (`lower`, `upper`, `strength`, `credibility`, `width`).
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.PLNIndefiniteTruth

section Coordinates

variable {U : Type*} [Fintype U]

/-- ITV lower-coordinate profile. -/
def itvLowerProfile (itvs : U → ITV) : U → ℝ := fun u => (itvs u).lower

/-- ITV upper-coordinate profile. -/
def itvUpperProfile (itvs : U → ITV) : U → ℝ := fun u => (itvs u).upper

/-- ITV midpoint-strength profile. -/
noncomputable def itvStrengthProfile (itvs : U → ITV) : U → ℝ := fun u => (itvs u).strength

/-- ITV credibility profile. -/
def itvCredibilityProfile (itvs : U → ITV) : U → ℝ := fun u => (itvs u).credibility

/-- ITV width profile. -/
noncomputable def itvWidthProfile (itvs : U → ITV) : U → ℝ := fun u => (itvs u).width

/-- Complemented ITV strength profile (`1 - strength`), used by the Ch.11
quantifier-exchange bridge in fuzzy semantics. -/
noncomputable def itvStrengthComplementProfile (itvs : U → ITV) : U → ℝ :=
  fun u => 1 - (itvStrengthProfile itvs u)

theorem nearOneFraction_lower_le_strength
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    nearOneFraction p (itvLowerProfile itvs) ≤ nearOneFraction p (itvStrengthProfile itvs) := by
  apply nearOneFraction_mono_of_pointwise
  · intro u
    change (itvs u).lower ≤ (itvs u).strength
    unfold ITV.strength
    linarith [(itvs u).lower_le_upper]
  · intro u
    exact (ITV.strength_in_unit (itvs u)).2

theorem nearOneFraction_strength_le_upper
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    nearOneFraction p (itvStrengthProfile itvs) ≤ nearOneFraction p (itvUpperProfile itvs) := by
  apply nearOneFraction_mono_of_pointwise
  · intro u
    change (itvs u).strength ≤ (itvs u).upper
    unfold ITV.strength
    linarith [(itvs u).lower_le_upper]
  · intro u
    exact (itvs u).upper_in_unit.2

/-- Main Ch.11 bridge bundle:
if lower and upper coordinate profiles satisfy the fuzzy interval, then midpoint-strength
does too. -/
theorem fuzzyIntervalHolds_strength_of_lower_upper
    (p : FuzzyQuantifierParams) (itvs : U → ITV)
    (hLower : fuzzyIntervalHolds p (itvLowerProfile itvs))
    (hUpper : fuzzyIntervalHolds p (itvUpperProfile itvs)) :
    fuzzyIntervalHolds p (itvStrengthProfile itvs) := by
  refine ⟨?_, ?_⟩
  · exact le_trans hLower.1 (nearOneFraction_lower_le_strength p itvs)
  · exact le_trans (nearOneFraction_strength_le_upper p itvs) hUpper.2

/-- Coordinate-specialized wrapper: lower profile. -/
theorem fuzzyIntervalHolds_itvLower
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyIntervalHolds p (itvLowerProfile itvs) ↔
      (p.LPC ≤ nearOneFraction p (itvLowerProfile itvs) ∧
        nearOneFraction p (itvLowerProfile itvs) ≤ p.UPC) := Iff.rfl

/-- Coordinate-specialized wrapper: upper profile. -/
theorem fuzzyIntervalHolds_itvUpper
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyIntervalHolds p (itvUpperProfile itvs) ↔
      (p.LPC ≤ nearOneFraction p (itvUpperProfile itvs) ∧
        nearOneFraction p (itvUpperProfile itvs) ≤ p.UPC) := Iff.rfl

/-- Coordinate-specialized wrapper: strength profile. -/
theorem fuzzyIntervalHolds_itvStrength
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyIntervalHolds p (itvStrengthProfile itvs) ↔
      (p.LPC ≤ nearOneFraction p (itvStrengthProfile itvs) ∧
        nearOneFraction p (itvStrengthProfile itvs) ≤ p.UPC) := Iff.rfl

/-- Coordinate-specialized wrapper: credibility profile. -/
theorem fuzzyIntervalHolds_itvCredibility
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyIntervalHolds p (itvCredibilityProfile itvs) ↔
      (p.LPC ≤ nearOneFraction p (itvCredibilityProfile itvs) ∧
        nearOneFraction p (itvCredibilityProfile itvs) ≤ p.UPC) := Iff.rfl

/-- Coordinate-specialized wrapper: width profile. -/
theorem fuzzyIntervalHolds_itvWidth
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyIntervalHolds p (itvWidthProfile itvs) ↔
      (p.LPC ≤ nearOneFraction p (itvWidthProfile itvs) ∧
        nearOneFraction p (itvWidthProfile itvs) ≤ p.UPC) := Iff.rfl

/-- ITV-path existential generalization on strength coordinate:
one near-one witness yields strictly positive fuzzy existential score. -/
theorem fuzzyExistsScore_pos_of_itvStrengthWitness
    [Nonempty U]
    (p : FuzzyQuantifierParams) (itvs : U → ITV) (c : U)
    (hc : nearOne p ((itvStrengthProfile itvs) c)) :
    0 < fuzzyExistsScore p (itvStrengthProfile itvs) :=
  fuzzyExistsScore_pos_of_witness_nearOne p (itvStrengthProfile itvs) c hc

/-- ITV-path universal specification on strength coordinate at `PCL = 1`. -/
theorem nearOne_itvStrength_of_fuzzyForAll_eq_one
    [Nonempty U]
    (p : FuzzyQuantifierParams) (itvs : U → ITV) (c : U)
    (hForAll : fuzzyForAllHolds p (itvStrengthProfile itvs))
    (hPCL : p.PCL = 1) :
    nearOne p ((itvStrengthProfile itvs) c) :=
  nearOne_of_fuzzyForAll_eq_one p (itvStrengthProfile itvs) c hForAll hPCL

/-- ITV-path quantifier-exchange bridge on strength coordinate:
`ThereExists` is equivalent to the complemented `nearOne`-mass inequality. -/
theorem fuzzyThereExistsHolds_itvStrength_iff_exchange
    (p : FuzzyQuantifierParams) (itvs : U → ITV) :
    fuzzyThereExistsHolds p (itvStrengthProfile itvs) ↔
      p.PCL ≤ 1 - nearOneFraction p (itvStrengthComplementProfile itvs) := by
  change fuzzyThereExistsHolds p (itvStrengthProfile itvs) ↔
    p.PCL ≤ 1 - nearOneFraction p (fun u => 1 - itvStrengthProfile itvs u)
  exact
    fuzzyThereExistsHolds_iff_nearOneComplement
      (p := p) (profile := itvStrengthProfile itvs)

/-- Core Chapter-11 rule-family bridge in ITV form (strength coordinate):
existential generalization + universal specification + exchange. -/
theorem ch11_itv_rule_family_core
    [Nonempty U]
    (p : FuzzyQuantifierParams) (itvs : U → ITV) (c : U) :
    (nearOne p ((itvStrengthProfile itvs) c) →
      0 < fuzzyExistsScore p (itvStrengthProfile itvs)) ∧
      ((fuzzyForAllHolds p (itvStrengthProfile itvs) →
          p.PCL = 1 →
          nearOne p ((itvStrengthProfile itvs) c)) ∧
        (fuzzyThereExistsHolds p (itvStrengthProfile itvs) ↔
          p.PCL ≤ 1 - nearOneFraction p (itvStrengthComplementProfile itvs))) := by
  refine ⟨?_, ?_⟩
  · intro hWitness
    exact fuzzyExistsScore_pos_of_itvStrengthWitness p itvs c hWitness
  · refine ⟨?_, ?_⟩
    · intro hForAll hPCL
      exact nearOne_itvStrength_of_fuzzyForAll_eq_one p itvs c hForAll hPCL
    · exact fuzzyThereExistsHolds_itvStrength_iff_exchange p itvs

end Coordinates

end Mettapedia.Logic.PLNFirstOrder
