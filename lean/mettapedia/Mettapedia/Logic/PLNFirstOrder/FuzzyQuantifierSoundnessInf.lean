import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsInf

/-!
# Arbitrary-Domain Fuzzy Quantifier Soundness

Theorem surface for the general-domain fuzzy quantifier layer.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

variable {U : Type*} [MeasurableSpace U]

/-- The arbitrary-domain fuzzy existential score is exactly the near-one mass. -/
theorem main_theorem_1_fuzzy_exists_is_nearOneMass_inf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    fuzzyExistsScoreInf p ν f = nearOneMassInf p ν f :=
  rfl

/-- Monotonicity of the arbitrary-domain fuzzy existential score. -/
theorem main_theorem_2_fuzzy_monotonicity_inf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    fuzzyExistsScoreInf p ν f ≤ fuzzyExistsScoreInf p ν g :=
  fuzzyExistsScoreInf_mono_of_pointwise p ν f g hfg

/-- Complement transport for arbitrary-domain fuzzy existential semantics. -/
theorem main_theorem_3_fuzzy_complement_transport_inf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    fuzzyThereExistsHoldsInf p ν f ↔
      p.PCL ≤ 1 - (nearOneMassInf p ν (FuzzyProfile.compl f) : ℝ) :=
  fuzzyThereExistsHoldsInf_iff_nearOneComplement p ν f

/-- Signature invariance of interval truth in the arbitrary-domain fuzzy semantics. -/
theorem main_theorem_4_fuzzy_signature_invariance_inf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hSig : ∀ u, nearOneInf p (f u : ℝ) ↔ nearOneInf p (g u : ℝ)) :
    fuzzyIntervalHoldsInf p ν f ↔ fuzzyIntervalHoldsInf p ν g :=
  fuzzyIntervalHoldsInf_iff_of_signatureEq p ν f g hSig

/-- Sugeno aggregation is monotone in the profile. -/
theorem main_theorem_5_sugeno_monotonicity_inf
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    sugenoScoreInf ν f ≤ sugenoScoreInf ν g :=
  sugenoScoreInf_mono ν f g hfg

omit [MeasurableSpace U] in
/-- The near-one cut of the constant-one profile is the whole domain. -/
theorem nearOneCutInf_constantOne
    (p : FuzzyQuantifierParamsInf) :
    nearOneCutInf p (FuzzyProfile.const (U := U) (1 : I)) = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    change nearOneInf p (1 : ℝ)
    constructor
    · linarith [p.hε.1]
    · norm_num

omit [MeasurableSpace U] in
/-- The near-zero cut of the constant-zero profile is the whole domain. -/
theorem nearZeroCutInf_constantZero
    (p : FuzzyQuantifierParamsInf) :
    nearZeroCutInf p (FuzzyProfile.const (U := U) (0 : I)) = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    change nearZeroInf p (0 : ℝ)
    constructor
    · norm_num
    · exact p.hε.1

/-- Constant-one profiles have near-one mass equal to the capacity of the whole domain. -/
theorem nearOneMassInf_constantOne_eq_cap_univ
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) :
    nearOneMassInf p ν (FuzzyProfile.const (U := U) (1 : I)) = ν Set.univ := by
  unfold nearOneMassInf
  rw [nearOneCutInf_constantOne]

/-- At `ε = 0`, the near-one mass of a crisp indicator is exactly the capacity of its support. -/
theorem nearOneMassInf_crispIndicator_eq_cap_of_epsilon_zero
    (p : FuzzyQuantifierParamsInf) (hε : p.ε = 0)
    (ν : FuzzyCapacity U) (A : Set U) :
    nearOneMassInf p ν (FuzzyProfile.crispIndicator A) = ν A := by
  unfold nearOneMassInf nearOneCutInf
  congr 1
  ext u
  by_cases hu : u ∈ A
  · simp [FuzzyProfile.crispIndicator, nearOneInf, hε, hu]
  · simp [FuzzyProfile.crispIndicator, nearOneInf, hε, hu]

/-- Constant-zero profiles have near-zero mass equal to the capacity of the whole domain. -/
theorem nearZeroMassInf_constantZero_eq_cap_univ
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) :
    nearZeroMassInf p ν (FuzzyProfile.const (U := U) (0 : I)) = ν Set.univ := by
  unfold nearZeroMassInf
  rw [nearZeroCutInf_constantZero]

/-- Constant-one profiles have maximal near-one mass for normalized capacities. -/
theorem nearOneMassInf_constantOne_eq_one
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (hν : FuzzyCapacity.IsNormalized ν) :
    nearOneMassInf p ν (FuzzyProfile.const (U := U) (1 : I)) = 1 := by
  rw [nearOneMassInf_constantOne_eq_cap_univ]
  exact hν

/-- Constant-zero profiles have maximal near-zero mass for normalized capacities. -/
theorem nearZeroMassInf_constantZero_eq_one
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (hν : FuzzyCapacity.IsNormalized ν) :
    nearZeroMassInf p ν (FuzzyProfile.const (U := U) (0 : I)) = 1 := by
  rw [nearZeroMassInf_constantZero_eq_cap_univ]
  exact hν

/-- Constant-zero Sugeno score is bottom. -/
theorem sugenoScoreInf_constantZero_eq_zero
    (ν : FuzzyCapacity U) :
    sugenoScoreInf ν (FuzzyProfile.const (U := U) (0 : I)) = 0 :=
  FuzzyCapacity.sugenoIntegral_constantZero ν

/-- Constant-one Sugeno score is top for normalized capacities. -/
theorem sugenoScoreInf_constantOne_eq_one
    (ν : FuzzyCapacity U) (hν : FuzzyCapacity.IsNormalized ν) :
    sugenoScoreInf ν (FuzzyProfile.const (U := U) (1 : I)) = 1 :=
  FuzzyCapacity.sugenoIntegral_constantOne ν hν

end Mettapedia.Logic.PLNFirstOrder
