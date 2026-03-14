import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSoundnessInf

/-!
# Arbitrary-Domain Fuzzy Quantifier Canary Suite

Concrete canaries for the infinitary fuzzy quantifier layer over a genuinely
infinite domain (`Nat`).
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Classical
open scoped unitInterval

instance : MeasurableSpace Nat := ⊤

/-- The unit-interval midpoint, used by the Nat canary capacity. -/
noncomputable def halfI : I := ⟨(1 / 2 : ℝ), by norm_num⟩

/-- Infinite support used for the main Nat canary profile. -/
def natEvenRange : Set Nat :=
  Set.range (fun n : Nat => 2 * n)

/-- Main infinite-domain crisp profile: true on infinitely many even numbers. -/
noncomputable def natParityProfile : FuzzyProfile Nat :=
  FuzzyProfile.crispIndicator natEvenRange

/-- Finite-support contrast profile: true only at `0`. -/
noncomputable def natSingletonProfile : FuzzyProfile Nat :=
  FuzzyProfile.crispIndicator ({0} : Set Nat)

/-- Normalized capacity with three levels:
`0` on empty sets, `1/2` on nonempty finite sets, and `1` on infinite sets. -/
noncomputable def natThreeLevelCapFn (A : Set Nat) : I := by
  classical
  exact if hInf : A.Infinite then
    (1 : I)
  else if hNe : A.Nonempty then
    halfI
  else
    (0 : I)

@[simp] theorem natThreeLevelCapFn_empty :
    natThreeLevelCapFn (∅ : Set Nat) = 0 := by
  classical
  simp [natThreeLevelCapFn]

theorem natThreeLevelCapFn_eq_one_of_infinite
    {A : Set Nat} (hAinf : A.Infinite) :
    natThreeLevelCapFn A = 1 := by
  classical
  simp [natThreeLevelCapFn, hAinf]

theorem natThreeLevelCapFn_eq_half_of_finite_nonempty
    {A : Set Nat} (hAfin : A.Finite) (hAne : A.Nonempty) :
    natThreeLevelCapFn A = halfI := by
  classical
  have hAinf : ¬ A.Infinite := hAfin.not_infinite
  simp [natThreeLevelCapFn, hAinf, hAne]

theorem natThreeLevelCapFn_mono
    {A B : Set Nat} (hAB : A ⊆ B) :
    natThreeLevelCapFn A ≤ natThreeLevelCapFn B := by
  classical
  by_cases hAinf : A.Infinite
  · rw [natThreeLevelCapFn_eq_one_of_infinite hAinf]
    rw [natThreeLevelCapFn_eq_one_of_infinite (hAinf.mono hAB)]
  · by_cases hAne : A.Nonempty
    · have hA : natThreeLevelCapFn A = halfI := by
        simp [natThreeLevelCapFn, hAinf, hAne]
      have hBne : B.Nonempty := hAne.mono hAB
      by_cases hBinf : B.Infinite
      · rw [hA, natThreeLevelCapFn_eq_one_of_infinite hBinf]
        change ((halfI : I) : ℝ) ≤ ((1 : I) : ℝ)
        norm_num [halfI]
      · have hB : natThreeLevelCapFn B = halfI := by
          simp [natThreeLevelCapFn, hBinf, hBne]
        rw [hA, hB]
    · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hAne
      subst hAempty
      rw [natThreeLevelCapFn_empty]
      change (0 : ℝ) ≤ (natThreeLevelCapFn B : ℝ)
      exact unitInterval.nonneg (natThreeLevelCapFn B)

noncomputable def natThreeLevelCapacity : FuzzyCapacity Nat where
  cap := natThreeLevelCapFn
  cap_empty := natThreeLevelCapFn_empty
  mono := by
    intro A B hAB
    exact natThreeLevelCapFn_mono hAB

theorem natThreeLevelCapacity_isNormalized :
    FuzzyCapacity.IsNormalized natThreeLevelCapacity := by
  unfold FuzzyCapacity.IsNormalized natThreeLevelCapacity
  simpa using
    natThreeLevelCapFn_eq_one_of_infinite (A := Set.univ) Set.infinite_univ

/-- Chapter-11 parameters for the Nat canaries. -/
noncomputable def natProxyParams : FuzzyQuantifierParamsInf where
  ε := 0
  LPC := 1 / 2
  UPC := 1
  PCL := 1 / 2
  hε := by constructor <;> norm_num
  hLPC := by constructor <;> norm_num
  hUPC := by constructor <;> norm_num
  hPCL := by constructor <;> norm_num
  hLPC_le_UPC := by norm_num

theorem natEvenRange_infinite : natEvenRange.Infinite := by
  simpa [natEvenRange] using
    (Set.infinite_range_of_injective (f := fun n : Nat => 2 * n) (by
      intro a b h
      exact (Nat.mul_left_cancel_iff (by norm_num : 0 < (2 : Nat))).mp h))

theorem natThreeLevelCapacity_evenRange_eq_one :
    natThreeLevelCapacity natEvenRange = 1 := by
  show natThreeLevelCapFn natEvenRange = 1
  exact natThreeLevelCapFn_eq_one_of_infinite natEvenRange_infinite

theorem natThreeLevelCapacity_singleton_eq_half :
    natThreeLevelCapacity ({0} : Set Nat) = halfI := by
  show natThreeLevelCapFn ({0} : Set Nat) = halfI
  exact natThreeLevelCapFn_eq_half_of_finite_nonempty
    (A := ({0} : Set Nat)) (by simp) (by simp)

theorem natSingleton_le_constOne (n : Nat) :
    natSingletonProfile n ≤ FuzzyProfile.const (U := Nat) (1 : I) n := by
  by_cases hn : n = 0
  · simp [natSingletonProfile, FuzzyProfile.crispIndicator, FuzzyProfile.const, hn]
  · simp [natSingletonProfile, FuzzyProfile.crispIndicator, FuzzyProfile.const, hn]

/-- De Morgan / complement transport canary on a genuinely infinite domain. -/
theorem canary_inf_fuzzy_nat_deMorgan :
    fuzzyThereExistsHoldsInf natProxyParams natThreeLevelCapacity natParityProfile ↔
      natProxyParams.PCL ≤
        1 - (nearOneMassInf natProxyParams natThreeLevelCapacity
          (FuzzyProfile.compl natParityProfile) : ℝ) :=
  main_theorem_3_fuzzy_complement_transport_inf
    natProxyParams natThreeLevelCapacity natParityProfile

/-- Monotonicity canary on an infinite domain. -/
theorem canary_inf_fuzzy_nat_monotonicity :
    fuzzyExistsScoreInf natProxyParams natThreeLevelCapacity natSingletonProfile ≤
      fuzzyExistsScoreInf natProxyParams natThreeLevelCapacity
        (FuzzyProfile.const (U := Nat) (1 : I)) :=
  main_theorem_2_fuzzy_monotonicity_inf
    natProxyParams
    natThreeLevelCapacity
    natSingletonProfile
    (FuzzyProfile.const (U := Nat) (1 : I))
    natSingleton_le_constOne

/-- Constant-profile canary for the infinitary fuzzy layer. -/
theorem canary_inf_fuzzy_nat_constant_one :
    nearOneMassInf natProxyParams natThreeLevelCapacity
        (FuzzyProfile.const (U := Nat) (1 : I)) = 1 ∧
      sugenoScoreInf natThreeLevelCapacity (FuzzyProfile.const (U := Nat) (1 : I)) = 1 := by
  constructor
  · exact nearOneMassInf_constantOne_eq_one
      natProxyParams natThreeLevelCapacity natThreeLevelCapacity_isNormalized
  · exact sugenoScoreInf_constantOne_eq_one
      natThreeLevelCapacity natThreeLevelCapacity_isNormalized

/-- The infinitary Nat canary distinguishes infinite and finite supports honestly. -/
theorem canary_inf_fuzzy_nat_support_contrast :
    nearOneMassInf natProxyParams natThreeLevelCapacity natParityProfile = 1 ∧
      nearOneMassInf natProxyParams natThreeLevelCapacity natSingletonProfile = halfI := by
  constructor
  · calc
      nearOneMassInf natProxyParams natThreeLevelCapacity natParityProfile
        = natThreeLevelCapacity natEvenRange := by
            simpa [natParityProfile] using
              nearOneMassInf_crispIndicator_eq_cap_of_epsilon_zero
                natProxyParams rfl natThreeLevelCapacity natEvenRange
      _ = 1 := natThreeLevelCapacity_evenRange_eq_one
  · calc
      nearOneMassInf natProxyParams natThreeLevelCapacity natSingletonProfile
        = natThreeLevelCapacity ({0} : Set Nat) := by
            simpa [natSingletonProfile] using
              nearOneMassInf_crispIndicator_eq_cap_of_epsilon_zero
                natProxyParams rfl natThreeLevelCapacity ({0} : Set Nat)
      _ = halfI := natThreeLevelCapacity_singleton_eq_half

end Mettapedia.Logic.PLNFirstOrder
