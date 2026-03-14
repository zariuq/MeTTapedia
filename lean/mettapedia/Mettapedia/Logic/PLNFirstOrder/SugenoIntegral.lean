import Mettapedia.Logic.PLNFirstOrder.FuzzyMeasureCore

/-!
# Sugeno Integral

Lean-friendly Sugeno-integral core for `[0,1]`-valued fuzzy profiles and
capacity-style fuzzy measures on crisp subsets.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

namespace FuzzyCapacity

variable {U : Type*} [MeasurableSpace U]

/-- Sugeno candidates are the thresholds `t` whose own level is below the capacity
of the corresponding threshold cut. -/
def sugenoCandidates (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Set I :=
  {t | t ≤ ν (FuzzyProfile.thresholdCut t f)}

/-- Sugeno integral of a `[0,1]`-valued fuzzy profile against a capacity. -/
noncomputable def sugenoIntegral (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  sSup (sugenoCandidates ν f)

theorem sugenoIntegral_in_unit (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    ((sugenoIntegral ν f : I) : ℝ) ∈ (I : Set ℝ) :=
  (sugenoIntegral ν f).2

theorem sugenoIntegral_mono
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    sugenoIntegral ν f ≤ sugenoIntegral ν g := by
  unfold sugenoIntegral sugenoCandidates
  refine sSup_le ?_
  intro t ht
  apply le_sSup
  have hcut :
      FuzzyProfile.thresholdCut t f ⊆ FuzzyProfile.thresholdCut t g := by
    intro u hu
    exact le_trans hu (hfg u)
  exact le_trans ht (ν.mono hcut)

omit [MeasurableSpace U] in
/-- Threshold cuts of crisp indicators collapse to either `univ` or the set itself. -/
theorem thresholdCut_crispIndicator
    (t : I) (A : Set U) :
    FuzzyProfile.thresholdCut t (FuzzyProfile.crispIndicator A) =
      if t = 0 then Set.univ else A := by
  ext u
  by_cases ht : t = 0
  · simp [FuzzyProfile.thresholdCut, FuzzyProfile.crispIndicator, ht]
  · have hnot_le_zero : ¬ t ≤ (0 : I) := by
      intro hle
      exact ht (le_antisymm hle bot_le)
    by_cases hu : u ∈ A
    · simp [FuzzyProfile.thresholdCut, FuzzyProfile.crispIndicator, ht, hu]
      exact unitInterval.le_one t
    · simp [FuzzyProfile.thresholdCut, FuzzyProfile.crispIndicator, ht, hu, hnot_le_zero]

/-- Sugeno of a crisp indicator is exactly the capacity of its support. -/
theorem sugenoIntegral_crispIndicator
    (ν : FuzzyCapacity U) (A : Set U) :
    sugenoIntegral ν (FuzzyProfile.crispIndicator A) = ν A := by
  unfold sugenoIntegral sugenoCandidates
  have hset :
      {t : I | t ≤ ν (FuzzyProfile.thresholdCut t (FuzzyProfile.crispIndicator A))} =
        {t : I | t ≤ ν A} := by
    ext t
    constructor
    · intro ht
      by_cases hzero : t = 0
      · subst hzero
        show (0 : I) ≤ ν A
        exact bot_le
      · have hcut :
            ({u | t ≤ (FuzzyProfile.crispIndicator A).eval u} : Set U) = A := by
          simpa [FuzzyProfile.thresholdCut, hzero] using
            thresholdCut_crispIndicator (U := U) t A
        change t ≤ ν A
        simpa [hcut] using ht
    · intro ht
      by_cases hzero : t = 0
      · subst hzero
        show (0 : I) ≤ ν (FuzzyProfile.thresholdCut 0 (FuzzyProfile.crispIndicator A))
        simp
      · have hcut :
            ({u | t ≤ (FuzzyProfile.crispIndicator A).eval u} : Set U) = A := by
          simpa [FuzzyProfile.thresholdCut, hzero] using
            thresholdCut_crispIndicator (U := U) t A
        show t ≤ ν ({u | t ≤ (FuzzyProfile.crispIndicator A).eval u} : Set U)
        simpa [hcut] using ht
  have hsSup :
      sSup ({t : I | t ≤ ν A}) = ν A := by
    apply le_antisymm
    · exact sSup_le_iff.mpr (by intro t ht; exact ht)
    · exact le_sSup (by simp)
  rw [hset]
  exact hsSup

theorem sugenoIntegral_constantZero
    (ν : FuzzyCapacity U) :
    sugenoIntegral ν (FuzzyProfile.const (U := U) (0 : I)) = 0 := by
  simpa [FuzzyProfile.const, FuzzyProfile.crispIndicator, ν.cap_empty] using
    sugenoIntegral_crispIndicator (U := U) ν (∅ : Set U)

theorem sugenoIntegral_constantOne
    (ν : FuzzyCapacity U)
    (hν : IsNormalized ν) :
    sugenoIntegral ν (FuzzyProfile.const (U := U) (1 : I)) = 1 := by
  simpa [FuzzyProfile.const, FuzzyProfile.crispIndicator, IsNormalized] using
    (sugenoIntegral_crispIndicator (U := U) ν (Set.univ : Set U)).trans hν

end FuzzyCapacity

end Mettapedia.Logic.PLNFirstOrder
