import Mettapedia.InformationTheory.FiniteDivergence
import Mettapedia.InformationTheory.ShannonEntropy.Shannon1948
import Mathlib.Data.ENNReal.BigOperators

/-!
# Predictive log loss and finite KL divergence

A real-valued log score is used on the support of the data law.
Probability zero on a possible data outcome gives infinite loss in the
extended-real interpretation, as in `FiniteDivergenceMeasure`.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FiniteRV

variable {X : Type*} [Fintype X]

/-- Expected negative log probability, in nats. -/
noncomputable def crossEntropy (data forecast : Prob X) : ℝ :=
  -∑ x, data.1 x * Real.log (forecast.1 x)

theorem crossEntropy_eq_entropy_add_kl (data forecast : Prob X)
    (support : ∀ x, 0 < data.1 x → 0 < forecast.1 x) :
    crossEntropy data forecast = shannonEntropyFin X data + klSum data.1 forecast.1 := by
  simp only [crossEntropy, shannonEntropyFin, Real.negMulLog, klSum_eq_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases (data.2.1 x).lt_or_eq with positive | zero
  · rw [Real.log_div positive.ne' (support x positive).ne']
    ring
  · simp [← zero]

theorem crossEntropy_self (data : Prob X) :
    crossEntropy data data = shannonEntropyFin X data := by
  rw [crossEntropy_eq_entropy_add_kl data data (fun _ h => h),
    klSum_self_eq_zero _ data.2.1, add_zero]

theorem crossEntropy_min (data forecast : Prob X)
    (support : ∀ x, 0 < data.1 x → 0 < forecast.1 x) :
    crossEntropy data data ≤ crossEntropy data forecast := by
  rw [crossEntropy_self, crossEntropy_eq_entropy_add_kl data forecast support]
  have nonneg := klSumOn_nonneg Finset.univ data.1 forecast.1
    (fun x _ => data.2.1 x) (fun x _ => forecast.2.1 x)
    (fun x _ => support x) (by rw [data.2.2, forecast.2.2])
  exact le_add_of_nonneg_right nonneg

theorem crossEntropy_min_eq_iff (data forecast : Prob X)
    (support : ∀ x, 0 < data.1 x → 0 < forecast.1 x) :
    crossEntropy data forecast = crossEntropy data data ↔ forecast = data := by
  constructor
  · intro equal
    rw [crossEntropy_eq_entropy_add_kl data forecast support, crossEntropy_self] at equal
    have diverges : klSum data.1 forecast.1 = 0 := by linarith
    apply Subtype.ext
    funext x
    exact (klSumOn_eq_zero_imp Finset.univ data.1 forecast.1
      (fun y _ => data.2.1 y) (fun y _ => forecast.2.1 y)
      (fun y _ => support y) (by rw [data.2.2, forecast.2.2])
      diverges x (Finset.mem_univ x)).symm
  · rintro rfl
    rfl

/-- A zero forecast incurs infinite loss on an outcome with positive data
mass. Outcomes outside the data support contribute zero. -/
noncomputable def extendedCrossEntropy (data forecast : Prob X) : ENNReal :=
  ∑ x, if 0 < data.1 x then
    if 0 < forecast.1 x then ENNReal.ofReal (-(data.1 x * Real.log (forecast.1 x))) else ⊤
  else 0

theorem extendedCrossEntropy_eq_top_iff (data forecast : Prob X) :
    extendedCrossEntropy data forecast = ⊤ ↔
      ∃ x, 0 < data.1 x ∧ forecast.1 x = 0 := by
  unfold extendedCrossEntropy
  rw [ENNReal.sum_eq_top]
  constructor
  · rintro ⟨x, _, h⟩
    by_cases hasData : 0 < data.1 x
    · by_cases hasForecast : 0 < forecast.1 x
      · simp [hasData, hasForecast, ENNReal.ofReal_ne_top] at h
      · exact ⟨x, hasData, le_antisymm (le_of_not_gt hasForecast) (forecast.2.1 x)⟩
    · simp [hasData] at h
  · rintro ⟨x, hasData, missing⟩
    exact ⟨x, Finset.mem_univ _, by simp [hasData, missing]⟩

theorem extendedCrossEntropy_eq_ofReal (data forecast : Prob X)
    (support : ∀ x, 0 < data.1 x → 0 < forecast.1 x) :
    extendedCrossEntropy data forecast = ENNReal.ofReal (crossEntropy data forecast) := by
  unfold crossEntropy extendedCrossEntropy
  rw [← Finset.sum_neg_distrib, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro x _
    rcases (data.2.1 x).lt_or_eq with positive | zero
    · simp [positive, support x positive]
    · simp [← zero]
  · intro x _
    have upper : forecast.1 x ≤ 1 :=
      (Finset.single_le_sum (fun y _ => forecast.2.1 y) (Finset.mem_univ x)).trans_eq forecast.2.2
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (data.2.1 x)
      (Real.log_nonpos (forecast.2.1 x) upper))

end Mettapedia.InformationTheory.FiniteRV
