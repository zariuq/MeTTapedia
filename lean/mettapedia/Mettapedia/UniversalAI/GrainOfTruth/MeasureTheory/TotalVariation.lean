import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Real

/-!
# Total Variation Bounds on Finite Spaces

Leike-style arguments frequently bound differences of values by distances between (finite-horizon)
predictive distributions. Since our action/percept alphabets are finite, all fixed-length prefix
spaces are finite, and we can use a simple `Finset`-based `L¹` bound.

This file provides a minimal lemma:

`|∫ f dμ - ∫ f dν| ≤ ∑ x, |μ{x} - ν{x}|`,

for bounded `f : α → ℝ` on a finite type `α`.

This is the “easy direction” behind total-variation/value-difference inequalities used in the
Thompson-sampling optimality proofs.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation

open scoped BigOperators
open MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A simple `L¹`-style distance between two measures on a finite type, using real masses of
singletons. -/
noncomputable def l1DistanceReal (μ ν : MeasureTheory.Measure α) : ℝ :=
  ∑ x : α, |μ.real {x} - ν.real {x}|

theorem abs_integral_sub_integral_le_l1DistanceReal (μ ν : MeasureTheory.Measure α) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1)
    (hμ : MeasureTheory.Integrable f μ) (hν : MeasureTheory.Integrable f ν) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ l1DistanceReal μ ν := by
  classical
  -- Expand integrals as finite sums over singletons.
  have hμ_sum : (∫ x, f x ∂μ) = ∑ x : α, μ.real {x} * f x := by
    simpa [smul_eq_mul] using (MeasureTheory.integral_fintype (μ := μ) (f := f) hμ)
  have hν_sum : (∫ x, f x ∂ν) = ∑ x : α, ν.real {x} * f x := by
    simpa [smul_eq_mul] using (MeasureTheory.integral_fintype (μ := ν) (f := f) hν)

  -- Reduce to a bound on a finite sum.
  have hRewrite :
      (∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x) =
        ∑ x : α, (μ.real {x} - ν.real {x}) * f x := by
    -- This is just linearity of `Finset.sum`.
    calc
      (∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x)
          = ∑ x : α, (μ.real {x} * f x - ν.real {x} * f x) := by
              exact
                (Finset.sum_sub_distrib (s := (Finset.univ : Finset α))
                      (f := fun x : α => μ.real {x} * f x)
                      (g := fun x : α => ν.real {x} * f x)).symm
      _ = ∑ x : α, (μ.real {x} - ν.real {x}) * f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simpa using (sub_mul (μ.real {x}) (ν.real {x}) (f x)).symm

  calc
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)|
        = |(∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x)| := by
            simp [hμ_sum, hν_sum]
    _ = |∑ x : α, (μ.real {x} - ν.real {x}) * f x| := by
          simp [hRewrite]
    _ ≤ ∑ x : α, |(μ.real {x} - ν.real {x}) * f x| := by
          simpa using (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset α))
            (f := fun x : α => (μ.real {x} - ν.real {x}) * f x))
    _ = ∑ x : α, |μ.real {x} - ν.real {x}| * |f x| := by
          simp [abs_mul]
    _ ≤ ∑ x : α, |μ.real {x} - ν.real {x}| * 1 := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have h0 : 0 ≤ |μ.real {x} - ν.real {x}| := abs_nonneg _
          exact mul_le_mul_of_nonneg_left (hf x) h0
    _ = ∑ x : α, |μ.real {x} - ν.real {x}| := by
          simp
    _ = l1DistanceReal μ ν := by
          simp [l1DistanceReal]

theorem abs_integral_sub_integral_le_mul_l1DistanceReal (μ ν : MeasureTheory.Measure α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ x, |f x| ≤ B)
    (hμ : MeasureTheory.Integrable f μ) (hν : MeasureTheory.Integrable f ν) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ B * l1DistanceReal μ ν := by
  classical
  -- Expand integrals as finite sums over singletons.
  have hμ_sum : (∫ x, f x ∂μ) = ∑ x : α, μ.real {x} * f x := by
    simpa [smul_eq_mul] using (MeasureTheory.integral_fintype (μ := μ) (f := f) hμ)
  have hν_sum : (∫ x, f x ∂ν) = ∑ x : α, ν.real {x} * f x := by
    simpa [smul_eq_mul] using (MeasureTheory.integral_fintype (μ := ν) (f := f) hν)

  -- Reduce to a bound on a finite sum.
  have hRewrite :
      (∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x) =
        ∑ x : α, (μ.real {x} - ν.real {x}) * f x := by
    calc
      (∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x)
          = ∑ x : α, (μ.real {x} * f x - ν.real {x} * f x) := by
              exact
                (Finset.sum_sub_distrib (s := (Finset.univ : Finset α))
                      (f := fun x : α => μ.real {x} * f x)
                      (g := fun x : α => ν.real {x} * f x)).symm
      _ = ∑ x : α, (μ.real {x} - ν.real {x}) * f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simpa using (sub_mul (μ.real {x}) (ν.real {x}) (f x)).symm

  calc
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)|
        = |(∑ x : α, μ.real {x} * f x) - (∑ x : α, ν.real {x} * f x)| := by
            simp [hμ_sum, hν_sum]
    _ = |∑ x : α, (μ.real {x} - ν.real {x}) * f x| := by
          simp [hRewrite]
    _ ≤ ∑ x : α, |(μ.real {x} - ν.real {x}) * f x| := by
          simpa using (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset α))
            (f := fun x : α => (μ.real {x} - ν.real {x}) * f x))
    _ = ∑ x : α, |μ.real {x} - ν.real {x}| * |f x| := by
          simp [abs_mul]
    _ ≤ ∑ x : α, |μ.real {x} - ν.real {x}| * B := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have h0 : 0 ≤ |μ.real {x} - ν.real {x}| := abs_nonneg _
          exact mul_le_mul_of_nonneg_left (hf x) h0
    _ = B * ∑ x : α, |μ.real {x} - ν.real {x}| := by
          -- factor out the constant `B`
          calc
            (∑ x : α, |μ.real {x} - ν.real {x}| * B) =
                ∑ x : α, B * |μ.real {x} - ν.real {x}| := by
                  simp [mul_comm]
            _ = B * ∑ x : α, |μ.real {x} - ν.real {x}| := by
                  simp [Finset.mul_sum]
    _ = B * l1DistanceReal μ ν := by
          simp [l1DistanceReal]

theorem l1DistanceReal_le_two_of_isProbability (μ ν : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    l1DistanceReal μ ν ≤ 2 := by
  classical
  -- Pointwise bound `|a - b| ≤ a + b`.
  have hTerm : ∀ x : α, |μ.real {x} - ν.real {x}| ≤ μ.real {x} + ν.real {x} := by
    intro x
    have hμ0 : 0 ≤ μ.real {x} := MeasureTheory.measureReal_nonneg
    have hν0 : 0 ≤ ν.real {x} := MeasureTheory.measureReal_nonneg
    -- Triangle inequality: `|a + b| ≤ |a| + |b|`, then simplify using nonnegativity.
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg hμ0, abs_of_nonneg hν0] using
      (abs_add_le (μ.real {x}) (-ν.real {x}))

  calc
    l1DistanceReal μ ν
        = ∑ x : α, |μ.real {x} - ν.real {x}| := rfl
    _ ≤ ∑ x : α, (μ.real {x} + ν.real {x}) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hTerm x
    _ = (∑ x : α, μ.real {x}) + (∑ x : α, ν.real {x}) := by
          simp [Finset.sum_add_distrib]
    _ = μ.real Set.univ + ν.real Set.univ := by
          -- rewrite the finite sums as real measures of `univ`
          have hμsum : (∑ x : α, μ.real {x}) = μ.real Set.univ := by
            simp
          have hνsum : (∑ x : α, ν.real {x}) = ν.real Set.univ := by
            simp
          simp [hμsum, hνsum]
    _ = 2 := by
          simpa using (one_add_one_eq_two : (1 : ℝ) + 1 = 2)

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation
