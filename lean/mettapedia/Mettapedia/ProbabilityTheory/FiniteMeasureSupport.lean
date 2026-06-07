import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finite Measure Support Lemmas

Small shared lemmas for finite measurable spaces.  Several probability and
exchangeability bridges need the same fact: finitely many singleton events
partition the universe, so a finite measure is determined by singleton masses.
-/

namespace Mettapedia.ProbabilityTheory.FiniteMeasureSupport

open MeasureTheory
open scoped BigOperators ENNReal

/-- On a finite measurable space, singleton masses add up to the mass of the
whole space. -/
theorem finiteMeasure_univ_eq_sum_singletons
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) :
    μ Set.univ = ∑ a : α, μ ({a} : Set α) := by
  have hpart : Set.univ = ⋃ a : α, ({a} : Set α) := by
    ext a
    simp
  rw [hpart, measure_iUnion
    (by
      intro i j hij
      exact Set.disjoint_singleton.mpr hij)
    (by
      intro i
      exact measurableSet_singleton i),
    tsum_fintype]

/-- A probability measure on a finite measurable space has singleton masses
summing to one. -/
theorem probabilityMeasure_sum_singletons_enn
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : ProbabilityMeasure α) :
    ∑ a : α, ((μ : Measure α) ({a} : Set α)) = 1 := by
  calc
    ∑ a : α, ((μ : Measure α) ({a} : Set α)) =
        (μ : Measure α) Set.univ := by
      exact (finiteMeasure_univ_eq_sum_singletons (μ : Measure α)).symm
    _ = 1 := measure_univ

/-- Coercing a `ProbabilityMeasure` singleton value to `ℝ≥0∞` agrees with
evaluating its underlying measure. -/
theorem probabilityMeasure_coe_singleton
    {α : Type*} [MeasurableSpace α]
    (μ : ProbabilityMeasure α) (a : α) :
    (μ ({a} : Set α) : ℝ≥0∞) = ((μ : Measure α) ({a} : Set α)) :=
  ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ _

end Mettapedia.ProbabilityTheory.FiniteMeasureSupport
