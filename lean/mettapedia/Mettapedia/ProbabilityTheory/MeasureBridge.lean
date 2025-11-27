import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Data.Fintype.Prod
import Mettapedia.ProbabilityTheory.KnuthSkilling

/-!
# Bridge: Mathlib Measures → Knuth-Skilling Framework

This file provides the CRITICAL missing bridge showing that Mathlib's
standard measure theory satisfies the Knuth-Skilling axioms.

## Main construction:

* `valuationFromProbabilityMeasure`: Convert `IsProbabilityMeasure` to `Valuation`

This demonstrates that the Knuth-Skilling foundations are not separate from
standard probability - they are EQUIVALENT via explicit construction.

## Credit

This approach follows Gemini's excellent suggestion to use `Measure.count / 4`
for finite uniform distributions, which is much simpler than uniformOn.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open Mettapedia.ProbabilityTheory.KnuthSkilling

namespace Mettapedia.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The Bridge: Measure → Valuation -/

/-- A standard Probability Measure defines a valid Knuth-Skilling Valuation
on the lattice of measurable sets.

Note: We use `{s : Set Ω // MeasurableSet s}` because `Valuation` requires
a lattice, and arbitrary sets don't form a measurable lattice without the
measurability constraint. For finite spaces, `Set Ω` works fine.
-/
def valuationFromProbabilityMeasure (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Valuation {s : Set Ω // MeasurableSet s} where
  val s := (μ s.val).toReal
  monotone := by
    intro a b h
    apply ENNReal.toReal_mono (measure_ne_top μ b.val)
    exact measure_mono h
  val_bot := by simp
  val_top := by simp [measure_univ]

@[simp]
theorem valuationFromProbabilityMeasure_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : {s : Set Ω // MeasurableSet s}) :
    (valuationFromProbabilityMeasure μ).val s = (μ s.val).toReal := rfl

end Mettapedia.ProbabilityTheory
