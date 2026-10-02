import Mettapedia.InformationTheory.ConditionalMutualInformation
import KnuthSkilling.Information.DivergenceMathlib

/-!
# Extended-valued meaning of finite divergence

The finite real divergence agrees with Mathlib's measure divergence on its
absolute-continuity domain. Unsupported atoms instead give infinite measure
divergence; the total real logarithm's value at zero must not hide that case.
The measure construction is the existing Knuth–Skilling discrete bridge.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Finset
open MeasureTheory
open KnuthSkilling.Information.Divergence
open KnuthSkilling.Information.Divergence.Countable
open scoped ENNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem divergenceCountable_eq_klSum (p q : Prob S) :
    divergenceInfCountable p.1 q.1 = klSum p.1 q.1 := by
  classical
  have atom : ∀ s, atomDivergenceExt (p.1 s) (q.1 s) =
      q.1 s - p.1 s + p.1 s * Real.log (p.1 s / q.1 s) := by
    intro s
    by_cases zero : p.1 s = 0
    · simp [atomDivergenceExt, zero]
    · simp [atomDivergenceExt, zero]
  simp only [divergenceInfCountable, tsum_fintype, atom, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, p.2.2, q.2.2, sub_self, zero_add, klSum, klSumOn]

theorem klDiv_eq_ofReal_klSum (p q : Prob S) (supported : ∀ s, 0 < p.1 s → 0 < q.1 s) :
    _root_.InformationTheory.klDiv (toMeasure p.1) (toMeasure q.1) =
      ENNReal.ofReal (klSum p.1 q.1) := by
  rw [← divergenceCountable_eq_klSum]
  exact klDiv_toMeasure_eq_ofReal_divergenceInfCountable p.1 q.1 p.2.1 q.2.1
    (fun s nonzero => supported s (lt_of_le_of_ne (p.2.1 s) (Ne.symm nonzero)))
    (hasSum_fintype _).summable (hasSum_fintype _).summable (hasSum_fintype _).summable

/-- A positive atom outside the reference support has infinite divergence. -/
theorem klDiv_top_of_unsupported (p q : Prob S) (s : S)
    (positive : 0 < p.1 s) (zero : q.1 s = 0) :
    _root_.InformationTheory.klDiv (toMeasure p.1) (toMeasure q.1) = ⊤ := by
  apply _root_.InformationTheory.klDiv_of_not_ac
  intro continuous
  have nullReference : toMeasure q.1 {s} = 0 := by simp [zero]
  have nullSource := continuous nullReference
  rw [toMeasure_apply_singleton] at nullSource
  exact (ENNReal.ofReal_pos.mpr positive).ne' nullSource

end Mettapedia.InformationTheory.FiniteRV
