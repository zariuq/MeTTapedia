import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Removing a datum from a weighted sample

A finite collection of weighted samples, drawn under finitely many outcomes with probabilities
`p`, is properly weighted for an unnormalized target `π` when its expected weighted sum is the
target's sum for every test function (`ProperlyWeighted`): the weighted sums are unbiased.

When the full target is the leave-one-out target times the removed datum's likelihood factor `L`,
dividing each weight by the factor at its sample gives a collection properly weighted for the
leave-one-out target, provided the factor vanishes nowhere (`ProperlyWeighted.divideOut`).  Where
it vanishes the full target has no mass and the samples never reach it, so dividing out cannot
recover the leave-one-out target there (`divideOut_fails_at_zero`).

This is the exact change of measure.  It says nothing about the variance of the reweighted sums or
the bias of a self-normalized estimator.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetractionSamples

open scoped NNReal

variable {Ω Θ : Type*} [Fintype Ω] [Fintype Θ] {n : ℕ}

/-- A finite weighted collection is properly weighted for the unnormalized target `π` when, for
every test function, its expected weighted sum is the target's sum. -/
def ProperlyWeighted (p : Ω → ℝ≥0) (θ : Ω → Fin n → Θ) (w : Ω → Fin n → ℝ≥0)
    (π : Θ → ℝ≥0) : Prop :=
  ∀ f : Θ → ℝ≥0, ∑ ω, p ω * ∑ s, w ω s * f (θ ω s) = ∑ t, π t * f t

/-- **Dividing out the likelihood factor of a removed datum** keeps the collection properly
weighted, for the leave-one-out target. -/
theorem ProperlyWeighted.divideOut {p : Ω → ℝ≥0} {θ : Ω → Fin n → Θ} {w : Ω → Fin n → ℝ≥0}
    {π L : Θ → ℝ≥0} (hL : ∀ t, L t ≠ 0) (h : ProperlyWeighted p θ w fun t => π t * L t) :
    ProperlyWeighted p θ (fun ω s => w ω s / L (θ ω s)) π := by
  intro f
  have key := h fun t => f t / L t
  calc ∑ ω, p ω * ∑ s, w ω s / L (θ ω s) * f (θ ω s)
      = ∑ ω, p ω * ∑ s, w ω s * (f (θ ω s) / L (θ ω s)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
    _ = ∑ t, π t * L t * (f t / L t) := key
    _ = ∑ t, π t * f t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_assoc, mul_div_cancel₀ (f t) (hL t)]

/-- **Where the removed factor vanishes, dividing out fails.**  On `Bool` the factor is `0` at
`false`.  The full target puts no mass there, a single sample at `true` is properly weighted for
it, and after dividing out the collection misses the leave-one-out mass at `false`. -/
theorem divideOut_fails_at_zero :
    ∃ (p : Unit → ℝ≥0) (θ : Unit → Fin 1 → Bool) (w : Unit → Fin 1 → ℝ≥0) (π L : Bool → ℝ≥0),
      ProperlyWeighted p θ w (fun t => π t * L t) ∧
        ¬ ProperlyWeighted p θ (fun ω s => w ω s / L (θ ω s)) π := by
  refine ⟨fun _ => 1, fun _ _ => true, fun _ _ => 1, fun _ => 1, fun t => if t then 1 else 0,
    ?_, ?_⟩
  · intro f
    simp
  · intro h
    have missing := h fun t => if t then 0 else 1
    simp at missing

end Mettapedia.PLN.WorldModel.ApproximateRetractionSamples

open Mettapedia.PLN.WorldModel.ApproximateRetractionSamples in
#print axioms ProperlyWeighted.divideOut
open Mettapedia.PLN.WorldModel.ApproximateRetractionSamples in
#print axioms divideOut_fails_at_zero
