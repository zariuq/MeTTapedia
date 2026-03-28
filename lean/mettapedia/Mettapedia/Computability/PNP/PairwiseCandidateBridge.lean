import Mettapedia.Computability.PNP.PairwiseSurvivorMoments
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

open scoped BigOperators

/-!
# P vs NP crux: pairwise candidate-hit bounds imply the survivor-moment model

This file bridges one step closer to a Valiant-Vazirani style sampler.  A finite
family of candidate-hit indicators with:

* common marginal hit rate `p`, and
* pairwise off-diagonal correlation bounded by `p^2`,

induces a survivor-count random variable whose first and factorial second
moments satisfy the abstract interface of `PairwiseSurvivorMoments.lean`.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- Total retained-candidate count for one hash choice. -/
def candidateHitCount (hit : α → Ω → ℕ) (ω : Ω) : ℕ :=
  ∑ a : α, hit a ω

omit [DecidableEq α] [DecidableEq Ω] [Nonempty Ω] in
theorem candidateHitCount_sum
    (hit : α → Ω → ℕ)
    (p : ℝ)
    (hmarg : ∀ a : α, ∑ ω : Ω, (hit a ω : ℝ) = Fintype.card Ω * p) :
    ∑ ω : Ω, (candidateHitCount hit ω : ℝ)
      = Fintype.card Ω * (Fintype.card α * p) := by
  calc
    ∑ ω : Ω, (candidateHitCount hit ω : ℝ)
      = ∑ ω : Ω, ∑ a : α, (hit a ω : ℝ) := by
          simp [candidateHitCount]
    _ = ∑ a : α, ∑ ω : Ω, (hit a ω : ℝ) := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, Fintype.card Ω * p := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact hmarg a
    _ = Fintype.card Ω * (Fintype.card α * p) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

omit [Fintype α] [Fintype Ω] [DecidableEq α] [DecidableEq Ω] [Nonempty Ω] in
theorem hit_sq_eq_hit
    (hit : α → Ω → ℕ)
    (h01 : ∀ a : α, ∀ ω : Ω, hit a ω = 0 ∨ hit a ω = 1) :
    ∀ a : α, ∀ ω : Ω, ((hit a ω : ℝ) ^ 2) = (hit a ω : ℝ) := by
  intro a ω
  rcases h01 a ω with h | h <;> rw [h] <;> norm_num

omit [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] in
theorem candidateHitCount_factorial_pointwise
    (hit : α → Ω → ℕ)
    (h01 : ∀ a : α, ∀ ω : Ω, hit a ω = 0 ∨ hit a ω = 1)
    (ω : Ω) :
    ((candidateHitCount hit ω : ℝ) * ((candidateHitCount hit ω : ℝ) - 1))
      =
    Finset.sum ((Finset.univ : Finset α).offDiag)
      (fun ab => (hit ab.1 ω : ℝ) * (hit ab.2 ω : ℝ)) := by
  let x : α → ℝ := fun a => hit a ω
  have hprod :
      (∑ a : α, x a) * ∑ b : α, x b
        =
      ∑ ab : α × α, x ab.1 * x ab.2 := by
    calc
      (∑ a : α, x a) * ∑ b : α, x b
        = ∑ a : α, x a * ∑ b : α, x b := by
            rw [Finset.sum_mul]
      _ = ∑ a : α, ∑ b : α, x a * x b := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.mul_sum]
      _ = ∑ ab : α × α, x ab.1 * x ab.2 := by
            simpa [Finset.univ_product_univ] using
              (Finset.sum_product
                (s := (Finset.univ : Finset α))
                (t := (Finset.univ : Finset α))
                (f := fun ab : α × α => x ab.1 * x ab.2)).symm
  have hsplit :
      (∑ ab : α × α, x ab.1 * x ab.2)
        =
      Finset.sum ((Finset.univ : Finset α).diag) (fun ab => x ab.1 * x ab.2)
        + Finset.sum ((Finset.univ : Finset α).offDiag) (fun ab => x ab.1 * x ab.2) := by
    rw [← Finset.univ_product_univ, ← Finset.diag_union_offDiag (s := (Finset.univ : Finset α))]
    rw [Finset.sum_union (Finset.disjoint_diag_offDiag (Finset.univ : Finset α))]
  have hdiag :
      Finset.sum ((Finset.univ : Finset α).diag) (fun ab => x ab.1 * x ab.2)
        =
      ∑ a : α, x a := by
    calc
      Finset.sum ((Finset.univ : Finset α).diag) (fun ab => x ab.1 * x ab.2)
        = ∑ a : α, x a * x a := by
            simp [Finset.diag, x]
      _ = ∑ a : α, x a := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            dsimp [x]
            simpa [pow_two] using hit_sq_eq_hit hit h01 a ω
  calc
    ((candidateHitCount hit ω : ℝ) * ((candidateHitCount hit ω : ℝ) - 1))
      = (∑ a : α, x a) * ∑ b : α, x b - ∑ a : α, x a := by
          simp [candidateHitCount, x]
          ring
    _ = (∑ ab : α × α, x ab.1 * x ab.2) - ∑ a : α, x a := by
          rw [hprod]
    _ = (Finset.sum ((Finset.univ : Finset α).diag) (fun ab => x ab.1 * x ab.2)
          + Finset.sum ((Finset.univ : Finset α).offDiag) (fun ab => x ab.1 * x ab.2))
          - ∑ a : α, x a := by
          rw [hsplit]
    _ = Finset.sum ((Finset.univ : Finset α).offDiag) (fun ab => x ab.1 * x ab.2) := by
          rw [hdiag]
          ring

omit [DecidableEq Ω] in
theorem candidateHitCount_factorialSecondMoment_le
    (hit : α → Ω → ℕ)
    (h01 : ∀ a : α, ∀ ω : Ω, hit a ω = 0 ∨ hit a ω = 1)
    (p : ℝ)
    (hpair :
      ∀ a b : α, a ≠ b →
        ∑ ω : Ω, (hit a ω : ℝ) * (hit b ω : ℝ) ≤ Fintype.card Ω * p ^ 2) :
    ∑ ω : Ω, (candidateHitCount hit ω : ℝ) * ((candidateHitCount hit ω : ℝ) - 1)
      ≤ Fintype.card Ω * (Fintype.card α * p) ^ 2 := by
  calc
    ∑ ω : Ω, (candidateHitCount hit ω : ℝ) * ((candidateHitCount hit ω : ℝ) - 1)
      = ∑ ω : Ω,
          Finset.sum ((Finset.univ : Finset α).offDiag)
            (fun ab => (hit ab.1 ω : ℝ) * (hit ab.2 ω : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro ω hω
          exact candidateHitCount_factorial_pointwise hit h01 ω
    _ = Finset.sum ((Finset.univ : Finset α).offDiag)
          (fun ab => ∑ ω : Ω, (hit ab.1 ω : ℝ) * (hit ab.2 ω : ℝ)) := by
          rw [Finset.sum_comm]
    _ ≤ Finset.sum ((Finset.univ : Finset α).offDiag)
          (fun _ => Fintype.card Ω * p ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro ab hab
          exact hpair ab.1 ab.2 (Finset.mem_offDiag.1 hab).2.2
    _ = (((Finset.univ : Finset α).offDiag.card : ℝ) * (Fintype.card Ω * p ^ 2)) := by
          simp
    _ = ((Fintype.card α * Fintype.card α - Fintype.card α : ℕ) : ℝ) * (Fintype.card Ω * p ^ 2) := by
          simp [Finset.offDiag_card]
    _ ≤ Fintype.card Ω * (Fintype.card α * p) ^ 2 := by
          have hcoef_nonneg : 0 ≤ (Fintype.card Ω : ℝ) * p ^ 2 := by positivity
          have hcard_nat :
              Fintype.card α * Fintype.card α - Fintype.card α
                ≤ Fintype.card α * Fintype.card α := by
            exact Nat.sub_le _ _
          have hcard :
              (((Fintype.card α * Fintype.card α - Fintype.card α : ℕ) : ℝ))
                ≤ (Fintype.card α : ℝ) * (Fintype.card α : ℝ) := by
            exact_mod_cast hcard_nat
          have hmul :
              (((Fintype.card α * Fintype.card α - Fintype.card α : ℕ) : ℝ)) * ((Fintype.card Ω : ℝ) * p ^ 2)
                ≤ ((Fintype.card α : ℝ) * (Fintype.card α : ℝ)) * ((Fintype.card Ω : ℝ) * p ^ 2) := by
            exact mul_le_mul_of_nonneg_right hcard hcoef_nonneg
          have hrhs :
              ((Fintype.card α : ℝ) * (Fintype.card α : ℝ)) * ((Fintype.card Ω : ℝ) * p ^ 2)
                = Fintype.card Ω * (Fintype.card α * p) ^ 2 := by
            ring
          exact hmul.trans_eq hrhs

/-- Package a candidate-wise pairwise correlation model as a survivor-moment model. -/
def pairwiseCandidateMomentModel
    (hit : α → Ω → ℕ)
    (h01 : ∀ a : α, ∀ ω : Ω, hit a ω = 0 ∨ hit a ω = 1)
    (p : ℝ)
    (hmarg : ∀ a : α, ∑ ω : Ω, (hit a ω : ℝ) = Fintype.card Ω * p)
    (hpair :
      ∀ a b : α, a ≠ b →
        ∑ ω : Ω, (hit a ω : ℝ) * (hit b ω : ℝ) ≤ Fintype.card Ω * p ^ 2) :
    PairwiseSurvivorMomentModel (Ω := Ω) where
  hitCount := candidateHitCount hit
  mean := Fintype.card α * p
  mean_eq := candidateHitCount_sum hit p hmarg
  factorialSecondMoment_le := by
    simpa [candidateHitCount, mul_assoc, mul_left_comm, mul_comm]
      using candidateHitCount_factorialSecondMoment_le hit h01 p hpair

end

end Mettapedia.Computability.PNP
