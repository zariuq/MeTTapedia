import Mettapedia.Logic.UniversalPrediction

/-!
# Anytime Universal-Mixture Approximation

This file packages a simple *anytime* approximation interface for the Chapter-3
universal mixture:

- `xiApproxFun ν w n x` = finite-prefix approximation using the first `n` mixture terms
- `xiApproxSemimeasure ν w hw n` = the corresponding finite semimeasure

The approximation is computationally meaningful:
- increasing `n` only adds nonnegative mixture mass,
- each finite approximation is still a semimeasure,
- and every approximation is bounded by the full mixture.

This is the right first interface for incremental Solomonoff-style
approximations: a resource parameter `n` gives a usable partial model whose
mass estimates improve monotonically toward the full mixture.
-/

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open scoped BigOperators

/-- Finite-prefix approximation of the universal mixture:
use only the first `n` weighted semimeasures. -/
noncomputable def xiApproxFun
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal) (n : ℕ) (x : BinString) : ENNReal :=
  Finset.sum (Finset.range n) (fun i => w i * ν i x)

theorem xiApproxFun_zero
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal) (x : BinString) :
    xiApproxFun ν w 0 x = 0 := by
  simp [xiApproxFun]

theorem xiApproxFun_succ
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal) (n : ℕ) (x : BinString) :
    xiApproxFun ν w (n + 1) x = xiApproxFun ν w n x + w n * ν n x := by
  simp [xiApproxFun, Finset.sum_range_succ, add_comm]

theorem xiApproxFun_mono
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    {n m : ℕ} (hnm : n ≤ m) (x : BinString) :
    xiApproxFun ν w n x ≤ xiApproxFun ν w m x := by
  induction hnm with
  | refl =>
      rfl
  | @step m hnm ih =>
      calc
        xiApproxFun ν w n x ≤ xiApproxFun ν w m x := ih
        _ ≤ xiApproxFun ν w (m + 1) x := by
              rw [xiApproxFun_succ]
              exact le_add_of_nonneg_right (by simp)

theorem xiApprox_root_le_sum_weights
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal) (n : ℕ) :
    xiApproxFun ν w n [] ≤ Finset.sum (Finset.range n) w := by
  unfold xiApproxFun
  refine Finset.sum_le_sum ?_
  intro i hi
  simpa using mul_le_mul_right ((ν i).root_le_one') (w i)

theorem xiApproxFun_le_xiFun
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal) (n : ℕ) (x : BinString) :
    xiApproxFun ν w n x ≤ xiFun ν w x := by
  unfold xiApproxFun xiFun
  simpa using (ENNReal.sum_le_tsum (s := Finset.range n) (f := fun i : ℕ => w i * ν i x))

/-- Finite-prefix semimeasure approximation to the full universal mixture. -/
noncomputable def xiApproxSemimeasure
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1) (n : ℕ) : Semimeasure where
  toFun := xiApproxFun ν w n
  superadditive' := by
    intro x
    unfold xiApproxFun
    calc
      Finset.sum (Finset.range n) (fun i => w i * ν i (x ++ [false])) +
          Finset.sum (Finset.range n) (fun i => w i * ν i (x ++ [true]))
          = Finset.sum (Finset.range n)
              (fun i => w i * ν i (x ++ [false]) + w i * ν i (x ++ [true])) := by
                rw [Finset.sum_add_distrib]
      _ ≤ Finset.sum (Finset.range n) (fun i => w i * ν i x) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            calc
              w i * ν i (x ++ [false]) + w i * ν i (x ++ [true])
                  = w i * (ν i (x ++ [false]) + ν i (x ++ [true])) := by
                      rw [mul_add]
              _ ≤ w i * ν i x := by
                  exact mul_le_mul_right ((ν i).superadditive' x) (w i)
  root_le_one' := by
    have hroot : xiApproxFun ν w n [] ≤ Finset.sum (Finset.range n) w :=
      xiApprox_root_le_sum_weights ν w n
    have hsum : Finset.sum (Finset.range n) w ≤ ∑' i, w i := by
      simpa using (ENNReal.sum_le_tsum (s := Finset.range n) (f := w))
    exact hroot.trans (hsum.trans hw)

theorem xiApproxSemimeasure_mono
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) (x : BinString) :
    (xiApproxSemimeasure ν w hw n) x ≤ (xiApproxSemimeasure ν w hw m) x := by
  exact xiApproxFun_mono ν w hnm x

theorem xiApproxSemimeasure_le_full
    (ν : ℕ → Semimeasure) (w : ℕ → ENNReal)
    (hw : (∑' i, w i) ≤ 1)
    (n : ℕ) (x : BinString) :
    (xiApproxSemimeasure ν w hw n) x ≤ (xiSemimeasure ν w hw) x := by
  exact xiApproxFun_le_xiFun ν w n x

/-- Canonical geometric anytime approximation to the Chapter-3 mixture. -/
noncomputable def xiGeomApproxSemimeasure
    (ν : ℕ → Semimeasure) (n : ℕ) : Semimeasure :=
  xiApproxSemimeasure ν geometricWeight tsum_geometricWeight_le_one n

theorem xiGeomApproxSemimeasure_mono
    (ν : ℕ → Semimeasure) {n m : ℕ} (hnm : n ≤ m) (x : BinString) :
    (xiGeomApproxSemimeasure ν n) x ≤ (xiGeomApproxSemimeasure ν m) x := by
  exact xiApproxSemimeasure_mono ν geometricWeight tsum_geometricWeight_le_one hnm x

theorem xiGeomApproxSemimeasure_le_full
    (ν : ℕ → Semimeasure) (n : ℕ) (x : BinString) :
    (xiGeomApproxSemimeasure ν n) x ≤ (xiGeomSemimeasure ν) x := by
  exact xiApproxSemimeasure_le_full ν geometricWeight tsum_geometricWeight_le_one n x

end Mettapedia.Logic.UniversalPrediction
