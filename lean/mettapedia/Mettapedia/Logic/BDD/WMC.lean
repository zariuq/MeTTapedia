import Mettapedia.Logic.BDD.Core
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# BDD Weighted Model Counting — Correctness

## Main result
`bdd_wmc_correct` — for well-formed BDD `f`, `bdd_wmc f env = weightedSat f.eval env`.

## References
- ProbMeTTa `lib_bdd.metta`, function `bdd-wmc`
- Bryant (1986), "Graph-Based Algorithms for Boolean Function Manipulation"
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Finset

noncomputable def varWeight (env : Fin n → ℝ≥0∞) (i : Fin n) (b : Bool) : ℝ≥0∞ :=
  if b then env i else 1 - env i

noncomputable def assignmentWeight (env : Fin n → ℝ≥0∞) (a : Fin n → Bool) : ℝ≥0∞ :=
  Finset.univ.prod (fun i => varWeight env i (a i))

@[simp] theorem varWeight_true (env : Fin n → ℝ≥0∞) (i : Fin n) :
    varWeight env i true = env i := if_pos rfl

@[simp] theorem varWeight_false (env : Fin n → ℝ≥0∞) (i : Fin n) :
    varWeight env i false = 1 - env i := if_neg Bool.noConfusion

noncomputable def bdd_wmc (f : BDD n) (env : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  match f with
  | .zero => 0
  | .one => 1
  | .node v lo hi => (1 - env v) * bdd_wmc lo env + env v * bdd_wmc hi env

noncomputable def weightedSat (φ : (Fin n → Bool) → Bool) (env : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  Finset.univ.sum fun a : Fin n → Bool =>
    if φ a then assignmentWeight env a else 0

@[simp] theorem bdd_wmc_zero (env : Fin n → ℝ≥0∞) : bdd_wmc (.zero : BDD n) env = 0 := rfl
@[simp] theorem bdd_wmc_one (env : Fin n → ℝ≥0∞) : bdd_wmc (.one : BDD n) env = 1 := rfl

theorem weightedSat_false (env : Fin n → ℝ≥0∞) :
    weightedSat (fun _ => false) env = 0 := by
  unfold weightedSat; simp

theorem weightedSat_true (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    weightedSat (fun _ => true) env = 1 := by
  unfold weightedSat assignmentWeight; simp only [ite_true]
  rw [← Fintype.prod_sum (fun i (b : Bool) => varWeight env i b)]
  apply Finset.prod_eq_one; intro i _
  simp only [Fintype.sum_bool, varWeight_false, varWeight_true]
  exact add_tsub_cancel_of_le (henv i)

theorem BDD.eval_independent (f : BDD n) (hf : f.Ordered (some bound))
    (a : Fin n → Bool) (v : Fin n) (hv : v ≤ bound) (b : Bool) :
    f.eval (Function.update a v b) = f.eval a := by
  induction f generalizing bound with
  | zero => simp | one => simp
  | node w lo hi ih_lo ih_hi =>
    cases hf with
    | node hlt hlo hhi _ =>
      have hw : bound < w := hlt _ rfl
      simp only [BDD.eval]
      rw [Function.update_of_ne (Ne.symm (Fin.ne_of_lt (lt_of_le_of_lt hv hw)))]
      split
      · exact ih_hi hhi (le_of_lt (lt_of_le_of_lt hv hw))
      · exact ih_lo hlo (le_of_lt (lt_of_le_of_lt hv hw))

/-! ## Shannon Decomposition

We prove that when `ψ_lo, ψ_hi` don't depend on variable `v`:
```
weightedSat (fun a => if a v then ψ_hi a else ψ_lo a) env
= (1 - env v) * weightedSat ψ_lo env + env v * weightedSat ψ_hi env
```

The proof uses a filter-split + bijection approach. -/

private noncomputable abbrev rw_ (env : Fin n → ℝ≥0∞) (v : Fin n) (a : Fin n → Bool) :=
  (Finset.univ.erase v).prod (fun i => varWeight env i (a i))

-- assignmentWeight = varWeight v (a v) * rw_
private theorem aw_split (env : Fin n → ℝ≥0∞) (a : Fin n → Bool) (v : Fin n) :
    assignmentWeight env a = varWeight env v (a v) * rw_ env v a :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

-- rw_ is unchanged when variable v is updated
private theorem rw_invariant (env : Fin n → ℝ≥0∞) (v : Fin n) (a : Fin n → Bool) (b : Bool) :
    rw_ env v (Function.update a v b) = rw_ env v a := by
  apply Finset.prod_congr rfl; intro i hi
  have hne : i ≠ v := by
    rw [Finset.mem_erase] at hi; exact hi.1
  rw [Function.update_of_ne hne]

-- Flip variable v
private def flip (v : Fin n) (a : Fin n → Bool) : Fin n → Bool := Function.update a v (!a v)

private theorem flip_self (v : Fin n) (a : Fin n → Bool) : flip v (flip v a) = a := by
  ext i; simp only [flip, Function.update]
  split <;> simp_all

private theorem flip_val (v : Fin n) (a : Fin n → Bool) : flip v a v = !a v := by
  simp [flip, Function.update_self]

-- Bijection lemma: filtered residual sums are equal when ψ is v-independent
private theorem residual_sum_eq (env : Fin n → ℝ≥0∞) (v : Fin n)
    (ψ : (Fin n → Bool) → Bool)
    (hψ : ∀ a b, ψ (Function.update a v b) = ψ a) :
    (univ.filter (fun a : Fin n → Bool => a v = true)).sum
      (fun a => if ψ a then rw_ env v a else 0) =
    (univ.filter (fun a : Fin n → Bool => a v = false)).sum
      (fun a => if ψ a then rw_ env v a else 0) := by
  apply Finset.sum_nbij' (flip v) (flip v)
  · -- flip maps true-filter to false-filter
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, by rw [flip_val, ha.2]; rfl⟩
  · -- flip maps false-filter to true-filter
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, by rw [flip_val, ha.2]; rfl⟩
  · -- left inverse
    intro a _; exact flip_self v a
  · -- right inverse
    intro a _; exact flip_self v a
  · -- values match
    intro a ha
    rw [Finset.mem_filter] at ha
    have hψ_eq : ψ (flip v a) = ψ a := hψ a (!a v)
    have hrw_eq : rw_ env v (flip v a) = rw_ env v a := rw_invariant env v a (!a v)
    rw [hψ_eq, hrw_eq]

-- Factor a weighted sum of v-independent ψ
private theorem wsat_factor (env : Fin n → ℝ≥0∞) (v : Fin n) (ψ : (Fin n → Bool) → Bool)
    (hψ : ∀ a b, ψ (Function.update a v b) = ψ a) (henv : env v ≤ 1) :
    weightedSat ψ env =
      (univ.filter (fun a : Fin n → Bool => a v = false)).sum
        (fun a => if ψ a then rw_ env v a else 0) := by
  unfold weightedSat
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a : Fin n → Bool => a v = true)]
  -- Rewrite ¬(a v = true) as (a v = false)
  have hfilt : univ.filter (fun a : Fin n → Bool => ¬(a v = true)) =
               univ.filter (fun a : Fin n → Bool => a v = false) := by
    ext a; simp [Bool.not_eq_true]
  rw [hfilt]
  -- Factor varWeight and collect: directly show each half
  have true_half :
      (univ.filter (fun a : Fin n → Bool => a v = true)).sum
        (fun a => if ψ a then assignmentWeight env a else 0) =
      env v * (univ.filter (fun a : Fin n → Bool => a v = true)).sum
        (fun a => if ψ a then rw_ env v a else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha
    obtain ⟨_, hav⟩ := Finset.mem_filter.mp ha
    split
    · rw [aw_split, hav, varWeight_true]
    · simp
  have false_half :
      (univ.filter (fun a : Fin n → Bool => a v = false)).sum
        (fun a => if ψ a then assignmentWeight env a else 0) =
      (1 - env v) * (univ.filter (fun a : Fin n → Bool => a v = false)).sum
        (fun a => if ψ a then rw_ env v a else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha
    obtain ⟨_, hav⟩ := Finset.mem_filter.mp ha
    split
    · rw [aw_split, hav, varWeight_false]
    · simp
  rw [true_half, false_half, residual_sum_eq env v ψ hψ, ← add_mul,
      add_tsub_cancel_of_le henv, one_mul]

theorem weightedSat_ite_split (env : Fin n → ℝ≥0∞) (v : Fin n)
    (ψ_lo ψ_hi : (Fin n → Bool) → Bool)
    (hlo : ∀ a b, ψ_lo (Function.update a v b) = ψ_lo a)
    (hhi : ∀ a b, ψ_hi (Function.update a v b) = ψ_hi a)
    (henv : env v ≤ 1) :
    weightedSat (fun a => if a v then ψ_hi a else ψ_lo a) env =
      (1 - env v) * weightedSat ψ_lo env + env v * weightedSat ψ_hi env := by
  -- Factor each RHS term
  rw [wsat_factor env v ψ_lo hlo henv, wsat_factor env v ψ_hi hhi henv]
  -- Expand LHS: split by a v
  unfold weightedSat
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a : Fin n → Bool => a v = true)]
  have hfilt : univ.filter (fun a : Fin n → Bool => ¬(a v = true)) =
               univ.filter (fun a : Fin n → Bool => a v = false) := by
    ext a; simp [Bool.not_eq_true]
  rw [hfilt]
  -- In the true-filter: if a v = true then ψ_hi a, weight factors to env v * rw_
  have lhs_true :
      (univ.filter (fun a : Fin n → Bool => a v = true)).sum
        (fun a => if (if a v = true then ψ_hi a else ψ_lo a) = true
          then assignmentWeight env a else 0) =
      env v * (univ.filter (fun a : Fin n → Bool => a v = true)).sum
        (fun a => if ψ_hi a then rw_ env v a else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha
    obtain ⟨_, hav⟩ := Finset.mem_filter.mp ha
    rw [hav]; simp only [ite_true]
    split
    · rw [aw_split, hav, varWeight_true]
    · simp
  -- In the false-filter: if a v = false then ψ_lo a, weight factors to (1-env v) * rw_
  have lhs_false :
      (univ.filter (fun a : Fin n → Bool => a v = false)).sum
        (fun a => if (if a v = true then ψ_hi a else ψ_lo a) = true
          then assignmentWeight env a else 0) =
      (1 - env v) * (univ.filter (fun a : Fin n → Bool => a v = false)).sum
        (fun a => if ψ_lo a then rw_ env v a else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha
    obtain ⟨_, hav⟩ := Finset.mem_filter.mp ha
    rw [hav]; simp only [Bool.false_eq_true, ite_false]
    split
    · rw [aw_split, hav, varWeight_false]
    · simp
  rw [lhs_true, lhs_false]
  -- Use bijection: the hi sum over {av=true} = hi sum over {av=false}
  rw [residual_sum_eq env v ψ_hi hhi]
  ring

/-! ## WMC Correctness -/

theorem bdd_wmc_correct (f : BDD n) (hf : f.Ordered bound)
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    bdd_wmc f env = weightedSat f.eval env := by
  induction f generalizing bound with
  | zero => simp [bdd_wmc, weightedSat]
  | one => simp [bdd_wmc]; exact (weightedSat_true env henv).symm
  | node v lo hi ih_lo ih_hi =>
    cases hf with
    | node hlt hlo hhi hne =>
      show (1 - env v) * bdd_wmc lo env + env v * bdd_wmc hi env = _
      rw [ih_lo hlo, ih_hi hhi]; symm
      show weightedSat (fun a => if a v then hi.eval a else lo.eval a) env = _
      exact weightedSat_ite_split env v lo.eval hi.eval
        (fun a b => BDD.eval_independent lo hlo a v le_rfl b)
        (fun a b => BDD.eval_independent hi hhi a v le_rfl b)
        (henv v)

/-- If some assignment `a` satisfies `φ` and has nonzero weight,
    then `weightedSat φ env ≠ 0`. -/
theorem weightedSat_ne_zero_of_witness (φ : (Fin n → Bool) → Bool)
    (env : Fin n → ℝ≥0∞) (a : Fin n → Bool)
    (hφ : φ a = true) (hw : assignmentWeight env a ≠ 0) :
    weightedSat φ env ≠ 0 := by
  unfold weightedSat
  apply ne_of_gt
  have hle : (if φ a then assignmentWeight env a else 0) ≤
      Finset.univ.sum (fun b : Fin n → Bool => if φ b then assignmentWeight env b else 0) :=
    Finset.single_le_sum (fun b _ => by
      show 0 ≤ if φ b then assignmentWeight env b else 0
      cases φ b <;> simp) (Finset.mem_univ a)
  calc 0 < assignmentWeight env a := by exact pos_iff_ne_zero.mpr hw
     _ = if φ a then assignmentWeight env a else 0 := by simp [hφ]
     _ ≤ _ := hle

end Mettapedia.Logic.BDDCore
