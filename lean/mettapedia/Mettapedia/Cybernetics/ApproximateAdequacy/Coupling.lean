import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Finite distributions and couplings

Probability distributions on a finite type, valued in any linearly ordered
field, and their couplings: joint weightings with prescribed marginals.  This
is the finite, field-generic layer beneath the Kantorovich lifting and the
behavioural pseudometrics of Desharnais, Gupta, Jagadeesan and Panangaden
(`Mettapedia.Cybernetics.ApproximateAdequacy.CouplingBound`).  Working over an
arbitrary field keeps certificates checkable in `ℚ`; the canonical metric
specialises to `ℝ`.

* **The coupling identity.**  Under any coupling, the difference of two
  expectations is the expectation of the pointwise difference
  (`Coupling.expect_sub_expect`); so every coupling bounds the difference of
  expectations by the cost of any pointwise bound
  (`Coupling.abs_expect_sub_le`).  This is the easy half of Kantorovich
  duality, and it is all the soundness theorems need.
* **Couplings that always exist**: the independent coupling
  (`Coupling.independent`), the reversed coupling (`Coupling.swap`), and the
  unique coupling of two point masses (`Coupling.weight_dirac`).
* **Product couplings** (`Coupling.prod`) add costs of separable cost
  functions (`Coupling.cost_prod_add`): the source of the parallel
  composition law.
* **Gluing** (`Coupling.glue`): couplings of `μ, ν` and `ν, ρ` glue to a
  coupling of `μ, ρ` whose cost is at most the sum of the two costs whenever
  the cost functions satisfy a triangle inequality
  (`Coupling.cost_glue_le`): the source of the sequential composition law.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {S T U : Type*} [Fintype S] [Fintype T] [Fintype U]

/-! ## Distributions and expectations -/

/-- A probability distribution on a finite type. -/
structure IsDistribution (μ : S → 𝕜) : Prop where
  nonneg : ∀ x, 0 ≤ μ x
  sum_eq_one : ∑ x, μ x = 1

/-- The expectation of `f` under the weighting `μ`. -/
def expect (μ : S → 𝕜) (f : S → 𝕜) : 𝕜 :=
  ∑ x, μ x * f x

section Expect

variable {μ : S → 𝕜}

theorem IsDistribution.le_one (distribution : IsDistribution μ) (x : S) : μ x ≤ 1 := by
  rw [← distribution.sum_eq_one]
  exact Finset.single_le_sum (fun y _ => distribution.nonneg y) (Finset.mem_univ x)

omit [IsStrictOrderedRing 𝕜] in
theorem expect_const (distribution : IsDistribution μ) (c : 𝕜) : expect μ (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, distribution.sum_eq_one, one_mul]

theorem expect_mono (distribution : IsDistribution μ) {f g : S → 𝕜} (le : ∀ x, f x ≤ g x) :
    expect μ f ≤ expect μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le x) (distribution.nonneg x)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem expect_add (μ : S → 𝕜) (f g : S → 𝕜) :
    expect μ (fun x => f x + g x) = expect μ f + expect μ g := by
  rw [expect, expect, expect, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => mul_add _ _ _

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem expect_mul_left (μ : S → 𝕜) (c : 𝕜) (f : S → 𝕜) :
    expect μ (fun x => c * f x) = c * expect μ f := by
  rw [expect, expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end Expect

/-! ## Couplings -/

/-- **A coupling** of `μ` and `ν`: a nonnegative joint weighting whose
marginals are `μ` and `ν`. -/
structure Coupling (μ : S → 𝕜) (ν : T → 𝕜) where
  weight : S → T → 𝕜
  nonneg : ∀ x y, 0 ≤ weight x y
  sum_right : ∀ x, ∑ y, weight x y = μ x
  sum_left : ∀ y, ∑ x, weight x y = ν y

namespace Coupling

variable {μ : S → 𝕜} {ν : T → 𝕜} {ρ : U → 𝕜}

/-- The cost of a coupling for a cost function `m`: the expectation of `m`
under the joint weighting. -/
def cost (ω : Coupling μ ν) (m : S → T → 𝕜) : 𝕜 :=
  ∑ x, ∑ y, ω.weight x y * m x y

variable (ω : Coupling μ ν)

theorem cost_nonneg {m : S → T → 𝕜} (nonneg : ∀ x y, 0 ≤ m x y) : 0 ≤ ω.cost m :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (ω.nonneg x y) (nonneg x y)

theorem cost_mono {m m' : S → T → 𝕜} (le : ∀ x y, m x y ≤ m' x y) : ω.cost m ≤ ω.cost m' :=
  Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (le x y) (ω.nonneg x y)

omit [IsStrictOrderedRing 𝕜] in
theorem cost_add (m m' : S → T → 𝕜) :
    ω.cost (fun x y => m x y + m' x y) = ω.cost m + ω.cost m' := by
  unfold cost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => mul_add _ _ _

omit [IsStrictOrderedRing 𝕜] in
theorem cost_mul_left (c : 𝕜) (m : S → T → 𝕜) :
    ω.cost (fun x y => c * m x y) = c * ω.cost m := by
  unfold cost
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

omit [IsStrictOrderedRing 𝕜] in
/-- The total weight of a coupling of a distribution is one. -/
theorem total (distribution : IsDistribution μ) : ∑ x, ∑ y, ω.weight x y = 1 := by
  rw [← distribution.sum_eq_one]
  exact Finset.sum_congr rfl fun x _ => ω.sum_right x

omit [IsStrictOrderedRing 𝕜] in
theorem cost_const (distribution : IsDistribution μ) (c : 𝕜) : ω.cost (fun _ _ => c) = c := by
  unfold cost
  have split : ∀ x, ∑ y, ω.weight x y * c = (∑ y, ω.weight x y) * c := fun x =>
    (Finset.sum_mul _ _ _).symm
  simp_rw [split]
  rw [← Finset.sum_mul, ω.total distribution, one_mul]

theorem cost_le_of_le (distribution : IsDistribution μ) {m : S → T → 𝕜} {B : 𝕜}
    (bound : ∀ x y, m x y ≤ B) : ω.cost m ≤ B :=
  (ω.cost_mono bound).trans (ω.cost_const distribution B).le

theorem weight_le_left (x : S) (y : T) : ω.weight x y ≤ μ x := by
  rw [← ω.sum_right x]
  exact Finset.single_le_sum (fun y' _ => ω.nonneg x y') (Finset.mem_univ y)

theorem weight_le_right (x : S) (y : T) : ω.weight x y ≤ ν y := by
  rw [← ω.sum_left y]
  exact Finset.single_le_sum (fun x' _ => ω.nonneg x' y) (Finset.mem_univ x)

theorem weight_eq_zero_of_left {x : S} (zero : μ x = 0) (y : T) : ω.weight x y = 0 :=
  le_antisymm (zero ▸ ω.weight_le_left x y) (ω.nonneg x y)

theorem weight_eq_zero_of_right {y : T} (zero : ν y = 0) (x : S) : ω.weight x y = 0 :=
  le_antisymm (zero ▸ ω.weight_le_right x y) (ω.nonneg x y)

omit [IsStrictOrderedRing 𝕜] in
/-- **The coupling identity**: the difference of two expectations is the
expectation of the pointwise difference under the coupling. -/
theorem expect_sub_expect (f : S → 𝕜) (g : T → 𝕜) :
    expect μ f - expect ν g = ∑ x, ∑ y, ω.weight x y * (f x - g y) := by
  have left : expect μ f = ∑ x, ∑ y, ω.weight x y * f x := by
    unfold expect
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← ω.sum_right x, Finset.sum_mul]
  have right : expect ν g = ∑ x, ∑ y, ω.weight x y * g y := by
    unfold expect
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← ω.sum_left y, Finset.sum_mul]
  rw [left, right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => (mul_sub _ _ _).symm

/-- **Every coupling bounds the difference of expectations** by the cost of a
pointwise bound: the easy half of Kantorovich duality. -/
theorem abs_expect_sub_le {f : S → 𝕜} {g : T → 𝕜} {m : S → T → 𝕜}
    (bound : ∀ x y, |f x - g y| ≤ m x y) : |expect μ f - expect ν g| ≤ ω.cost m := by
  rw [ω.expect_sub_expect f g]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (ω.nonneg x y)]
  exact mul_le_mul_of_nonneg_left (bound x y) (ω.nonneg x y)

/-- A coupling needs a pointwise bound only on pairs it actually relates.
This permits observation-compatible couplings for adaptive controllers. -/
theorem abs_expect_sub_le_on_support {f : S → 𝕜} {g : T → 𝕜} {m : S → T → 𝕜}
    (bound : ∀ x y, 0 < ω.weight x y → |f x - g y| ≤ m x y) :
    |expect μ f - expect ν g| ≤ ω.cost m := by
  rw [ω.expect_sub_expect f g]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (ω.nonneg x y)]
  by_cases zero : ω.weight x y = 0
  · simp [zero]
  · have positive : 0 < ω.weight x y := lt_of_le_of_ne (ω.nonneg x y) (Ne.symm zero)
    exact mul_le_mul_of_nonneg_left (bound x y positive) (ω.nonneg x y)

/-- **A coupling of zero cost is supported where the cost vanishes.** -/
theorem eq_zero_of_cost_nonpos {m : S → T → 𝕜} (nonneg : ∀ x y, 0 ≤ m x y)
    (zero : ω.cost m ≤ 0) {x : S} {y : T} (positive : ω.weight x y ≠ 0) : m x y = 0 := by
  have terms : ∀ x' ∈ Finset.univ, 0 ≤ ∑ y', ω.weight x' y' * m x' y' := fun x' _ =>
    Finset.sum_nonneg fun y' _ => mul_nonneg (ω.nonneg x' y') (nonneg x' y')
  have row : ∑ y', ω.weight x y' * m x y' = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg terms).mp
      (le_antisymm zero (Finset.sum_nonneg terms)) x (Finset.mem_univ x)
  have entry : ω.weight x y * m x y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y' _ => mul_nonneg (ω.nonneg x y') (nonneg x y')).mp
      row y (Finset.mem_univ y)
  exact (mul_eq_zero.mp entry).resolve_left positive

/-! ### Couplings that always exist -/

/-- **The independent coupling** of two distributions. -/
def independent (first : IsDistribution μ) (second : IsDistribution ν) : Coupling μ ν where
  weight x y := μ x * ν y
  nonneg x y := mul_nonneg (first.nonneg x) (second.nonneg y)
  sum_right x := by rw [← Finset.mul_sum, second.sum_eq_one, mul_one]
  sum_left y := by rw [← Finset.sum_mul, first.sum_eq_one, one_mul]

/-- **The reversed coupling.** -/
def swap : Coupling ν μ where
  weight y x := ω.weight x y
  nonneg y x := ω.nonneg x y
  sum_right y := ω.sum_left y
  sum_left x := ω.sum_right x

omit [IsStrictOrderedRing 𝕜] in
theorem cost_swap (m : S → T → 𝕜) : ω.swap.cost (fun y x => m x y) = ω.cost m := by
  unfold cost swap
  rw [Finset.sum_comm]

end Coupling

/-! ## Point masses -/

section Dirac

variable [DecidableEq S] [DecidableEq T]

/-- The point mass at `x₀`. -/
def dirac (x₀ : S) : S → 𝕜 :=
  fun x => if x = x₀ then 1 else 0

theorem isDistribution_dirac (x₀ : S) : IsDistribution (dirac (𝕜 := 𝕜) x₀) where
  nonneg x := by unfold dirac; split_ifs <;> norm_num
  sum_eq_one := by simp [dirac]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem expect_dirac (x₀ : S) (f : S → 𝕜) : expect (dirac x₀) f = f x₀ := by
  simp [expect, dirac]

/-- **Two point masses have exactly one coupling**, the point mass at the
pair. -/
theorem Coupling.weight_dirac {x₀ : S} {y₀ : T} (ω : Coupling (dirac (𝕜 := 𝕜) x₀) (dirac y₀))
    (x : S) (y : T) : ω.weight x y = if x = x₀ ∧ y = y₀ then 1 else 0 := by
  by_cases hx : x = x₀
  · by_cases hy : y = y₀
    · subst hx hy
      rw [if_pos ⟨rfl, rfl⟩]
      have row := ω.sum_right x
      rw [Finset.sum_eq_single y (fun y' _ other => ω.weight_eq_zero_of_right
          (by simp [dirac, other]) x) (fun absent => absurd (Finset.mem_univ y) absent)] at row
      simpa [dirac] using row
    · rw [if_neg fun both => hy both.2]
      exact ω.weight_eq_zero_of_right (by simp [dirac, hy]) x
  · rw [if_neg fun both => hx both.1]
    exact ω.weight_eq_zero_of_left (by simp [dirac, hx]) y

/-- The cost of the coupling of two point masses is the cost at the pair. -/
theorem Coupling.cost_dirac {x₀ : S} {y₀ : T} (ω : Coupling (dirac (𝕜 := 𝕜) x₀) (dirac y₀))
    (m : S → T → 𝕜) : ω.cost m = m x₀ y₀ := by
  unfold Coupling.cost
  simp_rw [ω.weight_dirac]
  simp [ite_and]

/-- The cost of a coupling of two weightings that are point masses. -/
theorem Coupling.cost_of_eq_dirac {μ : S → 𝕜} {ν : T → 𝕜} {x₀ : S} {y₀ : T}
    (ω : Coupling μ ν) (first : μ = dirac x₀) (second : ν = dirac y₀) (m : S → T → 𝕜) :
    ω.cost m = m x₀ y₀ := by
  subst first second
  exact ω.cost_dirac m

omit [DecidableEq S] in
/-- **A coupling with a point mass is forced**: all the mass of `x` goes to the
point. -/
theorem Coupling.weight_of_eq_dirac_right {μ : S → 𝕜} {ν : T → 𝕜} {y₀ : T} (ω : Coupling μ ν)
    (second : ν = dirac y₀) (x : S) (y : T) : ω.weight x y = if y = y₀ then μ x else 0 := by
  subst second
  by_cases hy : y = y₀
  · subst hy
    rw [if_pos rfl]
    have row := ω.sum_right x
    rw [Finset.sum_eq_single y (fun y' _ other => ω.weight_eq_zero_of_right
        (by simp [dirac, other]) x) (fun absent => absurd (Finset.mem_univ y) absent)] at row
    exact row
  · rw [if_neg hy]
    exact ω.weight_eq_zero_of_right (by simp [dirac, hy]) x

omit [DecidableEq S] in
/-- **The cost of a coupling with a point mass is an expectation.** -/
theorem Coupling.cost_of_eq_dirac_right {μ : S → 𝕜} {ν : T → 𝕜} {y₀ : T} (ω : Coupling μ ν)
    (second : ν = dirac y₀) (m : S → T → 𝕜) : ω.cost m = expect μ fun x => m x y₀ := by
  unfold Coupling.cost expect
  refine Finset.sum_congr rfl fun x _ => ?_
  simp_rw [ω.weight_of_eq_dirac_right second x]
  simp

/-- The coupling of two point masses. -/
def Coupling.ofDirac (x₀ : S) (y₀ : T) : Coupling (dirac (𝕜 := 𝕜) x₀) (dirac y₀) :=
  Coupling.independent (isDistribution_dirac x₀) (isDistribution_dirac y₀)

end Dirac

/-! ## Products -/

section Product

variable {S₁ S₂ T₁ T₂ : Type*} [Fintype S₁] [Fintype S₂] [Fintype T₁] [Fintype T₂]
  {μ₁ : S₁ → 𝕜} {μ₂ : S₂ → 𝕜} {ν₁ : T₁ → 𝕜} {ν₂ : T₂ → 𝕜}

/-- The product of two weightings. -/
def prodWeight (μ₁ : S₁ → 𝕜) (μ₂ : S₂ → 𝕜) : S₁ × S₂ → 𝕜 :=
  fun p => μ₁ p.1 * μ₂ p.2

theorem IsDistribution.prod (first : IsDistribution μ₁) (second : IsDistribution μ₂) :
    IsDistribution (prodWeight μ₁ μ₂) where
  nonneg p := mul_nonneg (first.nonneg p.1) (second.nonneg p.2)
  sum_eq_one := by
    unfold prodWeight
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, second.sum_eq_one, mul_one]
    exact first.sum_eq_one

/-- **The product of two couplings** couples the products. -/
def Coupling.prod (ω₁ : Coupling μ₁ ν₁) (ω₂ : Coupling μ₂ ν₂) :
    Coupling (prodWeight μ₁ μ₂) (prodWeight ν₁ ν₂) where
  weight p q := ω₁.weight p.1 q.1 * ω₂.weight p.2 q.2
  nonneg p q := mul_nonneg (ω₁.nonneg p.1 q.1) (ω₂.nonneg p.2 q.2)
  sum_right p := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ω₂.sum_right, ← Finset.sum_mul, ω₁.sum_right]
    rfl
  sum_left q := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ω₂.sum_left, ← Finset.sum_mul, ω₁.sum_left]
    rfl

/-- **Product couplings add the costs of separable cost functions.** -/
theorem Coupling.cost_prod_add (ω₁ : Coupling μ₁ ν₁) (ω₂ : Coupling μ₂ ν₂)
    (first : IsDistribution μ₁) (second : IsDistribution μ₂)
    (m₁ : S₁ → T₁ → 𝕜) (m₂ : S₂ → T₂ → 𝕜) :
    (ω₁.prod ω₂).cost (fun p q => m₁ p.1 q.1 + m₂ p.2 q.2) = ω₁.cost m₁ + ω₂.cost m₂ := by
  have total₁ := ω₁.total first
  have total₂ := ω₂.total second
  unfold Coupling.cost Coupling.prod
  simp only [Fintype.sum_prod_type]
  -- rearrange the four-fold sum into products of double sums
  have expand : ∀ (x₁ : S₁) (x₂ : S₂) (y₁ : T₁) (y₂ : T₂),
      ω₁.weight x₁ y₁ * ω₂.weight x₂ y₂ * (m₁ x₁ y₁ + m₂ x₂ y₂) =
        (ω₁.weight x₁ y₁ * m₁ x₁ y₁) * ω₂.weight x₂ y₂ +
          ω₁.weight x₁ y₁ * (ω₂.weight x₂ y₂ * m₂ x₂ y₂) := fun _ _ _ _ => by ring
  simp_rw [expand, Finset.sum_add_distrib]
  congr 1
  · calc ∑ x₁, ∑ x₂, ∑ y₁, ∑ y₂, ω₁.weight x₁ y₁ * m₁ x₁ y₁ * ω₂.weight x₂ y₂
        = ∑ x₁, ∑ y₁, ∑ x₂, ∑ y₂, ω₁.weight x₁ y₁ * m₁ x₁ y₁ * ω₂.weight x₂ y₂ := by
          refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_comm
      _ = ∑ x₁, ∑ y₁, ω₁.weight x₁ y₁ * m₁ x₁ y₁ * ∑ x₂, ∑ y₂, ω₂.weight x₂ y₂ := by
          refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun y₁ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x₂ _ => by rw [Finset.mul_sum]
      _ = ∑ x₁, ∑ y₁, ω₁.weight x₁ y₁ * m₁ x₁ y₁ := by rw [total₂]; simp
  · calc ∑ x₁, ∑ x₂, ∑ y₁, ∑ y₂, ω₁.weight x₁ y₁ * (ω₂.weight x₂ y₂ * m₂ x₂ y₂)
        = ∑ x₁, ∑ y₁, ∑ x₂, ∑ y₂, ω₁.weight x₁ y₁ * (ω₂.weight x₂ y₂ * m₂ x₂ y₂) := by
          refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_comm
      _ = ∑ x₁, ∑ y₁, ω₁.weight x₁ y₁ * ∑ x₂, ∑ y₂, ω₂.weight x₂ y₂ * m₂ x₂ y₂ := by
          refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun y₁ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x₂ _ => by rw [Finset.mul_sum]
      _ = ∑ x₂, ∑ y₂, ω₂.weight x₂ y₂ * m₂ x₂ y₂ := by
          simp_rw [← Finset.sum_mul]
          rw [total₁, one_mul]

end Product

/-! ## Gluing -/

namespace Coupling

variable {μ : S → 𝕜} {ν : T → 𝕜} {ρ : U → 𝕜}

/-- The glued weight: route the mass of `x` through each middle point `y` in
proportion to `ω₂`. -/
def glueWeight (ω₁ : Coupling μ ν) (ω₂ : Coupling ν ρ) (x : S) (z : U) : 𝕜 :=
  ∑ y, ω₁.weight x y * ω₂.weight y z / ν y

theorem nu_nonneg (ω₁ : Coupling μ ν) (y : T) : 0 ≤ ν y := by
  rw [← ω₁.sum_left y]
  exact Finset.sum_nonneg fun x _ => ω₁.nonneg x y

/-- Dividing by the middle marginal is harmless where the middle mass
vanishes. -/
theorem mul_div_middle_left (ω₁ : Coupling μ ν) (x : S) (y : T) :
    ω₁.weight x y * ν y / ν y = ω₁.weight x y := by
  by_cases zero : ν y = 0
  · rw [ω₁.weight_eq_zero_of_right zero x]; simp
  · rw [mul_div_assoc, div_self zero, mul_one]

theorem mul_div_middle_right (ω₂ : Coupling ν ρ) (y : T) (z : U) :
    ν y * ω₂.weight y z / ν y = ω₂.weight y z := by
  by_cases zero : ν y = 0
  · rw [ω₂.weight_eq_zero_of_left zero z]; simp
  · rw [mul_comm, mul_div_assoc, div_self zero, mul_one]

/-- **Gluing**: couplings of `μ, ν` and of `ν, ρ` give a coupling of
`μ, ρ`. -/
def glue (ω₁ : Coupling μ ν) (ω₂ : Coupling ν ρ) : Coupling μ ρ where
  weight := glueWeight ω₁ ω₂
  nonneg x z := Finset.sum_nonneg fun y _ =>
    div_nonneg (mul_nonneg (ω₁.nonneg x y) (ω₂.nonneg y z)) (ω₁.nu_nonneg y)
  sum_right x := by
    unfold glueWeight
    rw [Finset.sum_comm]
    calc ∑ y, ∑ z, ω₁.weight x y * ω₂.weight y z / ν y
        = ∑ y, ω₁.weight x y * ν y / ν y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_div, ← Finset.mul_sum, ω₂.sum_right]
      _ = μ x := by
          simp_rw [ω₁.mul_div_middle_left]
          exact ω₁.sum_right x
  sum_left z := by
    unfold glueWeight
    rw [Finset.sum_comm]
    calc ∑ y, ∑ x, ω₁.weight x y * ω₂.weight y z / ν y
        = ∑ y, ν y * ω₂.weight y z / ν y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_div, ← Finset.sum_mul, ω₁.sum_left]
      _ = ρ z := by
          simp_rw [ω₂.mul_div_middle_right]
          exact ω₂.sum_left z

/-- **The glued coupling costs at most the sum of the two costs**, for cost
functions satisfying a triangle inequality through every middle point. -/
theorem cost_glue_le (ω₁ : Coupling μ ν) (ω₂ : Coupling ν ρ) {m₁ : S → T → 𝕜}
    {m₂ : T → U → 𝕜} {m₃ : S → U → 𝕜} (triangle : ∀ x y z, m₃ x z ≤ m₁ x y + m₂ y z) :
    (ω₁.glue ω₂).cost m₃ ≤ ω₁.cost m₁ + ω₂.cost m₂ := by
  have weight_nonneg : ∀ x y z, 0 ≤ ω₁.weight x y * ω₂.weight y z / ν y := fun x y z =>
    div_nonneg (mul_nonneg (ω₁.nonneg x y) (ω₂.nonneg y z)) (ω₁.nu_nonneg y)
  have bound : (ω₁.glue ω₂).cost m₃ ≤
      ∑ x, ∑ z, ∑ y, ω₁.weight x y * ω₂.weight y z / ν y * (m₁ x y + m₂ y z) := by
    unfold cost glue glueWeight
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (triangle x y z) (weight_nonneg x y z)
  refine bound.trans (le_of_eq ?_)
  have first : ∑ x, ∑ z, ∑ y, ω₁.weight x y * ω₂.weight y z / ν y * m₁ x y = ω₁.cost m₁ := by
    unfold cost
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    calc ∑ z, ω₁.weight x y * ω₂.weight y z / ν y * m₁ x y
        = ω₁.weight x y * (∑ z, ω₂.weight y z) / ν y * m₁ x y := by
          rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
      _ = ω₁.weight x y * m₁ x y := by rw [ω₂.sum_right, ω₁.mul_div_middle_left]
  have second : ∑ x, ∑ z, ∑ y, ω₁.weight x y * ω₂.weight y z / ν y * m₂ y z = ω₂.cost m₂ := by
    unfold cost
    rw [Finset.sum_comm]
    calc ∑ z, ∑ x, ∑ y, ω₁.weight x y * ω₂.weight y z / ν y * m₂ y z
        = ∑ z, ∑ y, ∑ x, ω₁.weight x y * ω₂.weight y z / ν y * m₂ y z := by
          exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z, ∑ y, ω₂.weight y z * m₂ y z := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
          calc ∑ x, ω₁.weight x y * ω₂.weight y z / ν y * m₂ y z
              = (∑ x, ω₁.weight x y) * ω₂.weight y z / ν y * m₂ y z := by
                rw [Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
            _ = ω₂.weight y z * m₂ y z := by rw [ω₁.sum_left, ω₂.mul_div_middle_right]
      _ = ∑ y, ∑ z, ω₂.weight y z * m₂ y z := Finset.sum_comm
  rw [← first, ← second, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => mul_add _ _ _

end Coupling

end Mettapedia.Cybernetics.ApproximateAdequacy
