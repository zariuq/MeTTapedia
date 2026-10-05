import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Kantorovich duality on finite spaces

The Kantorovich lifting of `Cybernetics.ApproximateAdequacy.BisimulationMetric`
is the least cost of a coupling.  Its easy half bounds differences of
expectations; this module proves the hard half, so that the lifting is a
supremum over potentials as well as an infimum over couplings.

* **Transport duality** (`exists_dual_of_lt_cost`): when every coupling of two
  distributions costs more than `B`, a pair of potentials `φ, ψ` with
  `φ x + ψ y ≤ m x y` has expectations summing to more than `B`.  The proof
  separates the compact convex image of the simplex of joint weightings from
  the closed half-line of feasible marginals and costs (Hahn–Banach, through
  Mathlib's `geometric_hahn_banach_compact_closed`), and reads the separating
  functional as the potentials.
* **Kantorovich–Rubinstein form** (`exists_lipschitz_of_lt_kantorovich`): for a
  cost that vanishes on the diagonal and satisfies the triangle inequality, one
  potential suffices: a function `f` with `f x - f y ≤ d x y` whose expectations
  differ by more than `B`.  It is the infimal transform
  `f x = min_y (d x y - ψ y)` of the dual pair.
* **Duality** (`kantorovich_eq_iSup_lipschitz`): the lifting of such a cost is
  the supremum, over these functions, of the difference of expectations.

`Classical.choice` enters through `ℝ`, Hahn–Banach and the finite sums.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S T : Type*} [Fintype S] [Fintype T]

/-! ## The marginals and the cost as one linear map -/

/-- The row sums, the column sums and the cost of a joint weighting. -/
noncomputable def marginalsAndCost (m : S → T → ℝ) :
    (S × T → ℝ) →ₗ[ℝ] (S → ℝ) × (T → ℝ) × ℝ where
  toFun w := (fun x => ∑ y, w (x, y), fun y => ∑ x, w (x, y), ∑ x, ∑ y, w (x, y) * m x y)
  map_add' w w' := by
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  map_smul' r w := by
    ext <;> simp [Finset.mul_sum, mul_assoc]

/-- A continuous linear functional on potentials and a cost weight is read
coordinatewise. -/
theorem functional_apply [DecidableEq S] [DecidableEq T]
    (f : StrongDual ℝ ((S → ℝ) × (T → ℝ) × ℝ)) (a : S → ℝ) (b : T → ℝ) (r : ℝ) :
    f (a, b, r) = ∑ x, a x * f (Pi.single x 1, 0, 0) + ∑ y, b y * f (0, Pi.single y 1, 0) +
      r * f (0, 0, 1) := by
  have decompose : ((a, b, r) : (S → ℝ) × (T → ℝ) × ℝ) =
      ∑ x, a x • ((Pi.single x 1, 0, 0) : (S → ℝ) × (T → ℝ) × ℝ) +
        ∑ y, b y • ((0, Pi.single y 1, 0) : (S → ℝ) × (T → ℝ) × ℝ) +
          r • ((0, 0, 1) : (S → ℝ) × (T → ℝ) × ℝ) := by
    ext x <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [decompose, map_add, map_add, map_sum, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul]

/-! ## Transport duality -/

/-- **Transport duality.**  If every coupling of `μ` and `ν` costs more than
`B`, then some potentials `φ, ψ` with `φ x + ψ y ≤ m x y` have expectations
summing to more than `B`. -/
theorem exists_dual_of_lt_cost {μ : S → ℝ} {ν : T → ℝ} (first : IsDistribution μ)
    (second : IsDistribution ν) (m : S → T → ℝ) {B : ℝ}
    (above : ∀ ω : Coupling μ ν, B < ω.cost m) :
    ∃ (φ : S → ℝ) (ψ : T → ℝ), (∀ x y, φ x + ψ y ≤ m x y) ∧
      B < expect μ φ + expect ν ψ := by
  classical
  set L := marginalsAndCost (S := S) (T := T) m
  set z : (S → ℝ) × (T → ℝ) × ℝ := (-μ, -ν, -B)
  set K : Set ((S → ℝ) × (T → ℝ) × ℝ) := (fun p => z + p) '' (L '' stdSimplex ℝ (S × T))
  set C : Set ((S → ℝ) × (T → ℝ) × ℝ) := {p | p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2 ≤ 0}
  have K_convex : Convex ℝ K := ((convex_stdSimplex ℝ (S × T)).linear_image L).translate z
  have K_compact : IsCompact K :=
    ((isCompact_stdSimplex ℝ (S × T)).image L.continuous_of_finiteDimensional).image
      (continuous_const.add continuous_id)
  have C_convex : Convex ℝ C := by
    rintro p ⟨p₁, p₂, p₃⟩ q ⟨q₁, q₂, q₃⟩ a b a_nonneg b_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · simp [p₁, q₁]
    · simp [p₂, q₂]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a_nonneg p₃,
        mul_nonpos_of_nonneg_of_nonpos b_nonneg q₃]
  have C_closed : IsClosed C :=
    (isClosed_eq continuous_fst continuous_const).inter
      ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
        (isClosed_le (continuous_snd.comp continuous_snd) continuous_const))
  have disjoint : Disjoint K C := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨w, member, rfl⟩, rfl⟩ ⟨rows, columns, cost⟩
    have rows' : ∀ x, ∑ y, w (x, y) = μ x := fun x => by
      have := congrFun rows x
      simp only [z, L, marginalsAndCost, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add,
        Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
      linarith
    have columns' : ∀ y, ∑ x, w (x, y) = ν y := fun y => by
      have := congrFun columns y
      simp only [z, L, marginalsAndCost, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add,
        Prod.fst_add, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
      linarith
    have cost' : ∑ x, ∑ y, w (x, y) * m x y ≤ B := by
      simp only [z, L, marginalsAndCost, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add] at cost
      linarith
    let ω : Coupling μ ν := ⟨fun x y => w (x, y), fun x y => member.1 (x, y), rows', columns'⟩
    exact absurd (above ω) (not_lt.mpr cost')
  obtain ⟨f, u, v, belowK, u_lt_v, aboveC⟩ :=
    geometric_hahn_banach_compact_closed K_convex K_compact C_convex C_closed disjoint
  set gS : S → ℝ := fun x => f (Pi.single x 1, 0, 0)
  set gT : T → ℝ := fun y => f (0, Pi.single y 1, 0)
  set κ : ℝ := -f (0, 0, 1)
  have read : ∀ a b r, f (a, b, r) = ∑ x, a x * gS x + ∑ y, b y * gT y - r * κ := by
    intro a b r
    rw [functional_apply]
    ring
  have v_neg : v < 0 := by
    have := aboveC (0, 0, 0) ⟨rfl, rfl, le_rfl⟩
    rwa [show ((0, 0, 0) : (S → ℝ) × (T → ℝ) × ℝ) = 0 from rfl, map_zero] at this
  have u_neg : u < 0 := u_lt_v.trans v_neg
  have κ_nonneg : 0 ≤ κ := by
    by_contra nonneg
    have negative : κ < 0 := not_le.mp nonneg
    have member : ((0, 0, v / -κ) : (S → ℝ) × (T → ℝ) × ℝ) ∈ C :=
      ⟨rfl, rfl, div_nonpos_of_nonpos_of_nonneg v_neg.le (by linarith)⟩
    have := aboveC _ member
    rw [read] at this
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at this
    have cancel : v / -κ * κ = -v := by
      rw [div_neg, neg_mul, div_mul_cancel₀ v negative.ne]
    linarith
  set Gμ := expect μ gS
  set Gν := expect ν gT
  have point : ∀ x y, gS x - Gμ + (gT y - Gν) - (m x y - B) * κ < u := by
    intro x y
    have member : z + L (Pi.single (x, y) 1) ∈ K :=
      ⟨L (Pi.single (x, y) 1), ⟨_, single_mem_stdSimplex ℝ (x, y), rfl⟩, rfl⟩
    have value := belowK _ member
    have rowsSingle : ∀ x', ∑ y', (Pi.single (x, y) (1 : ℝ) : S × T → ℝ) (x', y') =
        (Pi.single x 1 : S → ℝ) x' := fun x' => by
      by_cases same : x' = x
      · subst same; simp [Pi.single_apply, Prod.ext_iff]
      · simp [Prod.ext_iff, same]
    have columnsSingle : ∀ y', ∑ x', (Pi.single (x, y) (1 : ℝ) : S × T → ℝ) (x', y') =
        (Pi.single y 1 : T → ℝ) y' := fun y' => by
      by_cases same : y' = y
      · subst same; simp [Pi.single_apply, Prod.ext_iff]
      · simp [Prod.ext_iff, same]
    have costSingle : ∑ x', ∑ y', (Pi.single (x, y) (1 : ℝ) : S × T → ℝ) (x', y') * m x' y' =
        m x y := by
      simp [Pi.single_apply, Prod.ext_iff, ite_and]
    have image : z + L (Pi.single (x, y) 1) =
        ((fun x' => (Pi.single x 1 : S → ℝ) x' - μ x'),
          (fun y' => (Pi.single y 1 : T → ℝ) y' - ν y'), m x y - B) := by
      simp only [z, L, marginalsAndCost, LinearMap.coe_mk, AddHom.coe_mk]
      ext x' <;> simp [rowsSingle, columnsSingle, costSingle, sub_eq_neg_add]
    rw [image, read] at value
    have rowsValue : ∑ x', ((Pi.single x 1 : S → ℝ) x' - μ x') * gS x' = gS x - Gμ := by
      simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, Gμ, expect]
    have columnsValue : ∑ y', ((Pi.single y 1 : T → ℝ) y' - ν y') * gT y' = gT y - Gν := by
      simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, Gν, expect]
    rw [rowsValue, columnsValue] at value
    exact value
  rcases κ_nonneg.lt_or_eq with κ_pos | κ_zero
  · refine ⟨fun x => κ⁻¹ * gS x + (B - κ⁻¹ * (Gμ + u)), fun y => κ⁻¹ * gT y - κ⁻¹ * Gν,
      fun x y => ?_, ?_⟩
    · have := point x y
      have scaled : κ⁻¹ * (gS x - Gμ + (gT y - Gν) - u) < m x y - B := by
        rw [inv_mul_lt_iff₀ κ_pos]
        linarith
      nlinarith [scaled]
    · have left : expect μ (fun x => κ⁻¹ * gS x + (B - κ⁻¹ * (Gμ + u))) =
          κ⁻¹ * Gμ + (B - κ⁻¹ * (Gμ + u)) := by
        rw [expect_add, expect_mul_left, expect_const first]
      have right : expect ν (fun y => κ⁻¹ * gT y - κ⁻¹ * Gν) = 0 := by
        have split : expect ν (fun y => κ⁻¹ * gT y - κ⁻¹ * Gν) =
            expect ν (fun y => κ⁻¹ * gT y + -(κ⁻¹ * Gν)) := by
          simp only [sub_eq_add_neg]
        rw [split, expect_add, expect_mul_left, expect_const second]
        ring
      rw [left, right]
      have : 0 < -(κ⁻¹ * u) := by
        have := mul_neg_of_pos_of_neg (inv_pos.mpr κ_pos) u_neg
        linarith
      linarith
  · exfalso
    have each : ∀ x y, gS x + gT y ≤ u + Gμ + Gν := fun x y => by
      have := point x y
      rw [← κ_zero, mul_zero] at this
      linarith
    have inner : ∀ x, gS x + Gν ≤ u + Gμ + Gν := fun x => by
      have averaged := expect_mono second (each x)
      rw [expect_add, expect_const second, expect_const second] at averaged
      exact averaged
    have outer := expect_mono first inner
    rw [expect_add, expect_const first, expect_const first] at outer
    linarith

/-! ## The Kantorovich–Rubinstein form -/

section Rubinstein

variable [Nonempty S] {μ ν : S → ℝ} {d : S → S → ℝ}

omit [Nonempty S] in
/-- The difference of expectations of a function that `d` bounds from above is
at most the cost of every coupling. -/
theorem expect_sub_expect_le_cost {f : S → ℝ} (lipschitz : ∀ x y, f x - f y ≤ d x y)
    (ω : Coupling μ ν) : expect μ f - expect ν f ≤ ω.cost d := by
  rw [ω.expect_sub_expect f f]
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (lipschitz x y) (ω.nonneg x y)

/-- **The Kantorovich–Rubinstein form of duality.**  For a cost vanishing on the
diagonal and satisfying the triangle inequality, a lifting above `B` is
witnessed by one function `f` with `f x - f y ≤ d x y`. -/
theorem exists_lipschitz_of_lt_kantorovich (first : IsDistribution μ)
    (second : IsDistribution ν) (self : ∀ x, d x x = 0)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z) {B : ℝ} (lt : B < kantorovich d μ ν) :
    ∃ f : S → ℝ, (∀ x y, f x - f y ≤ d x y) ∧ B < expect μ f - expect ν f := by
  obtain ⟨φ, ψ, dual, value⟩ := exists_dual_of_lt_cost first second d fun ω =>
    lt.trans_le (kantorovich_le first d ω)
  set f : S → ℝ := fun x => Finset.univ.inf' Finset.univ_nonempty fun y => d x y - ψ y
  refine ⟨f, fun x x' => ?_, ?_⟩
  · obtain ⟨y, _, attained⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S))
      fun y => d x' y - ψ y
    have le : f x ≤ d x y - ψ y := Finset.inf'_le _ (Finset.mem_univ y)
    have value' : f x' = d x' y - ψ y := attained
    linarith [triangle x x' y]
  · have φ_le : ∀ x, φ x ≤ f x := fun x =>
      Finset.le_inf' _ _ fun y _ => by linarith [dual x y]
    have ψ_le : ∀ y, ψ y ≤ -f y := fun y => by
      have := Finset.inf'_le (s := Finset.univ) (fun y' => d y y' - ψ y') (Finset.mem_univ y)
      change f y ≤ d y y - ψ y at this
      rw [self] at this
      linarith
    have left := expect_mono first φ_le
    have right := expect_mono second ψ_le
    have negate : expect ν (fun y => -f y) = -expect ν f := by
      rw [show (fun y => -f y) = fun y => (-1) * f y from funext fun y => by ring,
        expect_mul_left]
      ring
    rw [negate] at right
    linarith

/-- **Kantorovich duality.**  For a cost vanishing on the diagonal and
satisfying the triangle inequality, the lifting is the supremum of the
differences of expectations of the functions that the cost bounds. -/
theorem kantorovich_eq_iSup_lipschitz (first : IsDistribution μ) (second : IsDistribution ν)
    (self : ∀ x, d x x = 0) (triangle : ∀ x y z, d x z ≤ d x y + d y z) :
    kantorovich d μ ν =
      ⨆ f : {f : S → ℝ // ∀ x y, f x - f y ≤ d x y}, (expect μ f.1 - expect ν f.1) := by
  have : Nonempty {f : S → ℝ // ∀ x y, f x - f y ≤ d x y} :=
    (inferInstance : Nonempty S).elim fun base =>
      ⟨⟨fun x => d x base, fun x y => by linarith [triangle x y base]⟩⟩
  have bounded : BddAbove (Set.range fun f : {f : S → ℝ // ∀ x y, f x - f y ≤ d x y} =>
      expect μ f.1 - expect ν f.1) := by
    obtain ⟨ω, _⟩ := exists_optimal_coupling first second d
    exact ⟨ω.cost d, by
      rintro _ ⟨f, rfl⟩
      exact expect_sub_expect_le_cost f.2 ω⟩
  apply le_antisymm
  · by_contra not_le'
    have greater := not_le.mp not_le'
    obtain ⟨f, lipschitz, value⟩ := exists_lipschitz_of_lt_kantorovich first second self triangle
      greater
    exact absurd (le_ciSup bounded ⟨f, lipschitz⟩) (not_le.mpr value)
  · exact ciSup_le fun f => le_kantorovich first second fun ω => expect_sub_expect_le_cost f.2 ω

end Rubinstein

end Mettapedia.GSLT.Distinction.Probabilistic
