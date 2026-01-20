/-
# Hölder Embedding via OrderedSemigroups

This file provides an alternative path to the K&S representation theorem:

  `NoAnomalousPairs α` → Eric's `¬has_anomalous_pair α` → `holder_not_anom` → ℝ embedding

By using Eric Luap's complete Hölder embedding theorem from OrderedSemigroups,
we can derive the representation theorem directly from the no-anomalous-pairs condition,
without needing the custom infrastructure in `AlimovEmbedding.lean`.

## Main Results

- `holder_embedding_of_noAnomalousPairs`: Main embedding theorem
- `representation_from_noAnomalousPairs`: K&S representation from NoAnomalousPairs

## References

- Luap, E. (2024). "OrderedSemigroups: Formalization in Lean 4." github.com/ericluap/OrderedSemigroups
- Alimov, N. G. (1950). "On ordered semigroups." Izv. Akad. Nauk SSSR Ser. Mat. 14, 569–576.

-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Globalization
-- Import Eric's OrderedSemigroups
import OrderedSemigroups.Holder
-- Import for Multiplicative type tag lemmas
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subsemigroup.Defs

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs
open Multiplicative (toAdd ofAdd)
open Subsemigroup

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-! ## Section 1: K&S Algebra provides Semigroup structure

We show that a `KnuthSkillingAlgebraBase` naturally gives rise to a `Semigroup`
with `mul := op`. The identity `ident` becomes the monoid identity `1`.
-/

/-- The K&S `op` operation viewed as multiplication. -/
instance KSAlgebra_to_Semigroup : Semigroup α where
  mul := op
  mul_assoc := op_assoc

/-- The K&S `ident` as the monoid identity. -/
instance KSAlgebra_to_One : One α where
  one := ident

/-- K&S algebra has a monoid structure (with identity). -/
instance KSAlgebra_to_Monoid : Monoid α where
  mul := op
  mul_assoc := op_assoc
  one := ident
  one_mul := op_ident_left
  mul_one := op_ident_right
  npow n x := iterate_op x n
  npow_zero x := iterate_op_zero x
  npow_succ n x := by
    -- Need: iterate_op x (n + 1) = op (iterate_op x n) x
    -- From iterate_op_add with m=n, n'=1:
    --   op (iterate_op x n) (iterate_op x 1) = iterate_op x (n + 1)
    -- Since iterate_op x 1 = x, we get:
    --   op (iterate_op x n) x = iterate_op x (n + 1)
    have h := iterate_op_add x n 1
    simp only [iterate_op_one] at h
    exact h.symm

/-! ## Section 2: K&S Algebra is an Ordered Cancel Semigroup -/

/-- K&S algebra is a left ordered semigroup (left multiplication preserves order). -/
instance KSAlgebra_to_IsLeftOrderedSemigroup : IsLeftOrderedSemigroup α where
  mul_le_mul_left' a b hab c := by
    -- Need: a ≤ b → c * a ≤ c * b, i.e., op c a ≤ op c b
    rcases hab.lt_or_eq with hlt | heq
    · exact le_of_lt (op_strictMono_right c hlt)
    · rw [heq]

/-- K&S algebra is a right ordered semigroup (right multiplication preserves order). -/
instance KSAlgebra_to_IsRightOrderedSemigroup : IsRightOrderedSemigroup α where
  mul_le_mul_right' a b hab c := by
    -- Need: a ≤ b → a * c ≤ b * c, i.e., op a c ≤ op b c
    rcases hab.lt_or_eq with hlt | heq
    · exact le_of_lt (op_strictMono_left c hlt)
    · rw [heq]

/-- K&S algebra is a left ordered cancel semigroup. -/
instance KSAlgebra_to_IsLeftOrderedCancelSemigroup : IsLeftOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' a b c hab := by
    -- Need: a * b ≤ a * c → b ≤ c, i.e., op a b ≤ op a c → b ≤ c
    by_contra h_not
    push_neg at h_not
    have hlt : c < b := h_not
    have hlt' : op a c < op a b := op_strictMono_right a hlt
    exact absurd hab (not_le_of_gt hlt')

/-- K&S algebra is a right ordered cancel semigroup. -/
instance KSAlgebra_to_IsRightOrderedCancelSemigroup : IsRightOrderedCancelSemigroup α where
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' a b c hab := by
    -- Signature: ∀ a b c : α, b * a ≤ c * a → b ≤ c
    -- hab : b * a ≤ c * a (i.e., op b a ≤ op c a)
    -- Goal: b ≤ c
    by_contra h_not
    push_neg at h_not
    have hlt : c < b := h_not
    have hlt' : op c a < op b a := op_strictMono_left a hlt
    -- hlt' : op c a < op b a, but hab : op b a ≤ op c a - contradiction
    exact absurd hab (not_le_of_gt hlt')

/-- K&S algebra is an ordered cancel semigroup. -/
instance KSAlgebra_to_IsOrderedCancelSemigroup : IsOrderedCancelSemigroup α where
  mul_le_mul_left' := IsLeftOrderedSemigroup.mul_le_mul_left'
  le_of_mul_le_mul_right' := IsLeftOrderedCancelSemigroup.le_of_mul_le_mul_right'
  mul_le_mul_right' := IsRightOrderedSemigroup.mul_le_mul_right'
  le_of_mul_le_mul_left' := IsRightOrderedCancelSemigroup.le_of_mul_le_mul_left'

/-! ## Section 4: Definition equivalence

Our `AnomalousPair a b` is equivalent to Eric's `anomalous_pair a b`.
-/

/-- Our anomalous pair definition matches Eric's structurally.

Eric uses: `∀n : ℕ+, (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))`
We use:   `∀n : ℕ, 0 < n → (a^n < b^n ∧ b^n < a^(n+1)) ∨ (a^n > b^n ∧ b^n > a^(n+1))`

These are equivalent since ℕ+ ≃ {n : ℕ | 0 < n}.
-/
theorem anomalousPair_iff_eric (a b : α) :
    AnomalousPair a b ↔ anomalous_pair a b := by
  constructor
  · -- Our definition → Eric's
    intro hAnom n
    have hn_pos : 0 < (n : ℕ) := n.pos
    specialize hAnom n hn_pos
    -- Need to convert between iterate_op and ^
    simp only [HPow.hPow, Pow.pow] at hAnom ⊢
    convert hAnom using 2
  · -- Eric's → Our definition
    intro hEric n hn_pos
    specialize hEric ⟨n, hn_pos⟩
    simp only [HPow.hPow, Pow.pow, PNat.mk_coe, PNat.add_coe, PNat.val_ofNat] at hEric ⊢
    exact hEric

/-- No anomalous pairs in our sense ↔ no anomalous pairs in Eric's sense. -/
theorem noAnomalousPairs_iff_eric [NoAnomalousPairs α] :
    ¬has_anomalous_pair (α := α) := by
  intro ⟨a, b, hAnom⟩
  have hOurs : AnomalousPair a b := (anomalousPair_iff_eric a b).mpr hAnom
  exact NoAnomalousPairs.not_anomalous a b hOurs

theorem eric_noAnomalousPairs_to_ours (h : ¬has_anomalous_pair (α := α)) :
    NoAnomalousPairs α := by
  constructor
  intro a b hAnom
  have hEric : anomalous_pair a b := (anomalousPair_iff_eric a b).mp hAnom
  exact h ⟨a, b, hEric⟩

/-! ## Section 6: Main Embedding Theorem

Using Eric's `holder_not_anom`, we get an embedding into ℝ.
-/

/-- **Main Theorem**: If a K&S algebra has no anomalous pairs, it embeds into ℝ.

This is Eric's Hölder theorem specialized to our setting. The embedding is into
`Multiplicative ℝ`, where multiplication corresponds to addition of reals.
Thus, for any `a, b : α`:
- `Θ(op a b) = Θ a + Θ b` (in ℝ)
- `a ≤ b ↔ Θ a ≤ Θ b`
-/
theorem holder_embedding_of_noAnomalousPairs [NoAnomalousPairs α] :
    ∃ G : Subsemigroup (Multiplicative ℝ), Nonempty (α ≃*o G) := by
  have h : ¬has_anomalous_pair (α := α) := noAnomalousPairs_iff_eric
  exact holder_not_anom h

/-! ## Section 7: Extracting the Representation Function Θ

From the Hölder embedding, we construct the representation function Θ : α → ℝ
satisfying the K&S representation theorem requirements.
-/

/-- From the multiplicative order isomorphism, extract the additive representation.

In `Multiplicative ℝ`, the group operation is `*` which corresponds to `+` in ℝ.
An element `x : Multiplicative ℝ` with `Multiplicative.toAdd x = r` represents
the real number `r`. The group multiplication is `Multiplicative.ofAdd (r + s)`.
-/
noncomputable def theta_from_embedding [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) : α → ℝ :=
  fun a => Multiplicative.toAdd (iso a : Multiplicative ℝ)

theorem theta_preserves_order [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    ∀ a b : α, a ≤ b ↔ theta_from_embedding G iso a ≤ theta_from_embedding G iso b := by
  intro a b
  simp only [theta_from_embedding]
  constructor
  · intro hab
    have h1 : iso a ≤ iso b := iso.map_le_map_iff'.mpr hab
    exact h1
  · intro hθ
    have h1 : iso a ≤ iso b := hθ
    exact iso.map_le_map_iff'.mp h1

theorem theta_ident [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    theta_from_embedding G iso ident = 0 := by
  unfold theta_from_embedding
  -- We need to show: Multiplicative.toAdd (iso ident : Multiplicative ℝ) = 0
  -- This is equivalent to: (iso ident : Multiplicative ℝ) = 1

  -- Use the fact that for all x, ident * x = x, so iso(ident * x) = iso(x)
  -- But iso(ident * x) = iso(ident) * iso(x), so iso(ident) * iso(x) = iso(x)
  have h_left_id : ∀ x : α, op ident x = x := op_ident_left
  -- iso preserves multiplication, so iso(ident * x) = iso(ident) * iso(x)
  have h_map : ∀ x : α, iso (op ident x) = iso ident * iso x := fun x => map_mul iso ident x

  -- Since iso(ident * ident) = iso(ident) and iso(ident * ident) = iso(ident) * iso(ident),
  -- we have iso(ident) * iso(ident) = iso(ident)
  have h1 : (iso ident : G) * iso ident = iso ident := by
    rw [← h_map ident, h_left_id ident]

  -- Coerce to Multiplicative ℝ
  -- In a subsemigroup, multiplication is inherited: (x * y : G).val = x.val * y.val
  have h2 : (↑(iso ident) : Multiplicative ℝ) * ↑(iso ident) = ↑(iso ident) := by
    have h1' := congrArg (·.val) h1
    convert h1' using 1

  -- Convert to additive form: (x * y).toAdd = x.toAdd + y.toAdd
  have h3 : (↑(iso ident) : Multiplicative ℝ).toAdd +
            (↑(iso ident) : Multiplicative ℝ).toAdd =
            (↑(iso ident) : Multiplicative ℝ).toAdd := by
    have := congrArg Multiplicative.toAdd h2
    convert this using 1

  -- From x + x = x, we get x = 0
  linarith

theorem theta_additive [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    ∀ x y : α, theta_from_embedding G iso (op x y) =
               theta_from_embedding G iso x + theta_from_embedding G iso y := by
  intro x y
  unfold theta_from_embedding
  -- iso (x * y) = iso x * iso y, where * is op
  have h : iso (op x y) = iso x * iso y := map_mul iso x y
  simp only [h]
  -- In Multiplicative ℝ: toAdd (a * b) = toAdd a + toAdd b
  rfl

/-! ## Section 8: The Full Representation Theorem from NoAnomalousPairs -/

/-- **K&S Appendix A via Hölder**: `NoAnomalousPairs α` implies the representation theorem.

This is an alternative to the `KSSeparation`-based proof, using Eric's complete
Hölder embedding theorem.
-/
theorem representation_from_noAnomalousPairs [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  obtain ⟨G, ⟨iso⟩⟩ := holder_embedding_of_noAnomalousPairs (α := α)
  use theta_from_embedding G iso
  exact ⟨theta_preserves_order G iso, theta_ident G iso, theta_additive G iso⟩

/-! ## Section 9: Identity-Free Representation (Semigroup Version)

The Hölder/Alimov embedding does NOT require identity. This section makes that explicit.

**What identity provides:**
- Canonical normalization: Θ(ident) = 0 pins down the additive constant
- Without identity, Θ is defined only up to an additive constant

**K&S reference:** Lines 320, 340-342 of "Foundations of Inference" (2012) state
that the bottom element (identity) is "optional" in the lattice framework. -/

/-- **Semigroup Representation Theorem**: NoAnomalousPairs implies additive embedding into ℝ.
    This version does NOT require identity - Θ is defined up to an additive constant.

    Compared to `representation_from_noAnomalousPairs`:
    - Same: order-preserving, additive homomorphism
    - Missing: `Θ ident = 0` (no canonical zero point)

    This matches K&S's claim that identity is "optional" (K&S 2012, lines 340-342). -/
theorem representation_semigroup [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) := by
  obtain ⟨G, ⟨iso⟩⟩ := holder_embedding_of_noAnomalousPairs (α := α)
  use theta_from_embedding G iso
  exact ⟨theta_preserves_order G iso, theta_additive G iso⟩

/-- Identity provides canonical normalization: Θ(ident) = 0.
    Without identity, Θ is defined only up to an additive constant c:
    if Θ is a valid representation, so is Θ' = Θ + c.

    With identity, we can pin down c = 0 by requiring Θ(ident) = 0. -/
theorem identity_gives_canonical_normalization [NoAnomalousPairs α]
    (G : Subsemigroup (Multiplicative ℝ)) (iso : α ≃*o G) :
    theta_from_embedding G iso ident = 0 :=
  theta_ident G iso

/-- The representation is unique up to positive scaling.
    Identity pins down the additive constant (Θ(ident) = 0).
    A scale convention (e.g., choosing a reference element) pins down the scale.

    Proof strategy: Both embeddings respect the same order structure on iterates, so
    a^m ≤ x^n ↔ m·Θ₁(a) ≤ n·Θ₁(x) ↔ m·Θ₂(a) ≤ n·Θ₂(x).
    This forces Θ₁(x)/Θ₁(a) = Θ₂(x)/Θ₂(a) for positive elements. -/
theorem representation_uniqueness_structure [NoAnomalousPairs α]
    (Θ₁ Θ₂ : α → ℝ)
    (h1_ord : ∀ a b : α, a ≤ b ↔ Θ₁ a ≤ Θ₁ b)
    (h2_ord : ∀ a b : α, a ≤ b ↔ Θ₂ a ≤ Θ₂ b)
    (h1_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (h2_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y)
    (h1_ident : Θ₁ ident = 0)
    (h2_ident : Θ₂ ident = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x := by
  -- Handle trivial case: if all elements equal ident
  by_cases htriv : ∀ x : α, x = ident
  · refine ⟨1, one_pos, fun x => ?_⟩
    simp only [htriv x, h1_ident, h2_ident, mul_zero]
  -- Non-trivial: get a reference element a > ident
  push_neg at htriv
  obtain ⟨a, ha_ne⟩ := htriv
  have ha_pos : ident < a := lt_of_le_of_ne (ident_le a) (Ne.symm ha_ne)
  -- Both Θ values are positive for a > ident
  have hΘ1a_pos : 0 < Θ₁ a := by
    have h := (h1_ord ident a).mp (le_of_lt ha_pos)
    rw [h1_ident] at h
    rcases h.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; have : a ≤ ident := (h1_ord a ident).mpr (by rw [h1_ident]; exact le_of_eq heq.symm)
      exact not_lt.mpr this ha_pos
  have hΘ2a_pos : 0 < Θ₂ a := by
    have h := (h2_ord ident a).mp (le_of_lt ha_pos)
    rw [h2_ident] at h
    rcases h.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; have : a ≤ ident := (h2_ord a ident).mpr (by rw [h2_ident]; exact le_of_eq heq.symm)
      exact not_lt.mpr this ha_pos
  -- Define the scaling factor
  let c := Θ₂ a / Θ₁ a
  have hc_pos : 0 < c := div_pos hΘ2a_pos hΘ1a_pos
  refine ⟨c, hc_pos, fun x => ?_⟩
  -- Iteration lemmas
  have h_iter_Θ1 : ∀ y : α, ∀ n : ℕ, Θ₁ (iterate_op y n) = n * Θ₁ y := fun y n => by
    induction n with
    | zero => simp [iterate_op_zero, h1_ident]
    | succ n ih =>
      rw [iterate_op_succ, h1_add, ih]
      simp only [Nat.cast_succ]; ring
  have h_iter_Θ2 : ∀ y : α, ∀ n : ℕ, Θ₂ (iterate_op y n) = n * Θ₂ y := fun y n => by
    induction n with
    | zero => simp [iterate_op_zero, h2_ident]
    | succ n ih =>
      rw [iterate_op_succ, h2_add, ih]
      simp only [Nat.cast_succ]; ring
  -- For positive y, the ratios Θ₁(y)/Θ₁(a) and Θ₂(y)/Θ₂(a) are equal
  -- because both embeddings see the same order on a^m vs y^n
  have h_ratio_pos : ∀ y : α, ident < y → Θ₁ y / Θ₁ a = Θ₂ y / Θ₂ a := fun y hy => by
    have hΘ1y_pos : 0 < Θ₁ y := by
      have h := (h1_ord ident y).mp (le_of_lt hy)
      rw [h1_ident] at h
      rcases h.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have : y ≤ ident := (h1_ord y ident).mpr (by rw [h1_ident]; exact le_of_eq heq.symm)
        exact not_lt.mpr this hy
    have hΘ2y_pos : 0 < Θ₂ y := by
      have h := (h2_ord ident y).mp (le_of_lt hy)
      rw [h2_ident] at h
      rcases h.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have : y ≤ ident := (h2_ord y ident).mpr (by rw [h2_ident]; exact le_of_eq heq.symm)
        exact not_lt.mpr this hy
    -- Key: a^m ≤ y^n ↔ m·Θ₁(a) ≤ n·Θ₁(y) ↔ m·Θ₂(a) ≤ n·Θ₂(y)
    -- This means the set {m/n : a^m ≤ y^n} defines the same real for both ratios
    by_contra hne
    -- Either Θ₁(y)/Θ₁(a) < Θ₂(y)/Θ₂(a) or vice versa
    have hne' : Θ₁ y / Θ₁ a ≠ Θ₂ y / Θ₂ a := hne
    rcases hne'.lt_or_gt with hlt | hlt
    · -- Case 1: Θ₁(y)/Θ₁(a) < Θ₂(y)/Θ₂(a)
      obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn hlt
      have hq_pos : 0 < q := by
        have : (0 : ℝ) < Θ₁ y / Θ₁ a := div_pos hΘ1y_pos hΘ1a_pos
        exact_mod_cast lt_trans this hq_lo
      have hn_pos : 0 < q.den := q.den_pos
      have hm_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
      let m := q.num.toNat; let n := q.den
      have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      -- Cast q to ℝ: q = (q.num : ℝ) / q.den
      have hq_lo' : Θ₁ y / Θ₁ a < (q.num : ℝ) / q.den := by
        convert hq_lo using 1; simp [Rat.cast_def]
      have hq_hi' : (q.num : ℝ) / q.den < Θ₂ y / Θ₂ a := by
        convert hq_hi using 1; simp [Rat.cast_def]
      -- Key: (m : ℝ) = (q.num : ℝ) since m = q.num.toNat and q.num > 0
      have hm_eq : (m : ℝ) = (q.num : ℝ) := by
        have : (m : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hm_pos)
        exact_mod_cast this
      -- From Θ₁(y)/Θ₁(a) < q.num/n: y^n < a^m via Θ₁
      have h_order_1 : iterate_op y n < iterate_op a m := by
        rw [lt_iff_not_ge]; intro hle  -- hle : a^m ≤ y^n
        have hmΘ := (h1_ord (iterate_op a m) (iterate_op y n)).mp hle
        rw [h_iter_Θ1, h_iter_Θ1] at hmΘ  -- hmΘ : m * Θ₁ a ≤ n * Θ₁ y
        -- From Θ₁(y)/Θ₁(a) < m/n: n * Θ₁ y < m * Θ₁ a
        have hnΘ : (n : ℝ) * Θ₁ y < (m : ℝ) * Θ₁ a := by
          have h := mul_lt_mul_of_pos_right hq_lo' (mul_pos hn_pos' hΘ1a_pos)
          field_simp at h; rw [hm_eq]; linarith
        linarith
      -- From q.num/n < Θ₂(y)/Θ₂(a): a^m < y^n via Θ₂
      have h_order_2 : iterate_op a m < iterate_op y n := by
        rw [lt_iff_not_ge]; intro hle  -- hle : y^n ≤ a^m
        have hnΘ := (h2_ord (iterate_op y n) (iterate_op a m)).mp hle
        rw [h_iter_Θ2, h_iter_Θ2] at hnΘ  -- hnΘ : n * Θ₂ y ≤ m * Θ₂ a
        -- From m/n < Θ₂(y)/Θ₂(a): m * Θ₂ a < n * Θ₂ y
        have hmΘ : (m : ℝ) * Θ₂ a < (n : ℝ) * Θ₂ y := by
          have h := mul_lt_mul_of_pos_right hq_hi' (mul_pos hn_pos' hΘ2a_pos)
          field_simp at h; rw [hm_eq]; linarith
        linarith
      exact absurd h_order_2 (not_lt.mpr (le_of_lt h_order_1))
    · -- Case 2: Θ₂(y)/Θ₂(a) < Θ₁(y)/Θ₁(a) (symmetric)
      obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn hlt
      have hq_pos : 0 < q := by
        have : (0 : ℝ) < Θ₂ y / Θ₂ a := div_pos hΘ2y_pos hΘ2a_pos
        exact_mod_cast lt_trans this hq_lo
      have hn_pos : 0 < q.den := q.den_pos
      have hm_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
      let m := q.num.toNat; let n := q.den
      have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hq_lo' : Θ₂ y / Θ₂ a < (q.num : ℝ) / q.den := by
        convert hq_lo using 1; simp [Rat.cast_def]
      have hq_hi' : (q.num : ℝ) / q.den < Θ₁ y / Θ₁ a := by
        convert hq_hi using 1; simp [Rat.cast_def]
      -- Key: (m : ℝ) = (q.num : ℝ) since m = q.num.toNat and q.num > 0
      have hm_eq : (m : ℝ) = (q.num : ℝ) := by
        have : (m : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hm_pos)
        exact_mod_cast this
      -- From Θ₂(y)/Θ₂(a) < q.num/n: y^n < a^m via Θ₂
      have h_order_1 : iterate_op y n < iterate_op a m := by
        rw [lt_iff_not_ge]; intro hle  -- hle : a^m ≤ y^n
        have hmΘ := (h2_ord (iterate_op a m) (iterate_op y n)).mp hle
        rw [h_iter_Θ2, h_iter_Θ2] at hmΘ  -- hmΘ : m * Θ₂ a ≤ n * Θ₂ y
        -- From Θ₂(y)/Θ₂(a) < m/n: n * Θ₂ y < m * Θ₂ a
        have hnΘ : (n : ℝ) * Θ₂ y < (m : ℝ) * Θ₂ a := by
          have h := mul_lt_mul_of_pos_right hq_lo' (mul_pos hn_pos' hΘ2a_pos)
          field_simp at h; rw [hm_eq]; linarith
        linarith
      -- From q.num/n < Θ₁(y)/Θ₁(a): a^m < y^n via Θ₁
      have h_order_2 : iterate_op a m < iterate_op y n := by
        rw [lt_iff_not_ge]; intro hle  -- hle : y^n ≤ a^m
        have hnΘ := (h1_ord (iterate_op y n) (iterate_op a m)).mp hle
        rw [h_iter_Θ1, h_iter_Θ1] at hnΘ  -- hnΘ : n * Θ₁ y ≤ m * Θ₁ a
        -- From m/n < Θ₁(y)/Θ₁(a): m * Θ₁ a < n * Θ₁ y
        have hmΘ : (m : ℝ) * Θ₁ a < (n : ℝ) * Θ₁ y := by
          have h := mul_lt_mul_of_pos_right hq_hi' (mul_pos hn_pos' hΘ1a_pos)
          field_simp at h; rw [hm_eq]; linarith
        linarith
      exact absurd h_order_2 (not_lt.mpr (le_of_lt h_order_1))
  -- Main proof by cases on x
  rcases lt_trichotomy x ident with hx_lt | hx_eq | hx_gt
  · -- Case x < ident: need Archimedean property
    -- There exists n such that op x (a^n) > ident
    -- Then use additivity to reduce to positive case
    have hΘ1x_neg : Θ₁ x < 0 := by
      have h := (h1_ord x ident).mp (le_of_lt hx_lt)
      rw [h1_ident] at h
      rcases h.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have : ident ≤ x := (h1_ord ident x).mpr (by rw [h1_ident]; exact le_of_eq heq.symm)
        exact not_lt.mpr this hx_lt
    -- Find n such that x ⊕ a^n > ident
    -- Θ₁(x ⊕ a^n) = Θ₁(x) + n·Θ₁(a), want this > 0
    -- So need n > -Θ₁(x)/Θ₁(a)
    have h_exists : ∃ n : ℕ, 0 < Θ₁ x + n * Θ₁ a := by
      use Nat.ceil ((-Θ₁ x) / Θ₁ a) + 1
      have hceil : (-Θ₁ x) / Θ₁ a ≤ Nat.ceil ((-Θ₁ x) / Θ₁ a) := Nat.le_ceil _
      have hM_gt : ((Nat.ceil ((-Θ₁ x) / Θ₁ a) + 1 : ℕ) : ℝ) > (-Θ₁ x) / Θ₁ a := by
        have : (Nat.ceil ((-Θ₁ x) / Θ₁ a) : ℝ) + 1 > (-Θ₁ x) / Θ₁ a := by linarith
        convert this using 1
        simp only [Nat.cast_add, Nat.cast_one]
      -- From M > -Θ₁(x)/Θ₁(a), multiply by Θ₁(a) > 0: M * Θ₁(a) > -Θ₁(x)
      have hMa : ((Nat.ceil ((-Θ₁ x) / Θ₁ a) + 1 : ℕ) : ℝ) * Θ₁ a > -Θ₁ x := by
        have h := mul_lt_mul_of_pos_right hM_gt hΘ1a_pos
        rwa [div_mul_cancel₀ _ (ne_of_gt hΘ1a_pos)] at h
      linarith
    obtain ⟨n, hn⟩ := h_exists
    -- So Θ₁(x ⊕ a^n) > 0, meaning x ⊕ a^n > ident
    have hsum_pos : ident < op x (iterate_op a n) := by
      -- Derive strict order from non-strict: a < b ↔ ¬(b ≤ a)
      rw [lt_iff_not_ge]
      intro hle
      have := (h1_ord (op x (iterate_op a n)) ident).mp hle
      rw [h1_add, h_iter_Θ1, h1_ident] at this
      linarith
    -- Apply ratio equality to the positive element
    have h_sum_ratio := h_ratio_pos (op x (iterate_op a n)) hsum_pos
    -- Θ₁(x ⊕ a^n)/Θ₁(a) = Θ₂(x ⊕ a^n)/Θ₂(a)
    -- (Θ₁(x) + n·Θ₁(a))/Θ₁(a) = (Θ₂(x) + n·Θ₂(a))/Θ₂(a)
    rw [h1_add, h2_add, h_iter_Θ1, h_iter_Θ2] at h_sum_ratio
    -- Θ₁(x)/Θ₁(a) + n = Θ₂(x)/Θ₂(a) + n
    have hΘ1a_ne : Θ₁ a ≠ 0 := ne_of_gt hΘ1a_pos
    have hΘ2a_ne : Θ₂ a ≠ 0 := ne_of_gt hΘ2a_pos
    have h_x_ratio : Θ₁ x / Θ₁ a = Θ₂ x / Θ₂ a := by
      have h1 : (Θ₁ x + ↑n * Θ₁ a) / Θ₁ a = Θ₁ x / Θ₁ a + n := by
        field_simp [hΘ1a_ne]
      have h2 : (Θ₂ x + ↑n * Θ₂ a) / Θ₂ a = Θ₂ x / Θ₂ a + n := by
        field_simp [hΘ2a_ne]
      rw [h1, h2] at h_sum_ratio
      linarith
    -- Θ₂(x) = (Θ₂(a)/Θ₁(a)) · Θ₁(x)
    have : Θ₂ x = Θ₂ a / Θ₁ a * Θ₁ x := by
      have := congr_arg (· * Θ₂ a) h_x_ratio
      field_simp [hΘ1a_ne, hΘ2a_ne] at this ⊢
      linarith
    exact this
  · -- Case x = ident
    simp [hx_eq, h1_ident, h2_ident]
  · -- Case x > ident: direct application
    have h_x_ratio := h_ratio_pos x hx_gt
    have : Θ₂ x = Θ₂ a / Θ₁ a * Θ₁ x := by
      have := congr_arg (· * Θ₂ a) h_x_ratio
      field_simp at this ⊢
      linarith
    exact this

/-! ## Section 10: Unified Representation Interface

A common interface for representation results across different paths.
This allows unified reasoning about what each path provides.

**Three representation paths in K&S formalization:**
1. **Hölder path** (this file): `NoAnomalousPairs α` → embedding via Eric's theorem
2. **KSSeparation path** (`RepresentationTheorem/`): `KSSeparation α` → direct construction
3. **Direct cuts path** (planned): Dedekind cuts without separation axiom

**What identity adds:** Canonical normalization `Θ ident = 0`.
Without identity, Θ is defined only up to additive constant. -/

/-- **Representation result** (identity-free version).
    Captures the minimal structure: order embedding + additive homomorphism.
    This is what the Hölder/Alimov theorem provides without identity. -/
structure RepresentationResult (α : Type*) [KSSemigroupBase α] where
  /-- The representation function Θ : α → ℝ -/
  Θ : α → ℝ
  /-- Order-preserving: a ≤ b ↔ Θ a ≤ Θ b -/
  order_preserving : ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b
  /-- Additive homomorphism: Θ(x ⊕ y) = Θ x + Θ y -/
  additive : ∀ x y : α, Θ (op x y) = Θ x + Θ y

/-- **Normalized representation result** (with identity).
    Extends RepresentationResult with canonical normalization Θ(ident) = 0.
    This is what identity provides beyond the semigroup case. -/
structure NormalizedRepresentationResult (α : Type*) [KnuthSkillingAlgebraBase α]
    extends RepresentationResult α where
  /-- Canonical normalization: Θ(ident) = 0 -/
  ident_zero : Θ ident = 0

/-- Hölder path produces a RepresentationResult (identity-free). -/
noncomputable def holder_representation [NoAnomalousPairs α] : RepresentationResult α :=
  let h := representation_semigroup (α := α)
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2 }

/-- Hölder path produces a NormalizedRepresentationResult (with identity). -/
noncomputable def holder_normalized_representation [NoAnomalousPairs α] :
    NormalizedRepresentationResult α :=
  let h := representation_from_noAnomalousPairs (α := α)
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2.2
    ident_zero := (Classical.choose_spec h).2.1 }

/-- Strict order-preserving: a < b ↔ Θ a < Θ b -/
theorem RepresentationResult.strict_order_preserving {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : ∀ a b : α, a < b ↔ r.Θ a < r.Θ b := by
  intro a b
  constructor
  · intro hab
    have h1 : a ≤ b := le_of_lt hab
    have h2 : ¬(b ≤ a) := not_le_of_gt hab
    have hΘ1 : r.Θ a ≤ r.Θ b := (r.order_preserving a b).mp h1
    have hΘ2 : ¬(r.Θ b ≤ r.Θ a) := fun h => h2 ((r.order_preserving b a).mpr h)
    exact lt_of_le_of_ne hΘ1 (fun heq => hΘ2 (le_of_eq heq.symm))
  · intro hΘ
    have h1 : r.Θ a ≤ r.Θ b := le_of_lt hΘ
    have h2 : ¬(r.Θ b ≤ r.Θ a) := not_le_of_gt hΘ
    have ha1 : a ≤ b := (r.order_preserving a b).mpr h1
    have ha2 : ¬(b ≤ a) := fun h => h2 ((r.order_preserving b a).mp h)
    exact lt_of_le_of_ne ha1 (fun heq => ha2 (le_of_eq heq.symm))

/-- Representation is injective (order embedding). -/
theorem RepresentationResult.injective {α : Type*} [KSSemigroupBase α]
    (r : RepresentationResult α) : Function.Injective r.Θ := by
  intro a b hab
  have h1 : r.Θ a ≤ r.Θ b := le_of_eq hab
  have h2 : r.Θ b ≤ r.Θ a := le_of_eq hab.symm
  have ha1 : a ≤ b := (r.order_preserving a b).mpr h1
  have ha2 : b ≤ a := (r.order_preserving b a).mpr h2
  exact le_antisymm ha1 ha2

/-! ## Grid Path Representation

The grid path uses `KSSeparation` + globalization to produce representations.
Grid iteration uses `iterate_op x 0 = ident`, so identity is required for the construction.

**Identity-free separation (`KSSeparationSemigroup`)**:
- Uses `IsPositive` (Eric Luap's approach) instead of `ident < a`
- Uses `iterate_op_pnat` (ℕ+ iteration) instead of `iterate_op` (ℕ iteration)
- When identity exists: `KSSeparation ↔ KSSeparationSemigroup` (see `Algebra.lean`)

The parametric grid constructions (`mu_param`, `kGrid_param`) allow shifting
the base element, but the grid path itself produces `NormalizedRepresentationResult`
with the canonical `Θ(ident) = 0` normalization. -/

section GridPath
open Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem in
variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α] [RepresentationGlobalization α]

open Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem in
/-- Grid path produces a NormalizedRepresentationResult (with identity).
    This wraps the `RepresentationGlobalization` class into our unified interface. -/
noncomputable def grid_normalized_representation {α : Type*}
    [KnuthSkillingAlgebraBase α] [KSSeparation α] [RepresentationGlobalization α] :
    NormalizedRepresentationResult α :=
  let h := RepresentationGlobalization.exists_Theta (α := α)
  { Θ := Classical.choose h
    order_preserving := (Classical.choose_spec h).1
    additive := (Classical.choose_spec h).2.2
    ident_zero := (Classical.choose_spec h).2.1 }

open Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem in
/-- Grid path from `KSSeparationSemigroup` (when identity exists).

    When identity exists, `KSSeparationSemigroup` implies `KSSeparation` via
    the equivalence in `Algebra.lean`. This function shows the integration. -/
noncomputable def grid_normalized_representation_from_semigroup_sep {α : Type*}
    [KnuthSkillingAlgebraBase α] [KSSeparationSemigroup α]
    [@RepresentationGlobalization α _ (KSSeparation_of_KSSeparationSemigroup)] :
    NormalizedRepresentationResult α :=
  @grid_normalized_representation α _ KSSeparation_of_KSSeparationSemigroup _

open Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem in
/-- Grid path produces a RepresentationResult (identity-free interface).

    This extracts just the order + additivity properties from the normalized result.
    Since `NormalizedRepresentationResult` extends `RepresentationResult`, this is
    a simple extraction. The grid construction internally uses identity, but the
    resulting `Θ : α → ℝ` doesn't depend on `Θ(ident) = 0` for its properties.

    **Use case**: When you want to work with the unified `RepresentationResult`
    interface across all paths (Hölder, Grid, Cuts) without committing to identity. -/
noncomputable def grid_representation {α : Type*}
    [KnuthSkillingAlgebraBase α] [KSSeparation α] [RepresentationGlobalization α] :
    RepresentationResult α :=
  (grid_normalized_representation (α := α)).toRepresentationResult

end GridPath

/-! ## Path Comparison

**Hölder Path** (`NoAnomalousPairs`):
- Works on `KSSemigroupBase` (identity-free) → `RepresentationResult`
- Works on `KnuthSkillingAlgebraBase` (with identity) → `NormalizedRepresentationResult`
- Uses Eric Luap's OrderedSemigroups library

**Grid Path** (`KSSeparation` or `KSSeparationSemigroup`):
- Requires `KnuthSkillingAlgebraBase` (with identity) → `NormalizedRepresentationResult`
- Uses multi-grid construction and globalization via "triple family trick"
- With identity: `KSSeparation ↔ KSSeparationSemigroup` (both work via equivalence)

**Cuts Path** (`KSSeparationStrict`):
- Requires `KnuthSkillingAlgebraBase` (with identity) → `RepresentationResult` / `NormalizedRepresentationResult`
- Uses Dedekind cuts construction (DirectCuts.lean)
- Identity-free infrastructure: `cutSet_pnat`, `Θ_cuts_pnat`, Archimedean from separation

**Separation Classes**:
- `KSSeparation`: Uses `ident < a` (requires identity)
- `KSSeparationSemigroup`: Uses `IsPositive a` (identity-free definition, but construction needs identity)

**Uniqueness**: All paths produce representations unique up to positive scale
(see `representation_uniqueness_structure`). -/

section PathEquivalence

open Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
open KnuthSkillingAlgebraBase KSSemigroupBase

/-- **Path Equivalence Theorem**: The Hölder and Grid paths produce equivalent representations.

Both `holder_normalized_representation` and `grid_normalized_representation` satisfy order + additivity + ident=0.
By `representation_uniqueness_structure`, they're related by positive scaling.

This is a foundational result: K&S representation is unique up to scale,
regardless of which construction path is used. -/
theorem holder_grid_paths_equivalent {α : Type*}
    [KnuthSkillingAlgebraBase α] [NoAnomalousPairs α] [KSSeparation α] [RepresentationGlobalization α] :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, (grid_normalized_representation (α := α)).Θ x =
      c * (holder_normalized_representation (α := α)).Θ x := by
  exact representation_uniqueness_structure
    (holder_normalized_representation (α := α)).Θ
    (grid_normalized_representation (α := α)).Θ
    (holder_normalized_representation (α := α)).order_preserving
    (grid_normalized_representation (α := α)).order_preserving
    (holder_normalized_representation (α := α)).additive
    (grid_normalized_representation (α := α)).additive
    (holder_normalized_representation (α := α)).ident_zero
    (grid_normalized_representation (α := α)).ident_zero

/-- The Hölder path is the canonical identity-free representation.
    When identity exists, other paths are equivalent to it. -/
theorem holder_is_canonical {α : Type*} [KnuthSkillingAlgebraBase α] [NoAnomalousPairs α] :
    ∀ R : NormalizedRepresentationResult α,
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, R.Θ x = c * (holder_normalized_representation (α := α)).Θ x :=
  fun R => representation_uniqueness_structure
    (holder_normalized_representation (α := α)).Θ
    R.Θ
    (holder_normalized_representation (α := α)).order_preserving
    R.order_preserving
    (holder_normalized_representation (α := α)).additive
    R.additive
    (holder_normalized_representation (α := α)).ident_zero
    R.ident_zero

end PathEquivalence

end Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.HolderEmbedding
