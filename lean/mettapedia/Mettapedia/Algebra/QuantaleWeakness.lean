/-
# Quantale Weakness Theory

Formalization of Ben Goertzel's quantale-based weakness theory from
"Weakness and Its Quantale: Plausibility Theory from First Principles"

The key insight: Bennett's "weakness" measure generalizes to quantales,
providing a unified framework for plausibility, probability, and logical entropy.

## Core Definitions

- **Bennett's Weakness**: w(H) = |H| for an event H ⊆ U × U
- **Probabilistic Weakness**: wₚ(H) = Σ_{(u,v)∈H} p(u)·p(v)
- **Quantale Weakness**: w(H) = ⊕_{(u,v)∈H} [μ(u) ⊗ μ(v)]

## References

- Goertzel, "Weakness and Its Quantale"
- Rosenthal, "Quantales and their Applications"
- Ellerman, "Logical Entropy"
-/

import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Hammer

namespace Mettapedia.Algebra.QuantaleWeakness

open scoped ENNReal
open Finset

/-! ## Commutative Quantales

Mathlib's `IsQuantale` only requires `Semigroup`. We extend it with commutativity
for Goertzel's weakness theory.
-/

/-- A commutative quantale is a quantale where the product is commutative. -/
class IsCommQuantale (Q : Type*) [CommSemigroup Q] [CompleteLattice Q]
    extends IsQuantale Q where

/-- For a commutative quantale, we only need one direction of the distributivity law. -/
instance (priority := 100) IsCommQuantale.ofCommSemigroup
    {Q : Type*} [CommSemigroup Q] [CompleteLattice Q]
    (h : ∀ (x : Q) (s : Set Q), x * sSup s = ⨆ y ∈ s, x * y) :
    IsCommQuantale Q where
  mul_sSup_distrib := h
  sSup_mul_distrib s y := by
    simp only [mul_comm _ y]
    exact h y s

/-! ## ENNReal as a Quantale

The extended non-negative reals form a commutative quantale with multiplication.
-/

/-- ENNReal is a quantale under multiplication. -/
instance : IsQuantale ℝ≥0∞ where
  mul_sSup_distrib _ _ := ENNReal.mul_sSup
  sSup_mul_distrib _ _ := ENNReal.sSup_mul

/-- ENNReal is a commutative quantale. -/
instance : IsCommQuantale ℝ≥0∞ where

/-! ## Weakness Measure

The core definition: weakness assigns to each subset of U × U a value in the quantale.
-/

section WeaknessDef

variable {U : Type*} [Fintype U] {Q : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]

/-- A weight function assigns quantale values to universe elements. -/
structure WeightFunction (U : Type*) (Q : Type*) [Fintype U] [Monoid Q] where
  μ : U → Q

/-- The weakness of a subset H ⊆ U × U under weight function μ.

For probabilistic weakness: μ(u) = p(u) and ⊗ = ·, ⊕ = +
For Bennett weakness: μ(u) = 1 and Q = ℕ with standard operations
-/
noncomputable def weakness (wf : WeightFunction U Q) (H : Finset (U × U)) : Q :=
  sSup { wf.μ p.1 * wf.μ p.2 | p ∈ H }

end WeaknessDef

/-! ## Bennett's Weakness (Counting Case)

The simplest case: uniform weights on a finite set, counting pairs.
-/

section BennettWeakness

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Bennett's weakness is just the cardinality of H. -/
def bennettWeakness (H : Finset (U × U)) : ℕ := H.card

/-- The "non-distinction event" D ⊆ U × U consists of pairs where u = v. -/
def nonDistinctionEvent : Finset (U × U) :=
  Finset.univ.filter fun p => p.1 = p.2

/-- The distinction event is the complement of non-distinction. -/
def distinctionEvent : Finset (U × U) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

theorem nonDistinction_card : (nonDistinctionEvent (U := U)).card = Fintype.card U := by
  unfold nonDistinctionEvent
  have h : (univ.filter (fun p : U × U => p.1 = p.2)).card =
      (univ.image (fun u : U => (u, u))).card := by
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hp
      refine ⟨p.1, ?_⟩
      ext
      · rfl
      · exact hp
    · rintro ⟨u, rfl⟩
      rfl
  rw [h, card_image_of_injective]
  · rfl
  · intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1

theorem distinction_card :
    (distinctionEvent (U := U)).card = Fintype.card U * Fintype.card U - Fintype.card U := by
  unfold distinctionEvent
  have htotal : (univ : Finset (U × U)).card = Fintype.card U * Fintype.card U := by
    simp only [card_univ, Fintype.card_prod]
  have hcompl : (univ.filter (fun p : U × U => p.1 ≠ p.2)).card +
      (univ.filter (fun p : U × U => p.1 = p.2)).card = (univ : Finset (U × U)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext p
      simp only [mem_union, mem_filter, mem_univ, true_and, ne_eq]
      tauto
    · rw [disjoint_filter]
      intro x _ hx
      exact hx
  have hnd : (univ.filter (fun p : U × U => p.1 = p.2)).card = Fintype.card U := by
    convert nonDistinction_card (U := U)
  rw [htotal, hnd] at hcompl
  omega

end BennettWeakness

/-! ## Graphtropy and Logical Entropy

The weakness framework connects to logical entropy via graphtropy.
-/

section Graphtropy

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Graphtropy of a graph G on U is the weakness of its "non-edge" event divided by |U|². -/
noncomputable def graphtropy (edges : Finset (U × U)) : ℚ :=
  let nonEdges := univ.filter fun p => p ∉ edges ∧ p.1 ≠ p.2
  nonEdges.card / (Fintype.card U * Fintype.card U : ℕ)

/-- A partition Π of U induces a distinction relation: (u,v) ∈ d(Π) iff u,v in different blocks. -/
def partitionDistinction {n : ℕ} (π : Fin n → Finset U)
    (_h_cover : ∀ u : U, ∃ i, u ∈ π i)
    (_h_disjoint : ∀ i j, i ≠ j → Disjoint (π i) (π j)) : Finset (U × U) :=
  univ.filter fun p =>
    ∃ i j, i ≠ j ∧ p.1 ∈ π i ∧ p.2 ∈ π j

end Graphtropy

/-! ## Probability-Weighted Weakness

When Q = ℝ≥0∞ and weights are probabilities summing to 1.
-/

section ProbabilisticWeakness

variable {U : Type*} [Fintype U]

/-- A probability weight is a weight function where weights sum to 1. -/
structure ProbWeight (U : Type*) [Fintype U] extends WeightFunction U ℝ≥0∞ where
  sum_one : ∑ u : U, μ u = 1

/-- Probabilistic weakness using ENNReal. -/
noncomputable def probWeakness (pw : ProbWeight U) (H : Finset (U × U)) : ℝ≥0∞ :=
  H.sum fun p => pw.μ p.1 * pw.μ p.2

/-- The probabilistic weakness of the full space U × U equals 1.

Proof: ∑_{u,v} p(u)p(v) = (∑_u p(u))(∑_v p(v)) = 1·1 = 1 -/
theorem probWeakness_univ (pw : ProbWeight U) :
    probWeakness pw (univ : Finset (U × U)) = 1 := by
  unfold probWeakness
  -- ∑_{u,v} p(u)p(v) = (∑_u p(u))(∑_v p(v)) = 1·1 = 1
  rw [← univ_product_univ, Finset.sum_product]
  rw [← Fintype.sum_mul_sum]
  simp only [pw.sum_one, mul_one]

/-- Logical entropy of a distribution is 1 - ∑ p(u)².

This is Ellerman's logical entropy formula: h(p) = 1 - Σp_i²
It equals the probability that two independent draws give different values. -/
noncomputable def logicalEntropyDist (pw : ProbWeight U) : ℝ≥0∞ :=
  1 - ∑ u : U, pw.μ u * pw.μ u

/-- Logical entropy of a partition with block probabilities. -/
noncomputable def logicalEntropy {n : ℕ} (blockProbs : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  1 - ∑ i, blockProbs i * blockProbs i

section LogicalEntropyEquivalence

variable [DecidableEq U]

/-- The probabilistic weakness of the non-distinction event equals ∑ p(u)².

This is the "identification probability" - the chance two draws give the same value. -/
theorem probWeakness_nonDistinction (pw : ProbWeight U) :
    probWeakness pw nonDistinctionEvent = ∑ u : U, pw.μ u * pw.μ u := by
  unfold probWeakness nonDistinctionEvent
  -- The sum over diagonal {(u,u) | u ∈ U} equals ∑_u p(u)²
  have h : (univ.filter fun p : U × U => p.1 = p.2) =
      univ.image (fun u : U => (u, u)) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hp
      exact ⟨p.1, by ext <;> [rfl; exact hp]⟩
    · rintro ⟨u, rfl⟩
      rfl
  rw [h, sum_image]
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1

/-- The distinction and non-distinction events partition univ.

probWeakness pw distinctionEvent + probWeakness pw nonDistinctionEvent = 1 -/
theorem probWeakness_distinction_add_nonDistinction (pw : ProbWeight U) :
    probWeakness pw distinctionEvent + probWeakness pw nonDistinctionEvent = 1 := by
  unfold probWeakness distinctionEvent nonDistinctionEvent
  rw [← sum_union]
  · have hunion : (univ.filter fun p : U × U => p.1 ≠ p.2) ∪
        (univ.filter fun p : U × U => p.1 = p.2) = univ := by
      ext p
      simp only [mem_union, mem_filter, mem_univ, true_and, ne_eq]
      tauto
    rw [hunion]
    exact probWeakness_univ pw
  · rw [disjoint_filter]
    intro x _ hx
    exact hx

/-- **The Logical Entropy Equivalence Theorem**

The probabilistic weakness of the distinction event equals logical entropy:
  w_p({(u,v) | u ≠ v}) = 1 - ∑_u p(u)² = h(p)

This formally connects Bennett's "distinction" concept with Ellerman's "entropy" concept.
The distinction event D consists of pairs where u ≠ v, and its weakness equals the
probability that two independent draws from U give different values.

Reference: Ellerman, "An Introduction to Logical Entropy and Its Relation to Shannon Entropy" -/
theorem probWeakness_distinction_eq_logicalEntropy (pw : ProbWeight U) :
    probWeakness pw distinctionEvent = logicalEntropyDist pw := by
  unfold logicalEntropyDist
  -- From the partition: distinction + non-distinction = 1
  have hadd := probWeakness_distinction_add_nonDistinction pw
  -- And: non-distinction = ∑ p(u)²
  rw [probWeakness_nonDistinction] at hadd
  -- Need to show the sum is finite (≠ ∞) for ENNReal subtraction
  have hne_top : ∑ u : U, pw.μ u * pw.μ u ≠ ⊤ := by
    have hle : ∑ u : U, pw.μ u * pw.μ u ≤ 1 := by
      have hbound : ∀ u : U, pw.μ u ≤ 1 := fun u => by
        have : pw.μ u ≤ ∑ v : U, pw.μ v :=
          Finset.single_le_sum (fun _ _ => zero_le _) (mem_univ u)
        simp only [pw.sum_one] at this
        exact this
      calc ∑ u : U, pw.μ u * pw.μ u
          ≤ ∑ u : U, pw.μ u * 1 := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_mul_left' (hbound u) _
        _ = ∑ u : U, pw.μ u := by simp only [mul_one]
        _ = 1 := pw.sum_one
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  -- Use ENNReal.eq_sub_of_add_eq: a + c = b → a = b - c (when c ≠ ∞)
  exact ENNReal.eq_sub_of_add_eq hne_top hadd

/-- Logical entropy equals the sum over distinct pairs: h(p) = Σ_{u≠v} p(u)p(v)

This is the "dual" formula to h(p) = 1 - Σp_i² -/
theorem logicalEntropy_eq_sum_distinct (pw : ProbWeight U) :
    logicalEntropyDist pw = ∑ p ∈ distinctionEvent, pw.μ p.1 * pw.μ p.2 := by
  rw [← probWeakness_distinction_eq_logicalEntropy]
  rfl

end LogicalEntropyEquivalence

end ProbabilisticWeakness

/-! ## Setoid-Based Partition Entropy

Partitions on a finite set can be represented via Setoids (equivalence relations).
The distinction set of a Setoid is the set of pairs NOT in the same equivalence class.
Finer partitions (smaller equivalence classes) have larger distinction sets.

Note: Mathlib's Setoid has `r ≤ s` meaning r is finer (r.r implies s.r).
-/

section SetoidEntropy

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The distinction set of a Setoid: pairs (u,v) where u and v are NOT equivalent.
    Uses the Setoid's coercion to a relation: `r u v` means u ~ v. -/
def setoidDistinctionSet (r : Setoid U) [DecidableRel r.r] : Finset (U × U) :=
  Finset.univ.filter fun p => ¬r.r p.1 p.2

/-- The equivalence set: pairs (u,v) where u and v ARE equivalent. -/
def setoidEquivalenceSet (r : Setoid U) [DecidableRel r.r] : Finset (U × U) :=
  Finset.univ.filter fun p => r.r p.1 p.2

/-- The distinction and equivalence sets partition U × U. -/
theorem setoidDistinctionSet_union_equivalenceSet (r : Setoid U) [DecidableRel r.r] :
    setoidDistinctionSet r ∪ setoidEquivalenceSet r = Finset.univ := by
  ext p
  simp only [Finset.mem_union, setoidDistinctionSet, setoidEquivalenceSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The distinction and equivalence sets are disjoint. -/
theorem disjoint_setoidDistinctionSet_equivalenceSet (r : Setoid U) [DecidableRel r.r] :
    Disjoint (setoidDistinctionSet r) (setoidEquivalenceSet r) := by
  simp only [setoidDistinctionSet, setoidEquivalenceSet, Finset.disjoint_filter]
  intro x _ hx
  exact hx

/-- If r₁ ≤ r₂ (r₁ is finer), then the distinction set of r₁ contains the distinction set of r₂.
    Finer partition → more distinctions.

    Note: Mathlib's `r ≤ s` means `∀ x y, r.r x y → s.r x y`, i.e., r is finer. -/
theorem setoidDistinctionSet_mono {r₁ r₂ : Setoid U}
    [DecidableRel r₁.r] [DecidableRel r₂.r]
    (h : r₁ ≤ r₂) : setoidDistinctionSet r₂ ⊆ setoidDistinctionSet r₁ := by
  intro p hp
  simp only [setoidDistinctionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  intro hr₁
  exact hp (h hr₁)

/-- Cardinality version: finer partition has at least as many distinctions. -/
theorem setoidDistinctionSet_card_mono {r₁ r₂ : Setoid U}
    [DecidableRel r₁.r] [DecidableRel r₂.r]
    (h : r₁ ≤ r₂) : (setoidDistinctionSet r₂).card ≤ (setoidDistinctionSet r₁).card :=
  Finset.card_le_card (setoidDistinctionSet_mono h)

/-- The discrete Setoid: each element is only equivalent to itself.
    This is the finest partition. -/
def discreteSetoid' (U : Type*) : Setoid U where
  r := (· = ·)
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance discreteSetoid'_decidable : DecidableRel (discreteSetoid' U).r :=
  fun a b => inferInstanceAs (Decidable (a = b))

/-- The indiscrete Setoid: all elements are equivalent.
    This is the coarsest partition (single block). -/
def indiscreteSetoid' (U : Type*) : Setoid U where
  r := fun _ _ => True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

instance indiscreteSetoid'_decidable : DecidableRel (indiscreteSetoid' U).r :=
  fun _ _ => isTrue trivial

/-- The discrete Setoid refines every Setoid. -/
theorem discreteSetoid'_le (r : Setoid U) : discreteSetoid' U ≤ r :=
  fun {_ _} huv => huv ▸ r.refl' _

/-- Every Setoid refines the indiscrete Setoid. -/
theorem le_indiscreteSetoid' (r : Setoid U) : r ≤ indiscreteSetoid' U :=
  fun {_ _} _ => trivial

/-- The distinction set of the discrete Setoid is exactly the distinctionEvent. -/
theorem discreteSetoid'_distinctionSet :
    setoidDistinctionSet (discreteSetoid' U) = distinctionEvent := by
  ext p
  simp only [setoidDistinctionSet, discreteSetoid', Finset.mem_filter, Finset.mem_univ,
    true_and, distinctionEvent, ne_eq]

/-- The distinction set of the indiscrete Setoid is empty. -/
theorem indiscreteSetoid'_distinctionSet :
    setoidDistinctionSet (indiscreteSetoid' U) = ∅ := by
  ext p
  simp only [setoidDistinctionSet, indiscreteSetoid', Finset.mem_filter,
    Finset.mem_univ, true_and, not_true_eq_false, Finset.notMem_empty]

/-! ### Partition Entropy (Bennett/Uniform Weights)

For uniform weights, the logical entropy of a partition is proportional to
the cardinality of its distinction set. -/

/-- Bennett entropy of a Setoid: |distinction set| / |U × U|
    This is the probability that two uniform random draws are distinguished. -/
noncomputable def setoidBennettEntropy (r : Setoid U) [DecidableRel r.r] : ℚ :=
  (setoidDistinctionSet r).card / (Fintype.card U * Fintype.card U : ℕ)

/-- **Entropy Monotonicity Theorem (Bennett/Uniform Case)**

If r₁ ≤ r₂ (r₁ is finer), then entropy(r₁) ≥ entropy(r₂).
Finer partitions have higher entropy because they make more distinctions. -/
theorem setoidBennettEntropy_mono {r₁ r₂ : Setoid U}
    [DecidableRel r₁.r] [DecidableRel r₂.r]
    (h : r₁ ≤ r₂) : setoidBennettEntropy r₂ ≤ setoidBennettEntropy r₁ := by
  unfold setoidBennettEntropy
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℚ) ≤ _)
  exact Nat.cast_le.mpr (setoidDistinctionSet_card_mono h)

/-- The discrete Setoid has maximal entropy. -/
theorem setoidBennettEntropy_discrete_maximal (r : Setoid U) [DecidableRel r.r] :
    setoidBennettEntropy r ≤ setoidBennettEntropy (discreteSetoid' U) :=
  setoidBennettEntropy_mono (discreteSetoid'_le r)

/-- The indiscrete Setoid has zero entropy. -/
theorem setoidBennettEntropy_indiscrete :
    setoidBennettEntropy (indiscreteSetoid' U) = 0 := by
  unfold setoidBennettEntropy
  simp only [indiscreteSetoid'_distinctionSet, Finset.card_empty, Nat.cast_zero, zero_div]

end SetoidEntropy

/-! ## Residuation

Quantales have residuation operators that generalize implication.
-/

section Residuation

variable {Q : Type*} [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]

/-- Left residuation: x ⇨ₗ y = ⊔{z | z * x ≤ y} -/
noncomputable def leftResiduate (x y : Q) : Q :=
  sSup {z | z * x ≤ y}

/-- Right residuation: x ⇨ᵣ y = ⊔{z | x * z ≤ y} -/
noncomputable def rightResiduate (x y : Q) : Q :=
  sSup {z | x * z ≤ y}

/-- In a commutative semigroup with quantale structure, left and right residuation coincide. -/
theorem residuate_comm' {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (x y : Q) : leftResiduate x y = rightResiduate x y := by
  unfold leftResiduate rightResiduate
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, mul_comm]

/-- Galois connection for residuation. -/
theorem residuate_galois (x y z : Q) :
    z * x ≤ y ↔ z ≤ leftResiduate x y := by
  constructor
  · intro h
    exact le_sSup h
  · intro h
    calc z * x ≤ (leftResiduate x y) * x := mul_le_mul_right' h x
         _ = sSup {z | z * x ≤ y} * x := rfl
         _ = ⨆ w ∈ {z | z * x ≤ y}, w * x := IsQuantale.sSup_mul_distrib _ _
         _ ≤ y := by
           apply iSup₂_le
           intro w hw
           exact hw

end Residuation

/-! ## PLN-Style Inference in Quantales

Probabilistic Logic Networks (PLN) use truth values with "strength" to perform
uncertain inference. The quantale residuation provides the mathematical foundation:

- The residuate `x → y` (leftResiduate y x) represents implication strength
- Modus ponens: from w(A) and w(A → B), derive bounds on w(B)
- Deduction/Transitivity: (A → B) ⊗ (B → C) ≤ (A → C)

Reference: Goertzel et al., "Probabilistic Logic Networks"

Note: For left residuation `leftResiduate A B = sSup {z | z * A ≤ B}`,
the natural modus ponens is `(A →_L B) * A ≤ B`.
For right residuation `rightResiduate A B = sSup {z | A * z ≤ B}`,
it is `A * (A →_R B) ≤ B`.
In commutative quantales, both coincide.
-/

section PLNInference

variable {Q : Type*} [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]

/-- Notation: x → y in quantale logic (left residuation).
    Represents "implication from x to y" or "if x then y". -/
noncomputable def quantaleImplies (x y : Q) : Q := leftResiduate x y

/-- **Modus Ponens for Left Residuation**

(A →_L B) * A ≤ B

This is the correct form for left residuation. -/
theorem modusPonens_left (A B : Q) : (leftResiduate A B) * A ≤ B := by
  unfold leftResiduate
  calc sSup {z | z * A ≤ B} * A
      = ⨆ w ∈ {z | z * A ≤ B}, w * A := IsQuantale.sSup_mul_distrib _ _
    _ ≤ B := iSup₂_le (fun w hw => hw)

/-- **Modus Ponens for Right Residuation**

A * (A →_R B) ≤ B -/
theorem modusPonens_right (A B : Q) : A * (rightResiduate A B) ≤ B := by
  unfold rightResiduate
  calc A * sSup {z | A * z ≤ B}
      = ⨆ w ∈ {z | A * z ≤ B}, A * w := IsQuantale.mul_sSup_distrib _ _
    _ ≤ B := iSup₂_le (fun w hw => hw)

/-- **Modus Ponens (Commutative Quantales)**

In commutative quantales: A * (A → B) ≤ B

If we know A with strength α and "A implies B" with strength β,
then B has strength at least α ⊗ β.

This is the quantale version of: A ∧ (A → B) ⊢ B -/
theorem modusPonens {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (A B : Q) : A * (quantaleImplies A B) ≤ B := by
  rw [mul_comm]
  exact modusPonens_left A B

/-- Modus ponens with arguments swapped (for commutative quantales) -/
theorem modusPonens' {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (A B : Q) : (quantaleImplies A B) * A ≤ B :=
  modusPonens_left A B

/-- **Monotonicity of Implication (Right)**

If B ≤ C, then (A → B) ≤ (A → C).
Stronger conclusions from the same premise give stronger implications. -/
theorem quantaleImplies_mono_right (A : Q) {B C : Q} (h : B ≤ C) :
    quantaleImplies A B ≤ quantaleImplies A C := by
  unfold quantaleImplies leftResiduate
  apply sSup_le_sSup
  intro z hz
  exact hz.trans h

/-- **Monotonicity of Implication (Left, Contravariant)**

If A ≤ B, then (B → C) ≤ (A → C).
Weaker premises give stronger implications. -/
theorem quantaleImplies_antimono_left {A B : Q} (C : Q) (h : A ≤ B) :
    quantaleImplies B C ≤ quantaleImplies A C := by
  unfold quantaleImplies leftResiduate
  apply sSup_le_sSup
  intro z hz
  calc z * A ≤ z * B := mul_le_mul_left' h z
       _ ≤ C := hz

/-- **Lower Bound Inference (Commutative Quantales)**

If w(A) ≥ α and w(A → B) ≥ β (both bounds), then w(B) ≥ α ⊗ β.
This is the "forward inference" rule in PLN. -/
theorem lowerBoundInference {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (A B α β : Q) (hA : α ≤ A) (hImpl : β ≤ quantaleImplies A B) :
    α * β ≤ B := by
  calc α * β ≤ A * (quantaleImplies A B) := mul_le_mul' hA hImpl
       _ ≤ B := modusPonens A B

/-- **Adjunction Property (Fundamental)**

The core property: z * x ≤ y iff z ≤ (x → y).
This is exactly the Galois connection that defines implication. -/
theorem quantaleImplies_adjunction (x y z : Q) :
    z * x ≤ y ↔ z ≤ quantaleImplies x y :=
  residuate_galois x y z

/-- **Currying (Commutative Quantales)**

(A ⊗ B → C) = (A → (B → C))
The quantale version of logical currying. -/
theorem quantaleImplies_curry {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (A B C : Q) : quantaleImplies (A * B) C = quantaleImplies A (quantaleImplies B C) := by
  apply le_antisymm
  · -- ≤ direction: use adjunction twice
    -- Need: quantaleImplies (A * B) C ≤ quantaleImplies A (quantaleImplies B C)
    -- Equiv to: quantaleImplies (A * B) C * A ≤ quantaleImplies B C (by adjunction)
    -- Equiv to: quantaleImplies (A * B) C * A * B ≤ C (by adjunction)
    rw [← quantaleImplies_adjunction]
    rw [← quantaleImplies_adjunction]
    -- Need: ((A*B) → C) * A * B ≤ C
    -- By associativity and commutativity: = ((A*B) → C) * (A * B) ≤ C
    calc quantaleImplies (A * B) C * A * B
        = quantaleImplies (A * B) C * (A * B) := by rw [mul_assoc]
      _ ≤ C := modusPonens' (A * B) C
  · -- ≥ direction: use adjunction twice in reverse
    -- Need: quantaleImplies A (quantaleImplies B C) ≤ quantaleImplies (A * B) C
    -- Equiv to: quantaleImplies A (quantaleImplies B C) * (A * B) ≤ C
    rw [← quantaleImplies_adjunction]
    -- (A → (B → C)) * (A * B) ≤ C
    -- Rewrite: x * (A * B) = A * (x * B) by comm/assoc
    have heq : quantaleImplies A (quantaleImplies B C) * (A * B) =
        A * (quantaleImplies A (quantaleImplies B C) * B) := by
      rw [mul_comm (quantaleImplies A (quantaleImplies B C)) (A * B)]
      rw [mul_assoc A B, mul_comm B, ← mul_assoc]
    rw [heq]
    -- A * (x * B) = (A * x) * B ≤ (B→C) * B
    calc A * (quantaleImplies A (quantaleImplies B C) * B)
        = (A * quantaleImplies A (quantaleImplies B C)) * B := by rw [mul_assoc]
      _ ≤ quantaleImplies B C * B := by
          apply mul_le_mul_right'
          exact modusPonens A (quantaleImplies B C)
      _ ≤ C := modusPonens' B C

/-- **Transitivity/Deduction Rule (Syllogism) - Commutative Quantales**

(A → B) ⊗ (B → C) ≤ (A → C)

If "A implies B" with strength α and "B implies C" with strength β,
then "A implies C" with strength at least α ⊗ β.

This is the PLN deduction rule (quantale version of categorical composition). -/
theorem quantaleImplies_trans {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsQuantale Q]
    (A B C : Q) : (quantaleImplies A B) * (quantaleImplies B C) ≤ quantaleImplies A C := by
  -- By adjunction: need to show (A → B) * (B → C) * A ≤ C
  rw [← quantaleImplies_adjunction]
  -- Rewrite: (A → B) * (B → C) * A = (B → C) * ((A → B) * A) by comm/assoc
  have heq : quantaleImplies A B * quantaleImplies B C * A =
      quantaleImplies B C * (quantaleImplies A B * A) := by
    rw [mul_comm (quantaleImplies A B) (quantaleImplies B C)]
    rw [mul_assoc]
  rw [heq]
  calc quantaleImplies B C * (quantaleImplies A B * A)
      ≤ quantaleImplies B C * B := by
        apply mul_le_mul_left'
        exact modusPonens_left A B
    _ ≤ C := modusPonens' B C

end PLNInference

/-! ## Key Theorems from Goertzel's Paper -/

section GoertzelTheorems

variable {U : Type*} [Fintype U]

/-- The weakness of the empty event is the bottom element.
    Corresponds to: "impossible event has zero weakness" -/
theorem weakness_empty {Q : Type*} [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    (wf : WeightFunction U Q) :
    weakness wf ∅ = ⊥ := by
  unfold weakness
  convert sSup_empty
  ext q
  simp only [Set.mem_setOf_eq, Finset.notMem_empty, false_and, Set.mem_empty_iff_false]
  tauto

/-- Monotonicity: H₁ ⊆ H₂ implies w(H₁) ≤ w(H₂) -/
theorem weakness_mono {Q : Type*} [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    (wf : WeightFunction U Q) (H₁ H₂ : Finset (U × U)) (h : H₁ ⊆ H₂) :
    weakness wf H₁ ≤ weakness wf H₂ := by
  unfold weakness
  apply sSup_le_sSup
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact ⟨p, h hp, rfl⟩

end GoertzelTheorems

end Mettapedia.Algebra.QuantaleWeakness
