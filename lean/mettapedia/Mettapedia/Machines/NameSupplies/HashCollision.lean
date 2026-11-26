import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod

/-!
# Collision risk for fixed distinct name requests

The sample space contains all functions from the request positions to the
digest space with equal weight. This models independent uniform answers to
distinct queries. The pair bound is a finite counting result and applies to
a keyed implementation only under a separate random-function justification.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies.HashCollision

open Finset
open scoped BigOperators

private def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (univ ×ˢ univ).filter fun pair => pair.1 < pair.2

private theorem orderedPairs_card (n : ℕ) : (orderedPairs n).card = n.choose 2 := by
  rw [orderedPairs, Finset.card_product_filter_lt]
  simp

private noncomputable def equalAt (m : ℕ) {n : ℕ} (pair : Fin n × Fin n) :
    Finset (Fin n → Fin m) :=
  univ.filter fun hash => hash pair.1 = hash pair.2

/-- A table with an equal pair and one extra digest specifies an arbitrary
table: restore the second position from the extra digest. -/
private def restorePair {n m : ℕ} (i j : Fin n) (different : i ≠ j) :
    ({hash : Fin n → Fin m // hash i = hash j} × Fin m) ≃ (Fin n → Fin m) where
  toFun input := Function.update input.1.1 j input.2
  invFun hash := (⟨Function.update hash j (hash i), by simp [different]⟩, hash j)
  left_inv := by
    rintro ⟨⟨hash, equal⟩, extra⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases atSecond : k = j
      · subst k
        simpa [different] using equal
      · simp [different, atSecond]
    · simp
  right_inv := by
    intro hash
    funext k
    by_cases atSecond : k = j
    · subst k
      simp
    · simp [atSecond]

private theorem equalAt_card {n m : ℕ} (pair : Fin n × Fin n) (ordered : pair.1 < pair.2) :
    (equalAt m pair).card * m = m ^ n := by
  have counted := Fintype.card_congr (restorePair (m := m) _ _ (ne_of_lt ordered))
  simp only [Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin] at counted
  exact counted

/-- Tables that give the same digest to two distinct requests. -/
noncomputable def collisions (n m : ℕ) : Finset (Fin n → Fin m) := by
  classical
  exact (orderedPairs n).biUnion (equalAt m)

theorem mem_collisions_iff {n m : ℕ} (hash : Fin n → Fin m) :
    hash ∈ collisions n m ↔ ¬ Function.Injective hash := by
  classical
  simp only [collisions, Finset.mem_biUnion, orderedPairs, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and, equalAt]
  constructor
  · rintro ⟨⟨i, j⟩, ordered, equal⟩ injective
    exact (ne_of_lt ordered) (injective equal)
  · intro notInjective
    rw [Function.Injective, not_forall] at notInjective
    obtain ⟨i, notInjective⟩ := notInjective
    rw [not_forall] at notInjective
    obtain ⟨j, bad⟩ := notInjective
    have equal := (Classical.not_imp.mp bad).1
    have distinct := (Classical.not_imp.mp bad).2
    rcases lt_or_gt_of_ne distinct with ordered | ordered
    · exact ⟨(i, j), ordered, equal⟩
    · exact ⟨(j, i), ordered, equal.symm⟩

/-- Union bound in integers, with both denominators cleared. -/
theorem collision_count (n m : ℕ) :
    (collisions n m).card * m ≤ n.choose 2 * m ^ n := by
  classical
  calc
    (collisions n m).card * m ≤ (∑ pair ∈ orderedPairs n, (equalAt m pair).card) * m :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ pair ∈ orderedPairs n, (equalAt m pair).card * m := by rw [Finset.sum_mul]
    _ = (orderedPairs n).card * m ^ n := by
      apply Finset.sum_const_nat
      intro pair inside
      apply equalAt_card
      exact (Finset.mem_filter.mp inside).2
    _ = n.choose 2 * m ^ n := by rw [orderedPairs_card]

/-- For uniform tables of `bits`-bit digests, the collision probability
is at most the number of unordered pairs divided by the digest space. -/
theorem birthday_bound (requests bits : ℕ) :
    ((collisions requests (2 ^ bits)).card : ℚ) / ((2 ^ bits : ℕ) ^ requests : ℕ) ≤
      (requests.choose 2 : ℚ) / (2 ^ bits : ℕ) := by
  have mPositive : 0 < (2 : ℕ) ^ bits := pow_pos (by decide) _
  apply (div_le_div_iff₀ (by exact_mod_cast pow_pos mPositive requests) (by exact_mod_cast mPositive)).2
  exact_mod_cast collision_count requests (2 ^ bits)

/-- A one-bit digest has a collision on three distinct requests in every
table. The birthday model assigns positive mass to collisions. -/
theorem three_requests_one_bit (hash : Fin 3 → Fin 2) : hash ∈ collisions 3 2 := by
  rw [mem_collisions_iff]
  exact Fintype.not_injective_of_card_lt hash (by decide)

#print axioms mem_collisions_iff
#print axioms birthday_bound
#print axioms three_requests_one_bit

end Mettapedia.Machines.NameSupplies.HashCollision
