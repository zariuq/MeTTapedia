import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Moving one factor across a block of an ordered product

An ordered product in a monoid keeps the order in which factors were charged.
Two accounts that charge the same factors in different orders differ by moves of
single factors across blocks of others, and one fact decides every such move.

* **The exact condition** (`prod_cons_eq_prod_concat_iff`).  Charging `x` before a
  block or after it gives the same product exactly when `x` commutes with the
  product of the block.
* **The sufficient condition** (`prod_cons_eq_prod_concat_of_forall_commute`).
  Commuting with every factor of the block is enough.  It is not necessary once the
  block has two factors (`product_commutes_factor_does_not`).
* **The tile** (`prod_pair_eq_iff_commute`).  For a block of one factor the two
  conditions coincide: two adjacent factors swap exactly when they commute.  A swap
  inside any context follows (`prod_swap_of_commute`).

The production ledgers of `GSLT/Distinction/ProductionLicences` (eager against lazy
charging of a bound production) and the declared accounts of
`GSLT/Distinction/CausalGluing` (swaps of independent occurrences) are both instances.

Controls: in a commutative monoid every move is lawful
(`prod_cons_eq_prod_concat_of_comm`); in the free monoid no move of a factor across
a different one is (`free_monoid_tile_fails`); and a permutation that commutes with
the identity product `s * s` does not commute with `s`
(`product_commutes_factor_does_not`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.OrderedProductCommutation

section General

variable {M : Type*} [Monoid M]

/-- Charging one factor last. -/
theorem prod_concat_singleton (block : List M) (x : M) : (block ++ [x]).prod = block.prod * x := by
  induction block with
  | nil =>
      show x * 1 = 1 * x
      rw [mul_one, one_mul]
  | cons y rest ih =>
      show y * (rest ++ [x]).prod = y * rest.prod * x
      rw [ih, mul_assoc]

/-- **Moving one factor across a block**: charging `x` before the block or after it
gives the same ordered product exactly when `x` commutes with the block's product. -/
theorem prod_cons_eq_prod_concat_iff (x : M) (block : List M) :
    (x :: block).prod = (block ++ [x]).prod ↔ Commute x block.prod := by
  rw [prod_concat_singleton]
  exact Iff.rfl

/-- Commuting with every factor of the block is sufficient. -/
theorem prod_cons_eq_prod_concat_of_forall_commute {x : M} {block : List M}
    (commutes : ∀ y ∈ block, Commute x y) : (x :: block).prod = (block ++ [x]).prod :=
  (prod_cons_eq_prod_concat_iff x block).2 (Commute.list_prod_right block x commutes)

/-- **The tile**, the move across a block of one factor: two adjacent factors swap
exactly when they commute. -/
theorem prod_pair_eq_iff_commute (x y : M) : [x, y].prod = [y, x].prod ↔ Commute x y := by
  have move := prod_cons_eq_prod_concat_iff x [y]
  rw [show ([y] : List M).prod = y from mul_one y] at move
  exact move

/-- A lawful tile can be applied inside any context. -/
theorem prod_swap_of_commute {x y : M} (commute : Commute x y) (u v : List M) :
    (u ++ x :: y :: v).prod = (u ++ y :: x :: v).prod := by
  induction u with
  | nil =>
      show x * (y * v.prod) = y * (x * v.prod)
      rw [← mul_assoc, commute.eq, mul_assoc]
  | cons z rest ih =>
      show z * (rest ++ x :: y :: v).prod = z * (rest ++ y :: x :: v).prod
      rw [ih]

/-- Mapping a block with one occurrence charged last. -/
theorem map_concat_singleton {ι β : Type*} (coefficient : ι → β) (block : List ι) (i : ι) :
    (block ++ [i]).map coefficient = block.map coefficient ++ [coefficient i] := by
  induction block with
  | nil => rfl
  | cons j rest ih =>
      show coefficient j :: (rest ++ [i]).map coefficient =
        coefficient j :: (rest.map coefficient ++ [coefficient i])
      rw [ih]

/-- The move for factors indexed by occurrences through a coefficient map. -/
theorem map_prod_cons_eq_concat_iff {ι : Type*} (coefficient : ι → M) (i : ι) (block : List ι) :
    ((i :: block).map coefficient).prod = ((block ++ [i]).map coefficient).prod ↔
      Commute (coefficient i) (block.map coefficient).prod := by
  rw [map_concat_singleton]
  exact prod_cons_eq_prod_concat_iff (coefficient i) (block.map coefficient)

end General

/-! ## Controls -/

/-- **Positive**: in a commutative monoid every move is lawful. -/
theorem prod_cons_eq_prod_concat_of_comm {M : Type*} [CommMonoid M] (x : M) (block : List M) :
    (x :: block).prod = (block ++ [x]).prod :=
  (prod_cons_eq_prod_concat_iff x block).2 (Commute.all x block.prod)

/-- **Negative**: in the free monoid two different letters never swap. -/
theorem free_monoid_tile_fails :
    ([FreeMonoid.of 0, FreeMonoid.of 1] : List (FreeMonoid ℕ)).prod ≠
      [FreeMonoid.of 1, FreeMonoid.of 0].prod ∧
      ¬ Commute (FreeMonoid.of (0 : ℕ)) (FreeMonoid.of 1) := by
  refine ⟨fun same => ?_, fun commute => ?_⟩
  · have := congrArg FreeMonoid.toList same
    simp at this
  · have := congrArg FreeMonoid.toList commute.eq
    simp at this

/-- **The pairwise condition is not necessary.**  The transposition `x = (0 1)`
commutes with the product of the block `[s, s]`, which is the identity, while it
does not commute with the factor `s = (1 2)`.  Moving `x` across the block is
lawful although moving it across either factor alone is not. -/
theorem product_commutes_factor_does_not :
    let x : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let s : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    (x :: [s, s]).prod = ([s, s] ++ [x]).prod ∧ ¬ Commute x s := by
  intro x s
  refine ⟨(prod_cons_eq_prod_concat_iff x [s, s]).2 ?_, fun commute => ?_⟩
  · have identity : ([s, s] : List (Equiv.Perm (Fin 3))).prod = 1 := by decide
    rw [identity]
    exact Commute.one_right x
  · have : x * s = s * x := commute.eq
    revert this
    decide

end Mettapedia.Algebra.OrderedProductCommutation
