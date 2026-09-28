import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Free

/-!
# Ordered folds of a right monoid action

A monoid `M` acting on a state type `α` on the right (`MulAction Mᵐᵒᵖ α`,
written `x <• m` under `open scoped RightActions`) turns a left fold into one
product: folding `x <• m₁ <• ⋯ <• mₖ` equals acting once by `m₁ * ⋯ * mₖ`.
The product is in execution order, so `m₁` acts first. A left fold whose
step is a right action is therefore a list homomorphism into `M`. The usual
parallel evaluation strategies are then exact.

* `foldl_op_smul`, `foldl_map_op_smul`: the sequential fold equals the action
  of the ordered product.
* `lift_eq_prod_leaves`, `foldl_leaves`: every bracketing of the same ordered
  sequence has the same value. A bracketing is a binary tree in Mathlib's
  `FreeMagma`, and `leaves_eq_toFreeSemigroup` identifies its leaf sequence
  with Mathlib's associative normal form. This licenses reduction trees.
* `scanl_op_smul`, `getElem_scanl_op_smul`: every prefix state is the initial
  state acted on by the corresponding prefix product.
* `scanl_mul_eq_map_mul`: prefix products from any start are left translates
  of prefix products from `1`, so a chunk can be scanned before its start is
  known. `map_scanl_mul`: monoid homomorphisms commute with prefix products.
* `scanl_op_smul_flatten`: the three-phase blocked scan reproduces the
  sequential trajectory. The phases are chunk products, a scan of those
  products, and independent chunk-local scans.
* `foldl_op_smul_replicate`, `npowBinRec_eq_pow`: a constant stretch acts as
  a power, and repeated squaring computes that power.
* `foldl_op_smul_perm`, `foldl_map_op_smul_perm`: reordering is licensed when
  the factors pairwise commute. Associativity alone licenses regrouping, not
  permutation.

This file proves no statement about evaluation cost, machine arithmetic,
errors or effects. These are laws of the exact monoid action.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.ActionFold

open scoped RightActions

universe uM uα uι

variable {M : Type uM} {α : Type uα} [Monoid M] [MulAction Mᵐᵒᵖ α]

/-! ## Sequential folds -/

/-- **Fold exactness.** A left fold of right actions is the action of the
ordered product; the head of the list acts first. -/
theorem foldl_op_smul (l : List M) (x : α) :
    l.foldl (fun state m => state <• m) x = x <• l.prod := by
  induction l generalizing x with
  | nil => simp
  | cons m l ih => rw [List.foldl_cons, ih, List.prod_cons, op_smul_mul]

/-- Fold exactness for items carrying their coefficient. -/
theorem foldl_map_op_smul {ι : Type uι} (coeff : ι → M) (items : List ι) (x : α) :
    items.foldl (fun state i => state <• coeff i) x = x <• (items.map coeff).prod := by
  rw [← foldl_op_smul, List.foldl_map]

/-- Splitting the ordered factors splits the action. -/
theorem op_smul_prod_append (l₁ l₂ : List M) (x : α) :
    x <• (l₁ ++ l₂).prod = (x <• l₁.prod) <• l₂.prod := by
  rw [List.prod_append, op_smul_mul]

/-! ## Bracketings -/

section Bracketing

variable {ι : Type uι}

/-- The ordered leaf sequence of a bracketing. -/
def leaves : FreeMagma ι → List ι
  | .of i => [i]
  | .mul s t => leaves s ++ leaves t

@[simp] theorem leaves_of (i : ι) : leaves (FreeMagma.of i) = [i] := rfl

@[simp] theorem leaves_mul (s t : FreeMagma ι) :
    leaves (s * t) = leaves s ++ leaves t := rfl

theorem leaves_ne_nil (t : FreeMagma ι) : leaves t ≠ [] := by
  induction t with
  | ih1 i => simp
  | ih2 s t hs _ => simp [hs]

/-- The leaf sequence is Mathlib's associative normal form of the
bracketing: the image of the bracketing in the free semigroup. -/
theorem leaves_eq_toFreeSemigroup (t : FreeMagma ι) :
    leaves t = (FreeMagma.toFreeSemigroup t).head :: (FreeMagma.toFreeSemigroup t).tail := by
  induction t with
  | ih1 i => rfl
  | ih2 s t hs ht =>
      rw [leaves_mul, map_mul, hs, ht]
      rfl

/-- Every bracketing evaluates to the ordered product of its leaves. -/
theorem lift_eq_prod_leaves (coeff : ι → M) (t : FreeMagma ι) :
    FreeMagma.lift coeff t = ((leaves t).map coeff).prod := by
  induction t with
  | ih1 i => simp
  | ih2 s t hs ht => rw [map_mul, hs, ht, leaves_mul, List.map_append, List.prod_append]

/-- **Bracketing independence.** Two bracketings of the same ordered
sequence have the same value. -/
theorem lift_eq_of_leaves_eq (coeff : ι → M) {s t : FreeMagma ι}
    (h : leaves s = leaves t) : FreeMagma.lift coeff s = FreeMagma.lift coeff t := by
  rw [lift_eq_prod_leaves, lift_eq_prod_leaves, h]

/-- A fold over the leaves of a bracketing is the action of its bracketed
value. Any reduction tree over the ordered items computes the fold. -/
theorem foldl_leaves (coeff : ι → M) (t : FreeMagma ι) (x : α) :
    (leaves t).foldl (fun state i => state <• coeff i) x = x <• FreeMagma.lift coeff t := by
  rw [foldl_map_op_smul, lift_eq_prod_leaves]

end Bracketing

/-! ## Prefix scans -/

/-- Prefix states from an already accumulated factor. -/
theorem scanl_op_smul_from (l : List M) (x : α) (start : M) :
    l.scanl (fun state m => state <• m) (x <• start) =
      (l.scanl (· * ·) start).map (x <• ·) := by
  induction l generalizing start with
  | nil => simp
  | cons m l ih =>
      simp only [List.scanl_cons, List.map_cons]
      rw [op_smul_op_smul, ih]

/-- **Scan exactness.** The sequential trajectory is the initial state acted
on by each prefix product. -/
theorem scanl_op_smul (l : List M) (x : α) :
    l.scanl (fun state m => state <• m) x = (l.scanl (· * ·) 1).map (x <• ·) := by
  have h := scanl_op_smul_from l x 1
  rwa [MulOpposite.op_one, one_smul] at h

/-- Every entry of the trajectory is the action of one prefix product. -/
theorem getElem_scanl_op_smul (l : List M) (x : α) (i : ℕ)
    (h : i < (l.scanl (fun state m => state <• m) x).length) :
    (l.scanl (fun state m => state <• m) x)[i] = x <• (l.take i).prod := by
  rw [List.getElem_scanl, foldl_op_smul]

/-- Prefix products from any start are left translates of prefix products
from `1`. A chunk's local prefix products do not depend on its start. -/
theorem scanl_mul_eq_map_mul (l : List M) (start : M) :
    l.scanl (· * ·) start = (l.scanl (· * ·) 1).map (start * ·) := by
  induction l generalizing start with
  | nil => simp
  | cons m l ih =>
      simp only [List.scanl_cons, List.map_cons, mul_one, one_mul]
      rw [ih (start * m), ih m, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      simp [mul_assoc]

/-- Monoid homomorphisms commute with prefix products. -/
theorem map_scanl_mul {N : Type*} [Monoid N] {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (φ : F) (l : List M) (start : M) :
    (l.scanl (· * ·) start).map φ = (l.map φ).scanl (· * ·) (φ start) := by
  induction l generalizing start with
  | nil => simp
  | cons m l ih => simp [ih, map_mul]

/-- **Blocked scan.** Split the ordered factors into chunks. Phase 1 reduces
each chunk to its product. Phase 2 scans those products from the initial
state, giving every chunk's starting state. Phase 3 scans every chunk from
its own start, independently. Dropping each chunk scan's repeated start and
concatenating reproduces the sequential trajectory exactly. -/
theorem scanl_op_smul_flatten (chunks : List (List M)) (x : α) :
    chunks.flatten.scanl (fun state m => state <• m) x =
      x :: (List.zipWith
        (fun start chunk => (chunk.scanl (fun state m => state <• m) start).tail)
        ((chunks.map List.prod).scanl (fun state m => state <• m) x) chunks).flatten := by
  induction chunks generalizing x with
  | nil => simp
  | cons chunk chunks ih =>
      have hstart : chunk.scanl (fun state m => state <• m) x =
          x :: (chunk.scanl (fun state m => state <• m) x).tail := by
        cases chunk <;> simp
      rw [List.flatten_cons, List.scanl_append, foldl_op_smul, ih, List.tail_cons,
        List.map_cons, List.scanl_cons, List.zipWith_cons_cons, List.flatten_cons,
        ← List.cons_append, ← hstart]

/-! ## Constant stretches -/

/-- A constant stretch acts as a power. -/
theorem foldl_op_smul_replicate (n : ℕ) (m : M) (x : α) :
    (List.replicate n m).foldl (fun state m => state <• m) x = x <• m ^ n := by
  rw [foldl_op_smul, List.prod_replicate]

/-- Exponentiation by repeated squaring computes monoid powers. -/
theorem npowBinRec_eq_pow (n : ℕ) (m : M) : npowBinRec n m = m ^ n := by
  induction n with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

/-! ## Reordering -/

/-- **Reordering license.** A permutation of pairwise commuting factors
does not change the fold. -/
theorem foldl_op_smul_perm {l₁ l₂ : List M} (h : l₁.Perm l₂)
    (hc : l₁.Pairwise Commute) (x : α) :
    l₁.foldl (fun state m => state <• m) x = l₂.foldl (fun state m => state <• m) x := by
  rw [foldl_op_smul, foldl_op_smul, h.prod_eq' hc]

/-- Reordering items whose coefficients pairwise commute. -/
theorem foldl_map_op_smul_perm {ι : Type uι} (coeff : ι → M) {items₁ items₂ : List ι}
    (h : items₁.Perm items₂)
    (hc : ∀ i ∈ items₁, ∀ j ∈ items₁, Commute (coeff i) (coeff j)) (x : α) :
    items₁.foldl (fun state i => state <• coeff i) x =
      items₂.foldl (fun state i => state <• coeff i) x := by
  have hpair : (items₁.map coeff).Pairwise Commute := by
    rw [List.pairwise_map]
    exact List.pairwise_of_forall_mem_list hc
  rw [foldl_map_op_smul, foldl_map_op_smul, (h.map coeff).prod_eq' hpair]

/-- Reordering is free for coefficients drawn from a pairwise commuting set,
such as a commutative submonoid. -/
theorem foldl_map_op_smul_perm_of_mem {ι : Type uι} (S : Set M)
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (coeff : ι → M) (hcoeff : ∀ i, coeff i ∈ S)
    {items₁ items₂ : List ι} (h : items₁.Perm items₂) (x : α) :
    items₁.foldl (fun state i => state <• coeff i) x =
      items₂.foldl (fun state i => state <• coeff i) x :=
  foldl_map_op_smul_perm coeff h (fun i _ j _ => hS _ (hcoeff i) _ (hcoeff j)) x

end Mettapedia.Algebra.ActionFold
