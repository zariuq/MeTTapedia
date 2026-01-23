import Mathlib.Algebra.Order.Archimedean.Basic

import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# Mathlib Bridge for Knuth–Skilling

Mathlib's main "Archimedean ordered group embeds into `ℝ`" theorem
(`Mathlib/Data/Real/Embedding.lean`) is stated for additive *commutative groups*.

K&S Appendix A starts from a *noncommutative* operation `op` and derives commutativity as a theorem.
So the embedding theorem is not directly applicable to a raw `[KnuthSkillingAlgebra α]`.

This file provides a small bridge: under `[KSSeparation α]`, we derive both commutativity
and the Archimedean property (from `SandwichSeparation.lean`), and show these imply mathlib's
`Archimedean` typeclass (for the induced additive commutative monoid).
-/

/-- Type wrapper interpreting `KnuthSkillingAlgebraBase.op` as addition and `ident` as `0`. -/
structure KSAdd (α : Type*) where
  val : α

namespace KSAdd

@[ext] theorem ext {α : Type*} {x y : KSAdd α} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance {α : Type*} [LE α] : LE (KSAdd α) := ⟨fun x y => x.val ≤ y.val⟩
instance {α : Type*} [LT α] : LT (KSAdd α) := ⟨fun x y => x.val < y.val⟩

instance {α : Type*} [LinearOrder α] : PartialOrder (KSAdd α) where
  le x y := x.val ≤ y.val
  lt x y := x.val < y.val
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm x y hxy hyx := by
    apply KSAdd.ext
    exact le_antisymm hxy hyx
  lt_iff_le_not_ge x y := by
    -- transport the linear-order characterization of `<` from `α`
    simpa using (lt_iff_le_not_ge : x.val < y.val ↔ x.val ≤ y.val ∧ ¬ y.val ≤ x.val)

instance {α : Type*} [KnuthSkillingAlgebra α] : Zero (KSAdd α) :=
  ⟨⟨ident⟩⟩

instance {α : Type*} [KnuthSkillingAlgebra α] : Add (KSAdd α) :=
  ⟨fun x y => ⟨op x.val y.val⟩⟩

@[simp] theorem val_zero {α : Type*} [KnuthSkillingAlgebra α] : (0 : KSAdd α).val = ident := rfl
@[simp] theorem val_add {α : Type*} [KnuthSkillingAlgebra α] (x y : KSAdd α) :
    (x + y).val = op x.val y.val := rfl

/-- Turn a commutative K&S operation into an additive commutative monoid structure (on the wrapper). -/
def instAddCommMonoid {α : Type*} [KnuthSkillingAlgebra α]
    (hcomm : ∀ x y : α, op x y = op y x) : AddCommMonoid (KSAdd α) where
  add := (· + ·)
  zero := (0 : KSAdd α)
  nsmul n x := ⟨iterate_op x.val n⟩
  nsmul_zero x := by
    ext
    simp [iterate_op_zero, val_zero]
  nsmul_succ n x := by
    ext
    have hswap : op x.val (iterate_op x.val n) = op (iterate_op x.val n) x.val := by
      simpa using (hcomm x.val (iterate_op x.val n))
    simpa [iterate_op_succ, val_add] using hswap
  add_assoc x y z := by
    ext
    simpa [val_add] using (op_assoc x.val y.val z.val)
  zero_add x := by
    ext
    simpa [val_add, val_zero] using (op_ident_left x.val)
  add_zero x := by
    ext
    simpa [val_add, val_zero] using (op_ident_right x.val)
  add_comm x y := by
    ext
    simpa [val_add] using (hcomm x.val y.val)

/-- Under `KSSeparation`, we get mathlib's `Archimedean` once we view `op` as commutative addition.

Commutativity and the Archimedean property are both derived from `KSSeparation`
(see `SandwichSeparation.lean`). -/
theorem archimedean_of_KSSeparation {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α] :
    @Archimedean (KSAdd α) (instAddCommMonoid (α := α)
      (fun x y => SandwichSeparation.SeparationToCommutativity.op_comm_of_KSSeparation x y))
      (by infer_instance) := by
  classical
  letI : AddCommMonoid (KSAdd α) := instAddCommMonoid (α := α)
    (fun x y => SandwichSeparation.SeparationToCommutativity.op_comm_of_KSSeparation x y)
  refine ⟨?_⟩
  intro x y hy
  -- Apply the K&S Archimedean (derived from KSSeparation) with `x := y` (positive) and `y := x` (arbitrary).
  obtain ⟨n, hn⟩ := SandwichSeparation.SeparationToArchimedean.op_archimedean_of_separation y.val x.val (by
    -- `0 < y` in the wrapper is `ident < y.val` in `α`.
    simpa [KSAdd.val_zero] using hy)
  -- Convert K&S's strict bound into the ≤ bound demanded by mathlib's `Archimedean`.
  refine ⟨n + 1, ?_⟩
  have hn' : x.val < iterate_op y.val (n + 1) := by
    simpa [nat_iterate_eq_iterate_op_succ] using hn
  -- `nsmul` for our induced `AddCommMonoid` is `iterate_op`.
  exact (le_of_lt hn')

/-- Legacy: `op_archimedean` implies mathlib's `Archimedean` given commutativity.
This version takes an explicit Archimedean hypothesis for use in contexts without `KSSeparation`. -/
theorem archimedean_of_op_archimedean_explicit {α : Type*} [KnuthSkillingAlgebra α]
    (hcomm : ∀ x y : α, op x y = op y x)
    (harch : ∀ (a x : α), ident < a → ∃ n : ℕ, x < Nat.iterate (op a) n a) :
    @Archimedean (KSAdd α) (instAddCommMonoid (α := α) hcomm) (by infer_instance) := by
  classical
  letI : AddCommMonoid (KSAdd α) := instAddCommMonoid (α := α) hcomm
  refine ⟨?_⟩
  intro x y hy
  -- Apply the Archimedean hypothesis with `a := y` (positive) and `x := x` (arbitrary).
  obtain ⟨n, hn⟩ := harch y.val x.val (by
    -- `0 < y` in the wrapper is `ident < y.val` in `α`.
    simpa [KSAdd.val_zero] using hy)
  -- Convert K&S's strict bound into the ≤ bound demanded by mathlib's `Archimedean`.
  refine ⟨n + 1, ?_⟩
  have hn' : x.val < iterate_op y.val (n + 1) := by
    simpa [nat_iterate_eq_iterate_op_succ] using hn
  -- `nsmul` for our induced `AddCommMonoid` is `iterate_op`.
  exact (le_of_lt hn')

end KSAdd

end Mettapedia.ProbabilityTheory.KnuthSkilling
