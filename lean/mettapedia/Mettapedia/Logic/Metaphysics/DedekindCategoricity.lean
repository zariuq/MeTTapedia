import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic

/-!
# Dedekind categoricity: second-order Peano structures are isomorphic

The contrast pole to Henkin latitude: with **full** second-order induction (induction
over *all* subsets of the carrier), the natural numbers are pinned up to isomorphism
(Dedekind 1888). Any two `PeanoStructure`s are isomorphic by a unique zero- and
successor-preserving equivalence (`dedekind_categoricity`).

The statement is deliberately *structural* (a `Set`-quantified induction field rather
than a formula in the MSO syntax of `MonadicSecondOrder.lean`): the Boolean-algebra
signature there cannot express `succ`, and the structural form is exactly what "full
semantics" means in the ambient type theory. Under Henkin semantics — induction only
for sets in a designated family — the categoricity argument is unavailable, which is
the latitude the companion files make precise.
-/

namespace Mettapedia.Logic.Metaphysics

universe u v

/-- A second-order Peano structure: a carrier with zero and successor, where successor
is injective, misses zero, and **full** (all-subsets) induction holds. -/
structure PeanoStructure : Type (u + 1) where
  /-- The carrier. -/
  carrier : Type u
  /-- Zero. -/
  zero : carrier
  /-- Successor. -/
  succ : carrier → carrier
  succ_inj : Function.Injective succ
  succ_ne_zero : ∀ x, succ x ≠ zero
  /-- Full second-order induction: every subset containing zero and closed under
  successor is everything. -/
  induction : ∀ S : Set carrier, zero ∈ S → (∀ x ∈ S, succ x ∈ S) → S = Set.univ

namespace PeanoStructure

variable (P : PeanoStructure.{u}) (Q : PeanoStructure.{v})

/-- The canonical map from `ℕ`. -/
def fromNat : ℕ → P.carrier
  | 0 => P.zero
  | n + 1 => P.succ (fromNat n)

@[simp] theorem fromNat_zero : P.fromNat 0 = P.zero := rfl
@[simp] theorem fromNat_succ (n : ℕ) : P.fromNat (n + 1) = P.succ (P.fromNat n) := rfl

theorem fromNat_injective : Function.Injective P.fromNat := by
  intro n m h
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => exact absurd h.symm (P.succ_ne_zero _)
  | succ n ih =>
    cases m with
    | zero => exact absurd h (P.succ_ne_zero _)
    | succ m => exact congrArg Nat.succ (ih (P.succ_inj h))

theorem fromNat_surjective : Function.Surjective P.fromNat := by
  have h := P.induction (Set.range P.fromNat) ⟨0, rfl⟩
    (fun x ⟨n, hn⟩ => ⟨n + 1, by simp [hn]⟩)
  intro y
  have hy : y ∈ Set.range P.fromNat := h ▸ Set.mem_univ y
  exact hy

theorem fromNat_bijective : Function.Bijective P.fromNat :=
  ⟨P.fromNat_injective, P.fromNat_surjective⟩

/-- The canonical equivalence between any two second-order Peano structures. -/
noncomputable def equiv : P.carrier ≃ Q.carrier :=
  (Equiv.ofBijective _ P.fromNat_bijective).symm.trans
    (Equiv.ofBijective _ Q.fromNat_bijective)

theorem equiv_fromNat (n : ℕ) : P.equiv Q (P.fromNat n) = Q.fromNat n := by
  have h : (Equiv.ofBijective _ P.fromNat_bijective).symm (P.fromNat n) = n :=
    (Equiv.ofBijective _ P.fromNat_bijective).symm_apply_apply n
  simp [equiv, h]

@[simp] theorem equiv_zero : P.equiv Q P.zero = Q.zero :=
  P.equiv_fromNat Q 0

theorem equiv_succ (x : P.carrier) :
    P.equiv Q (P.succ x) = Q.succ (P.equiv Q x) := by
  obtain ⟨n, rfl⟩ := P.fromNat_surjective x
  rw [← P.fromNat_succ, equiv_fromNat, equiv_fromNat]
  exact Q.fromNat_succ n

end PeanoStructure

/-- **Dedekind categoricity.** Any two second-order Peano structures are isomorphic by a
zero- and successor-preserving equivalence: full second-order induction pins the natural
numbers. (Contrast: Henkin-relativized induction admits nonstandard models — the
latitude made precise in the companion files.) -/
theorem dedekind_categoricity (P : PeanoStructure.{u}) (Q : PeanoStructure.{v}) :
    ∃ e : P.carrier ≃ Q.carrier, e P.zero = Q.zero ∧
      ∀ x, e (P.succ x) = Q.succ (e x) :=
  ⟨P.equiv Q, P.equiv_zero Q, P.equiv_succ Q⟩

end Mettapedia.Logic.Metaphysics

