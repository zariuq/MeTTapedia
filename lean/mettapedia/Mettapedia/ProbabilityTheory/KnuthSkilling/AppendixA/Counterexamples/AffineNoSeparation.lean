import Mathlib.Data.PNat.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.WithBot

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical

/-!
# A failed countermodel attempt: affine-composition-style semidirect product

This file is intentionally **not** a `KnuthSkillingAlgebra` instance.

It records a natural noncommutative candidate operation on `WithBot (PNat ×ₗ ℕ)` that is
associative and strictly monotone (w.r.t. lex order), but **cannot** satisfy the K&S
Archimedean-style axiom `op_archimedean` because it has elements of multiplicative “scale” `1`
whose iterates never surpass elements of larger scale.

Moral: any attempt to build a noncommutative K&S model by “affine composition” must *exclude*
scale `1` (or otherwise change the order/axioms), and this interacts badly with having a bottom
identity and total order.

This is useful when searching for a noncommutative countermodel to K&S: it eliminates one common
idea early, with a short formal proof.
-/

abbrev AffBase := PNat ×ₗ ℕ
abbrev Aff := WithBot AffBase

namespace Aff

-- Pin the `WithBot` order instances on this `Option` type (avoids instance mismatch noise).
instance (priority := 10000) : LE (Option AffBase) := WithBot.instLE
instance (priority := 10000) : LT (Option AffBase) := WithBot.instLT
instance (priority := 10000) : OrderBot (Option AffBase) := WithBot.instOrderBot
instance (priority := 10000) [Preorder AffBase] : Preorder (Option AffBase) := WithBot.instPreorder
instance (priority := 10000) [LinearOrder AffBase] : LinearOrder (Option AffBase) := WithBot.linearOrder

def baseOp (p q : AffBase) : AffBase :=
  (p.1 * q.1, p.2 + (p.1 : ℕ) * q.2)

def op : Aff → Aff → Aff
  | ⊥, b => b
  | a, ⊥ => a
  | some p, some q => some (baseOp p q)

def ident : Aff := (⊥ : Aff)

def fst : Aff → ℕ
  -- Use `1` as the “scale” of the `WithBot` identity for multiplicative bookkeeping.
  -- This is just a helper for this file (not part of any K&S structure).
  | ⊥ => 1
  | some p => (p.1 : ℕ)

@[simp] theorem fst_bot : fst (⊥ : Aff) = 1 := rfl
@[simp] theorem fst_some (p : AffBase) : fst (some p : Aff) = (p.1 : ℕ) := rfl

theorem fst_op (x y : Aff) : fst (op x y) = fst x * fst y := by
  cases x <;> cases y <;> simp [fst, op, baseOp]

theorem baseOp_assoc (p q r : AffBase) : baseOp (baseOp p q) r = baseOp p (baseOp q r) := by
  apply Prod.ext
  · simp [baseOp, mul_assoc]
  · simp [baseOp, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem op_assoc : ∀ x y z : Aff, op (op x y) z = op x (op y z) := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [op, baseOp_assoc]

theorem op_noncomm :
    ∃ x y : Aff, op x y ≠ op y x := by
  classical
  let x : Aff := (some ((⟨2, by decide⟩ : PNat), 1))
  let y : Aff := (some ((⟨3, by decide⟩ : PNat), 1))
  refine ⟨x, y, ?_⟩
  simp [x, y, op, baseOp]
  decide

/-!
## Why `op_archimedean` fails for this candidate

Take `x` with first coordinate (scale) `1` and `y` with first coordinate `2`.
Then iterating `x` never changes the first coordinate, so `y` is never below an iterate of `x`.
-/

def x1 : Aff := some ((⟨1, Nat.one_pos⟩ : PNat), 0)
def y2 : Aff := some ((⟨2, by decide⟩ : PNat), 0)

theorem fst_x1 : fst x1 = 1 := by rfl
theorem fst_y2 : fst y2 = 2 := by rfl

theorem op_x1_self : op x1 x1 = x1 := by
  simp [x1, op, baseOp]

theorem not_op_archimedean_candidate :
    ¬ (∀ x y : Aff, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x) := by
  intro h
  have hx : ident < x1 := by
    have hx_ne : (x1 : Aff) ≠ ⊥ := by simp [x1]
    exact (WithBot.bot_lt_iff_ne_bot (x := (x1 : Aff))).2 hx_ne
  rcases h x1 y2 hx with ⟨n, hn⟩
  -- Since `op x1 x1 = x1`, all iterates of `(op x1)` at `x1` are constant.
  have h_iter : Nat.iterate (op x1) n x1 = x1 := by
    simpa using (Function.iterate_fixed (f := op x1) (x := x1) op_x1_self n)
  have hn' : y2 < x1 := by simpa [h_iter] using hn
  -- But `y2 < x1` is impossible: we can explicitly show `x1 < y2` since `1 < 2`
  -- in the lex order on the base.
  have hx1_lt_y2 : x1 < y2 := by
    -- Reduce to the base lex comparison.
    refine (WithBot.coe_lt_coe
        (a := (toLex ((⟨1, Nat.one_pos⟩ : PNat), (0 : ℕ)) : PNat × ℕ))
        (b := (toLex ((⟨2, by decide⟩ : PNat), (0 : ℕ)) : PNat × ℕ))).2 ?_
    -- Use the lex rule: compare first coordinates.
    refine (Prod.Lex.toLex_lt_toLex
        (x := ((⟨1, Nat.one_pos⟩ : PNat), (0 : ℕ)))
        (y := ((⟨2, by decide⟩ : PNat), (0 : ℕ)))).2 ?_
    exact Or.inl (by
      -- `1 < 2` in `PNat`
      exact (PNat.coe_lt_coe _ _).2 (by decide))
  have : ¬ y2 < x1 := not_lt_of_ge (le_of_lt hx1_lt_y2)
  exact this hn'

end Aff

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
