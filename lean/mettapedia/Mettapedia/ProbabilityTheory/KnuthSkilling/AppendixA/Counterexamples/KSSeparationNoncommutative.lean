import Mathlib.Order.WithBot
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical KnuthSkillingAlgebra

/-!
# Attempt: Noncommutative `KSSeparation` Model

This file records a **failed attempt** to build a *noncommutative* `KnuthSkillingAlgebra` model
that still satisfies `KSSeparation`.

The goal would be a genuine counterexample to:

> `KSSeparation α` ⇒ `∀ x y, op x y = op y x`.

What we currently have is weaker but still informative:
1. A natural “twisted addition” with `u₁ * u₂` is actually **commutative** (so it cannot refute
   anything).
2. A genuinely asymmetric twist such as `u₁^2 * u₂` breaks **associativity** (so it cannot even
   form a `KnuthSkillingAlgebra`).

So the “polynomial twist in a second coordinate” route does not (yet) yield a countermodel.
-/

abbrev TwistedBase := ℕ × ℤ
abbrev Twisted := WithBot TwistedBase

namespace Twisted

-- Pin the WithBot order instances
instance (priority := 10000) : LE (Option TwistedBase) := WithBot.instLE
instance (priority := 10000) : LT (Option TwistedBase) := WithBot.instLT
instance (priority := 10000) : OrderBot (Option TwistedBase) := WithBot.instOrderBot
instance (priority := 10000) [Preorder TwistedBase] : Preorder (Option TwistedBase) := WithBot.instPreorder
instance (priority := 10000) : LinearOrder (Option TwistedBase) := by
  letI : LinearOrder TwistedBase := Prod.Lex.linearOrder
  exact WithBot.linearOrder

def baseOp (p q : TwistedBase) : TwistedBase :=
  let u₁ := p.1
  let x₁ := p.2
  let u₂ := q.1
  let x₂ := q.2
  -- The twist: add `u₁ * u₂`.  This looks asymmetric at first glance, but it is actually symmetric.
  (u₁ + u₂, x₁ + x₂ + (u₁ * u₂ : ℤ))

def op : Twisted → Twisted → Twisted
  | ⊥, b => b
  | a, ⊥ => a
  | some p, some q => some (baseOp p q)

def ident : Twisted := (⊥ : Twisted)

@[simp] theorem op_bot_left (x : Twisted) : op ⊥ x = x := by cases x <;> rfl
@[simp] theorem op_bot_right (x : Twisted) : op x ⊥ = x := by cases x <;> rfl
@[simp] theorem op_some_some (p q : TwistedBase) : op (some p) (some q) = some (baseOp p q) := rfl

-- Associativity
theorem baseOp_assoc (p q r : TwistedBase) : baseOp (baseOp p q) r = baseOp p (baseOp q r) := by
  simp only [baseOp]
  ext
  · -- First component: just addition
    ring
  · -- Second component: check the twist terms
    -- LHS: (x₁ + x₂ + u₁*u₂) + x₃ + (u₁+u₂)*u₃
    --    = x₁ + x₂ + x₃ + u₁*u₂ + u₁*u₃ + u₂*u₃
    -- RHS: x₁ + (x₂ + x₃ + u₂*u₃) + u₁*(u₂+u₃)
    --    = x₁ + x₂ + x₃ + u₂*u₃ + u₁*u₂ + u₁*u₃
    ring

theorem op_assoc : ∀ x y z : Twisted, op (op x y) z = op x (op y z) := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [op, baseOp_assoc]

  /-- The `u₁ * u₂` twist is symmetric, so this operation is commutative (hence useless as a
  noncommutative countermodel). -/
  theorem op_comm : ∀ x y : Twisted, op x y = op y x := by
    intro x y
    cases x <;> cases y <;> simp [op, baseOp]
    · -- `some`/`some`: reduce to equality of the underlying pair.
      apply Option.some.inj
      ext <;> ring_nf

end Twisted

/-!
## Attempt 2: Asymmetric twist

Use `twist(u₁, u₂) = u₁² * u₂` which is genuinely asymmetric:
- `twist(1, 2) = 1² * 2 = 2`
- `twist(2, 1) = 2² * 1 = 4`
-/

namespace Twisted2

abbrev TwistedBase := ℕ × ℤ
abbrev Twisted := WithBot TwistedBase

instance (priority := 10000) : LE (Option TwistedBase) := WithBot.instLE
instance (priority := 10000) : LT (Option TwistedBase) := WithBot.instLT
instance (priority := 10000) : OrderBot (Option TwistedBase) := WithBot.instOrderBot
instance (priority := 10000) [Preorder TwistedBase] : Preorder (Option TwistedBase) := WithBot.instPreorder
instance (priority := 10000) : LinearOrder (Option TwistedBase) := by
  letI : LinearOrder TwistedBase := Prod.Lex.linearOrder
  exact WithBot.linearOrder

def baseOp (p q : TwistedBase) : TwistedBase :=
  let u₁ := p.1
  let x₁ := p.2
  let u₂ := q.1
  let x₂ := q.2
  -- Asymmetric twist: u₁² * u₂
  (u₁ + u₂, x₁ + x₂ + (u₁^2 * u₂ : ℤ))

def op : Twisted → Twisted → Twisted
  | ⊥, b => b
  | a, ⊥ => a
  | some p, some q => some (baseOp p q)

def ident : Twisted := (⊥ : Twisted)

@[simp] theorem op_bot_left (x : Twisted) : op ⊥ x = x := by cases x <;> rfl
@[simp] theorem op_bot_right (x : Twisted) : op x ⊥ = x := by cases x <;> rfl

  /-- The asymmetric `u₁^2 * u₂` twist breaks associativity (so it cannot underlie a
  `KnuthSkillingAlgebra`). -/
  theorem not_op_assoc :
      ¬ (∀ x y z : Twisted, op (op x y) z = op x (op y z)) := by
    intro h
    have h' := h (some (1, 0)) (some (1, 0)) (some (1, 0))
    -- Explicitly compute both sides: they differ in the second coordinate.
    -- LHS = some (3, 5), RHS = some (3, 3).
    have hne : (some (3, 5) : Twisted) ≠ some (3, 3) := by
      decide
    exact hne (by simpa [op, baseOp] using h')

end Twisted2

/-!
The u₁²*u₂ twist breaks associativity! Let me try a different approach.

## Attempt 3: Minimal asymmetric twist that preserves associativity

The challenge: find f(u₁, u₂) such that:
1. f(u₁, u₂) ≠ f(u₂, u₁) for some u₁, u₂ (asymmetric)
2. f(u₁, u₂) + f(u₁+u₂, u₃) = f(u₂, u₃) + f(u₁, u₂+u₃) (associativity)
3. f has polynomial growth (for Archimedean property)

Actually, condition 2 is very restrictive! Let me check if ANY asymmetric f works...

If we expand associativity for op (op (u₁,x₁) (u₂,x₂)) (u₃,x₃):
- LHS second coord: (x₁ + x₂ + f(u₁,u₂)) + x₃ + f(u₁+u₂, u₃)
- RHS second coord: x₁ + (x₂ + x₃ + f(u₂,u₃)) + f(u₁, u₂+u₃)

For equality:
  f(u₁,u₂) + f(u₁+u₂, u₃) = f(u₂,u₃) + f(u₁, u₂+u₃)

This is a strong functional equation! Does it force f to be symmetric?

Let u₁=u₂=u₃=1:
  f(1,1) + f(2,1) = f(1,1) + f(1,2)
  ⟹ f(2,1) = f(1,2)

Let u₁=1, u₂=2, u₃=1:
  f(1,2) + f(3,1) = f(2,1) + f(1,3)

We know f(1,2) = f(2,1), so:
  f(2,1) + f(3,1) = f(2,1) + f(1,3)
  ⟹ f(3,1) = f(1,3)

By induction, this seems to force f(m,n) = f(n,m) for all m,n!

  **Conclusion (heuristic):** in this “twist in the second coordinate” family, associativity
  appears to force symmetry (hence commutativity).

This means we CANNOT build a counterexample with this approach.
-/

/-!
## What This Means

If I can't build a noncommutative associative algebra with the separation property,
then maybe:

1. **KSSeparation DOES force commutativity** (and K&S/Goertzel proofs are correct but incomplete)
2. **The proof exists but is subtle** (need to extract it from K&S paper)
3. **Need to try a completely different algebra structure** (not (ℕ × ℤ, twisted addition))

Let me think about other approaches...

**Alternative: Non-additive base**
Instead of ℕ × ℤ, use a genuinely different structure.
For example: (ℕ, +) but with MATRIX multiplication for the second component?

Or: Use quaternions (non-commutative but associative)?

Actually, the K-S axioms assume a LINEAR ORDER, which rules out matrices/quaternions.

**Alternative: Different twist in a different coordinate**
What if the first coordinate is also twisted?
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
