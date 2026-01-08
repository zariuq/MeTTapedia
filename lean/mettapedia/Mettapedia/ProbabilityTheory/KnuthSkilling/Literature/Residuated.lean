import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Lattice

/-!
# Residuated structures (Jenei 2019 / Hahn embedding for residuated semigroups)

This file formalizes the core algebraic interfaces used in the Hahn-embedding paper for
residuated semigroups/lattices.

Primary source:
- Sándor Jenei, “The Hahn embedding theorem for a class of residuated semigroups”
  (arXiv:1910.01387v4), Definition 1.1 and surrounding discussion.
  Local PDF: `literature/KS_codex/Jipsen_Tuyt_2019_Hahn_Embedding.pdf`

We start with the (commutative) residuated-monoid interface and prove the standard “exchange”
property (Def. 1.1, “exchange property”) from adjointness.

Deep representation theorems are tracked separately as explicit `Prop` interfaces (no `sorry`).
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open Classical

/-!
## Residuated commutative monoids (adjointness)

Jenei’s Definition 1.1 assumes a commutative monoid operation `⋆` with a residual `→` such that

`x ⋆ y ≤ z` iff `y ≤ x → z`.
-/

class ResiduatedMonoid (α : Type*) extends CommMonoid α, PartialOrder α where
  /-- The residual operation `x → z`. -/
  res : α → α → α
  /-- Adjointness: `x ⋆ y ≤ z ↔ y ≤ x → z`. -/
  adj : ∀ x y z : α, x * y ≤ z ↔ y ≤ res x z

namespace ResiduatedMonoidLemmas

variable {α : Type*} [ResiduatedMonoid α]

infixr:70 " ⟿ " => ResiduatedMonoid.res

/-!
### Exchange law (Jenei Def. 1.1, “exchange property”)

In Jenei’s commutative setting, adjointness implies:

`(x ⋆ y) → z = x → (y → z)`.

This is a standard lemma for residuated monoids; we include it as a proved theorem here so later
files can use it without re-deriving the algebra.
-/
theorem exchange (x y z : α) : ((x * y) ⟿ z) = (x ⟿ (y ⟿ z)) := by
  apply le_antisymm
  · -- `(x*y)→z ≤ x→(y→z)`; by adjointness with base `x`, it suffices to show:
    -- `x * ((x*y)→z) ≤ (y→z)`.
    have hx : x * ((x * y) ⟿ z) ≤ y ⟿ z := by
      -- By adjointness with base `y`, it suffices to show:
      -- `y * (x * ((x*y)→z)) ≤ z`.
      apply (ResiduatedMonoid.adj y (x * ((x * y) ⟿ z)) z).1
      have hxy : (x * y) * ((x * y) ⟿ z) ≤ z := by
        -- adjointness with `x*y` and reflexivity
        exact (ResiduatedMonoid.adj (x * y) ((x * y) ⟿ z) z).2 le_rfl
      -- Rewrite to `y * (x * t)` using commutativity/associativity.
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxy
    exact (ResiduatedMonoid.adj x ((x * y) ⟿ z) (y ⟿ z)).1 hx
  · -- `x→(y→z) ≤ (x*y)→z`; by adjointness with base `x*y`, it suffices to show:
    -- `(x*y) * (x→(y→z)) ≤ z`.
    have : (x * y) * (x ⟿ (y ⟿ z)) ≤ z := by
      -- It suffices to show `x * (x→(y→z)) ≤ (y→z)` and then use adjointness with `y`.
      have hx : x * (x ⟿ (y ⟿ z)) ≤ y ⟿ z :=
        (ResiduatedMonoid.adj x (x ⟿ (y ⟿ z)) (y ⟿ z)).2 le_rfl
      have hy : y * (x * (x ⟿ (y ⟿ z))) ≤ z :=
        (ResiduatedMonoid.adj y (x * (x ⟿ (y ⟿ z))) z).2 (by
          simpa [mul_assoc] using hx)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hy
    exact (ResiduatedMonoid.adj (x * y) (x ⟿ (y ⟿ z)) z).1 this

/-!
### Basic consequences of adjointness

These are standard “residuation” lemmas used throughout the Hahn-embedding literature:

* `x * (x ⟿ z) ≤ z`
* multiplication is monotone in each argument
* the residual is monotone in its second argument and antitone in its first
-/

theorem le_res_of_mul_le (x y z : α) (h : x * y ≤ z) : y ≤ x ⟿ z :=
  (ResiduatedMonoid.adj x y z).1 h

theorem mul_le_of_le_res (x y z : α) (h : y ≤ x ⟿ z) : x * y ≤ z :=
  (ResiduatedMonoid.adj x y z).2 h

theorem mul_res_le (x z : α) : x * (x ⟿ z) ≤ z :=
  (ResiduatedMonoid.adj x (x ⟿ z) z).2 le_rfl

theorem mul_mono_right (x : α) : Monotone fun y : α => x * y := by
  intro y y' hyy'
  -- By adjointness, it suffices to show `y ≤ x ⟿ (x*y')`.
  apply (ResiduatedMonoid.adj x y (x * y')).2
  have : y' ≤ x ⟿ (x * y') := (ResiduatedMonoid.adj x y' (x * y')).1 le_rfl
  exact hyy'.trans this

theorem mul_mono_left (y : α) : Monotone fun x : α => x * y := by
  -- commutativity reduces to `mul_mono_right`
  simpa [mul_comm] using (mul_mono_right (α := α) y)

theorem res_mono_right (x : α) : Monotone fun z : α => x ⟿ z := by
  intro z z' hzz'
  -- By adjointness, it suffices to show `x * (x ⟿ z) ≤ z'`.
  apply (ResiduatedMonoid.adj x (x ⟿ z) z').1
  exact (mul_res_le (α := α) x z).trans hzz'

theorem res_anti_left (z : α) : Antitone fun x : α => x ⟿ z := by
  intro x x' hxx'
  -- By adjointness, it suffices to show `x * (x' ⟿ z) ≤ z`.
  apply (ResiduatedMonoid.adj x (x' ⟿ z) z).1
  have hx' : x' * (x' ⟿ z) ≤ z := mul_res_le (α := α) x' z
  have hx : x * (x' ⟿ z) ≤ x' * (x' ⟿ z) := by
    -- monotonicity in the first argument
    exact (mul_mono_left (α := α) (x' ⟿ z) hxx')
  exact hx.trans hx'

end ResiduatedMonoidLemmas

/-!
## Hahn-embedding theorem interface (residuated setting)

Jenei’s main results require substantial additional structure (lattice, involution, chain,
finitely many idempotents, …). We record the target as an explicit `Prop` so later work can connect
this literature codex to a precise Lean hypothesis list without introducing `sorry`.
-/

/-!
### Where the embedding statements live

The actual embedding statements from Jenei (2019) are recorded (as explicit `Prop` interfaces) in:

- `Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.ResiduatedHahnEmbedding`
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature
