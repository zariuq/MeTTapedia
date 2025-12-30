/-
# Common Combination Rules

Unified abstraction for evidence combination across probability theories.

## Key Insight

ALL probability theories have some notion of combining evidence/information:
- **Classical**: P(A ∩ B) = P(A) · P(B|A)  (product rule)
- **D-S**: Dempster's rule of combination
- **K&S**: The ⊕ operation (associative, monotone)
- **Quantum**: Tensor product of density matrices

This module captures the COMMON structure: an associative operation
that combines plausibilities/beliefs.

## Distinction

- **Additive**: P(A ∪ B) = P(A) + P(B) when disjoint
- **Multiplicative**: P(A ∩ B) = P(A) · P(B|A)
- **General**: x ⊕ y with associativity and monotonicity
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Common

/-!
## §1: Abstract Combination Operations
-/

/-- A combination operation on a type α.
    This is the core abstraction for combining plausibilities. -/
structure CombinationOp (α : Type*) where
  /-- The combination operation -/
  op : α → α → α
  /-- Identity element (if it exists) -/
  ident : Option α

/-- A monoid-like combination: associative with identity. -/
structure MonoidalCombination (α : Type*) extends CombinationOp α where
  /-- Identity exists -/
  hasIdent : ident.isSome
  /-- Get the identity -/
  identity : α := ident.get hasIdent
  /-- Associativity -/
  assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  /-- Right identity -/
  ident_right : ∀ x : α, op x identity = x
  /-- Left identity -/
  ident_left : ∀ x : α, op identity x = x

namespace MonoidalCombination

variable {α : Type*} (c : MonoidalCombination α)

/-- Iterate the operation n times: x ⊕ x ⊕ ... ⊕ x -/
def iterate (x : α) : ℕ → α
  | 0 => c.identity
  | n + 1 => c.op x (iterate x n)

/-- iterate 1 x = x -/
theorem iterate_one (x : α) : c.iterate x 1 = x := by
  simp [iterate, c.ident_right]

/-- iterate (n + 1) x = x ⊕ iterate n x -/
theorem iterate_succ (x : α) (n : ℕ) :
    c.iterate x (n + 1) = c.op x (c.iterate x n) := rfl

end MonoidalCombination

/-!
## §2: Ordered Combinations (for K&S and Classical)
-/

/-- A combination operation that respects order. -/
structure OrderedCombination (α : Type*) [Preorder α]
    extends MonoidalCombination α where
  /-- Monotonicity in first argument -/
  mono_left : ∀ y : α, Monotone (fun x => op x y)
  /-- Monotonicity in second argument -/
  mono_right : ∀ x : α, Monotone (fun y => op x y)

namespace OrderedCombination

variable {α : Type*} [Preorder α] (c : OrderedCombination α)

/-- Combined monotonicity: a ≤ b and c ≤ d implies op a c ≤ op b d -/
theorem mono {a b x y : α} (hab : a ≤ b) (hxy : x ≤ y) :
    c.op a x ≤ c.op b y :=
  le_trans (c.mono_left x hab) (c.mono_right b hxy)

end OrderedCombination

/-!
## §3: Commutative Combinations
-/

/-- A commutative combination operation. -/
structure CommutativeCombination (α : Type*)
    extends MonoidalCombination α where
  /-- Commutativity -/
  comm : ∀ x y : α, op x y = op y x

namespace CommutativeCombination

variable {α : Type*} (c : CommutativeCombination α)

/-- Commutativity gives us both associativities for free -/
theorem left_comm (x y z : α) : c.op x (c.op y z) = c.op y (c.op x z) := by
  rw [← c.assoc, c.comm x y, c.assoc]

end CommutativeCombination

/-!
## §4: Real-Valued Combination Rules
-/

/-- A combination rule on real-valued plausibilities.
    This captures both additive (sum rule) and multiplicative (product rule) cases. -/
structure RealCombinationRule where
  /-- The combination function -/
  combine : ℝ → ℝ → ℝ
  /-- Identity value (0 for addition, 1 for multiplication) -/
  identVal : ℝ
  /-- Associativity -/
  assoc : ∀ x y z, combine (combine x y) z = combine x (combine y z)
  /-- Right identity -/
  ident_right : ∀ x, combine x identVal = x

/-- Addition rule: combine = + with identity 0 -/
def additionRule : RealCombinationRule where
  combine := (· + ·)
  identVal := 0
  assoc := add_assoc
  ident_right := add_zero

/-- Multiplication rule: combine = × with identity 1 -/
def multiplicationRule : RealCombinationRule where
  combine := (· * ·)
  identVal := 1
  assoc := mul_assoc
  ident_right := mul_one

/-!
## §5: Compatibility with Valuations
-/

/-- A valuation is compatible with a combination rule if it respects the operation. -/
structure CompatibleValuation (L : Type*) [Lattice L] [BoundedOrder L]
    (rule : RealCombinationRule) where
  /-- The valuation function -/
  val : L → ℝ
  /-- Monotonicity -/
  mono : ∀ a b, a ≤ b → val a ≤ val b
  /-- Normalization: ⊥ → 0 -/
  val_bot : val ⊥ = 0
  /-- Normalization: ⊤ → 1 -/
  val_top : val ⊤ = 1
  /-- Compatibility condition: for disjoint elements, val(a ⊔ b) follows the rule -/
  disjoint_combine : ∀ a b, a ⊓ b = ⊥ → val (a ⊔ b) = rule.combine (val a) (val b)

/-!
## §6: The K&S Combination as a Special Case

The K&S ⊕ operation is an OrderedCombination with additional Archimedean property.
-/

/-- An Archimedean combination: no infinitesimals.
    This is the key property that forces isomorphism to (ℝ≥0, +). -/
structure ArchimedeanCombination (α : Type*) [LinearOrder α]
    extends OrderedCombination α where
  /-- Identity is minimal -/
  ident_min : ∀ x : α, identity ≤ x
  /-- Archimedean: for any x > identity and any y, some iterate of x exceeds y -/
  archimedean : ∀ x y, identity < x → ∃ n : ℕ, y < toMonoidalCombination.iterate x n

/-!
## §7: Summary

This module provides:
1. **CombinationOp**: Basic operation structure
2. **MonoidalCombination**: Associative with identity
3. **OrderedCombination**: Monotone combinations
4. **CommutativeCombination**: Commutative combinations
5. **RealCombinationRule**: Addition and multiplication rules
6. **ArchimedeanCombination**: The K&S axiom system

These abstract the common patterns across:
- Classical probability (additive for disjoint, multiplicative for conditioning)
- Dempster-Shafer (Dempster's combination rule)
- Knuth-Skilling (the ⊕ operation)
- Quantum (tensor products)
-/

end Mettapedia.ProbabilityTheory.Common
