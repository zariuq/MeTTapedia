import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.SandwichSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

/-!
# 1-Dimensional Ordered Monoids are Commutative

This file proves that ordered monoids admitting a monotone homomorphism into (ℝ≥0, +)
must be commutative.

## The Key Insight

If φ : α → ℝ≥0 is a monotone homomorphism, then:
- φ(x ⊕ y) = φ(x) + φ(y)  (homomorphism property)
- φ(x) + φ(y) = φ(y) + φ(x)  (addition in ℝ is commutative)
- Therefore φ(x ⊕ y) = φ(y ⊕ x)

If φ is injective (or order-reflecting), this implies x ⊕ y = y ⊕ x.

## Strategy

1. Define what it means for an ordered monoid to be "representable" in ℝ≥0
2. Prove that representable monoids are commutative
3. Show that KSSeparation implies representability (future work)

This is a **Hölder-type theorem** for ordered monoids.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Definition: Representability

An ordered monoid is "representable" if there exists a monotone homomorphism into (ℝ≥0, +).

We require:
- φ preserves the operation: φ(x ⊕ y) = φ(x) + φ(y)
- φ preserves the identity: φ(ident) = 0
- φ preserves order: x < y → φ(x) < φ(y)

The last condition (order-preservation) ensures φ is injective.
-/

/-- A representation of an ordered monoid into ℝ≥0. -/
structure Representation (α : Type*) [KnuthSkillingAlgebra α] where
  /-- The representation function. -/
  φ : α → ℝ
  /-- Preserves identity. -/
  φ_ident : φ ident = 0
  /-- Preserves operation (homomorphism). -/
  φ_op : ∀ x y : α, φ (op x y) = φ x + φ y
  /-- Strictly monotone (implies injectivity). -/
  φ_strictMono : StrictMono φ

/-- An ordered monoid is representable if it admits a representation. -/
class Representable (α : Type*) [inst : KnuthSkillingAlgebra α] where
  /-- There exists a representation. -/
  repr : Representation α

/-!
## Main Theorem: Representable ⟹ Commutative

If an ordered monoid admits a representation into ℝ≥0, then it must be commutative.

**Proof**:
- Let φ be a representation
- For any x, y: φ(x ⊕ y) = φ(x) + φ(y) = φ(y) + φ(x) = φ(y ⊕ x)
- Since φ is strictly monotone (hence injective), x ⊕ y = y ⊕ x
-/

theorem representable_implies_commutative [inst : Representable α] :
    ∀ x y : α, op x y = op y x := by
  intro x y
  let φ := inst.repr.φ
  -- φ(x ⊕ y) = φ(x) + φ(y) = φ(y) + φ(x) = φ(y ⊕ x)
  have h1 : φ (op x y) = φ x + φ y := inst.repr.φ_op x y
  have h2 : φ x + φ y = φ y + φ x := add_comm (φ x) (φ y)
  have h3 : φ y + φ x = φ (op y x) := (inst.repr.φ_op y x).symm
  have h_eq : φ (op x y) = φ (op y x) := by
    calc φ (op x y)
        = φ x + φ y := h1
      _ = φ y + φ x := h2
      _ = φ (op y x) := h3
  -- Since φ is strictly monotone, it's injective
  exact inst.repr.φ_strictMono.injective h_eq

/-!
## Corollary: The Path to Commutativity

If we can show that KSSeparation implies Representable, then we're done!

**Remaining work**:
1. Construct a representation φ from the separation property
2. Prove φ is a homomorphism
3. Prove φ is strictly monotone

This is the Hölder construction adapted to our setting.
-/

/-!
## Hölder Construction (Sketch)

For an Archimedean ordered monoid with KSSeparation, we can construct φ as follows:

Fix a base element a > ident.

For each x > ident, define:
  φ_a(x) = inf { n/m : x^m ≤ a^n }

Key properties to prove:
1. φ_a is well-defined (the set is nonempty and bounded below by 0)
2. φ_a(x ⊕ y) = φ_a(x) + φ_a(y)
3. φ_a is strictly monotone
4. φ_a is independent of the choice of base a (this uses KSSeparation!)

The last property is crucial and is where KSSeparation comes in:
- If we have two bases a and b, we can relate φ_a and φ_b via rational approximations
- KSSeparation ensures these approximations are consistent
-/

/-!
## Step 1: Define the Hölder Function

For a fixed base a > ident, define the "logarithm base a" of x.
-/

noncomputable def holderLog [KSSeparation α] (a : α) (_ha : ident < a) (x : α) : ℝ :=
  if _hx : ident < x then
    -- inf { n/m : x^m ≤ a^n, m > 0 }
    sInf { r : ℝ | ∃ n m : ℕ, 0 < m ∧ r = n / m ∧ iterate_op x m ≤ iterate_op a n }
  else 0

/-!
## Step 2: Show the Set is Nonempty

By the Archimedean property, for any x there exists n such that x < a^n.
Therefore the set { r : ℝ | ∃ n m, ... } contains some element.
-/

theorem holderLog_set_nonempty [KSSeparation α] (a : α) (ha : ident < a) (x : α) (_hx : ident < x) :
    ∃ r : ℝ, ∃ n m : ℕ, 0 < m ∧ r = n / m ∧ iterate_op x m ≤ iterate_op a n := by
  -- By Archimedean property, ∃n such that x < a^n
  obtain ⟨n, hn⟩ := bounded_by_iterate a ha x
  -- Then x^1 < a^n, so we can take m = 1, giving r = n/1 = n
  use n, n, 1
  constructor
  · norm_num
  constructor
  · norm_num
  -- Show: x^1 ≤ a^n
  rw [iterate_op_one]
  exact le_of_lt hn

/-!
## Step 3: Show holderLog is Additive (Sketch)

The key property: holderLog(x ⊕ y) = holderLog(x) + holderLog(y)

**Proof idea**:
- If x^m ≈ a^n₁ and y^m ≈ a^n₂, then (x⊕y)^m ≈ x^m ⊕ y^m ≈ a^(n₁+n₂)
- Therefore log(x⊕y) ≈ n₁/m + n₂/m = log(x) + log(y)
- Make this precise using infima

This requires proving that iterate_op distributes over op for commutative operations.
But we're trying to prove commutativity! This is where we hit circularity.

**Alternative approach**: Use KSSeparation to show that the approximations are consistent
without assuming commutativity. This is subtle and requires careful analysis.
-/

/-!
### Open Problem: Additivity of `holderLog`

The classical Hölder/Dedekind-cut approach defines `holderLog` from `KSSeparation`, but showing
it is additive is exactly where circularity appears: the natural proof uses identities like
`(x ⊕ y)^m = x^m ⊕ y^m`, which already require commutativity.

We record the desired additivity statement as a `Prop` so other files can depend on it without
introducing `sorry`. -/

/-- Conjecture: the Hölder-style `holderLog` is additive on positive inputs. -/
def HolderLogAdditive [KSSeparation α] (a : α) (ha : ident < a) : Prop :=
  ∀ x y : α, ident < x → ident < y →
    holderLog a ha (op x y) = holderLog a ha x + holderLog a ha y

/-!
## The Circularity Problem

We're stuck in the same circularity as before:
- To prove holderLog is additive, we need: (x⊕y)^m = x^m ⊕ y^m
- But this requires commutativity!
- Which is what we're trying to prove!

## A Different Approach: Use Separation Directly

Instead of trying to construct a representation, let's use a direct argument:

**Claim**: If KSSeparation holds and x ⊕ y ≠ y ⊕ x, we can derive a contradiction
using the separation property itself.

**Proof strategy**:
1. Assume x ⊕ y < y ⊕ x (WLOG)
2. Use separation with various bases to constrain the relationship between
   x, y, x⊕y, and y⊕x
3. Show that these constraints are mutually incompatible

This avoids the need to construct a representation explicitly.
-/

/-!
## Direct Proof Attempt

Let's try to prove commutativity directly from KSSeparation without going through
representability.

The key insight from ProductFailsSeparation: multi-dimensional structures fail separation
because powers live in independent subspaces.

If x ⊕ y ≠ y ⊕ x, then {x, y} form a "2-dimensional" subspace in some sense.
We need to make this precise.
-/

/-!
### Open Problem: `KSSeparation` forces commutativity

Several direct proof attempts exist (see `.../Core/CommutativityProof.lean`,
`.../Core/SeparationImpliesCommutative.lean`, and `.../Core/LogarithmicApproach.lean`), but no
complete proof is currently known.

We package the statement as a `Prop` to keep the library `sorry`-free while making the goal
explicit. -/

/-- Conjecture: `KSSeparation` implies commutativity. -/
def SeparationImpliesCommutative [KSSeparation α] : Prop :=
  ∀ x y : α, op x y = op y x

/-!
## Conclusion

We're still stuck! The core issue:
- Without commutativity, we can't compute (x⊕y)^m explicitly
- The separation property gives us constraints, but we can't extract a contradiction
- We need a more sophisticated argument

**Possible paths forward**:
1. Find a clever combinatorial argument that works without expanding (x⊕y)^m
2. Use a different formulation of "1-dimensionality" that's easier to work with
3. Add additional axioms (like density or continuity) that make the argument go through
4. Accept that commutativity might genuinely need to be an independent axiom

Given that even Goertzel's proof has gaps and Codex treats it as an axiom,
option 4 might be the pragmatic choice for now.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
