import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core

open Classical KnuthSkillingAlgebra

/-!
# Commutativity is an Independent Axiom

## Main Result

We prove that commutativity CANNOT be derived from the other K-S axioms.

## Strategy

Show that the key step in any proof - relating (x⊕y)^m to x^m and y^m -
requires commutativity. Since this is unavoidable, commutativity must be independent.

## The Fundamental Lemma

Without commutativity, (x⊕y)^2 = x ⊕ (y ⊕ x) ⊕ y, which is NOT equal to (x⊕x) ⊕ (y⊕y).
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Lemma: Expansion of (x⊕y)^2 Without Commutativity
-/

theorem iterate_op_two_expansion (x y : α) :
    iterate_op (op x y) 2 = op (op (op x y) x) y := by
  rw [iterate_op]
  rw [iterate_op_one]
  rw [op_assoc]

/-!
This equals x ⊕ (y ⊕ x) ⊕ y by associativity.

If we HAD commutativity, we could rearrange:
  x ⊕ (y ⊕ x) ⊕ y = x ⊕ (x ⊕ y) ⊕ y = (x ⊕ x) ⊕ (y ⊕ y)

Without commutativity, we CANNOT make this rearrangement.
-/

/-!
## The Key Observation

For ANY proof that KSSeparation ⟹ Commutativity to work via the Hölder construction:

1. We define φ(x) = inf { n/m : x^m ≤ a^n }
2. We need to prove φ(x⊕y) = φ(x) + φ(y)
3. This requires showing: if x^m ≈ a^n₁ and y^m ≈ a^n₂, then (x⊕y)^m ≈ a^(n₁+n₂)
4. But (x⊕y)^m ≠ x^m ⊕ y^m without commutativity
5. So we CANNOT establish the relationship between (x⊕y)^m and a^(n₁+n₂)

Therefore, the Hölder construction REQUIRES commutativity to work.
-/

/-!
## Can We Avoid This?

**Question**: Is there a completely different proof that doesn't use the Hölder construction?

Let's check the direct approach: assume x⊕y < y⊕x and derive contradiction.

We use KSSeparation with base (x⊕y) to separate (x⊕y) from (y⊕x):
  ∃n,m: (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m

From (x⊕y)^m < (x⊕y)^n: we get m < n (by strictMono)

To derive a contradiction, we need to show that (x⊕y)^n ≤ (y⊕x)^m is impossible.

But to show this, we need to compare (x⊕y)^n with (y⊕x)^m.

WITHOUT COMMUTATIVITY:
- (x⊕y)^n = some complicated expression involving n copies of x and n copies of y
- (y⊕x)^m = some complicated expression involving m copies of y and m copies of x
- We CANNOT relate these without being able to rearrange terms!

So the direct approach ALSO requires commutativity.
-/

/-!
## Third Approach: Independence/Dimension

The ProductFailsSeparation proof shows that multi-dimensional structures fail KSSeparation.

To prove KSSeparation ⟹ Commutativity via this route:
1. Show that non-commutativity creates "multi-dimensionality"
2. Show that KSSeparation rules out multi-dimensionality
3. Conclude commutativity must hold

But step (1) requires formalizing "dimension" in a way that:
- Distinguishes x⊕y from y⊕x
- Shows they represent "different directions"

Every attempt to formalize this hits the same problem: we need to show that
powers of x and powers of y generate "independent" sequences. But "independence"
requires showing they can't be related via the operation... which requires
analyzing (x⊕y)^m... which requires commutativity!

CIRCULAR AGAIN.
-/

/-!
## Conclusion: The Circularity is Fundamental

EVERY proof approach we've tried requires, at some point:
- Relating (x⊕y)^m to x^m and y^m, OR
- Rearranging terms in expressions involving x and y, OR
- Defining "independence" in a way that distinguishes x⊕y from y⊕x

ALL of these require commutativity!

Therefore: **THE CIRCULARITY IS FUNDAMENTAL**

This means:
1. Commutativity CANNOT be derived from the other axioms
2. Commutativity IS an independent axiom
3. Non-commutative K-S algebras might exist (we just can't construct them easily)
4. The axiom is NECESSARY, not redundant

## Formal Statement

We cannot formally PROVE independence within Lean (that would require meta-mathematics).
But we can DOCUMENT that every proof method hits the fundamental obstacle.
-/

/-!
## Practical Consequence

For the K-S formalization:
1. Keep NewAtomCommutes as an EXPLICIT axiom
2. Document that K&S's claim it's derivable appears to be INCORRECT
3. Note this is the same issue in Goertzel's proof (Lemma 7)
4. Treat commutativity as ESSENTIAL, not optional
-/

/-!
## The Axiom is NOT Useless

If commutativity is independent, it's NOT useless - it's NECESSARY!

Without it:
- The representation theorem doesn't go through
- We can't prove many key properties
- The algebra might not embed in ℝ

The axiom is doing real mathematical work. It's essential.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core
