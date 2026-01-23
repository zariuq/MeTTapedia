import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core

open Classical KnuthSkillingAlgebra

/-!
# Historical Note: Early Commutativity-Proof Dead Ends

This file predates the “mass counting” proof that the iterate/power sandwich axiom `KSSeparation`
forces global commutativity.

Current status in this development:
- `KSSeparation → ∀ x y, op x y = op y x` is proven in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Proofs/GridInduction/Core/SeparationImpliesCommutative.lean`.
- The core argument appears in
  `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Axioms/SandwichSeparation.lean`.

We keep the lemma below because it is a good “sanity check” for why the naïve distributivity step
`(x⊕y)^m = x^m ⊕ y^m` cannot be used before commutativity is established.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Lemma: Expansion of `(x⊕y)^2` Without Commutativity
-/

theorem iterate_op_two_expansion (x y : α) :
    iterate_op (op x y) 2 = op (op (op x y) x) y := by
  -- Unfold `iterate_op` at `2` and `1`, then reassociate.
  simp [iterate_op, op_ident_right]
  simpa using (op_assoc (op x y) x y).symm

/-!
By associativity, this is `(x ⊕ y) ⊕ x ⊕ y`. Without commutativity, there is no reason for this
to coincide with `(x ⊕ x) ⊕ (y ⊕ y)`.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core
