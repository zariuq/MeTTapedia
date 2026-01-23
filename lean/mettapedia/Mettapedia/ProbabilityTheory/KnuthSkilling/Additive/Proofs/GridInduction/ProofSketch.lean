import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.SeparationImpliesCommutative

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical KnuthSkillingAlgebra

/-!
# Representation Theorem: Proof Sketch / Reviewer Guide

This file contains **no new mathematics**. It is a compact “entry point” for reviewers that
packages the main dependency chain into a handful of short theorems.

## Where to start

1. `.../Additive/Proofs/GridInduction/ProofSketch.lean` (this file)
2. `.../Additive/Proofs/GridInduction/Main.lean` (public API)
3. `.../Additive/Proofs/GridInduction/Globalization.lean` (the globalization construction; “triple family”)
4. `.../Additive/Proofs/GridInduction/Core/Induction/*` (the B-empty extension step, i.e. the large proof)

## Separation and commutativity

Key observation: the iterate/power sandwich axiom already forces commutativity:
`KSSeparation → op commutative`. In the main pipeline, we use this early to obtain `GridComm`
for arbitrary grids.

The proof of commutativity from separation lives in:
`Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Axioms/SandwichSeparation.lean`,
and is bridged into the representation-theorem namespace by:
`.../Additive/Proofs/GridInduction/Core/SeparationImpliesCommutative.lean`.

## Paper cross-reference

See `paper/ks-formalization.tex`, Section `sec:main` (representation theorem) and
Section `sec:commutativity` (separation ⇒ commutativity).
-/

section Commutativity

variable (α : Type*) [KnuthSkillingAlgebra α]

/-- `KSSeparation` forces commutativity of `op`. -/
theorem op_comm_of_KSSeparation [KSSeparation α] : ∀ x y : α, op x y = op y x :=
  Core.op_comm_of_KSSeparation (α := α)

end Commutativity

section Representation

variable (α : Type*) [KnuthSkillingAlgebra α]

/-- A convenient “no typeclass plumbing” wrapper:
`KSSeparationStrict` suffices to run the full Appendix-A-style pipeline. -/
theorem associativity_representation_of_KSSeparationStrict [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  classical
  letI : KSSeparation α := KSSeparationStrict.toKSSeparation (α := α)
  letI : RepresentationGlobalization α := representationGlobalization_of_KSSeparationStrict (α := α)
  exact associativity_representation (α := α)

/-- If `[KSSeparation α]` holds and the order is dense, then strict separation is available and we
can run the globalization instance. -/
theorem associativity_representation_of_KSSeparation_of_denselyOrdered'
    [KSSeparation α] [DenselyOrdered α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      ∀ x y : α, Θ (op x y) = Θ x + Θ y := by
  exact associativity_representation_of_KSSeparation_of_denselyOrdered (α := α)

end Representation

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
