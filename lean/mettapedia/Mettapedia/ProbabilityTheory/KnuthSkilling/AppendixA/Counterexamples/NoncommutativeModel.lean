import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples.KSSeparationNotDerivable
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples.RankObstructionLinear

/-!
# Noncommutative models for `KnuthSkillingAlgebra`?

This file explores whether the `KnuthSkillingAlgebra` axioms are already strong enough to
force commutativity, by attempting to build a noncommutative model.

Status:
- There are easy noncommutative models of `KnuthSkillingAlgebra` (see `KSSeparationNotDerivable.lean`).
- Every “natural” noncommutative construction tried so far (free monoids, semidirect/lex products,
  affine-composition-style models, …) fails `KSSeparation`.

This file records the *open* countermodel search problem explicitly:

> Does there exist a noncommutative `KnuthSkillingAlgebra` that *does* satisfy `KSSeparation`?

If yes, it refutes the K&S Appendix A commutativity claim as formalized here.
If no, then proving nonexistence is a promising alternate route to the main theorem.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open KnuthSkillingAlgebra

/-- A “true” countermodel to the Appendix-A commutativity theorem would be a noncommutative
`KnuthSkillingAlgebra` that also satisfies `KSSeparation`. -/
def NoncommutativeKSSeparationCountermodel : Prop :=
  ∃ (α : Type),
    ∃ (_ : KnuthSkillingAlgebra α),
      ∃ (_ : KSSeparation α),
        ∃ x y : α, op x y ≠ op y x

/-- There exists a noncommutative `KnuthSkillingAlgebra` (so commutativity is not automatic). -/
theorem exists_noncommutative_knuthskilling :
    ∃ (α : Type), ∃ (_ : KnuthSkillingAlgebra α), ∃ x y : α, op x y ≠ op y x := by
  simpa using exists_knuthskilling_noncomm

/-- There exists a `KnuthSkillingAlgebra` that does **not** satisfy `KSSeparation`. -/
theorem exists_knuthskilling_not_separation' :
    ∃ (α : Type), ∃ (_ : KnuthSkillingAlgebra α), ¬ KSSeparation α := by
  simpa using exists_knuthskilling_not_separation

/-!
## A practical obstruction checklist for countermodel-hunting

`RankObstructionLinear.lean` proves that if a candidate model admits a monotone additive “rank”
into an ordered additive monoid `β`, and there is a strict chain of three positive elements
sharing the same rank, then `KSSeparation` is impossible.

This rules out a wide class of noncommutative constructions that come with an obvious “size”
coordinate (word length, lex-first coordinate, grading, …) and a nontrivial fiber.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
