import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.Composition

/-!
# Sequential and parallel valuations from a concurrent cost algebra

A concurrent cost algebra has two total monoidal compositions on one carrier.
This module exposes each composition as a `PartialMonoid`, the algebra used by
generic proof-relevant event valuations.  The conversion is structure-level:
it does not choose a scheduler, claim that two events are independent, or
identify the sequential and parallel accounts.

The WorkSpan instance supplies a negative control: both valuation algebras are
total and lawful, but they disagree on two nonempty unit branches.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.ConcurrentCostValuation

open Mettapedia.GSLT

universe u

/-- Sequential composition viewed as the total fragment of a partial event
valuation algebra. -/
def sequentialPartialMonoid {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) : PartialMonoid Cost where
  unit := algebra.zero
  op := fun first second => some (algebra.sequential first second)
  unit_op := by
    intro value
    rw [algebra.sequential_zero_left]
  op_unit := by
    intro value
    rw [algebra.sequential_zero_right]
  op_assoc := by
    intro first second third
    simp only [Option.bind_some]
    rw [algebra.sequential_assoc]

/-- Parallel composition viewed as the total fragment of a partial event
valuation algebra.  Using it for an event family still requires independent
evidence that the events may run in parallel. -/
def parallelPartialMonoid {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) : PartialMonoid Cost where
  unit := algebra.zero
  op := fun left right => some (algebra.parallel left right)
  unit_op := by
    intro value
    rw [algebra.parallel_zero_left]
  op_unit := by
    intro value
    rw [algebra.parallel_zero_right]
  op_assoc := by
    intro first second third
    simp only [Option.bind_some]
    rw [algebra.parallel_assoc]

/-- Every sequential grade pair is accepted; this construction adds no
resource-rejection policy. -/
theorem sequential_op_isSome {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) (first second : Cost) :
    ((sequentialPartialMonoid algebra).op first second).isSome :=
  rfl

/-- Every parallel grade pair is accepted by the valuation algebra itself.
Semantic or resource independence is a separate admission obligation. -/
theorem parallel_op_isSome {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) (left right : Cost) :
    ((parallelPartialMonoid algebra).op left right).isSome :=
  rfl

/-- The concrete WorkSpan sequential valuation algebra. -/
abbrev workSpanSequential : PartialMonoid WorkSpan :=
  sequentialPartialMonoid WorkSpan.algebra

/-- The concrete WorkSpan parallel valuation algebra. -/
abbrev workSpanParallel : PartialMonoid WorkSpan :=
  parallelPartialMonoid WorkSpan.algebra

/-- Positive control: two unit jobs accumulate exactly two units of work and
two units of sequential span. -/
theorem workSpanSequential_two_units :
    workSpanSequential.op ⟨1, 1⟩ ⟨1, 1⟩ = some ⟨2, 2⟩ :=
  rfl

/-- Positive control: the same jobs have parallel span one. -/
theorem workSpanParallel_two_units :
    workSpanParallel.op ⟨1, 1⟩ ⟨1, 1⟩ = some ⟨2, 1⟩ :=
  rfl

/-- Negative control: lawfulness and totality do not collapse the two
compositions. -/
theorem workSpan_valuation_compositions_distinct :
    workSpanSequential.op ⟨1, 1⟩ ⟨1, 1⟩ ≠
      workSpanParallel.op ⟨1, 1⟩ ⟨1, 1⟩ := by
  decide

#print axioms sequentialPartialMonoid
#print axioms parallelPartialMonoid
#print axioms workSpan_valuation_compositions_distinct

end Mettapedia.Algebra.ConcurrentCostValuation
