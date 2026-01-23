import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
# Counterexample: `KSSeparation` is not derivable from `KnuthSkillingAlgebra`

This file packages the semidirect model (`SemidirectNoSeparation.lean`) as two small existential
statements:

1. There exists a noncommutative `KnuthSkillingAlgebra`.
2. There exists a `KnuthSkillingAlgebra` that does **not** satisfy `KSSeparation`.

These are minimal *formal* blockers against any proof attempt that tries to deduce
`KSSeparation` (or commutativity) from the base axioms alone.
-/

theorem exists_knuthskilling_noncomm :
    ∃ (α : Type) (_ : KnuthSkillingAlgebra α), ∃ x y : α, op x y ≠ op y x := by
  refine ⟨SD, inferInstance, SD.exX, SD.exY, ?_⟩
  simpa [KnuthSkillingAlgebraBase.op, SD.op] using SD.op_not_comm

theorem exists_knuthskilling_not_separation :
    ∃ (α : Type) (_ : KnuthSkillingAlgebra α), ¬ Mettapedia.ProbabilityTheory.KnuthSkilling.KSSeparation α := by
  refine ⟨SD, inferInstance, ?_⟩
  simpa using SD.not_KSSeparation

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples
