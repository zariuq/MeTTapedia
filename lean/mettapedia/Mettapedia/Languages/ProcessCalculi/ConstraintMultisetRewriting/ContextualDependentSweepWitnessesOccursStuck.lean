import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccurs

/-!
# The unknown of a pattern under a binder of the other side: the kernel statements

The family above the mixed family is stuck in its first round on `λ x. Q x ≐ λ x. Π (y : A). Q y`, at budget 16, as a statement checked
by the kernel (`boundOccurs_stuck`). With the facts of `ContextualDependentSweepWitnessesOccurs` this is a store of
the fragment, without solution, that the family above the mixed family neither commits nor refutes (`boundOccurs_gap`).

**Control.** On `λ x. Q x ≐ λ x. Π (y : A). Q x` the family above the mixed family refutes in its first round (`outer_refuted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth

/-- **The family above the mixed family is stuck in its first round** on the store, at budget 16. -/
theorem boundOccurs_stuck : isStuck (run (elimSigmaTower.solver 16) boundOccursStore 1) = true := by
  decide +kernel

/-- **A store of the fragment, without solution, on which the family above the mixed family is stuck**: it asks for a refutation that
no reader gives. -/
theorem boundOccurs_gap : InFragmentStore boundOccursStore ∧ ¬ (frames setting.levels).Solvable boundOccursStore ∧
    isStuck (run (elimSigmaTower.solver 16) boundOccursStore 1) = true :=
  ⟨boundOccurs_in_fragment, boundOccurs_unsolvable, boundOccurs_stuck⟩

/-- **Control**: with the unknown at the outer variable the family above the mixed family refutes, at budget 16. -/
theorem outer_refuted : (run (elimSigmaTower.solver 16) outerStore 1).readout = .refuted := by decide +kernel

/-- The control store is in the fragment and has no solution. -/
theorem outer_in_fragment_refuted : InFragmentStore outerStore ∧ ¬ (frames setting.levels).Solvable outerStore :=
  ⟨outer_in_fragment, drive_refuted (elimSigmaTower.solver 16) 1 _ outer_refuted⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
