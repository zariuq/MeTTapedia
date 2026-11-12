import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccursOuter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccursStuck

/-!
# The repair of the witness, as kernel statements

On `λ x. Q x ≐ λ x. Π (y : A). Q y` the family with the occurs rule at a bound variable refutes in its first round,
at budget 16 (`boundOccurs_bound_refuted`). So the store is in the fragment, has no solution, the family below is
stuck on it, and this family refutes it (`boundOccurs_repaired`).
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

/-- **The family with the occurs rule at a bound variable refutes the witness** in its first round, at budget 16. -/
theorem boundOccurs_bound_refuted : (run (boundTower.solver 16) boundOccursStore 1).readout = .refuted := by
  decide +kernel

/-- **A store of the fragment without solution, stuck under the family below, refuted by this family.** -/
theorem boundOccurs_repaired : InFragmentStore boundOccursStore ∧
    ¬ (frames setting.levels).Solvable boundOccursStore ∧
    isStuck (run (elimSigmaTower.solver 16) boundOccursStore 1) = true ∧
    (run (boundTower.solver 16) boundOccursStore 1).readout = .refuted :=
  ⟨boundOccurs_in_fragment, boundOccurs_unsolvable, boundOccurs_stuck, boundOccurs_bound_refuted⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
