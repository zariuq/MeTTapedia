import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWithin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairsRaisedRun

/-!
# `pairRaisedStore` is repaired: a kernel statement

`pairRaisedStore`, `p ≐ ⟨A, A⟩` at `Σ (_ : U0). U1` with `A : U0, p : Σ (_ : U0). U0`: the family with the
refutation of a universe is stuck on it in its first round (`pairRaised_stuck`), and the family that reads every
equation at its least annotation through the components of Σ types commits (`pairRaised_within_committed`). Both
runs are evaluated by the kernel, at budget 16.
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

/-- **The family that reads through components commits** on `pairRaisedStore`, at budget 16. -/
theorem pairRaised_within_committed :
    (run (withinTower.solver 16) pairRaisedStore 2).readout = .commit := by decide +kernel

/-- **A store of the fragment, solvable, on which the family below is stuck and this family commits.** -/
theorem pairRaised_repaired : InFragmentStore pairRaisedStore ∧
    (frames setting.levels).Solvable pairRaisedStore ∧
    isStuck (run (sortTower.solver 16) pairRaisedStore 1) = true ∧
    (run (withinTower.solver 16) pairRaisedStore 2).readout = .commit :=
  ⟨pairRaised_in_fragment, pairRaised_solvable, pairRaised_stuck, pairRaised_within_committed⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
