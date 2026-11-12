import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairs

/-!
# The top family is stuck on `pairRaisedStore`: a kernel statement

`pairRaisedStore`, `p ≐ ⟨A, A⟩` at `Σ (_ : U0). U1` with `A : U0, p : Σ (_ : U0). U0`, is in the dynamic pattern
fragment and solvable; the top family (`sortTower`) is stuck on it in its first round, at budget 16. The run is
evaluated by the kernel. It is alone in this module: together with another run of the same size it exceeds the
memory of the check.
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

/-- **The top family is stuck** on `pairRaisedStore` in its first round, at budget 16. -/
theorem pairRaised_stuck : isStuck (run (sortTower.solver 16) pairRaisedStore 1) = true := by decide +kernel

/-- **A solvable store of the fragment on which the top family is stuck**: the reading at the least annotation
does not lower a component of a Σ type. -/
theorem pairRaised_gap : InFragmentStore pairRaisedStore ∧ (frames setting.levels).Solvable pairRaisedStore ∧
    isStuck (run (sortTower.solver 16) pairRaisedStore 1) = true :=
  ⟨pairRaised_in_fragment, pairRaised_solvable, pairRaised_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
