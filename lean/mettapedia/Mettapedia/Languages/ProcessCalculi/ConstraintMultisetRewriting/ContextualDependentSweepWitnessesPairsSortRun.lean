import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesPairs

/-!
# The top family is stuck on `pairSortStore`: a kernel statement

`pairSortStore`, `p ≐ ⟨A, U0⟩` at `Σ (_ : U0). U1` with `A : U0, p : Σ (_ : U0). U0`, is in the dynamic pattern
fragment and has no solution; the top family (`sortTower`) is stuck on it in its first round, at budget 16. The run
is evaluated by the kernel. It is alone in this module: together with another run of the same size it exceeds the
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

/-- **The top family is stuck** on `pairSortStore` in its first round, at budget 16. -/
theorem pairSort_stuck : isStuck (run (sortTower.solver 16) pairSortStore 1) = true := by decide +kernel

/-- **A store of the fragment without solution on which the top family is stuck**: the refutation of a universe
does not read the components of a pair. -/
theorem pairSort_gap : InFragmentStore pairSortStore ∧ ¬ (frames setting.levels).Solvable pairSortStore ∧
    isStuck (run (sortTower.solver 16) pairSortStore 1) = true :=
  ⟨pairSort_in_fragment, pairSort_unsolvable, pairSort_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
