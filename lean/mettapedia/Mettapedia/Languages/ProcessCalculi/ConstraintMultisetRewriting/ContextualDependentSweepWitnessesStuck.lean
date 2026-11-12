import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnesses

/-!
# The base family is stuck on a projection below an application at an applied base type

The kernel run of the base family on `belowStore`,
`λ G g. (fst g) X ≐ λ G g. (fst g) A` at `Π (G : U0 → U0) (g : Σ (_ : U0 → G A). U0). G A`: stuck in its first
round at budget 16 (`below_stuck`). The store is in the fragment and solvable (`below_in_fragment`,
`below_solvable`), so the base family is not accepting at this budget (`below_gap`).

Stuckness at every budget is not proved here.
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

/-- **The base family is stuck in its first round** on the store, at budget 16. -/
theorem below_stuck : isStuck (run (baseTower.solver 16) belowStore 1) = true := by decide +kernel

/-- **A store of the fragment, solvable, on which the base family is stuck.** -/
theorem below_gap : InFragmentStore belowStore ∧ (frames setting.levels).Solvable belowStore ∧
    isStuck (run (baseTower.solver 16) belowStore 1) = true :=
  ⟨below_in_fragment, below_solvable, below_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
