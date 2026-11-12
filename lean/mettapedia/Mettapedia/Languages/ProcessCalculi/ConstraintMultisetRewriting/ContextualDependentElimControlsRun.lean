import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesStuck

/-!
# The mixed family commits where the base family is stuck

The kernel run of the mixed family on `belowStore`, `λ G g. (fst g) X ≐ λ G g. (fst g) A` at
`Π (G : U0 → U0) (g : Σ (_ : U0 → G A). U0). G A`: it commits at budget 16 (`below_mixed_committed`). The base
family is stuck on the same store at that budget (`below_stuck`), so the store separates the two families
(`below_repaired`).

The kernel runs on the other two witnesses (`nestedStore` under the mixed family, `sigmaBaseStore` under the family
above it) need more memory than the checking budget allows and are not kernel statements; their compiled runs read
`committed`.
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

/-- **The mixed family commits on the store**, at budget 16. -/
theorem below_mixed_committed : (run (mixedTower.solver 16) belowStore 8).readout = .commit := by decide +kernel

/-- **A store of the fragment, solvable, on which the base family is stuck and the mixed family commits.** -/
theorem below_repaired : InFragmentStore belowStore ∧ (frames setting.levels).Solvable belowStore ∧
    isStuck (run (baseTower.solver 16) belowStore 1) = true ∧
    (run (mixedTower.solver 16) belowStore 8).readout = .commit :=
  ⟨below_in_fragment, below_solvable, below_stuck, below_mixed_committed⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
