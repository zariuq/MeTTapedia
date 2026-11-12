import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesLeast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesUniverseStuck

/-!
# The raised store is repaired: kernel statements

`raisedStore`, `X ≐ A` at `U1` with `A X : U0`: the family with the occurs rule at a bound variable is stuck on it
in its first round (`raised_stuck`), and the family that reads every equation at its least annotation commits
(`raised_least_committed`). Both runs are evaluated by the kernel, at budget 16. The same for `raisedPiStore`,
`X ≐ Π (_ : A). A` at `U1` (`raisedPi_repaired`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth ContextualDependentEtaDepth.BaseControls

/-- **The family that reads every equation at its least annotation commits** on `X ≐ A` at `U1`, at budget 16. -/
theorem raised_least_committed : (run (leastTower.solver 16) raisedStore 2).readout = .commit := by decide +kernel

/-- **A store of the fragment, solvable, on which the family below is stuck and this family commits.** -/
theorem raised_repaired : InFragmentStore raisedStore ∧ (frames setting.levels).Solvable raisedStore ∧
    isStuck (run (boundTower.solver 16) raisedStore 1) = true ∧
    (run (leastTower.solver 16) raisedStore 2).readout = .commit :=
  ⟨raised_in_fragment, raised_solvable, raised_stuck, raised_least_committed⟩

/-- **The family commits** on `X ≐ Π (_ : A). A` at `U1`, at budget 16. -/
theorem raisedPi_least_committed : (run (leastTower.solver 16) raisedPiStore 2).readout = .commit := by
  decide +kernel

/-- **A store of the fragment on which the family below is stuck and this family commits.** -/
theorem raisedPi_repaired : InFragmentStore raisedPiStore ∧
    isStuck (run (boundTower.solver 16) raisedPiStore 1) = true ∧
    (run (leastTower.solver 16) raisedPiStore 2).readout = .commit :=
  ⟨raisedPi_in_fragment, raisedPi_stuck, raisedPi_least_committed⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
