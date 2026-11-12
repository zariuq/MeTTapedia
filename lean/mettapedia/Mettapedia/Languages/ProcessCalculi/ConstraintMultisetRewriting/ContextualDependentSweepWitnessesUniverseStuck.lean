import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesUniverse

/-!
# An unknown equated above its own universe: the kernel statements

The family with the occurs rule at a bound variable is stuck in its first round on `X ≐ A` at `U1`, over
`A : U0, X : U0`, at budget 16, as a statement checked by the kernel (`raised_stuck`). With the facts of
`ContextualDependentSweepWitnessesUniverse` this is a store of the fragment, solvable, that the family neither
commits nor refutes (`raised_gap`). The same holds for `X ≐ Π (_ : A). A` at `U1`, without the solvability
(`raisedPi_stuck`).

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
open ContextualDependentPatternFiring.Controls ContextualDependentEtaDepth ContextualDependentEtaDepth.BaseControls

/-- **The family is stuck in its first round** on `X ≐ A` at `U1`, at budget 16. -/
theorem raised_stuck : isStuck (run (boundTower.solver 16) raisedStore 1) = true := by decide +kernel

/-- **A store of the fragment, solvable, on which the family with the occurs rule at a bound variable is stuck.** -/
theorem raised_gap : InFragmentStore raisedStore ∧ (frames setting.levels).Solvable raisedStore ∧
    isStuck (run (boundTower.solver 16) raisedStore 1) = true :=
  ⟨raised_in_fragment, raised_solvable, raised_stuck⟩

/-- The family is stuck in its first round on `X ≐ Π (_ : A). A` at `U1`, at budget 16. -/
theorem raisedPi_stuck : isStuck (run (boundTower.solver 16) raisedPiStore 1) = true := by decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
