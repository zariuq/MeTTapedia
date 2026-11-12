import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesRetyped

/-!
# The top family is stuck on `loopStore`: a kernel statement

`loopStore`, `λ x. P x ≐ λ x. Id U0 x x` at `Π (x : U0). U1` with `P : U1 → U1`, is in the dynamic pattern fragment
and has no solution; the top family (`sortTower`) is stuck on it in its first round, at budget 16. The run is
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

/-- **The top family is stuck** on `loopStore` in its first round, at budget 16. -/
theorem loop_stuck : isStuck (run (sortTower.solver 16) loopStore 1) = true := by decide +kernel

/-- **A store of the fragment without solution on which the top family is stuck**: a refutation is missing. -/
theorem loop_gap : InFragmentStore loopStore ∧ ¬ (frames setting.levels).Solvable loopStore ∧
    isStuck (run (sortTower.solver 16) loopStore 1) = true :=
  ⟨loop_in_fragment, loop_unsolvable, loop_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
