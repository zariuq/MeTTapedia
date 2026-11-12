import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulative

/-!
# The top family is stuck on `fixedStore`: a kernel statement

`fixedStore`, `λ x. F x ≐ λ x. x` at `Π (x : U0). U0` with `F : U1 → U0`, is in the dynamic pattern fragment and
has no solution; the top family (`sortTower`) is stuck on it in its first round, at budget 16. The run is evaluated
by the kernel. It is alone in this module: together with another run of the same size it exceeds the memory of the
check.
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

/-- **The top family is stuck** on `fixedStore` in its first round, at budget 16. -/
theorem fixed_stuck : isStuck (run (sortTower.solver 16) fixedStore 1) = true := by decide +kernel

/-- **A store of the fragment without solution on which the top family is stuck**: a refutation is missing. -/
theorem fixed_gap : InFragmentStore fixedStore ∧ ¬ (frames setting.levels).Solvable fixedStore ∧
    isStuck (run (sortTower.solver 16) fixedStore 1) = true :=
  ⟨fixed_in_fragment, fixed_unsolvable, fixed_stuck⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
