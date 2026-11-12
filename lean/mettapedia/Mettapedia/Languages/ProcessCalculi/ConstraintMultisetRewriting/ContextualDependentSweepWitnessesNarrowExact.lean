import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExactControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowUpdate

/-!
# What stands between the conditional decision on exact stores and its hypothesis

`narrowStore`, `X ≐ Π (y : Y). Y` at `U1` with `X : U0, Y : U1`, is in the dynamic pattern fragment, has exact
arguments and has a principal answer; and the top family (`pairTower`) is stuck on it wherever its compiled run
reads `stuck` (`narrow_exact_gap_of_ending`). The compiled run reads `stuck` at budget 16; that reading is an
evaluation, and the kernel statement of the stuck run is the one for the family two layers below, `sortTower`
(`narrow_gap`). So the hypothesis of
`ContextualDependentEtaDepth.tower_pair_decided_of_uncovered_exact` asks for a reader that the family does not
have: the narrowing of a declaration.
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

/-- **A store of the fragment with exact arguments and a principal answer on which the top family is stuck**
wherever its compiled run reads `stuck`: the missing reader is the narrowing of a declaration. -/
theorem narrow_exact_gap_of_ending {fuel rounds : Nat}
    (read : endingPair fuel rounds ctxAXY narrowStore = .stuck) :
    InFragmentStore narrowStore ∧ storeExact narrowStore = true ∧
      (∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAXY), (frames setting.levels).Principal narrowStore answer) ∧
      isStuck (run (pairTower.solver fuel) narrowStore rounds) = true :=
  ⟨narrow_in_fragment, narrow_exact, narrow_principal, stuck_of_endingPair read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
