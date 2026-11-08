import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringRowsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusPairEtaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTwinsUnderControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjectionsControls

/-!
# The census controls under the flexible-base family

Every control store of the census (R99, R107 and this layer), run by the flexible-base solver `flexOnly` at budget 16
for eight rounds. A commit is a principal answer and a refutation certifies that the store has no solution
(`Outcome.readout_eq_refuted`), so on these stores the readout is the right answer. The cumulative family, the last one,
acts only where the flexible-base round is stuck, so it has the same run on every store decided here
(`ContextualDependentCumulative.cumulative_run_of_flex`).

| Stores | Readout |
|---|---|
| inversion, older inversion, flex–flex adjacent, exchange, dependent, far, intersection, flexible, prunable, matching | commit |
| flexible base, nested and applied projections (R99), same heads, a projection spine, twins, homogeneous, endpoints | commit |
| the second projection spine, the projector (pair η) | commit |
| occurs, head-free, rigid out-of-scope, older rigid, swapped | refuted |
| nested clash, argument, deep argument, projections, formers, refl, local, pair η, pair constant, endpoint (constant heads) | refuted |
| clashing twins, nested endpoints, under a local, under, a clashing projection spine | refuted |
| the cumulative argument `λ x. F x ≐ λ x. x`, `F : U1 → U1` | suspended |
| the intersection equation twice (`twiceStore`) | suspended |

The two suspended stores are in the fragment and solvable (`cumulative_in_fragment`, `cumulative_solvable`,
`twice_in_fragment`, `twice_solvable`). The cumulative family reads the first
(`ContextualDependentCumulative.Controls.cumulative_committed`). The second, intersection when another equation mentions
the metavariable, is the open row at this budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance2.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentSpineEta.Controls
open ContextualDependentPatternFiring.Controls

/-! ## Commits -/

theorem inversion_last : (run flexOnly inversionStore 8).readout = .commit := by decide +kernel
theorem olderInversion_last : (run flexOnly olderInversionStore 8).readout = .commit := by decide +kernel
theorem adjacent_last : (run flexOnly adjacentStore 8).readout = .commit := by decide +kernel
theorem exchange_last : (run flexOnly exchangeStore 8).readout = .commit := by decide +kernel
theorem dependent_last : (run flexOnly dependentStore 8).readout = .commit := by decide +kernel
theorem far_last : (run flexOnly farStore 8).readout = .commit := by decide +kernel
theorem intersection_last : (run flexOnly intersectionStore 8).readout = .commit := by decide +kernel
theorem flexible_last : (run flexOnly flexibleStore 8).readout = .commit := by decide +kernel
theorem prunable_last : (run flexOnly prunableStore 8).readout = .commit := by decide +kernel
theorem matching_last : (run flexOnly matchingStore 8).readout = .commit := by decide +kernel

theorem flexibleBase_last : (run flexOnly ContextualDependentCensus.Controls.flexibleBaseStore 8).readout = .commit := by
  decide +kernel
theorem nested_last : (run flexOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .commit := by
  decide +kernel
theorem applied_last : (run flexOnly ContextualDependentCensus.Controls.appliedStore 8).readout = .commit := by
  decide +kernel
theorem sameHeads_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.sameHeadsStore 8).readout = .commit := by decide +kernel
theorem projectionSpine_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.projectionSpineStore 8).readout = .commit := by
  decide +kernel
theorem twin_last : (run flexOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by
  decide +kernel
theorem homogeneous_last :
    (run flexOnly ContextualDependentTwinsUnder.Controls.homogeneousStore 8).readout = .commit := by decide +kernel
theorem endpointsCommit_last :
    (run flexOnly ContextualDependentIdEndpoints.Controls.endpointsCommitStore 8).readout = .commit := by
  decide +kernel
theorem secondSpine_last :
    (run flexOnly ContextualDependentConstantHeadsProjections.Controls.secondSpineStore 8).readout = .commit := by
  decide +kernel
theorem projector_last :
    (run flexOnly ContextualDependentCensusPairEta.Controls.projectorStore 8).readout = .commit := by decide +kernel

/-! ## Refutations -/

theorem occurs_last : (run flexOnly occursStore 8).readout = .refuted := by decide +kernel
theorem headFree_last : (run flexOnly headFreeStore 8).readout = .refuted := by decide +kernel
theorem rigid_last : (run flexOnly rigidStore 8).readout = .refuted := by decide +kernel
theorem older_last : (run flexOnly olderStore 8).readout = .refuted := by decide +kernel
theorem swapped_last : (run flexOnly swappedStore 8).readout = .refuted := by decide +kernel

theorem nestedClash_last :
    (run flexOnly ContextualDependentCensus.Controls.nestedClashStore 8).readout = .refuted := by decide +kernel
theorem argument_last : (run flexOnly ContextualDependentCensus.Controls.argumentStore 8).readout = .refuted := by
  decide +kernel
theorem deepArgument_last :
    (run flexOnly ContextualDependentCensus.Controls.deepArgumentStore 8).readout = .refuted := by decide +kernel
theorem projections_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.projectionsStore 8).readout = .refuted := by
  decide +kernel
theorem former_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.formerStore 8).readout = .refuted := by decide +kernel
theorem refl_last : (run flexOnly ContextualDependentConstantHeads.Controls.reflStore 8).readout = .refuted := by
  decide +kernel
theorem local_last : (run flexOnly ContextualDependentConstantHeads.Controls.localStore 8).readout = .refuted := by
  decide +kernel
theorem pairEta_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.pairEtaStore 8).readout = .refuted := by decide +kernel
theorem pairConstant_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.pairConstantStore 8).readout = .refuted := by
  decide +kernel
theorem endpoint_last :
    (run flexOnly ContextualDependentConstantHeads.Controls.endpointStore 8).readout = .refuted := by decide +kernel
theorem clashTwin_last :
    (run flexOnly ContextualDependentTwinsUnder.Controls.clashTwinStore 8).readout = .refuted := by decide +kernel
theorem nestedEndpoints_last :
    (run flexOnly ContextualDependentIdEndpoints.Controls.nestedStore 8).readout = .refuted := by decide +kernel
theorem underLocal_last :
    (run flexOnly ContextualDependentIdEndpoints.Controls.underLocalStore 8).readout = .refuted := by decide +kernel
theorem under_last : (run flexOnly ContextualDependentIdEndpoints.Controls.underStore 8).readout = .refuted := by
  decide +kernel
theorem clashSpine_last :
    (run flexOnly ContextualDependentConstantHeadsProjections.Controls.clashSpineStore 8).readout = .refuted := by
  decide +kernel

/-! ## The open rows -/

/-- **The cumulative argument stays suspended** under the last family: in the fragment, solvable, not read. -/
theorem cumulative_open :
    InFragmentStore cumulativeStore ∧ (frames setting.levels).Solvable cumulativeStore ∧
      (run flexOnly cumulativeStore 8).readout = .suspended :=
  ⟨cumulative_in_fragment, cumulative_solvable, by decide +kernel⟩

/-- **The intersection equation twice stays suspended** under the last family: in the fragment, solvable, not read. -/
theorem twice_open :
    InFragmentStore ContextualDependentIntersection.Controls.twiceStore ∧
      (frames setting.levels).Solvable ContextualDependentIntersection.Controls.twiceStore ∧
      (run flexOnly ContextualDependentIntersection.Controls.twiceStore 8).readout = .suspended :=
  ⟨ContextualDependentIntersection.Controls.twice_in_fragment, ContextualDependentIntersection.Controls.twice_solvable,
    by decide +kernel⟩

end ContextualDependentAcceptance2.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
