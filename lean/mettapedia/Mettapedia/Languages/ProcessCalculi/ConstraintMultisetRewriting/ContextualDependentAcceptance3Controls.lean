import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralInPlaceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosureControls

/-!
# The census under the last family

The last family is the in-place family (`ContextualDependentIntersectionGeneral.inPlaceFamily`): the cumulative family,
then general intersection at the newest metavariable, after rotation, and in place. On every control store of the
census (R86 through R116, the gap witnesses `twiceStore` and the twin store included), at budget 16:

* the run of eight rounds is **decided** (committed or refuted, never suspended), and
* the residual store after each of the first eight rounds, whenever the run is cut off there, has Miller sides
  (`finalDecided`).

These are runs at one budget, the evidence the class and the family are built against. They are not a decision
theorem. The reduction `inPlace_decided_of_settling_miller` is conditional on firing and closure on the Miller class,
and at the tower that hypothesis fails: the fragment holds `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). The census is split over this module and `…Acceptance3ControlsHeads`, `…Acceptance3ControlsRest`, to keep each
check within its memory budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance3.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentSpineEta.Controls ContextualDependentPatternFiring.Controls
open ContextualDependentCumulative.Controls ContextualDependentShortClosure.Controls
open ContextualDependentIntersectionGeneral.InPlaceControls

/-- Decided under the last family at budget 16 in eight rounds, with Miller sides after every cut-off round. -/
noncomputable def finalDecided {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  (match (run inPlaceOnly problem 8).readout with
    | .suspended => false
    | _ => true) &&
  (List.range 8).all fun rounds =>
    match run inPlaceOnly problem rounds with
    | .cutoff state => state.remaining.all sidesMiller
    | _ => true

theorem inversion_final : finalDecided inversionStore = true := by decide +kernel
theorem olderInversion_final : finalDecided olderInversionStore = true := by decide +kernel
theorem adjacent_final : finalDecided adjacentStore = true := by decide +kernel
theorem exchange_final : finalDecided exchangeStore = true := by decide +kernel
theorem dependent_final : finalDecided dependentStore = true := by decide +kernel
theorem far_final : finalDecided farStore = true := by decide +kernel
theorem intersection_final : finalDecided intersectionStore = true := by decide +kernel
theorem flexible_final : finalDecided flexibleStore = true := by decide +kernel
theorem prunable_final : finalDecided prunableStore = true := by decide +kernel
theorem matching_final : finalDecided matchingStore = true := by decide +kernel
theorem flexibleBase_final : finalDecided ContextualDependentCensus.Controls.flexibleBaseStore = true := by
  decide +kernel
theorem nested_final : finalDecided ContextualDependentCensus.Controls.nestedStore = true := by decide +kernel
theorem applied_final : finalDecided ContextualDependentCensus.Controls.appliedStore = true := by decide +kernel
end ContextualDependentAcceptance3.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
