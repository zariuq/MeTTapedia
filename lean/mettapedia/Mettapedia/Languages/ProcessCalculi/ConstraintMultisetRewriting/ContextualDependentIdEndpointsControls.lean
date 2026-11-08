import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusPairEtaControls

/-!
# The occurs check at identity endpoints, on concrete stores

Over `A X : U0`, at `U1`:

* **`X ≐ Id U0 X X`** is in the dynamic pattern fragment and has no solution. The pairs solver leaves it
  suspended; the endpoints solver refutes it with a certificate.
* **`X ≐ Σ (Id U0 A X) A`**, an endpoint under a domain, is refuted the same way.
* **Commit control.** `Id U0 X A ≐ Id U0 A A` has no occurrence of a side in the other; the endpoints
  solver does not refute it, and commits `X := A`.
* **Under an abstraction**, at `U0 → U1`: `λ y. X ≐ λ y. Id U0 X y` and `λ y. X ≐ λ y. Id U0 X X` are in the
  fragment and have no solution; the pairs solver leaves them suspended, the endpoints solver refutes them.
* **Regressions** keep their readouts. The decomposition of a projection spine stays unread.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIdEndpoints.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls
open ContextualDependentConstantHeads.Controls ContextualDependentCensusPairEta.Controls

/-- The endpoints solver of the tower controls, as a fuel-indexed family. -/
noncomputable def endpointsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  endpointsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The endpoints solver at budget 16. -/
noncomputable def endpointsOnly : Solver setting.levels := endpointsTower.solver 16

/-- `X ≐ Σ (Id U0 A X) A` at `U1`. -/
def nestedStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 universe1 (.var 0) (by decide +kernel),
    at16 universe1 (.sigma (.id (.head (.sort Tower.zero)) (.var 1) (.var 0)) (.var 2)) (by decide +kernel))]

/-- `Id U0 X A ≐ Id U0 A A` at `U1`. -/
def endpointsCommitStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 universe1 (.id (.head (.sort Tower.zero)) (.var 0) (.var 1)) (by decide +kernel),
    at16 universe1 (.id (.head (.sort Tower.zero)) (.var 1) (.var 1)) (by decide +kernel))]

theorem nested_in_fragment : InFragmentStore nestedStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

/-! ## Runs -/

theorem endpoint_pairs_suspended' : (run pairsOnly endpointStore 8).readout = .suspended := by decide +kernel

/-- **`X ≐ Id U0 X X` is refuted.** -/
theorem endpoint_refuted : (run endpointsOnly endpointStore 8).readout = .refuted := by decide +kernel

theorem endpoint_unsolvable : ¬ (frames setting.levels).Solvable endpointStore :=
  drive_refuted endpointsOnly 8 _ endpoint_refuted

/-- **`X ≐ Id U0 X X` is in the fragment and has no solution.** -/
theorem endpoint_in_fragment_refuted : InFragmentStore endpointStore ∧ ¬ (frames setting.levels).Solvable endpointStore :=
  ⟨endpoint_in_fragment, endpoint_unsolvable⟩

theorem nested_pairs_suspended : (run pairsOnly nestedStore 8).readout = .suspended := by decide +kernel

theorem nested_refuted : (run endpointsOnly nestedStore 8).readout = .refuted := by decide +kernel

theorem nested_unsolvable : ¬ (frames setting.levels).Solvable nestedStore :=
  drive_refuted endpointsOnly 8 _ nested_refuted

/-- **Commit control**: no occurrence of a side in the other; both solvers commit. -/
theorem endpointsCommit_pairs_committed : (run pairsOnly endpointsCommitStore 8).readout = .commit := by
  decide +kernel
theorem endpointsCommit_committed : (run endpointsOnly endpointsCommitStore 8).readout = .commit := by decide +kernel

/-- **Regressions.** -/
theorem projector_endpoints_committed : (run endpointsOnly projectorStore 8).readout = .commit := by decide +kernel
theorem pairEta_endpoints_refuted : (run endpointsOnly pairEtaStore 8).readout = .refuted := by decide +kernel
theorem projections_endpoints_refuted : (run endpointsOnly projectionsStore 8).readout = .refuted := by decide +kernel
theorem twin_endpoints_committed :
    (run endpointsOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel
theorem clashTwin_endpoints_refuted :
    (run endpointsOnly ContextualDependentTwinsUnder.Controls.clashTwinStore 8).readout = .refuted := by decide +kernel

/-! ## Under an abstraction -/

theorem lifted_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))))).isSome := by
  decide +kernel

/-- `U0 → U1`. -/
def lifted : TypeOver twoTypes := formedAt _ lifted_formed

/-- `λ y. X ≐ λ y. Id U0 X y` at `U0 → U1`. -/
def underLocalStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 lifted (.lam (.var 1)) (by decide +kernel),
    at16 lifted (.lam (.id (.head (.sort Tower.zero)) (.var 1) (.var 0))) (by decide +kernel))]

/-- `λ y. X ≐ λ y. Id U0 X X` at `U0 → U1`. -/
def underStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 lifted (.lam (.var 1)) (by decide +kernel),
    at16 lifted (.lam (.id (.head (.sort Tower.zero)) (.var 1) (.var 1))) (by decide +kernel))]

theorem underLocal_in_fragment : InFragmentStore underLocalStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem under_in_fragment : InFragmentStore underStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem underLocal_pairs_suspended : (run pairsOnly underLocalStore 8).readout = .suspended := by decide +kernel
theorem underLocal_refuted : (run endpointsOnly underLocalStore 8).readout = .refuted := by decide +kernel
theorem underLocal_unsolvable : ¬ (frames setting.levels).Solvable underLocalStore :=
  drive_refuted endpointsOnly 8 _ underLocal_refuted

theorem under_pairs_suspended : (run pairsOnly underStore 8).readout = .suspended := by decide +kernel
theorem under_refuted : (run endpointsOnly underStore 8).readout = .refuted := by decide +kernel
theorem under_unsolvable : ¬ (frames setting.levels).Solvable underStore :=
  drive_refuted endpointsOnly 8 _ under_refuted

/-! ## Still unread, at budget 16 -/

/-- `λ g. fst (g X) ≐ λ g. fst (g A)`: the decomposition of a projection spine. -/
theorem projectionSpine_endpoints_suspended :
    (run endpointsOnly projectionSpineStore 8).readout = .suspended := by decide +kernel

end ContextualDependentIdEndpoints.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
