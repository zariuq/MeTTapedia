import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjectionsRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsControls

/-!
# Projection spines on concrete stores

Over `A X : U0`, at `(U0 → Σ U0 U0) → U0`:

* **`λ g. fst (g X) ≐ λ g. fst (g A)`** is in the dynamic pattern fragment and is solved by `X := A`. The
  endpoints solver leaves it suspended; the projections solver decomposes it into `λ g. X ≐ λ g. A` and
  solves it, with a principal answer.
* **`λ g. snd (g X) ≐ λ g. snd (g A)`** is decided the same way.
* **`λ g. fst (g (Π A A)) ≐ λ g. fst (g (Σ A A))`** is in the fragment and has no solution: its piece is a
  clash of formers under the abstraction. The projections solver refutes it.
* **Regressions** keep their readouts.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeadsProjections.Controls

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
open ContextualDependentIdEndpoints.Controls

/-- The projections solver of the tower controls, as a fuel-indexed family. -/
noncomputable def projectionsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  projectionsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The projections solver at budget 16. -/
noncomputable def projectionsOnly : Solver setting.levels := projectionsTower.solver 16

/-- `λ g. snd (g X) ≐ λ g. snd (g A)`. -/
def secondSpineStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 generator (.lam (.snd (.app (.var 0) (.var 1)))) (by decide +kernel),
    at16 generator (.lam (.snd (.app (.var 0) (.var 2)))) (by decide +kernel))]

/-- `λ g. fst (g (Π A A)) ≐ λ g. fst (g (Σ A A))`. -/
def clashSpineStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 generator (.lam (.fst (.app (.var 0) (.pi (.var 2) (.var 3))))) (by decide +kernel),
    at16 generator (.lam (.fst (.app (.var 0) (.sigma (.var 2) (.var 3))))) (by decide +kernel))]

theorem secondSpine_in_fragment : InFragmentStore secondSpineStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem clashSpine_in_fragment : InFragmentStore clashSpineStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

/-! ## Runs -/

theorem projectionSpine_endpoints_suspended' :
    (run endpointsOnly projectionSpineStore 8).readout = .suspended := by decide +kernel

/-- **`λ g. fst (g X) ≐ λ g. fst (g A)` commits.** -/
theorem projectionSpine_committed : (run projectionsOnly projectionSpineStore 8).readout = .commit := by
  decide +kernel

/-- **It is decided with a principal answer.** -/
theorem projectionSpine_in_fragment_principal : InFragmentStore projectionSpineStore ∧
    ∃ state finished, run projectionsOnly projectionSpineStore 8 = .solved state finished ∧
      (frames setting.levels).Principal projectionSpineStore state.answer := by
  refine ⟨projectionSpine_in_fragment, ?_⟩
  have committed := projectionSpine_committed
  cases outcome : run projectionsOnly projectionSpineStore 8 with
  | solved state finished => exact ⟨state, finished, rfl, state.completed finished⟩
  | refuted _ => rw [outcome] at committed; cases committed
  | stuck _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

theorem secondSpine_endpoints_suspended : (run endpointsOnly secondSpineStore 8).readout = .suspended := by
  decide +kernel
theorem secondSpine_committed : (run projectionsOnly secondSpineStore 8).readout = .commit := by decide +kernel

theorem clashSpine_endpoints_suspended : (run endpointsOnly clashSpineStore 8).readout = .suspended := by
  decide +kernel
theorem clashSpine_refuted : (run projectionsOnly clashSpineStore 8).readout = .refuted := by decide +kernel
theorem clashSpine_unsolvable : ¬ (frames setting.levels).Solvable clashSpineStore :=
  drive_refuted projectionsOnly 8 _ clashSpine_refuted

/-- **Regressions.** -/
theorem endpoint_projections_refuted : (run projectionsOnly endpointStore 8).readout = .refuted := by decide +kernel
theorem under_projections_refuted :
    (run projectionsOnly ContextualDependentIdEndpoints.Controls.underStore 8).readout = .refuted := by decide +kernel
theorem projector_projections_committed : (run projectionsOnly projectorStore 8).readout = .commit := by
  decide +kernel
theorem projections_projections_refuted : (run projectionsOnly projectionsStore 8).readout = .refuted := by
  decide +kernel
theorem twin_projections_committed :
    (run projectionsOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel
theorem sameHeads_projections_committed : (run projectionsOnly sameHeadsStore 8).readout = .commit := by
  decide +kernel

end ContextualDependentConstantHeadsProjections.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
