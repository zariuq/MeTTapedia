import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusPairEta
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsControls

/-!
# A pair against a neutral term, on concrete stores

* **Commit.** Over `A : U0, H : Σ U0 U0 → U0`, the equation `λ p. (H p, snd p) ≐ λ p. p` at
  `Σ U0 U0 → Σ U0 U0` is in the dynamic pattern fragment and is solved by `H := λ p. fst p`. The heads
  solver leaves it suspended; the pairs solver expands `p` to `(fst p, snd p)`, decomposes, and solves
  `H`, with a principal answer.
* **Refutation.** Over `A X : U0`, `λ p. (X, snd p) ≐ λ p. p` and `λ p. (A, A) ≐ λ p. p` are in the
  fragment and have no solution (`X` would have to be `fst p`). The heads solver leaves them suspended;
  the pairs solver refutes them with a certificate.
* **Regressions** keep their readouts, and the two shapes still unread stay suspended at budget 16.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensusPairEta.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls
open ContextualDependentConstantHeads.Controls

/-- The pairs solver of the tower controls, as a fuel-indexed family. -/
noncomputable def pairsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  pairsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The pairs solver at budget 16. -/
noncomputable def pairsOnly : Solver setting.levels := pairsTower.solver 16

/-! ## A context with a projector -/

theorem projector_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    ContextualDependentInversion.Controls.typeContext
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `Σ U0 U0 → U0`, over `A : U0`. -/
def projectorType : TypeOver ContextualDependentInversion.Controls.typeContext :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 ContextualDependentInversion.Controls.typeContext
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).get
      projector_formed).val

/-- `A : U0, H : Σ U0 U0 → U0`. -/
abbrev withProjector := extend ContextualDependentInversion.Controls.typeContext projectorType

theorem pairsHere_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 withProjector
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
      (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))).isSome := by
  decide +kernel

/-- `Σ U0 U0 → Σ U0 U0`, over `A, H`. -/
def pairsHere : TypeOver withProjector :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withProjector
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
      (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))).get pairsHere_formed).val

/-- A checked term over `A, H` at a formed type. -/
def checkedHere (type : TypeOver withProjector) (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 withProjector.raw code type.code).isSome = true) :
    TotalTerm withProjector :=
  ⟨type, ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 withProjector.raw code type.code).get accepted).down withProjector.formed type.isType⟩⟩

/-- `λ p. (H p, snd p) ≐ λ p. p`. -/
def projectorStore : EquationStore (TotalTerm withProjector) :=
  [(checkedHere pairsHere (.lam (.pair (.app (.var 1) (.var 0)) (.snd (.var 0)))) (by decide +kernel),
    checkedHere pairsHere (.lam (.var 0)) (by decide +kernel))]

theorem projectorStore_length : projectorStore.length = 1 := rfl

def projectorEquation : Equation (TotalTerm withProjector) :=
  projectorStore.head (List.ne_nil_of_length_pos (by rw [projectorStore_length]; decide))

theorem projectorStore_eq : projectorStore = [projectorEquation] := rfl

/-- **The projector store is in the dynamic pattern fragment.** -/
theorem projector_in_fragment : InFragmentStore projectorStore := by
  rw [projectorStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl projectorEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-! ## Runs -/

theorem projector_heads_suspended : (run headsOnly projectorStore 8).readout = .suspended := by decide +kernel

/-- **The pairs solver commits**, with the answer `H := λ p. fst p`. -/
theorem projector_committed : (run pairsOnly projectorStore 8).readout = .commit := by decide +kernel

theorem projector_in_fragment_principal : InFragmentStore projectorStore ∧
    ∃ state finished, run pairsOnly projectorStore 8 = .solved state finished ∧
      (frames setting.levels).Principal projectorStore state.answer := by
  refine ⟨projector_in_fragment, ?_⟩
  have committed := projector_committed
  cases outcome : run pairsOnly projectorStore 8 with
  | solved state finished => exact ⟨state, finished, rfl, state.completed finished⟩
  | refuted _ => rw [outcome] at committed; cases committed
  | stuck _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

theorem pairEta_refuted : (run pairsOnly pairEtaStore 8).readout = .refuted := by decide +kernel

theorem pairEta_unsolvable : ¬ (frames setting.levels).Solvable pairEtaStore :=
  drive_refuted pairsOnly 8 _ pairEta_refuted

theorem pairConstant_refuted : (run pairsOnly pairConstantStore 8).readout = .refuted := by decide +kernel

theorem pairConstant_unsolvable : ¬ (frames setting.levels).Solvable pairConstantStore :=
  drive_refuted pairsOnly 8 _ pairConstant_refuted

/-- **Regressions.** -/
theorem projections_pairs_refuted : (run pairsOnly projectionsStore 8).readout = .refuted := by decide +kernel
theorem sameHeads_pairs_committed : (run pairsOnly sameHeadsStore 8).readout = .commit := by decide +kernel
theorem twin_pairs_committed :
    (run pairsOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel

/-! ## Still unread, at budget 16 -/

theorem projectionSpine_pairs_suspended : (run pairsOnly projectionSpineStore 8).readout = .suspended := by
  decide +kernel
theorem endpoint_pairs_suspended : (run pairsOnly endpointStore 8).readout = .suspended := by decide +kernel

end ContextualDependentCensusPairEta.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
