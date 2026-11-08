import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTwinsUnderControls

/-!
# Head clashes on concrete stores, and the shapes still unread

Over `A X : U0`. Each of the first four stores is in the dynamic pattern fragment and has no solution;
the ranked abstraction solver leaves it suspended, and the heads solver refutes it with a certificate:

* `λ p. fst p ≐ λ p. snd p` at `Σ U0 U0 → U0`: two projections of one local;
* `λ p. fst p ≐ λ p. Π A A` at `Σ U0 U0 → U0`: a neutral type against a Π type;
* `λ p. fst p ≐ λ p. refl A` at `Σ (Id U0 A A) U0 → Id U0 A A`: reflexivity against a projection;
* `λ Y p y. fst p ≐ λ Y p y. y` at `(Y : U0) → Σ Y Y → Y → Y`: a projection against a local, at a local type.

**Commit control.** `λ p. Π (fst p) A ≐ λ p. Π (fst p) X` has one skeleton on both sides of each
piece; the heads solver does not refute it, and commits `X := A`, as the ranked abstraction solver does.

**Shapes still unread**, suspended by the heads solver at budget 16 and eight rounds (a run at one
budget, not a proof for every budget):

* `λ g. fst (g X) ≐ λ g. fst (g A)` at `(U0 → Σ U0 U0) → U0`, solvable by `X := A`: the decomposition of
  a projection spine;
* `λ p. (X, snd p) ≐ λ p. p` and `λ p. (A, A) ≐ λ p. p` at `Σ U0 U0 → Σ U0 U0`, unsolvable: a pair
  against a neutral term (η for Σ);
* `X ≐ Id U0 X X` at `U1`, unsolvable: an occurrence at an identity endpoint.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeads.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls

/-- The heads solver of the tower controls, as a fuel-indexed family. -/
noncomputable def headsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  headsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The heads solver at budget 16. -/
noncomputable def headsOnly : Solver setting.levels := headsTower.solver 16

/-- A checked term over `A X` at a formed type. -/
abbrev at16 (type : TypeOver twoTypes) (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes.raw code type.code).isSome = true) : TotalTerm twoTypes :=
  ⟨type, checkedAt type code accepted⟩

/-! ## The annotations -/

theorem projection_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `Σ U0 U0 → U0`. -/
def projection : TypeOver twoTypes := formedAt _ projection_formed

theorem paths_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.sigma (.id (.head (.sort Tower.zero)) (.var 1) (.var 1)) (.head (.sort Tower.zero)))
      (.id (.head (.sort Tower.zero)) (.var 2) (.var 2)))).isSome := by
  decide +kernel

/-- `Σ (Id U0 A A) U0 → Id U0 A A`. -/
def paths : TypeOver twoTypes := formedAt _ paths_formed

theorem local_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.head (.sort Tower.zero)) (.pi (.sigma (.var 0) (.var 1)) (.pi (.var 1) (.var 2))))).isSome := by
  decide +kernel

/-- `(Y : U0) → Σ Y Y → Y → Y`. -/
def atLocal : TypeOver twoTypes := formedAt _ local_formed

theorem pairs_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
      (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))).isSome := by
  decide +kernel

/-- `Σ U0 U0 → Σ U0 U0`. -/
def pairs : TypeOver twoTypes := formedAt _ pairs_formed

theorem generator_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.head (.sort Tower.zero)) (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
      (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `(U0 → Σ U0 U0) → U0`. -/
def generator : TypeOver twoTypes := formedAt _ generator_formed

theorem universe1_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.head (.sort (.succ Tower.zero)))).isSome := by
  decide +kernel

/-- `U1`. -/
def universe1 : TypeOver twoTypes := formedAt _ universe1_formed

/-! ## The clash stores -/

/-- `λ p. fst p ≐ λ p. snd p`. -/
def projectionsStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 projection (.lam (.fst (.var 0))) (by decide +kernel), at16 projection (.lam (.snd (.var 0))) (by decide +kernel))]

/-- `λ p. fst p ≐ λ p. Π A A`. -/
def formerStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 projection (.lam (.fst (.var 0))) (by decide +kernel),
    at16 projection (.lam (.pi (.var 2) (.var 3))) (by decide +kernel))]

/-- `λ p. fst p ≐ λ p. refl A`. -/
def reflStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 paths (.lam (.fst (.var 0))) (by decide +kernel), at16 paths (.lam (.refl (.var 2))) (by decide +kernel))]

/-- `λ Y p y. fst p ≐ λ Y p y. y`. -/
def localStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 atLocal (.lam (.lam (.lam (.fst (.var 1))))) (by decide +kernel),
    at16 atLocal (.lam (.lam (.lam (.var 0)))) (by decide +kernel))]

/-- `λ p. Π (fst p) A ≐ λ p. Π (fst p) X`. -/
def sameHeadsStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 projection (.lam (.pi (.fst (.var 0)) (.var 3))) (by decide +kernel),
    at16 projection (.lam (.pi (.fst (.var 0)) (.var 2))) (by decide +kernel))]

/-! ## The stores still unread -/

/-- `λ g. fst (g X) ≐ λ g. fst (g A)`. -/
def projectionSpineStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 generator (.lam (.fst (.app (.var 0) (.var 1)))) (by decide +kernel),
    at16 generator (.lam (.fst (.app (.var 0) (.var 2)))) (by decide +kernel))]

/-- `λ p. (X, snd p) ≐ λ p. p`. -/
def pairEtaStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 pairs (.lam (.pair (.var 1) (.snd (.var 0)))) (by decide +kernel), at16 pairs (.lam (.var 0)) (by decide +kernel))]

/-- `λ p. (A, A) ≐ λ p. p`. -/
def pairConstantStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 pairs (.lam (.pair (.var 2) (.var 2))) (by decide +kernel), at16 pairs (.lam (.var 0)) (by decide +kernel))]

/-- `X ≐ Id U0 X X` at `U1`. -/
def endpointStore : EquationStore (TotalTerm twoTypes) :=
  [(at16 universe1 (.var 0) (by decide +kernel),
    at16 universe1 (.id (.head (.sort Tower.zero)) (.var 0) (.var 0)) (by decide +kernel))]

/-! ## Membership in the fragment -/

/-- Membership of a one-equation store over `A X`, read by the normalizer. -/
theorem single_in_fragment (type : TypeOver twoTypes) (left right : Term twoTypes type)
    (normal : ExecutableReduction.step setting.R (fun _ => none) type.code = none)
    (depth : ContextualDependentPatternSolver.lamDepth left.code ≤ piCount type.code)
    (leftSide : ∀ code, ContextualDependentExecutableJoin.Star (R := setting.R)
        (openCode (ContextualDependentPatternSolver.lamDepth left.code) left.code) code →
      ContextualDependentExecutableJoin.Normal setting.R code →
      InFragmentCode twoTypes.raw (ContextualDependentPatternSolver.lamDepth left.code) code)
    (rightSide : ∀ code, ContextualDependentExecutableJoin.Star (R := setting.R)
        (openCode (ContextualDependentPatternSolver.lamDepth left.code) right.code) code →
      ContextualDependentExecutableJoin.Normal setting.R code →
      InFragmentCode twoTypes.raw (ContextualDependentPatternSolver.lamDepth left.code) code) :
    InFragmentStore [((⟨type, left⟩ : TotalTerm twoTypes), (⟨type, right⟩ : TotalTerm twoTypes))] := by
  intro equation member
  rw [List.mem_singleton.mp member]
  exact ⟨IsType.refl type.isType, (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr normal, depth,
    leftSide, rightSide⟩

theorem projections_in_fragment : InFragmentStore projectionsStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem former_in_fragment : InFragmentStore formerStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem refl_in_fragment : InFragmentStore reflStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem local_in_fragment : InFragmentStore localStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem projectionSpine_in_fragment : InFragmentStore projectionSpineStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem pairEta_in_fragment : InFragmentStore pairEtaStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem endpoint_in_fragment : InFragmentStore endpointStore :=
  single_in_fragment _ _ _ (by decide +kernel) (by decide +kernel)
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

/-! ## Runs -/

theorem projections_any_suspended : (run anyOnly projectionsStore 8).readout = .suspended := by decide +kernel
theorem projections_refuted : (run headsOnly projectionsStore 8).readout = .refuted := by decide +kernel
theorem projections_unsolvable : ¬ (frames setting.levels).Solvable projectionsStore :=
  drive_refuted headsOnly 8 _ projections_refuted

theorem former_any_suspended : (run anyOnly formerStore 8).readout = .suspended := by decide +kernel
theorem former_refuted : (run headsOnly formerStore 8).readout = .refuted := by decide +kernel
theorem former_unsolvable : ¬ (frames setting.levels).Solvable formerStore :=
  drive_refuted headsOnly 8 _ former_refuted

theorem refl_any_suspended : (run anyOnly reflStore 8).readout = .suspended := by decide +kernel
theorem refl_refuted : (run headsOnly reflStore 8).readout = .refuted := by decide +kernel
theorem refl_unsolvable : ¬ (frames setting.levels).Solvable reflStore :=
  drive_refuted headsOnly 8 _ refl_refuted

theorem local_any_suspended : (run anyOnly localStore 8).readout = .suspended := by decide +kernel
theorem local_refuted : (run headsOnly localStore 8).readout = .refuted := by decide +kernel
theorem local_unsolvable : ¬ (frames setting.levels).Solvable localStore :=
  drive_refuted headsOnly 8 _ local_refuted

/-- **Commit control**: equal skeletons are not refuted; both solvers commit. -/
theorem sameHeads_any_committed : (run anyOnly sameHeadsStore 8).readout = .commit := by decide +kernel
theorem sameHeads_committed : (run headsOnly sameHeadsStore 8).readout = .commit := by decide +kernel

/-- **Regressions**: the twin controls keep their readouts. -/
theorem twin_heads_committed :
    (run headsOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel
theorem clashTwin_heads_refuted :
    (run headsOnly ContextualDependentTwinsUnder.Controls.clashTwinStore 8).readout = .refuted := by decide +kernel

/-! ## Still unread, at budget 16 -/

theorem projectionSpine_suspended : (run headsOnly projectionSpineStore 8).readout = .suspended := by decide +kernel
theorem pairEta_suspended : (run headsOnly pairEtaStore 8).readout = .suspended := by decide +kernel
theorem pairConstant_suspended : (run headsOnly pairConstantStore 8).readout = .suspended := by decide +kernel
theorem endpoint_suspended : (run headsOnly endpointStore 8).readout = .suspended := by decide +kernel

end ContextualDependentConstantHeads.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
