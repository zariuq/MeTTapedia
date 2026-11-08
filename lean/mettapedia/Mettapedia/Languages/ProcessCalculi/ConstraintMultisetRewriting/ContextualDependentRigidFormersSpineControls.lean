import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersSpineRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaExpansionControls

/-!
# Neutral spines with two arguments on concrete stores

The metavariable is `F : (A : U0) (g : A → A → A) (x y : A) → A`; the equations sit at that type,
read under the locals `A g x y`.

* **A clash.** `λ A g x y. g x y ≐ λ A g x y. g y x` decomposes into `x ≐ y` and `y ≐ x`, distinct
  locals: refuted with a certificate.
* **A solution.** `λ A g x y. g x y ≐ λ A g x y. g (F A g x y) y` decomposes into `x ≐ F A g x y` and
  `y ≐ y`; the pattern rule solves `F := λ A g x y. x` at once, and the spine solver commits with a
  principal answer.
* R84's one-argument decomposition and the distinct-locals rule read neither store.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers.SpineControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentFragment.Controls

/-- The spine solver of the tower controls, as a fuel-indexed family. -/
abbrev spineTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  spineFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The spine solver at budget 16. -/
def spineOnly : Solver setting.levels := spineTower.solver 16

/-- `(A : U0) (g : A → A → A) (x y : A) → A`. -/
def binaryCode {n : Nat} : Tower.Tm n :=
  .pi (.head (.sort Tower.zero)) (.pi (.pi (.var 0) (.pi (.var 1) (.var 2))) (.pi (.var 1) (.pi (.var 2) (.var 3))))

theorem binary_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 (empty Tower.rules)
    binaryCode).isSome := by decide +kernel

/-- `F`'s type. -/
def binaryWhole : TypeOver (empty Tower.rules) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 (empty Tower.rules) binaryCode).get binary_formed).val

/-- The context `F : (A : U0) (g : A → A → A) (x y : A) → A`. -/
abbrev binaryContext := extend (empty Tower.rules) binaryWhole

theorem annotation_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 binaryContext binaryCode).isSome := by
  decide +kernel

/-- The equations' type, over `F`. -/
def annotation : TypeOver binaryContext :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 binaryContext binaryCode).get annotation_formed).val

/-- A term of the annotation, checked by the executable checker. -/
def checked (code : Tower.Tm 1)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 binaryContext.raw code annotation.code).isSome = true) :
    Term binaryContext annotation :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 binaryContext.raw code annotation.code).get accepted).down binaryContext.formed annotation.isType⟩

/-- `λ A g x y. g x y`. -/
def straightCode : Tower.Tm 1 := .lam (.lam (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))))

/-- `λ A g x y. g y x`. -/
def crossedCode : Tower.Tm 1 := .lam (.lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))))

/-- `λ A g x y. g (F A g x y) y`. -/
def metaCode : Tower.Tm 1 :=
  .lam (.lam (.lam (.lam (.app (.app (.var 2)
    (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0))) (.var 0)))))

theorem straight_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 binaryContext.raw straightCode annotation.code).isSome = true := by
  decide +kernel

theorem crossed_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 binaryContext.raw crossedCode annotation.code).isSome = true := by
  decide +kernel

theorem meta_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 binaryContext.raw metaCode annotation.code).isSome = true := by
  decide +kernel

/-- `λ A g x y. g x y ≐ λ A g x y. g y x`. -/
def crossedSpineStore : EquationStore (TotalTerm binaryContext) :=
  [(⟨annotation, checked straightCode straight_checked⟩, ⟨annotation, checked crossedCode crossed_checked⟩)]

/-- `λ A g x y. g x y ≐ λ A g x y. g (F A g x y) y`. -/
def metaSpineStore : EquationStore (TotalTerm binaryContext) :=
  [(⟨annotation, checked straightCode straight_checked⟩, ⟨annotation, checked metaCode meta_checked⟩)]

/-- **The spine solver refutes the crossed spines**, with a certificate. -/
theorem crossed_spine_refuted : (run spineOnly crossedSpineStore 2).readout = .refuted := by decide +kernel

theorem crossed_spine_unsolvable : ¬ (frames setting.levels).Solvable crossedSpineStore :=
  drive_refuted spineOnly 2 _ crossed_spine_refuted

/-- **The spine solver commits on the pattern store**, with a principal answer. -/
theorem meta_spine_solved : (run spineOnly metaSpineStore 3).readout = .commit := by decide +kernel

theorem meta_spine_principal :
    ∃ state finished, run spineOnly metaSpineStore 3 = .solved state finished ∧
      (frames setting.levels).Principal metaSpineStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit meta_spine_solved
  exact ⟨state, finished, solved, drive_solved_principal spineOnly solved⟩

/-- R84's one-argument decomposition reads neither store. -/
theorem one_argument_none : (ContextualDependentRigidDecomposition.decomposeSearch (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal 16 crossedSpineStore).isNone = true ∧
    (ContextualDependentRigidDecomposition.decomposeSearch (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal 16 metaSpineStore).isNone = true := by
  constructor <;> decide +kernel

/-- Nor does the distinct-locals rule before the decomposition. -/
theorem locals_before_none : (ContextualDependentRigidDecomposition.localsRule (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) 16 crossedSpineStore).isNone = true := by
  decide +kernel

end ContextualDependentRigidFormers.SpineControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
