import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaExpansion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionRefutedControls

/-!
# η-expansion on concrete stores

The metavariable is `F : (A : U0) (f : A → A) (x : A) → A`.

* **η-expansion solves.** `λ A f. f ≐ λ A f x. F A f x`: read from the left, the reading compares the
  local `f` with `λ x. F A f x`, which the pattern, prune, exchange, distinct-locals and
  local-decomposition rules do not read at budget 16. Read from the right, the neutral `f` is
  η-expanded: `F A f x ≐ f x`, a Miller pattern, solved by `F := λ A f x. f x`. The η solver commits
  with a principal answer.
* **It changes nothing where the depths agree.** On R84's store `λ A c x y. c (F A c x) ≐ λ A c x y. c x`
  the η solver commits as before.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaExpansion.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls ContextualDependentPatternSolver.OccursControls
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentFragment.Controls
open ContextualDependentGeneralPattern

/-- The η solver of the tower controls, as a fuel-indexed family. -/
abbrev etaTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  etaFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The η solver at budget 16. -/
def etaOnly : Solver setting.levels := etaTower.solver 16

/-- The context `F : (A : U0) (f : A → A) (x : A) → A`. -/
abbrev metaContext := extend (empty Tower.rules) selfWhole

/-- `(A : U0) (f : A → A) → A → A` over `F`. -/
def annotationCode : Tower.Tm 1 := .pi (.head (.sort Tower.zero)) (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (.var 2)))

theorem annotation_formed :
    (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 metaContext annotationCode).isSome = true := by decide +kernel

/-- The annotation, formed by the executable type former. -/
def annotation : TypeOver metaContext :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 metaContext annotationCode).get annotation_formed).val

/-- A term of the annotation, checked by the executable checker. -/
def checked (code : Tower.Tm 1)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 metaContext.raw code annotation.code).isSome = true) :
    Term metaContext annotation :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 metaContext.raw code annotation.code).get accepted).down metaContext.formed annotation.isType⟩

/-- `λ A f. f`. -/
def neutralCode : Tower.Tm 1 := .lam (.lam (.var 0))

/-- `λ A f x. F A f x`. -/
def patternCode : Tower.Tm 1 := .lam (.lam (.lam (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))

theorem neutral_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 metaContext.raw neutralCode annotation.code).isSome = true := by
  decide +kernel

theorem pattern_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 metaContext.raw patternCode annotation.code).isSome = true := by
  decide +kernel

/-- `λ A f. f ≐ λ A f x. F A f x`. -/
def etaStore : EquationStore (TotalTerm metaContext) :=
  [(⟨annotation, checked neutralCode neutral_checked⟩, ⟨annotation, checked patternCode pattern_checked⟩)]

/-- **The η solver commits on it.** -/
theorem eta_solved : (run etaOnly etaStore 2).readout = .commit := by decide +kernel

theorem eta_principal :
    ∃ state finished, run etaOnly etaStore 2 = .solved state finished ∧
      (frames setting.levels).Principal etaStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit eta_solved
  exact ⟨state, finished, solved, drive_solved_principal etaOnly solved⟩

/-- **Where the depths agree nothing changes**: R84's decomposition store still commits. -/
theorem agreeing_depths_solved :
    (run etaOnly ContextualDependentRigidDecomposition.RefutedControls.solvedStore 2).readout = .commit := by
  decide +kernel

/-- And R84's refuted store is still refuted. -/
theorem agreeing_depths_refuted :
    (run etaOnly ContextualDependentRigidDecomposition.RefutedControls.refutedStore 2).readout = .refuted := by
  decide +kernel

/-! ## Which rules read the store at budget 16 -/

/-- **The η rule fires on it.** -/
theorem eta_rule_fires : (etaSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16 etaStore).isSome = true := by decide +kernel

/-- The pattern, prune and exchange rules read nothing. -/
theorem eta_first_rule_none : (firstRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique 16 etaStore).isNone = true := by
  decide +kernel

/-- The distinct-locals rule reads nothing. -/
theorem eta_locals_none : (ContextualDependentRigidDecomposition.localsRule (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) 16 etaStore).isNone = true := by decide +kernel

/-- The local-application decomposition reads nothing. -/
theorem eta_decompose_none : (ContextualDependentRigidDecomposition.decomposeSearch (S := setting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal 16 etaStore).isNone = true := by decide +kernel

end ContextualDependentEtaExpansion.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
