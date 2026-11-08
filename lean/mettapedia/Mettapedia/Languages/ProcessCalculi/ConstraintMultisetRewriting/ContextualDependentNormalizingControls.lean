import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionControls

/-!
# The normalizing solver on a store with a redex in its annotation

Over `T : U0, F : (a b : T) → U0`, the crossed pattern `λ x y. F y x ≐ λ x y. Id T x y` is solved
by the pattern rule. Its annotation `(x y : T) → U0` is replaced here by the β-redex
`(λ _. (x y : T) → U0) T`, which is a typed-equal annotation of the same equation. Such redexes
are what instantiation leaves in annotations.

* The rigid solver only suspends the expanded store: spine discovery reads Π binders from the
  annotation's syntax, so the pattern, prune and exchange rules never see the pattern.
* The normalizing solver normalizes the annotation first and commits with a principal answer.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizing.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver.Controls ContextualDependentRigidDecomposition.Controls

/-- The normalizing solver in the cumulative tower, with the rigid solver's parameters. -/
def normalizingOnly : Solver setting.levels :=
  normalizingSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    (tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- The context `T : U0, F : (a b : T) → U0`. -/
abbrev outer := extend types outerWhole

/-- `(λ _. A) a`, a one-step β-expansion of `A`. -/
def redex {n : Nat} (A a : Tower.Tm n) : Tower.Tm n := .app (.lam (Presentation.rename wk A)) a

theorem redex_reduces {n : Nat} (A a : Tower.Tm n) : Reduces setting.R (redex A a) A := by
  have contracted : StepCore setting.R.computation setting.R.headEq (redex A a) (inst0 a (Presentation.rename wk A)) :=
    .betaPi _ _
  rw [inst0_rename_wk] at contracted
  exact Relation.ReflTransGen.single contracted

/-- The crossed pattern equation. -/
def crossedEquation : Equation (TotalTerm outer) :=
  crossedStore.head (List.ne_nil_of_length_pos (by rw [crossed_store_length]; decide))

/-- Form an annotation with the executable type former. -/
def formed (code : Tower.Tm outer.arity) :=
  ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 outer code

theorem leftFormed : (formed (redex crossedEquation.1.1.code (.var 1))).isSome := by decide +kernel

theorem rightFormed : (formed (redex crossedEquation.2.1.code (.var 1))).isSome := by decide +kernel

/-- The left annotation, expanded. -/
def leftType : TypeOver outer := ((formed (redex crossedEquation.1.1.code (.var 1))).get leftFormed).val

/-- The right annotation, expanded. -/
def rightType : TypeOver outer := ((formed (redex crossedEquation.2.1.code (.var 1))).get rightFormed).val

theorem expanded_typeEq {original expanded : TypeOver outer} (code : expanded.code = redex original.code (.var 1)) :
    TypeEq setting.R outer.raw original.code expanded.code := by
  have path : Reduces setting.R expanded.code original.code := by
    rw [code]
    exact redex_reduces _ _
  exact (Reduces.typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads outer.formed path
    expanded.isType).symm

/-- **The expanded equation**: the same sides at the β-expanded annotations. -/
def expandedEquation : Equation (TotalTerm outer) :=
  (⟨leftType, crossedEquation.1.2.convertType leftType
      (expanded_typeEq ((formed (redex crossedEquation.1.1.code (.var 1))).get leftFormed).property)⟩,
    ⟨rightType, crossedEquation.2.2.convertType rightType
      (expanded_typeEq ((formed (redex crossedEquation.2.1.code (.var 1))).get rightFormed).property)⟩)

def expandedStore : EquationStore (TotalTerm outer) := [expandedEquation]

/-- The annotation really carries a redex. -/
theorem expanded_annotation_redex :
    expandedEquation.1.1.code = redex crossedEquation.1.1.code (.var 1) :=
  ((formed (redex crossedEquation.1.1.code (.var 1))).get leftFormed).property

/-- **The rigid solver only suspends the expanded store.** -/
theorem expanded_rigid_suspended : (run rigidOnly expandedStore 4).readout = .suspended := by decide +kernel

/-- **The normalizing solver commits on it.** -/
theorem expanded_normalizing_solved : (run normalizingOnly expandedStore 2).readout = .commit := by decide +kernel

theorem expanded_normalizing_principal :
    ∃ state finished, run normalizingOnly expandedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal expandedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit expanded_normalizing_solved
  exact ⟨state, finished, solved, drive_solved_principal normalizingOnly solved⟩

/-- The original crossed store is solved by both solvers. -/
theorem crossed_normalizing_solved : (run normalizingOnly crossedStore 2).readout = .commit := by decide +kernel

end ContextualDependentNormalizing.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
