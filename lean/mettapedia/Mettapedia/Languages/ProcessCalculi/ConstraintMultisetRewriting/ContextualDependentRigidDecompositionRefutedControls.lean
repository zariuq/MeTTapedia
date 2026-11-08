import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionRuleControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionControls

/-!
# Rigid–rigid decomposition, solved and refuted, under a wider telescope

The metavariable is `F : (A : U0) (c : A → A) (x : A) → A`; the equation's telescope is
`A : U0, c : A → A, x : A, y : A`, one local wider than `F`'s arguments. The annotation and both
sides are formed and checked by the executable type former and checker, not written by hand.

* `λ A c x y. c (F A c x) ≐ λ A c x y. c y` is decomposed at `c` into `F A c x ≐ y`, and the pattern
  rule refutes that: `y` is not among `F`'s arguments. The decomposition solver refutes the store
  with a certificate. The full solver alone only suspends it.
* `λ A c x y. c (F A c x) ≐ λ A c x y. c x` is decomposed into `F A c x ≐ x`, which is solved; the
  run commits with a principal answer.
* The non-pattern `F x x ≐ Id T y x` stays suspended under the new rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidDecomposition.RefutedControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver.Controls ContextualDependentPatternSolver.OccursControls
open ContextualDependentRigidDecomposition.RuleControls

/-- The context `F : (A : U0) (c : A → A) (x : A) → A`. -/
abbrev metaContext := extend (empty Tower.rules) selfWhole

/-- `(A : U0) (c : A → A) (x y : A) → A` over `F`. -/
def annotationCode : Tower.Tm 1 :=
  .pi (.head (.sort Tower.zero)) (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (.pi (.var 2) (.var 3))))

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

/-- `λ A c x y. c (F A c x)`. -/
def appliedCode : Tower.Tm 1 :=
  .lam (.lam (.lam (.lam (.app (.var 2) (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1))))))

/-- `λ A c x y. c y`. -/
def outsideCode : Tower.Tm 1 := .lam (.lam (.lam (.lam (.app (.var 2) (.var 0)))))

/-- `λ A c x y. c x`. -/
def insideCode : Tower.Tm 1 := .lam (.lam (.lam (.lam (.app (.var 2) (.var 1)))))

theorem applied_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 metaContext.raw appliedCode annotation.code).isSome = true := by
  decide +kernel

theorem outside_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 metaContext.raw outsideCode annotation.code).isSome = true := by
  decide +kernel

theorem inside_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 metaContext.raw insideCode annotation.code).isSome = true := by
  decide +kernel

/-- `λ A c x y. c (F A c x) ≐ λ A c x y. c y`. -/
def refutedStore : EquationStore (TotalTerm metaContext) :=
  [(⟨annotation, checked appliedCode applied_checked⟩, ⟨annotation, checked outsideCode outside_checked⟩)]

/-- `λ A c x y. c (F A c x) ≐ λ A c x y. c x`. -/
def solvedStore : EquationStore (TotalTerm metaContext) :=
  [(⟨annotation, checked appliedCode applied_checked⟩, ⟨annotation, checked insideCode inside_checked⟩)]

/-- **Decomposition, then a certified refutation.** -/
theorem refuted_by_decomposition : (run decomposeOnly refutedStore 1).readout = .refuted := by decide +kernel

theorem refuted_store_unsolvable : ¬ (frames setting.levels).Solvable refutedStore :=
  drive_refuted decomposeOnly 1 _ refuted_by_decomposition

/-- The full solver alone only suspends it. -/
theorem refuted_full_suspended : (run full refutedStore 4).readout = .suspended := by decide +kernel

/-- **Decomposition, then a principal answer.** -/
theorem solved_by_decomposition : (run decomposeOnly solvedStore 2).readout = .commit := by decide +kernel

theorem solved_principal :
    ∃ state finished, run decomposeOnly solvedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal solvedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit solved_by_decomposition
  exact ⟨state, finished, solved, drive_solved_principal decomposeOnly solved⟩

/-! ## A non-pattern stays residual under the new rules -/

/-- `F x x ≐ Id T y x` is neither a pattern nor decomposable: the decomposition solver, which runs
the distinct-locals rule and the full solver after decomposition, still only suspends it. -/
theorem repeated_decompose_suspended :
    (run decomposeOnly ContextualDependentPatternSolver.Controls.repeatedStore 4).readout = .suspended := by
  decide +kernel

theorem repeated_rigid_suspended :
    (run ContextualDependentRigidDecomposition.Controls.rigidOnly
      ContextualDependentPatternSolver.Controls.repeatedStore 4).readout = .suspended := by
  decide +kernel

end ContextualDependentRigidDecomposition.RefutedControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
