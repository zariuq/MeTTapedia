import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitControls

/-!
# A store just outside the condition "every declaration is a universe family"

Both solvers answer by renaming unknowns, or by `λ x. F x`, inside the same telescope; that answer is typed because
every declaration is a closed family, which no answer changes. Over `A : U0, z : A → A, X : U0 → U0, Y : U0 → U0`,
the declaration `z : A → A` depends on an unknown, so the condition fails although the equation
`λ x. X x ≐ λ x. Y x` has the shape both solvers read.

* `dependent_unread`: the reading of the declarations rejects the telescope;
* `dependent_stuck_families`, `dependent_stuck_fit`: neither solver acts; the store is postponed;
* `dependent_solvable`: the store is solvable (`A := G`, `z := λ y. y`, `X := Y := λ x. x`), so no refutation of
  it would be sound.

The condition is a condition of these answers, not a statement about principality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- `U0`. -/
def universeZero : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U0) (by decide +kernel)

/-- `A : U0`. -/
abbrev ctxTypeA := extend (empty setting.R) universeZero

/-- `A → A`, over `A`. -/
def typeOfZ : TypeOver ctxTypeA := formIn ctxTypeA (.pi (.var 0) (.var 1)) (by decide +kernel)

/-- `A : U0, z : A → A`. -/
abbrev ctxTypeAZ := extend ctxTypeA typeOfZ

/-- `U0 → U0`, over `A z`. -/
def endoAZ : TypeOver ctxTypeAZ := formIn ctxTypeAZ (.pi (.head U0) (.head U0)) (by decide +kernel)

/-- `A : U0, z : A → A, X : U0 → U0`. -/
abbrev ctxTypeAZX := extend ctxTypeAZ endoAZ

/-- `U0 → U0`, over `A z X`. -/
def endoAZX : TypeOver ctxTypeAZX := formIn ctxTypeAZX (.pi (.head U0) (.head U0)) (by decide +kernel)

/-- `A : U0, z : A → A, X : U0 → U0, Y : U0 → U0`. -/
abbrev ctxDependent := extend ctxTypeAZX endoAZX

/-- `Π (x : U0). U0`, over the four. -/
def dependentType : TypeOver ctxDependent := formIn ctxDependent (.pi (.head U0) (.head U0)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x`. -/
def dependentEquation : Equation (TotalTerm ctxDependent) :=
  (termIn ctxDependent dependentType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxDependent dependentType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def dependentStore : EquationStore (TotalTerm ctxDependent) := [dependentEquation]

/-- **The reading of the declarations rejects the telescope**: `z : A → A` is not a closed family. -/
theorem dependent_unread : allFamiliesB (S := setting) ctxDependent = false := by decide +kernel

/-- **The families solver does not act on the store.** -/
theorem dependent_stuck_families : isStuck (run towerSolver dependentStore 1) = true := by decide +kernel

/-- **Nor does the solver of fitting groups.** -/
theorem dependent_stuck_fit : isStuck (run fitTowerSolver dependentStore 1) = true := by decide +kernel

/-- `A := G, z := λ y. y, X := λ x. x, Y := λ x. x`, for the ground type `G`. -/
def dependentSolution : empty setting.R ⟶ ctxDependent :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) universeZero (.head .legacyGround) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxTypeA (termIn ctxTypeA typeOfZ (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxTypeAZ (termIn ctxTypeAZ endoAZ (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxTypeAZX (termIn ctxTypeAZX endoAZX (.lam (.var 0)) (by decide +kernel)).2

/-- **The store is solvable**, so no refutation of it would be sound. -/
theorem dependent_solvable : (frames setting.levels).Solvable dependentStore :=
  solvable_by dependentSolution dependentEquation.1.2 dependentEquation.2.2 (by decide +kernel)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
