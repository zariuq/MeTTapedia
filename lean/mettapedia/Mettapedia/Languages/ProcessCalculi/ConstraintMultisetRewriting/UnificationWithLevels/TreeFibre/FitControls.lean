import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DomainRaisingControls

/-!
# Controls for the solver of fitting groups, in the tree's tower

* **A store of the cross shape, decided** (`raise_inside_fit`, `raise_fit_committed`, `raise_fit_principal`): over
  `X : U0 → U1` and `Y : U1 → U0`, `λ x. X x ≐ λ x. Y x` is in the fragment; the solver raises `X := λ x. Y x` and
  commits.
* **The re-reading at work** (`three_inside`, `three_committed`, `three_principal`): over `X : U0 → U1`,
  `Y : U1 → U0`, `Z : U0 → U1`, the store `λ x. X x ≐ λ x. Y x`, `λ x. X x ≐ λ x. Z x`. After `X := λ x. Y x`
  the second equation is re-read as `λ x. Y x ≐ λ x. Z x`, and `Z := λ x. Y x`; the solver commits.
* **The cross store has the shape but not the grouping** (`cross_fit_read`, `cross_not_fit_inside`,
  `cross_fit_stuck`, `cross_postponed_by_fit`): its equation is read, its two unknowns share an equation, and neither
  fits the other. The solver is stuck on it, and every run of it stops postponed.
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

/-- The solver of fitting groups at the tower's facts. -/
def fitTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  fitSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete

/-! ## A store of the cross shape, decided -/

/-- **It is in the fragment of fitting groups.** -/
theorem raise_inside_fit : InFitFragment raiseStore := inFitFragment_of_B (by decide +kernel)

/-- **The solver commits on it.** -/
theorem raise_fit_committed : (run fitTowerSolver raiseStore 2).readout = .commit := by decide +kernel

theorem raise_fit_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUpDown), (frames setting.levels).Principal raiseStore answer :=
  principal_of_inFitFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete raise_inside_fit

/-! ## The re-reading at work -/

/-- `U0 → U1`, over `X Y`. -/
def familyThird : TypeOver ctxUpDown := formIn ctxUpDown (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `X : U0 → U1, Y : U1 → U0, Z : U0 → U1`. -/
abbrev ctxThree := extend ctxUpDown familyThird

/-- `Π (x : U0). U1`, over `X Y Z`. -/
def threeType : TypeOver ctxThree := formIn ctxThree (.pi (.head U0) (.head U1)) (by decide +kernel)

def etaXThree : TotalTerm ctxThree := termIn ctxThree threeType (.lam (.app (.var 3) (.var 0))) (by decide +kernel)
def etaYThree : TotalTerm ctxThree := termIn ctxThree threeType (.lam (.app (.var 2) (.var 0))) (by decide +kernel)
def etaZThree : TotalTerm ctxThree := termIn ctxThree threeType (.lam (.app (.var 1) (.var 0))) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x`, `λ x. X x ≐ λ x. Z x`. -/
def threeStore : EquationStore (TotalTerm ctxThree) := [(etaXThree, etaYThree), (etaXThree, etaZThree)]

theorem three_inside : InFitFragment threeStore := inFitFragment_of_B (by decide +kernel)

/-- **The solver commits**: `X := λ x. Y x`, the second equation re-read, then `Z := λ x. Y x`. -/
theorem three_committed : (run fitTowerSolver threeStore 3).readout = .commit := by decide +kernel

theorem three_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxThree), (frames setting.levels).Principal threeStore answer :=
  principal_of_inFitFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete three_inside

/-! ## The cross store has the shape but not the grouping -/

/-- **Its equation is read.** -/
theorem cross_fit_read : (readFitData (S := setting) crossEquation).isSome = true := by decide +kernel

/-- **It lies outside the fragment**: its two unknowns share an equation and neither fits the other. -/
theorem cross_not_fit_inside : ¬ InFitFragment crossStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have together := grouped crossEquation List.mem_cons_self v
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans crossLeft_code))
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans crossRight_code))
  have dl : famCode [U0] U0 = famCode [v.pl] v.cl := crossX_declared.symm.trans (hl ▸ v.declared_left)
  have dr : famCode [U1] U1 = famCode [v.pr] v.cr := crossY_declared.symm.trans (hr ▸ v.declared_right)
  obtain ⟨hpl, hcl⟩ := famCode_inj dl
  obtain ⟨hpr, hcr⟩ := famCode_inj dr
  have pl : v.pl = U0 := ((List.cons.inj hpl).1).symm
  have pr : v.pr = U1 := ((List.cons.inj hpr).1).symm
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  rcases comparable v.left v.right different together v.pl v.cl v.pr v.cr v.declared_left v.declared_right
    with fits | fits
  · have codomain := fits.2
    rw [← hcl, ← hcr] at codomain
    exact absurd codomain (by decide)
  · have domain := fits.1
    rw [pl, pr] at domain
    exact absurd domain (by decide)

/-- **The solver is stuck on it.** -/
theorem cross_fit_stuck : isStuck (run fitTowerSolver crossStore 1) = true := by decide +kernel

/-- **Every run of the solver on it stops postponed**, at an exact residual without a principal answer. -/
theorem cross_postponed_by_fit :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run fitTowerSolver crossStore larger = run fitTowerSolver crossStore fuel ∧
      ∃ state, run fitTowerSolver crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames setting.levels) crossStore state.answer state.remaining ∧
        DependentFibre.NoPrincipal setting.levels state.remaining :=
  DependentFibre.cross_run_postponed fitTowerSolver

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
