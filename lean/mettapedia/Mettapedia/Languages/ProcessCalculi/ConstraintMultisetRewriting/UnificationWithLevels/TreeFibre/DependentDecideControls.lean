import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentDecide
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentCodomainsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhasesControls

/-!
# Controls: equations with dependent codes decided as data, in the tree's tower

* **Each one-equation store with a dependent code is decided by computation**: the dep store and `depY` solved
  (`dep_decided`, `depY_decided`); `depHigh` solved by narrowing `Y : U2` to `U1` through the binder
  (`depHigh_decided`); the occurs check and the misfit domain head refute (`depOcc_decided`, `depMis_decided`).
* **Stores**: `X ≐ Π (y : U0). Π (_ : Y). y` and `w ≐ w'` over `X : U1, Y : U2, Z : U1, w : Z, w' : Z`. The three
  solvers in phases do not decide it (`dh_without`): the first equation needs narrowing. With the decision of
  dependent codes added to the base, two phases decide it (`dh_phases`, `dh_principal`): the narrowing first, then
  `w ≐ w'` by the in-place solver.
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

/-- **One equation with a dependent code, decided in the tower.** -/
abbrev towerDepDecide {Θ : Context setting.R} (e : Equation (TotalTerm Θ)) :=
  depDecide (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) ContextualDependentNormalCheckingTower.head_typing_unique
    ContextualDependentExecutableChecking.declared (fun ha hb => LevelGlb.towerGlb_total ha hb) e

theorem dep_decided : decidedKind (towerDepDecide depEquation) = 1 := by decide +kernel
theorem depY_decided : decidedKind (towerDepDecide depYEquation) = 1 := by decide +kernel

/-- **Narrowing through the binder, computed.** -/
theorem depHigh_decided : decidedKind (towerDepDecide depHighEquation) = 1 := by decide +kernel

/-- **The occurs check and the misfit head, computed.** -/
theorem depOcc_decided : decidedKind (towerDepDecide depOccEquation) = 2 := by decide +kernel
theorem depMis_decided : decidedKind (towerDepDecide depMisEquation) = 2 := by decide +kernel

/-- The decision of dependent codes, then the three solvers. -/
def towerDepBase {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  (depBase (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) ContextualDependentNormalCheckingTower.head_typing_unique
    ContextualDependentExecutableChecking.declared (fun ha hb => LevelGlb.towerGlb_total ha hb) problem).orElse
    fun _ => towerBase problem

/-- **Deciding in phases from the decision of dependent codes and the three solvers.** -/
abbrev towerDepAll (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  phases (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerDepBase fuel depth problem

def dhZ : TypeOver ctxDepHigh := formIn ctxDepHigh (.head U1) (by decide +kernel)
abbrev ctxDh1 := extend ctxDepHigh dhZ
def dhW : TypeOver ctxDh1 := formIn ctxDh1 (.var 0) (by decide +kernel)
abbrev ctxDh2 := extend ctxDh1 dhW
def dhW' : TypeOver ctxDh2 := formIn ctxDh2 (.var 1) (by decide +kernel)
/-- `X : U1, Y : U2, Z : U1, w : Z, w' : Z`. -/
abbrev ctxDh := extend ctxDh2 dhW'
def dhUType : TypeOver ctxDh := formIn ctxDh (.head U2) (by decide +kernel)
def dhZType : TypeOver ctxDh := formIn ctxDh (.var 2) (by decide +kernel)

/-- `X ≐ Π (y : U0). Π (_ : Y). y` at `U2`. -/
def dhNarrow : Equation (TotalTerm ctxDh) :=
  (termIn ctxDh dhUType (.var 4) (by decide +kernel),
    termIn ctxDh dhUType (.pi (.head U0) (.pi (.var 4) (.var 1))) (by decide +kernel))

/-- `w ≐ w'` at `Z`. -/
def dhPoint : Equation (TotalTerm ctxDh) :=
  (termIn ctxDh dhZType (.var 1) (by decide +kernel), termIn ctxDh dhZType (.var 0) (by decide +kernel))

def dhStore : EquationStore (TotalTerm ctxDh) := [dhNarrow, dhPoint]

/-- **The three solvers in phases do not decide it**: the first equation needs narrowing. -/
theorem dh_without : decidedKind (towerAll 6 2 dhStore) = 0 := by decide +kernel

/-- **With the decision of dependent codes, two phases decide it.** -/
theorem dh_phases : decidedKind (towerDepAll 6 1 dhStore) = 1 := by decide +kernel

theorem dh_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDh),
    (frames setting.levels).Principal dhStore answer := principal_of_decided dh_phases

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
