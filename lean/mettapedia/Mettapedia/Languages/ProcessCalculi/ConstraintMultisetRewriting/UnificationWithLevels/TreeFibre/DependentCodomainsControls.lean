import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentCodomains
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsControls

/-!
# Controls: codomains that use their argument, in the tree's tower

* **The dep store** `X ≐ Π (y : U0). y` over `X : U1`: the right side fits `X`'s universe, so `X := Π (y : U0). y` is
  principal by the general rule (`dep_fits`, `dep_fit_principal`); before, this one store had a proof by hand.
* **An unknown inside a codomain that uses the argument**: `X ≐ Π (y : U0). Π (_ : Y). y` over `X : U1, Y : U0`. Outside
  the pieces of arrow codes and outside the earlier union (`depY_outside`, `depY_piece`); principal by the rule
  (`depY_fit_principal`).
* **Where narrowing is needed**: the same right side over `X : U1, Y : U2`, at `U2`, outside every piece. The forcing
  through the binder narrows `Y` to `U1` (`DependentNarrowing`): the store is settled (`depHigh_settles`), solvable
  (`depHigh_solvable`), so it has a principal answer (`depHigh_principal`).
* **Refutations through the binder**: the occurs check (`depOcc_refuted`: `X ≐ Π (y : U0). Π (_ : X). y`) and a misfit
  head (`depMis_refuted`: `X ≐ Π (y : U1). y` over `X : U1`, the domain `U1` typed by no universe below `U1`).
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

/-! ## The dep store -/

/-- **The dep store's right side fits**: `Π (y : U0). y` is a type of `U1`. -/
def dep_fits : FitSolvable (S := setting) depEquation where
  v := U1
  X := 0
  u := U1
  annotation_left := rfl
  annotation_right := rfl
  side_left := rfl
  declared := rfl
  universe_u := by decide +kernel
  universe_v := by decide +kernel
  absent := by decide +kernel
  fits := depEquation.2.2.typed
  apart := by decide +kernel

/-- **`X := Π (y : U0). y` is principal**, by the general rule. -/
theorem dep_fit_principal : (frames setting.levels).Principal depStore (fitSolve dep_fits) :=
  fitSolve_principal TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete dep_fits

/-! ## An unknown inside a codomain that uses the argument -/

def depYX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
abbrev ctxDepY1 := extend (empty setting.R) depYX
def depYY : TypeOver ctxDepY1 := formIn ctxDepY1 (.head U0) (by decide +kernel)
/-- `X : U1, Y : U0`. -/
abbrev ctxDepY := extend ctxDepY1 depYY
def depYType : TypeOver ctxDepY := formIn ctxDepY (.head U1) (by decide +kernel)

/-- `X ≐ Π (y : U0). Π (_ : Y). y` at `U1`: the codomain uses `y`, and holds the unknown `Y`. -/
def depYEquation : Equation (TotalTerm ctxDepY) :=
  (termIn ctxDepY depYType (.var 1) (by decide +kernel),
    termIn ctxDepY depYType (.pi (.head U0) (.pi (.var 1) (.var 1))) (by decide +kernel))

def depYStore : EquationStore (TotalTerm ctxDepY) := [depYEquation]

theorem depY_outside : inArrowsCodB ExecutableTowerChoices.choices depYStore = false := by decide +kernel
theorem depY_piece : towerClassify depYStore = none := by decide +kernel

def depY_fits : FitSolvable (S := setting) depYEquation where
  v := U1
  X := 1
  u := U1
  annotation_left := rfl
  annotation_right := rfl
  side_left := rfl
  declared := rfl
  universe_u := by decide +kernel
  universe_v := by decide +kernel
  absent := by decide +kernel
  fits := depYEquation.2.2.typed
  apart := by decide +kernel

/-- **Principal by the rule**: `X := Π (y : U0). Π (_ : Y). y`, `Y` kept. -/
theorem depY_fit_principal : (frames setting.levels).Principal depYStore (fitSolve depY_fits) :=
  fitSolve_principal TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete depY_fits

/-! ## Where narrowing would be needed -/

def depHighY : TypeOver ctxDepY1 := formIn ctxDepY1 (.head U2) (by decide +kernel)
/-- `X : U1, Y : U2`. -/
abbrev ctxDepHigh := extend ctxDepY1 depHighY
def depHighType : TypeOver ctxDepHigh := formIn ctxDepHigh (.head U2) (by decide +kernel)

/-- `X ≐ Π (y : U0). Π (_ : Y). y` at `U2`, `Y` declared above `X`'s universe. -/
def depHighEquation : Equation (TotalTerm ctxDepHigh) :=
  (termIn ctxDepHigh depHighType (.var 1) (by decide +kernel),
    termIn ctxDepHigh depHighType (.pi (.head U0) (.pi (.var 1) (.var 1))) (by decide +kernel))

def depHighStore : EquationStore (TotalTerm ctxDepHigh) := [depHighEquation]

theorem depHigh_outside : inArrowsCodB ExecutableTowerChoices.choices depHighStore = false := by decide +kernel
theorem depHigh_piece : towerClassify depHighStore = none := by decide +kernel

/-- `X := Π (y : U0). Π (_ : G). y`, `Y := G`. -/
def depHighSolution : empty setting.R ⟶ ctxDepHigh :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) depYX (.pi (.head U0) (.pi (.head .legacyGround) (.var 1))) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxDepY1 (termIn ctxDepY1 depHighY (.head .legacyGround) (by decide +kernel)).2

theorem depHigh_solvable : (frames setting.levels).Solvable depHighStore :=
  ⟨_, depHighSolution, models_by depHighSolution depHighEquation.1.2 depHighEquation.2.2 (by decide +kernel)⟩

/-- The view of the equation: `X : U1`, the right side a dependent code below `U1`. -/
def depHigh_flex : FlexDep (S := setting) depHighEquation where
  v := U2
  X := 1
  u := U1
  annotation_left := rfl
  annotation_right := rfl
  side_left := rfl
  declared := rfl
  universe_u := by decide +kernel
  universe_v := by decide +kernel
  code := .pi (.head U0) (.pi (.var 1) (.var 1) fun inside => absurd inside (by decide +kernel))
    fun _ => ⟨U0, rfl, by decide +kernel⟩

/-- **Settled by the rule with narrowing through the binder.** -/
theorem depHigh_settles : Settles depHighStore :=
  dep_settles TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) ContextualDependentNormalCheckingTower.head_typing_unique
    ContextualDependentExecutableChecking.declared (fun ha hb => LevelGlb.towerGlb_total ha hb) depHigh_flex
    (atUniverses_of_B (S := setting) (by decide +kernel)) (by decide +kernel)

/-- **A principal answer**: `Y` narrowed to `U1`, `X := Π (y : U0). Π (_ : Y). y`. -/
theorem depHigh_principal : ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDepHigh),
    (frames setting.levels).Principal depHighStore answer := by
  rcases depHigh_settles.principal_or_unsolvable with found | absent
  · exact found
  · exact absurd depHigh_solvable absent

/-! ## Refutations through the binder -/

def depOccX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
/-- `X : U1`. -/
abbrev ctxDepOcc := extend (empty setting.R) depOccX
def depOccType : TypeOver ctxDepOcc := formIn ctxDepOcc (.head U2) (by decide +kernel)

/-- `X ≐ Π (y : U0). Π (_ : X). y` at `U2`: `X` occurs under a binder whose codomain uses its argument. -/
def depOccEquation : Equation (TotalTerm ctxDepOcc) :=
  (termIn ctxDepOcc depOccType (.var 0) (by decide +kernel),
    termIn ctxDepOcc depOccType (.pi (.head U0) (.pi (.var 1) (.var 1))) (by decide +kernel))

def depOcc_flex : FlexDep (S := setting) depOccEquation where
  v := U2
  X := 0
  u := U1
  annotation_left := rfl
  annotation_right := rfl
  side_left := rfl
  declared := rfl
  universe_u := by decide +kernel
  universe_v := by decide +kernel
  code := .pi (.head U0) (.pi (.var 1) (.var 1) fun inside => absurd inside (by decide +kernel))
    fun _ => ⟨U0, rfl, by decide +kernel⟩

/-- **The occurs check refutes**, through the binder. -/
theorem depOcc_refuted : ¬ (frames setting.levels).Solvable [depOccEquation] :=
  dep_occurs_refutes TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete depOcc_flex (by decide +kernel) (by decide +kernel)
    []

def depMisType : TypeOver ctxDepOcc := formIn ctxDepOcc (.head U2) (by decide +kernel)

/-- `X ≐ Π (y : U1). y` at `U2`, `X : U1`: the domain `U1` is typed by `U2`, not below `U1`. -/
def depMisEquation : Equation (TotalTerm ctxDepOcc) :=
  (termIn ctxDepOcc depMisType (.var 0) (by decide +kernel),
    termIn ctxDepOcc depMisType (.pi (.head U1) (.var 0)) (by decide +kernel))

def depMis_flex : FlexDep (S := setting) depMisEquation where
  v := U2
  X := 0
  u := U1
  annotation_left := rfl
  annotation_right := rfl
  side_left := rfl
  declared := rfl
  universe_u := by decide +kernel
  universe_v := by decide +kernel
  code := .pi (.head U1) (.var 0) fun _ => ⟨U1, rfl, by decide +kernel⟩

/-- **A misfit head refutes**, at the domain that binds the variable the codomain uses. -/
theorem depMis_refuted : ¬ (frames setting.levels).Solvable [depMisEquation] :=
  dep_misfitHead_refutes TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete depMis_flex (h₀ := U1) (by decide +kernel)
    codMisfitHead_fails []

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
