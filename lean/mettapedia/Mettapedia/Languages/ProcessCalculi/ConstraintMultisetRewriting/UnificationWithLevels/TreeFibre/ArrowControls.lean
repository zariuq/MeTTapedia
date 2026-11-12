import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidControls

/-!
# Controls for equations between arrow codes, in the tree's tower

The solver of equations between arrow codes at the tower's facts (`arrowTowerSolver`); membership, readings and runs
evaluated by the kernel.

* **The flex-rigid fragment lies inside** (`inArrows_of_flexRigid`).
* **The restriction of the flex-rigid fragment was not needed** (`twiceArrow_inside`, `twiceArrow_committed`,
  `twiceArrow_principal`): over `X : U2, Y Z : U0`, `X ≐ Π (_ : Y). U0` and `X ≐ Π (_ : Z). U0`, outside the flex-rigid
  fragment, is decided: `X := Π (_ : Y). U0`, then the two Π types decompose to `Y ≐ Z`, then `Y := Z`.
* **Orientation** (`orient_outside_flexRigid`, `orient_inside`, `orient_committed`): `Π (_ : Y). U0 ≐ X` over
  `X : U1, Y : U2` is solved from the right, `Y` lowered.
* **Decomposition, then narrowing** (`decompose_inside`, `decompose_committed`): over `X : U0, Y : U1`,
  `Π (_ : X). U0 ≐ Π (_ : Y). U0` at `U2` decomposes to `X ≐ Y`; `Y` is lowered to `U0` and `X := Y`.
* **Clashes** (`headClash_refuted`, `piHead_refuted`, `codomainClash_refuted`): `U0 ≐ U1`, `Π (_ : Y). U0 ≐ U0` and
  `Π (_ : Y). U0 ≐ Π (_ : Y). U1` are refuted.
* **Just outside** (`level_outside_arrows`, `level_stuck_arrows`, `over_outside_arrows`, `over_stuck_arrows`):
  incomparable declared universes, and an unknown at a codomain; the solver is stuck on both.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

/-- **The flex-rigid fragment lies inside the fragment of equations between arrow codes.** -/
theorem inArrows_of_flexRigid {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
    {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFlexRigid choices problem) : InArrows choices problem := by
  refine ⟨inside.universes, inside.chain, fun e member => ?_, fun e member => ⟨fun h hh => ?_,
    inside.typedHeads e member⟩⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact ⟨⟨v.v, v.annotation_left, v.annotation_right, v.universe_v, v.side_left ▸ .var v.X, v.arrow⟩⟩
  · obtain ⟨v⟩ := inside.shapes e member
    rw [v.side_left] at hh
    cases hh

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- The solver of equations between arrow codes at the tower's facts. -/
def arrowTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  arrowSolver (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique

/-! ## The restriction of the flex-rigid fragment was not needed -/

theorem twiceArrow_inside : InArrows ExecutableTowerChoices.choices frTwiceStore :=
  inArrows_of_B _ (by decide +kernel)

/-- **The solver commits**: `X := Π (_ : Y). U0`; the Π types decompose to `Y ≐ Z`; `Y := Z`. -/
theorem twiceArrow_committed : (run arrowTowerSolver frTwiceStore 4).readout = .commit := by decide +kernel

theorem twiceArrow_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTwoZeroZero), (frames setting.levels).Principal frTwiceStore answer :=
  principal_of_commit twiceArrow_committed

/-! ## Orientation -/

/-- `Π (_ : Y). U0 ≐ X` at `U2`, over `X : U1, Y : U2`. -/
def orientStore : EquationStore (TotalTerm ctxOneTwo) :=
  [(termIn ctxOneTwo typeTwo (.pi (.var 0) (.head U0)) (by decide +kernel),
    termIn ctxOneTwo typeTwo (.var 1) (by decide +kernel))]

theorem orient_outside_flexRigid : inFlexRigidB ExecutableTowerChoices.choices orientStore = false := by
  decide +kernel

theorem orient_inside : InArrows ExecutableTowerChoices.choices orientStore := inArrows_of_B _ (by decide +kernel)

/-- **The solver commits**, from the right: `Y` lowered to `U1`, `X := Π (_ : Y). U0`. -/
theorem orient_committed : (run arrowTowerSolver orientStore 2).readout = .commit := by decide +kernel

/-! ## Decomposition, then narrowing -/

def universeZeroEmpty : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U0) (by decide +kernel)
abbrev ctxZero := extend (empty setting.R) universeZeroEmpty
def universeOneOverZero : TypeOver ctxZero := formIn ctxZero (.head U1) (by decide +kernel)
/-- `X : U0, Y : U1`. -/
abbrev ctxZeroOne := extend ctxZero universeOneOverZero
def typeTwoZeroOne : TypeOver ctxZeroOne := formIn ctxZeroOne (.head U2) (by decide +kernel)

/-- `Π (_ : X). U0 ≐ Π (_ : Y). U0` at `U2`. -/
def decomposeStore : EquationStore (TotalTerm ctxZeroOne) :=
  [(termIn ctxZeroOne typeTwoZeroOne (.pi (.var 1) (.head U0)) (by decide +kernel),
    termIn ctxZeroOne typeTwoZeroOne (.pi (.var 0) (.head U0)) (by decide +kernel))]

theorem decompose_inside : InArrows ExecutableTowerChoices.choices decomposeStore :=
  inArrows_of_B _ (by decide +kernel)

/-- **The solver commits**: decomposition to `X ≐ Y`, then `Y` lowered to `U0` and `X := Y`. -/
theorem decompose_committed : (run arrowTowerSolver decomposeStore 3).readout = .commit := by decide +kernel

theorem decompose_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxZeroOne), (frames setting.levels).Principal decomposeStore answer :=
  principal_of_commit decompose_committed

/-! ## Clashes -/

/-- `U0 ≐ U1` at `U2`. -/
def headClashStore : EquationStore (TotalTerm ctxOneZero) :=
  [(termIn ctxOneZero typeTwoMisfit (.head U0) (by decide +kernel),
    termIn ctxOneZero typeTwoMisfit (.head U1) (by decide +kernel))]

theorem headClash_refuted : (run arrowTowerSolver headClashStore 1).readout = .refuted := by decide +kernel

/-- `Π (_ : Y). U0 ≐ U0` at `U2`. -/
def piHeadStore : EquationStore (TotalTerm ctxOneZero) :=
  [(termIn ctxOneZero typeTwoMisfit (.pi (.var 0) (.head U0)) (by decide +kernel),
    termIn ctxOneZero typeTwoMisfit (.head U0) (by decide +kernel))]

theorem piHead_refuted : (run arrowTowerSolver piHeadStore 1).readout = .refuted := by decide +kernel

/-- `Π (_ : Y). U0 ≐ Π (_ : Y). U1` at `U2`. -/
def codomainClashStore : EquationStore (TotalTerm ctxOneZero) :=
  [(termIn ctxOneZero typeTwoMisfit (.pi (.var 0) (.head U0)) (by decide +kernel),
    termIn ctxOneZero typeTwoMisfit (.pi (.var 0) (.head U1)) (by decide +kernel))]

theorem codomainClash_refuted : (run arrowTowerSolver codomainClashStore 1).readout = .refuted := by
  decide +kernel

theorem codomainClash_unsolvable : ¬ (frames setting.levels).Solvable codomainClashStore :=
  refuted_of_readout codomainClash_refuted

/-! ## Just outside -/

theorem level_outside_arrows : inArrowsB ExecutableTowerChoices.choices frLevelStore = false := by decide +kernel

theorem level_stuck_arrows : isStuck (run arrowTowerSolver frLevelStore 1) = true := by decide +kernel

theorem over_outside_arrows : inArrowsB ExecutableTowerChoices.choices overStore = false := by decide +kernel

theorem over_stuck_arrows : isStuck (run arrowTowerSolver overStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
