import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TowerGlb

/-!
# Controls for flex-rigid equations without the chain, in the tree's tower

The solver narrowing to greatest lower bounds at the tower's facts, computed head typings and greatest lower bound
(`frGlbTowerSolver`). Membership and runs are evaluated by the kernel.

* **The chain was not needed** (`frLevel_glb_inside`, `frLevel_glb_committed`, `frLevel_glb_principal`,
  `chain_not_needed`): over `X : U_a, Y : U_b`, the equation `X ≐ Y` at `U_{max a b}` lies outside the fragment with
  the chain, whose solver is stuck on it; it lies inside the fragment without the chain, and the solver lowers `Y`
  to `U0`, the greatest lower bound of `U_a` and `U_b`, sets `X := Y`, and commits; the answer is principal.
* **Three level variables** (`frThree_outside_chain`, `frThree_glb_inside`, `frThree_glb_committed`,
  `frThree_glb_principal`): over `X : U_a, Y : U_b, Z : U_c`, the equations `X ≐ Π (_ : Y). G` at `U_{max a b}`
  (`G` the ground type, in `U0`) and `Z ≐ Y` at `U_{max b c}`. `Y` is lowered to `U0` and `X := Π (_ : Y). G`; the
  second equation then fits, and `Z := Y`.
* **The chain's stores and refutations are unchanged** (`frNarrow_glb_committed`, `frChain_glb_committed`,
  `frOccurs_glb_refuted`, `frMisfit_glb_refuted`).
* **Still just outside** (`frOver_glb_outside`, `frOver_glb_stuck`, `frTwice_glb_outside`, `frTwice_glb_stuck`): an
  unknown at a codomain (`X ≐ Π (y : Y). Y`), and one unknown on the left twice.
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

/-- The flex-rigid solver narrowing to the tower's greatest lower bounds. -/
def frGlbTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  flexRigidGlbSolver (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique

/-! ## Incomparable universes, decided -/

theorem frLevel_glb_inside : InFlexRigidGlb ExecutableTowerChoices.choices frLevelStore :=
  inFlexRigidGlb_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered to `U0`, the greatest lower bound of `U_a` and `U_b`, then `X := Y`. -/
theorem frLevel_glb_committed : (run frGlbTowerSolver frLevelStore 2).readout = .commit := by decide +kernel

theorem frLevel_glb_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUab), (frames setting.levels).Principal frLevelStore answer :=
  principal_of_commit frLevel_glb_committed

/-- **The chain was not needed**: the store lies outside the fragment with the chain, whose solver is stuck on it,
and inside the fragment without the chain, with a principal answer. -/
theorem chain_not_needed :
    ¬ InFlexRigid ExecutableTowerChoices.choices frLevelStore ∧ isStuck (run frTowerSolver frLevelStore 1) = true ∧
      InFlexRigidGlb ExecutableTowerChoices.choices frLevelStore ∧
      ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUab), (frames setting.levels).Principal frLevelStore answer :=
  ⟨frLevel_outside, frLevel_stuck, frLevel_glb_inside, frLevel_glb_principal⟩

/-! ## Three level variables -/

/-- Universes at the level variable `c` and at `max b c`. -/
abbrev Uc : Tower.Head := .sort (.param 2)
abbrev Ubc : Tower.Head := .sort (.max (.param 1) (.param 2))

def universeC : TypeOver ctxUab := formIn ctxUab (.head Uc) (by decide +kernel)

/-- `X : U_a, Y : U_b, Z : U_c`. -/
abbrev ctxUabc := extend ctxUab universeC

def typeABc : TypeOver ctxUabc := formIn ctxUabc (.head Uab) (by decide +kernel)
def typeBC : TypeOver ctxUabc := formIn ctxUabc (.head Ubc) (by decide +kernel)

/-- `X ≐ Π (_ : Y). G` at `U_{max a b}`, and `Z ≐ Y` at `U_{max b c}`. -/
def frThreeStore : EquationStore (TotalTerm ctxUabc) :=
  [(termIn ctxUabc typeABc (.var 2) (by decide +kernel),
      termIn ctxUabc typeABc (.pi (.var 1) (.head .legacyGround)) (by decide +kernel)),
    (termIn ctxUabc typeBC (.var 0) (by decide +kernel), termIn ctxUabc typeBC (.var 1) (by decide +kernel))]

/-- **Outside the fragment with the chain**: the three universes are pairwise incomparable. -/
theorem frThree_outside_chain : inFlexRigidB ExecutableTowerChoices.choices frThreeStore = false := by
  decide +kernel

theorem frThree_glb_inside : InFlexRigidGlb ExecutableTowerChoices.choices frThreeStore :=
  inFlexRigidGlb_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered to `U0` and `X := Π (_ : Y). G`; then `Z := Y`. -/
theorem frThree_glb_committed : (run frGlbTowerSolver frThreeStore 3).readout = .commit := by decide +kernel

theorem frThree_glb_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUabc), (frames setting.levels).Principal frThreeStore answer :=
  principal_of_commit frThree_glb_committed

/-! ## The chain's stores and refutations are unchanged -/

theorem frNarrow_glb_committed : (run frGlbTowerSolver frNarrowStore 2).readout = .commit := by decide +kernel
theorem frChain_glb_committed : (run frGlbTowerSolver frChainStore 3).readout = .commit := by decide +kernel
theorem frOccurs_glb_refuted : (run frGlbTowerSolver frOccursStore 1).readout = .refuted := by decide +kernel
theorem frMisfit_glb_refuted : (run frGlbTowerSolver frMisfitStore 1).readout = .refuted := by decide +kernel

/-! ## Still just outside -/

/-- **An unknown at a codomain** is not an arrow code. -/
theorem frOver_glb_outside : inFlexRigidGlbB ExecutableTowerChoices.choices overStore = false := by decide +kernel
theorem frOver_glb_stuck : isStuck (run frGlbTowerSolver overStore 1) = true := by decide +kernel

/-- **One unknown on the left twice.** -/
theorem frTwice_glb_outside : inFlexRigidGlbB ExecutableTowerChoices.choices frTwiceStore = false := by
  decide +kernel
theorem frTwice_glb_stuck : isStuck (run frGlbTowerSolver frTwiceStore 2) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
