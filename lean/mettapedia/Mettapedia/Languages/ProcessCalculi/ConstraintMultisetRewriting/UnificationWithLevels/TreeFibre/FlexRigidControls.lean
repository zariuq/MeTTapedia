import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternRules

/-!
# Controls for flex-rigid stores, in the tree's tower

The flex-rigid solver at the tower's facts, with the tower's computed head typings (`frTowerSolver`); membership,
readings and runs evaluated by the kernel.

* **Narrow and solve** (`frNarrow_inside`, `frNarrow_committed`, `frNarrow_principal`): over `X : U1, Y : U2`,
  `X ≐ Π (_ : Y). U0` at `U2`. `Y` lies above `X`'s universe; the solver lowers `Y` to `U1` and sets
  `X := Π (_ : Y). U0`, and commits.
* **Two steps** (`frChain_inside`, `frChain_committed`, `frChain_principal`): adding `Z : U3` and `Y ≐ Π (_ : Z). U0`
  at `U3`. After the first step `Y : U1`, and `Z` is lowered to `U1` in its turn.
* **Occurs** (`frOccurs_inside`, `frOccurs_refuted`): `X ≐ Π (_ : X). U0` at `U1` is refuted with a certificate.
* **Misfit** (`frMisfit_inside`, `frMisfit_refuted`, `frTooLarge_refuted`): over `X : U1, Y : U0`,
  `X ≐ Π (_ : Y). U1` at `U2` and `X ≐ U1` at `U2` are refuted: `U1` is not a type of `U1`.
* **Just outside: incomparable universes** (`frLevel_outside`, `frLevel_stuck`, `frLevel_solvable`): `X : U_a`,
  `Y : U_b` with level variables, `X ≐ Y`: the declared universes are not comparable at every valuation; the solver
  is stuck, and the store is solvable.
* **Just outside: an unknown at a codomain** (`frOver_outside`, `frOver_stuck`, `frOver_solvable`): `X ≐ Π (y : Y). Y`
  over `X : U1, Y : U2` is not an arrow code.
* **Just outside: one unknown on the left twice** (`frTwice_outside`, `frTwice_stuck`): over `X : U2, Y Z : U0`,
  `X ≐ Π (_ : Y). U0` and `X ≐ Π (_ : Z). U0`. After `X := Π (_ : Y). U0` the second equation is rigid on both
  sides, which this fragment does not decompose: the solver stops postponed.
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

/-- The flex-rigid solver at the tower's facts. -/
def frTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  flexRigidSolver (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique

/-- A run that refutes certifies that the store has no solution. -/
theorem refuted_of_readout {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {solver : ContextualDependentWorklist.Solver setting.levels} {fuel : Nat}
    (refuted : (run solver original fuel).readout = .refuted) : ¬ (frames setting.levels).Solvable original :=
  Outcome.readout_eq_refuted refuted

/-! ## Narrow and solve -/

/-- `X ≐ Π (_ : Y). U0` at `U2`, over `X : U1, Y : U2`. -/
def frNarrowStore : EquationStore (TotalTerm ctxOneTwo) :=
  [(termIn ctxOneTwo typeTwo (.var 1) (by decide +kernel),
    termIn ctxOneTwo typeTwo (.pi (.var 0) (.head U0)) (by decide +kernel))]

theorem frNarrow_inside : InFlexRigid ExecutableTowerChoices.choices frNarrowStore :=
  inFlexRigid_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered to `U1`, then `X := Π (_ : Y). U0`. -/
theorem frNarrow_committed : (run frTowerSolver frNarrowStore 2).readout = .commit := by decide +kernel

theorem frNarrow_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxOneTwo), (frames setting.levels).Principal frNarrowStore answer :=
  principal_of_commit frNarrow_committed

/-! ## Two steps -/

/-- `U3`, over `X Y`. -/
def universeThree : TypeOver ctxOneTwo := formIn ctxOneTwo (.head U3) (by decide +kernel)

/-- `X : U1, Y : U2, Z : U3`. -/
abbrev ctxOneTwoThree := extend ctxOneTwo universeThree

def typeTwoChain : TypeOver ctxOneTwoThree := formIn ctxOneTwoThree (.head U2) (by decide +kernel)
def typeThreeChain : TypeOver ctxOneTwoThree := formIn ctxOneTwoThree (.head U3) (by decide +kernel)

/-- `X ≐ Π (_ : Y). U0` at `U2`, and `Y ≐ Π (_ : Z). U0` at `U3`. -/
def frChainStore : EquationStore (TotalTerm ctxOneTwoThree) :=
  [(termIn ctxOneTwoThree typeTwoChain (.var 2) (by decide +kernel),
      termIn ctxOneTwoThree typeTwoChain (.pi (.var 1) (.head U0)) (by decide +kernel)),
    (termIn ctxOneTwoThree typeThreeChain (.var 1) (by decide +kernel),
      termIn ctxOneTwoThree typeThreeChain (.pi (.var 0) (.head U0)) (by decide +kernel))]

theorem frChain_inside : InFlexRigid ExecutableTowerChoices.choices frChainStore :=
  inFlexRigid_of_B _ (by decide +kernel)

/-- **The solver commits in two steps.** -/
theorem frChain_committed : (run frTowerSolver frChainStore 3).readout = .commit := by decide +kernel

theorem frChain_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxOneTwoThree), (frames setting.levels).Principal frChainStore answer :=
  principal_of_commit frChain_committed

/-! ## Occurs -/

def typeOneX : TypeOver ctxOne := formIn ctxOne (.head U1) (by decide +kernel)

/-- `X ≐ Π (_ : X). U0` at `U1`, over `X : U1`. -/
def frOccursStore : EquationStore (TotalTerm ctxOne) :=
  [(termIn ctxOne typeOneX (.var 0) (by decide +kernel),
    termIn ctxOne typeOneX (.pi (.var 0) (.head U0)) (by decide +kernel))]

theorem frOccurs_inside : InFlexRigid ExecutableTowerChoices.choices frOccursStore :=
  inFlexRigid_of_B _ (by decide +kernel)

/-- **The solver refutes it**, by the occurs check. -/
theorem frOccurs_refuted : (run frTowerSolver frOccursStore 1).readout = .refuted := by decide +kernel

theorem frOccurs_unsolvable : ¬ (frames setting.levels).Solvable frOccursStore := refuted_of_readout frOccurs_refuted

/-! ## Misfit -/

/-- `U0`, over `X : U1`. -/
def universeZeroOverOne : TypeOver ctxOne := formIn ctxOne (.head U0) (by decide +kernel)

/-- `X : U1, Y : U0`. -/
abbrev ctxOneZero := extend ctxOne universeZeroOverOne

def typeTwoMisfit : TypeOver ctxOneZero := formIn ctxOneZero (.head U2) (by decide +kernel)

/-- `X ≐ Π (_ : Y). U1` at `U2`. -/
def frMisfitStore : EquationStore (TotalTerm ctxOneZero) :=
  [(termIn ctxOneZero typeTwoMisfit (.var 1) (by decide +kernel),
    termIn ctxOneZero typeTwoMisfit (.pi (.var 0) (.head U1)) (by decide +kernel))]

theorem frMisfit_inside : InFlexRigid ExecutableTowerChoices.choices frMisfitStore :=
  inFlexRigid_of_B _ (by decide +kernel)

/-- **The solver refutes it**: the codomain `U1` is not a type of `U1`. -/
theorem frMisfit_refuted : (run frTowerSolver frMisfitStore 1).readout = .refuted := by decide +kernel

theorem frMisfit_unsolvable : ¬ (frames setting.levels).Solvable frMisfitStore := refuted_of_readout frMisfit_refuted

/-- `X ≐ U1` at `U2`. -/
def frTooLargeStore : EquationStore (TotalTerm ctxOneZero) :=
  [(termIn ctxOneZero typeTwoMisfit (.var 1) (by decide +kernel),
    termIn ctxOneZero typeTwoMisfit (.head U1) (by decide +kernel))]

/-- **The solver refutes it**: `U1` is not a type of `U1`. -/
theorem frTooLarge_refuted : (run frTowerSolver frTooLargeStore 1).readout = .refuted := by decide +kernel

/-! ## Just outside: incomparable universes -/

def universeA : TypeOver (empty setting.R) := formIn (empty setting.R) (.head Ua) (by decide +kernel)
abbrev ctxUa := extend (empty setting.R) universeA
def universeB : TypeOver ctxUa := formIn ctxUa (.head Ub) (by decide +kernel)
/-- `X : U_a, Y : U_b`. -/
abbrev ctxUab := extend ctxUa universeB
def typeAB : TypeOver ctxUab := formIn ctxUab (.head Uab) (by decide +kernel)

/-- `X ≐ Y` at `U_{max a b}`. -/
def frLevelEquation : Equation (TotalTerm ctxUab) :=
  (termIn ctxUab typeAB (.var 1) (by decide +kernel), termIn ctxUab typeAB (.var 0) (by decide +kernel))

def frLevelStore : EquationStore (TotalTerm ctxUab) := [frLevelEquation]

theorem frLevelX_declared : Ctx.lookup ctxUab.raw 1 = .head Ua := by decide +kernel
theorem frLevelY_declared : Ctx.lookup ctxUab.raw 0 = .head Ub := by decide +kernel

/-- **It lies outside the fragment**: the two declared universes are comparable at no common direction. -/
theorem frLevel_outside : ¬ InFlexRigid ExecutableTowerChoices.choices frLevelStore := by
  intro inside
  rcases inside.chain 1 0 Ua Ub frLevelX_declared frLevelY_declared with below | above
  · exact level_undecided.1 below
  · exact level_undecided.2 above

/-- **The solver is stuck on it.** -/
theorem frLevel_stuck : isStuck (run frTowerSolver frLevelStore 1) = true := by decide +kernel

/-- `X := G, Y := G`, for the ground type `G`. -/
def frLevelGround : empty setting.R ⟶ ctxUab :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) universeA (.head .legacyGround) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxUa (termIn ctxUa universeB (.head .legacyGround) (by decide +kernel)).2

/-- **It is solvable.** -/
theorem frLevel_solvable : (frames setting.levels).Solvable frLevelStore :=
  solvable_by frLevelGround frLevelEquation.1.2 frLevelEquation.2.2 (by decide +kernel)

/-! ## Just outside: an unknown at a codomain -/

/-- **`X ≐ Π (y : Y). Y` lies outside**: it is not an arrow code. -/
theorem frOver_outside : inFlexRigidB ExecutableTowerChoices.choices overStore = false := by decide +kernel

/-- **The solver is stuck on it.** -/
theorem frOver_stuck : isStuck (run frTowerSolver overStore 1) = true := by decide +kernel

/-- **It is solvable**, by `X := Π (y : U0). U0, Y := U0`. -/
theorem frOver_solvable : (frames setting.levels).Solvable overStore := ⟨_, overSolution, over_solution_models⟩

/-! ## Just outside: one unknown on the left twice -/

def universeTwoEmpty : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U2) (by decide +kernel)
abbrev ctxTwo := extend (empty setting.R) universeTwoEmpty
def universeZeroOverTwo : TypeOver ctxTwo := formIn ctxTwo (.head U0) (by decide +kernel)
abbrev ctxTwoZero := extend ctxTwo universeZeroOverTwo
def universeZeroOverTwoZero : TypeOver ctxTwoZero := formIn ctxTwoZero (.head U0) (by decide +kernel)
/-- `X : U2, Y : U0, Z : U0`. -/
abbrev ctxTwoZeroZero := extend ctxTwoZero universeZeroOverTwoZero
def typeTwoTwice : TypeOver ctxTwoZeroZero := formIn ctxTwoZeroZero (.head U2) (by decide +kernel)

/-- `X ≐ Π (_ : Y). U0` and `X ≐ Π (_ : Z). U0`, at `U2`. -/
def frTwiceStore : EquationStore (TotalTerm ctxTwoZeroZero) :=
  [(termIn ctxTwoZeroZero typeTwoTwice (.var 2) (by decide +kernel),
      termIn ctxTwoZeroZero typeTwoTwice (.pi (.var 1) (.head U0)) (by decide +kernel)),
    (termIn ctxTwoZeroZero typeTwoTwice (.var 2) (by decide +kernel),
      termIn ctxTwoZeroZero typeTwoTwice (.pi (.var 0) (.head U0)) (by decide +kernel))]

/-- **It lies outside**: `X` is the left side of two equations. -/
theorem frTwice_outside : inFlexRigidB ExecutableTowerChoices.choices frTwiceStore = false := by decide +kernel

/-- **After one step the solver is stuck**: the second equation is rigid on both sides. -/
theorem frTwice_stuck : isStuck (run frTowerSolver frTwiceStore 2) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
