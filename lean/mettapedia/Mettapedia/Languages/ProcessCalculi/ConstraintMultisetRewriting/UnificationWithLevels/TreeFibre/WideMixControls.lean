import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAuditControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerControls

/-!
# Controls: Miller patterns mixed with glb-join families, decided in one rank

Every run is driven by the common rank, evaluated by the kernel.

* **The residual of a glb join**: `λ x y. F x y ≐ λ x y. Z y x` over `Z : U1 → U1 → U0, F : U0 → U1 → U0`. The Miller
  reader does not read it (`Z`'s domains are not the binders'), nor the family reader (a permutation); the wide reader
  does (`residual_readers`). The direction by domain order solves `F := λ a b. Z b a` (`residual_committed`), with a
  principal answer.
* **The crossed mix** of `InPlaceAuditControls`, where every earlier solver of the tree is stuck, commits under the
  solver of one rank (`cx_committed`, `cx_principal`): the glb join first, its answer re-reading the Miller side of `X`
  as a wide side of the joined unknown, then the direction by domain order. So does the obstruction store of
  `MixedObstructionControls` (`mj_committed`).
* **The pieces still go through**: a Miller permutation, a store pruned on both sides, the glb group with level
  variables, the join alone (`pieces_committed`).
* **Where it stops**: two unknowns with wider domains each, `F G : U1 → U0 → U0`, related by a permutation over binders
  `U0 U0`, cross under the permutation; the store is solvable (`crossedWide_solvable`), and every solver of the tree,
  this one included, is stuck on it at every budget (`crossedWide_stuck`): it needs the glb join under a permutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace WideControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open TreeFibre.Controls (U0 U1 towerMixedSolver towerMixedJoinSolver)
open TreeFibre.AuditControls (inPlace step undecided_every_budget principal_of_rankCommit)

/-- **The solver of one rank for Miller patterns mixed with glb-join families**, at the tower's facts. -/
def towerMixWide : ContextualDependentWorklist.Solver setting.levels :=
  Miller.mixWideSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique Controls.towerJoin Controls.towerJoin_sound
    LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found)

/-- **The wide solver alone**, at the tower's facts. -/
def towerWide : ContextualDependentWorklist.Solver setting.levels :=
  Miller.wideSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Miller.Controls.towerInh

/-! ## The residual of a glb join -/

/-- `Z : U1 → U1 → U0`. -/
def resZ : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U1) (.pi (.head U1) (.head U0))) (by decide +kernel)
abbrev rc1 := extend (empty setting.R) resZ
/-- `F : U0 → U1 → U0`. -/
def resF : TypeOver rc1 := formIn rc1 (.pi (.head U0) (.pi (.head U1) (.head U0))) (by decide +kernel)
/-- `Z : U1 → U1 → U0, F : U0 → U1 → U0`. -/
abbrev ctxRes := extend rc1 resF
def resType : TypeOver ctxRes := formIn ctxRes (.pi (.head U0) (.pi (.head U1) (.head U0))) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. Z y x`. -/
def residualEq : Equation (TotalTerm ctxRes) :=
  (termIn ctxRes resType (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxRes resType (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel))

def residualStore : EquationStore (TotalTerm ctxRes) := [residualEq]

/-- **Read by the wide reader only.** -/
theorem residual_readers : (Miller.readEq (S := setting) residualEq).isSome = false ∧
    (readFlexK (S := setting) residualEq).isSome = false ∧ (Miller.readWide (S := setting) residualEq).isSome = true := by
  decide +kernel

/-- **The direction by domain order solves it**: `F := λ a b. Z b a`. -/
theorem residual_committed : (runRank towerWide residualStore).readout = .commit := by decide +kernel

theorem residual_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxRes), (frames setting.levels).Principal residualStore answer :=
  principal_of_rankCommit residual_committed

/-- **The earlier solvers of one rank are stuck on it.** -/
theorem residual_earlier_stuck : (runRank towerMixedSolver residualStore).readout = .suspended ∧
    (runRank towerMixedJoinSolver residualStore).readout = .suspended := by decide +kernel

/-! ## The crossed mix and the obstruction store -/

/-- **The crossed mix commits under one rank**, where every earlier solver of the tree is stuck. -/
theorem cx_committed : (runRank towerMixWide AuditControls.cxStore).readout = .commit := by decide +kernel

theorem cx_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ AuditControls.ctxCx),
      (frames setting.levels).Principal AuditControls.cxStore answer :=
  principal_of_rankCommit cx_committed

/-- **The obstruction store commits under one rank.** -/
theorem mj_committed : (runRank towerMixWide Controls.mjStore).readout = .commit := by decide +kernel

theorem mj_principal_rank :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Controls.ctxMJ), (frames setting.levels).Principal Controls.mjStore answer :=
  principal_of_rankCommit mj_committed

/-- **The pieces still go through**: a Miller permutation, a store pruned on both sides, the glb group with level
variables, the join alone, the Miller equation alone. -/
theorem pieces_committed : (runRank towerMixWide Miller.Controls.permStore).readout = .commit ∧
    (runRank towerMixWide Miller.Controls.bothStore).readout = .commit ∧
    (runRank towerMixWide Controls.levelStore).readout = .commit ∧
    (runRank towerMixWide [AuditControls.cxJoin]).readout = .commit ∧
    (runRank towerMixWide [AuditControls.cxMiller]).readout = .commit := by decide +kernel

/-! ## Where it stops: the glb join under a permutation -/

/-- `F : U1 → U0 → U0`. -/
def cwF : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U1) (.pi (.head U0) (.head U0))) (by decide +kernel)
abbrev cw1 := extend (empty setting.R) cwF
/-- `G : U1 → U0 → U0`. -/
def cwG : TypeOver cw1 := formIn cw1 (.pi (.head U1) (.pi (.head U0) (.head U0))) (by decide +kernel)
/-- `F G : U1 → U0 → U0`. -/
abbrev ctxCw := extend cw1 cwG
def cwType : TypeOver ctxCw := formIn ctxCw (.pi (.head U0) (.pi (.head U0) (.head U0))) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. G y x` over binders `U0 U0`: both unknowns wider, crossed under the permutation. -/
def crossedWideEq : Equation (TotalTerm ctxCw) :=
  (termIn ctxCw cwType (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxCw cwType (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))

def crossedWideStore : EquationStore (TotalTerm ctxCw) := [crossedWideEq]

/-- `F G := λ a b. Ground`. -/
def crossedWideSolution : empty setting.R ⟶ ctxCw :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) cwF (.lam (.lam (.head .legacyGround))) (by decide +kernel)).2 ≫
    Elimination.instantiate cw1 (termIn cw1 cwG (.lam (.lam (.head .legacyGround))) (by decide +kernel)).2

theorem crossedWide_solvable : (frames setting.levels).Solvable crossedWideStore :=
  ⟨_, crossedWideSolution,
    models_by crossedWideSolution crossedWideEq.1.2 crossedWideEq.2.2 (by decide +kernel)⟩

/-- **Every solver of the tree is stuck on it**, this one included. -/
theorem crossedWide_stuck : (runRank towerMixWide crossedWideStore).readout = .suspended ∧
    (runRank inPlace crossedWideStore).readout = .suspended ∧
    (runRank towerMixedSolver crossedWideStore).readout = .suspended ∧
    (runRank towerMixedJoinSolver crossedWideStore).readout = .suspended := by decide +kernel

/-- **So no budget decides it**, for the solver of one rank. -/
theorem crossedWide_undecided : ∀ fuel, ¬ (run towerMixWide crossedWideStore fuel).Decided :=
  undecided_every_budget crossedWide_stuck.1

end WideControls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
