import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Trimming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupsInitial

/-!
# Control: the solvers' own answers, trimmed, are initial solutions

* **Glb groups** (`chain_*`): the solver of glb groups solves the three-unknown chain store (`glbChainStore`:
  `X : U0 → U_a`, `Y : U0 → U_b`, `W : U0 → U1`) in three rounds: `X` and `Y` lowered to `U0 → U0` and
  `X := λ x. Y x`, then `W := λ x. Y x`. Its answer keeps all three unknowns declared. The trimming theorem applies
  to it as the kernel computes it (`chainState`): the answer fixes only `Y` and mentions only `Y`, and `Y` keeps its
  domain below its declaration. Deleting `X` and `W` gives the initial solution (`chain_trimmed_initial`).
* **Flex-rigid without the chain** (`three_*`): over `X : U_a, Y : U_b, Z : U_c`, the solver lowers `Y` to `U0`,
  sets `X := Π (_ : Y). G` and `Z := Y`. Deleting `X` and `Z` gives the initial solution (`three_trimmed_initial`).
* **Miller patterns** (`perm_*`, `both_*`): on `λ x y. F x y ≐ λ x y. G y x` the solver solves one unknown by the
  other; deleting it gives the initial solution (`perm_trimmed_initial`). On `λ x y z. F x y ≐ λ x y z. G y z` both
  unknowns are pruned in place: the answer applies a redeclared unknown to the kept locals, so it mentions an unknown
  it does not fix and the trimming theorem does not apply (`both_not_fixedSupport`).
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

/-- **The state of the solved run** on the chain store, as the kernel computes it. -/
def chainState : Update setting.levels glbChainStore :=
  (run glbTowerSolver glbChainStore 3).state?.get (by decide +kernel)

theorem chainState_finished : chainState.remaining = [] := by decide +kernel

/-- **The solver's answer is principal.** -/
theorem chainState_principal : (frames setting.levels).Principal glbChainStore chainState.answer :=
  chainState.completed chainState_finished

theorem chain_same : chainState.target.arity = ctxABW.arity := by decide +kernel

/-- The declared family of each unknown of the answer's telescope. -/
def chainView (j : Fin chainState.target.arity) : List Tower.Head × Tower.Head :=
  (readFam (Ctx.lookup chainState.target.raw j)).getD ([], U0)

theorem chain_declared :
    ∀ j, Ctx.lookup chainState.target.raw j = famCode (chainView j).1 (chainView j).2 := by
  decide +kernel

theorem chain_universes :
    ∀ j, AllUniverses setting.R (chainView j).1 ∧ setting.R.isUniverse (chainView j).2 := by
  decide +kernel

/-- **The answer fixes the unknowns it mentions.** -/
theorem chain_fixedSupport : ∀ (i : Fin ctxABW.arity) (j : Fin chainState.target.arity),
    j ∈ (chainState.answer.substitution i).support →
      chainState.answer.substitution (Fin.cast chain_same j) = .var j := by
  decide +kernel

/-- The declared codomain of each unknown in the store's telescope. -/
def chainOuter (j : Fin chainState.target.arity) : Tower.Head :=
  ((readFam (Ctx.lookup ctxABW.raw (Fin.cast chain_same j))).getD ([], U0)).2

theorem chain_lowered_facts : ∀ j : Fin chainState.target.arity,
    chainState.answer.substitution (Fin.cast chain_same j) = .var j →
      Ctx.lookup ctxABW.raw (Fin.cast chain_same j) = famCode (chainView j).1 (chainOuter j) ∧
        setting.R.isUniverse (chainOuter j) ∧ setting.R.cumulative (chainView j).2 (chainOuter j) := by
  decide +kernel

/-- **Only `Y` is kept**: `X` and `W` are deleted. -/
theorem chain_kept : (keptOf chainState.answer chain_same).map Fin.val = [1] := by decide +kernel

/-- **The solver's answer on the chain store, with `X` and `W` deleted, is the initial solution.** -/
theorem chain_trimmed_initial :
    InitialSolution (frames setting.levels) glbChainStore
      (trimOut chainView chain_declared chain_universes Miller.Controls.towerInh
        (keptOf chainState.answer chain_same) ≫ chainState.answer) :=
  initial_of_trimmed TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Miller.Controls.towerInh chainState_principal
    chain_same chainView chain_declared chain_universes chain_fixedSupport
    (fun j fixed => ⟨chainOuter j, chain_lowered_facts j fixed⟩)

/-! ## The general theorem at the tower -/

/-- The declared families of the chain store's telescope. -/
def ctxABWView (j : Fin ctxABW.arity) : List Tower.Head × Tower.Head :=
  (readFam (Ctx.lookup ctxABW.raw j)).getD ([], U0)

theorem ctxABW_views : ∀ j, Ctx.lookup ctxABW.raw j = famCode (ctxABWView j).1 (ctxABWView j).2 ∧
    AllUniverses setting.R (ctxABWView j).1 ∧ setting.R.isUniverse (ctxABWView j).2 := by
  decide +kernel

/-- **The chain store has an initial solution**, by the general theorem on the fragment of glb groups: the solver's
answer with its solved unknowns deleted. -/
theorem glbChain_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxABW), InitialSolution (frames setting.levels) glbChainStore answer :=
  glbGroup_initial TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) glbChain_inside Miller.Controls.towerInh
    (fun j => ⟨_, _, ctxABW_views j⟩) (fun ha hb => LevelGlb.towerGlb_total ha hb)

/-! ## Flex-rigid without the chain -/

/-- **The state of the solved run** on three level variables. -/
def threeState : Update setting.levels frThreeStore :=
  (run frGlbTowerSolver frThreeStore 3).state?.get (by decide +kernel)

theorem threeState_finished : threeState.remaining = [] := by decide +kernel

theorem threeState_principal : (frames setting.levels).Principal frThreeStore threeState.answer :=
  threeState.completed threeState_finished

theorem three_same : threeState.target.arity = ctxUabc.arity := by decide +kernel

def threeView (j : Fin threeState.target.arity) : List Tower.Head × Tower.Head :=
  (readFam (Ctx.lookup threeState.target.raw j)).getD ([], U0)

theorem three_declared :
    ∀ j, Ctx.lookup threeState.target.raw j = famCode (threeView j).1 (threeView j).2 := by
  decide +kernel

theorem three_universes :
    ∀ j, AllUniverses setting.R (threeView j).1 ∧ setting.R.isUniverse (threeView j).2 := by
  decide +kernel

theorem three_fixedSupport : ∀ (i : Fin ctxUabc.arity) (j : Fin threeState.target.arity),
    j ∈ (threeState.answer.substitution i).support →
      threeState.answer.substitution (Fin.cast three_same j) = .var j := by
  decide +kernel

def threeOuter (j : Fin threeState.target.arity) : Tower.Head :=
  ((readFam (Ctx.lookup ctxUabc.raw (Fin.cast three_same j))).getD ([], U0)).2

theorem three_lowered_facts : ∀ j : Fin threeState.target.arity,
    threeState.answer.substitution (Fin.cast three_same j) = .var j →
      Ctx.lookup ctxUabc.raw (Fin.cast three_same j) = famCode (threeView j).1 (threeOuter j) ∧
        setting.R.isUniverse (threeOuter j) ∧ setting.R.cumulative (threeView j).2 (threeOuter j) := by
  decide +kernel

/-- **Only `Y` is kept**: `X` and `Z` are deleted. -/
theorem three_kept : (keptOf threeState.answer three_same).map Fin.val = [1] := by decide +kernel

/-- **The solver's answer on three level variables, with `X` and `Z` deleted, is the initial solution.** -/
theorem three_trimmed_initial :
    InitialSolution (frames setting.levels) frThreeStore
      (trimOut threeView three_declared three_universes Miller.Controls.towerInh
        (keptOf threeState.answer three_same) ≫ threeState.answer) :=
  initial_of_trimmed TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Miller.Controls.towerInh threeState_principal
    three_same threeView three_declared three_universes three_fixedSupport
    (fun j fixed => ⟨threeOuter j, three_lowered_facts j fixed⟩)

/-! ## Miller patterns: solving is trimmed; pruning in place is outside the trimming theorem -/

/-- **The state of the solved run** on the permutation store `λ x y. F x y ≐ λ x y. G y x`. Irreducible for the
elaborator; the kernel evaluates it. -/
@[irreducible] def permState : Update setting.levels Miller.Controls.permStore :=
  (run Miller.Controls.millerTower Miller.Controls.permStore 3).state?.get (by decide +kernel)

theorem permState_finished : permState.remaining = [] := by decide +kernel

theorem permState_principal :
    (frames setting.levels).Principal Miller.Controls.permStore permState.answer :=
  permState.completed permState_finished

theorem perm_same : permState.target.arity = Miller.Controls.ctxBB.arity := by decide +kernel

def permView (j : Fin permState.target.arity) : List Tower.Head × Tower.Head :=
  (readFam (Ctx.lookup permState.target.raw j)).getD ([], U0)

theorem perm_declared :
    ∀ j, Ctx.lookup permState.target.raw j = famCode (permView j).1 (permView j).2 := by
  decide +kernel

theorem perm_universes :
    ∀ j, AllUniverses setting.R (permView j).1 ∧ setting.R.isUniverse (permView j).2 := by
  decide +kernel

theorem perm_fixedSupport : ∀ (i : Fin Miller.Controls.ctxBB.arity) (j : Fin permState.target.arity),
    j ∈ (permState.answer.substitution i).support →
      permState.answer.substitution (Fin.cast perm_same j) = .var j := by
  decide +kernel

def permOuter (j : Fin permState.target.arity) : Tower.Head :=
  ((readFam (Ctx.lookup Miller.Controls.ctxBB.raw (Fin.cast perm_same j))).getD ([], U0)).2

theorem perm_lowered_facts : ∀ j : Fin permState.target.arity,
    permState.answer.substitution (Fin.cast perm_same j) = .var j →
      Ctx.lookup Miller.Controls.ctxBB.raw (Fin.cast perm_same j) = famCode (permView j).1 (permOuter j) ∧
        setting.R.isUniverse (permOuter j) ∧ setting.R.cumulative (permView j).2 (permOuter j) := by
  decide +kernel

/-- **One of the two unknowns is kept.** -/
theorem perm_kept : (keptOf permState.answer perm_same).length = 1 := by decide +kernel

/-- **The Miller solver's answer on the permutation store, with the solved unknown deleted, is the initial
solution.** -/
theorem perm_trimmed_initial :
    InitialSolution (frames setting.levels) Miller.Controls.permStore
      (trimOut permView perm_declared perm_universes Miller.Controls.towerInh
        (keptOf permState.answer perm_same) ≫ permState.answer) :=
  initial_of_trimmed TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Miller.Controls.towerInh permState_principal
    perm_same permView perm_declared perm_universes perm_fixedSupport
    (fun j fixed => ⟨permOuter j, perm_lowered_facts j fixed⟩)

/-- **The state of the solved run** on `λ x y z. F x y ≐ λ x y z. G y z`: both unknowns pruned to `y`. -/
@[irreducible] def bothState : Update setting.levels Miller.Controls.bothStore :=
  (run Miller.Controls.millerTower Miller.Controls.bothStore 5).state?.get (by decide +kernel)

theorem both_same : bothState.target.arity = Miller.Controls.ctxBB.arity := by decide +kernel

/-- **Pruning in place is outside the trimming theorem**: the answer mentions an unknown it does not fix, the pruned
unknown declared again at fewer arguments, whose answer applies it to the kept locals. -/
theorem both_not_fixedSupport : ¬ ∀ (i : Fin Miller.Controls.ctxBB.arity) (j : Fin bothState.target.arity),
    j ∈ (bothState.answer.substitution i).support →
      bothState.answer.substitution (Fin.cast both_same j) = .var j := by
  decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
