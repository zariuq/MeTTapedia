import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinControls

/-!
# Controls: stores mixing glb-join families and arrow codes, in the tree's tower

The spare store's equation (`λ x. X x ≐ λ x. Y x` over `X : U0 → U0, Y : U2 → U1`, a glb-join equation whose domains are
not exact, so not a Miller equation) with an equation between arrow codes (`Z ≐ Π (_ : U0). U0`, `Z : U1`):
* the earlier union reads it into no piece (`sj_piece`), and the solver mixing Miller patterns with arrow codes is stuck
  on it (`sj_mixed_suspended`);
* it is a mixed join store (`sj_inMixedJoin`), and the mixed join solver commits in both orders (`sj_committed`,
  `sjSwapped_committed`).
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

/-- **The mixed join solver at the tower's facts.** -/
def towerMixedJoinSolver : ContextualDependentWorklist.Solver setting.levels :=
  mixedJoinSolver (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found)

/-- **Decided in the tower.** -/
theorem towerMixedJoin_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMixedJoin ExecutableTowerChoices.choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run towerMixedJoinSolver original larger = run towerMixedJoinSolver original fuel ∧
        ((∃ state finished, run towerMixedJoinSolver original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run towerMixedJoinSolver original larger = .refuted absent)) :=
  mixedJoin_decided (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerJoin_total (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

def sjZ : TypeOver ctxSpare := formIn ctxSpare (.head U1) (by decide +kernel)
/-- `X : U0 → U0, Y : U2 → U1, Z : U1`. -/
abbrev ctxSJ := extend ctxSpare sjZ
def sjFamType : TypeOver ctxSJ := formIn ctxSJ (.pi (.head U0) (.head U1)) (by decide +kernel)
def sjUniType : TypeOver ctxSJ := formIn ctxSJ (.head U1) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1`: a glb-join equation, `Y`'s domain not the binder's. -/
def sjFlex : Equation (TotalTerm ctxSJ) :=
  (termIn ctxSJ sjFamType (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
    termIn ctxSJ sjFamType (.lam (.app (.var 2) (.var 0))) (by decide +kernel))

/-- `Z ≐ Π (_ : U0). U0` at `U1`. -/
def sjArrow : Equation (TotalTerm ctxSJ) :=
  (termIn ctxSJ sjUniType (.var 0) (by decide +kernel),
    termIn ctxSJ sjUniType (.pi (.head U0) (.head U0)) (by decide +kernel))

def sjStore : EquationStore (TotalTerm ctxSJ) := [sjFlex, sjArrow]

/-- **In no piece of the earlier union.** -/
theorem sj_piece : towerClassify sjStore = none := by decide +kernel

/-- **The solver mixing Miller patterns and arrow codes is stuck on it**: the glb-join equation is no Miller equation. -/
theorem sj_mixed_suspended : (run towerMixedSolver sjStore 5).readout = .suspended := by decide +kernel

/-- **A mixed join store.** -/
theorem sj_inMixedJoin : InMixedJoin ExecutableTowerChoices.choices sjStore :=
  .inr ⟨by decide +kernel, [sjFlex], [sjArrow], List.Perm.refl _, inGlbJoinFragmentK_of_B (by decide +kernel),
    fun e member => by
      obtain rfl := List.mem_singleton.mp member
      exact inArrowsCod_of_B _ (by decide +kernel)⟩

/-- **The mixed join solver commits**: the join, then the arrow solver. -/
theorem sj_committed : (run towerMixedJoinSolver sjStore 3).readout = .commit := by decide +kernel
theorem sj_suspended_before : (run towerMixedJoinSolver sjStore 2).readout = .suspended := by decide +kernel

/-- **In the other order too.** -/
theorem sjSwapped_committed : (run towerMixedJoinSolver [sjArrow, sjFlex] 3).readout = .commit := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
