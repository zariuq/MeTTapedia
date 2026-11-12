import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsControls

/-!
# Controls: one solver with one rank for stores mixing Miller patterns and arrow codes, in the tree's tower

* **The mixed solver in the tower** (`towerMixedSolver`, `towerMixed_decided`).
* **The blend store**, a Miller equation of families with an equation between arrow codes, which the union of the
  pieces reads into no piece: inside, and committed in both orders (`blend_mixed_committed`, `blendSwapped_committed`).
* **A shared unknown**: `λ z. X ≐ λ z. F z` with `X ≐ Π (_ : U0). U0` over `F : U0 → U1, X : U1`. The unknown `X` is
  met by a Miller equation under a binder and by an equation between arrow codes. In no piece of the union; inside the
  mixed fragment; committed in both orders (`shared_committed`, `sharedSwapped_committed`): the Miller equations come
  first.
* **Why the Miller equations come first**: solving the equation between arrow codes first would leave
  `λ z. Π (_ : U0). U0 ≐ λ z. F z`, which lies outside the mixed fragment (`shLeft_outside`) and is pending
  (`shLeft_suspended`), though solvable (`shLeft_solvable`). And the solver of arrow codes alone is stuck on the blend
  store with its equation between arrow codes first (`blendSwapped_arrows_suspended`).
* **One rank where the pieces' ranks disagree**: one round on `Π (_ : U0). X ≐ Π (_ : U0). Y` decomposes it. The Miller
  rank rises, from `(2, 1)` to `(2, 2)` (`dec_round_raises_millerRank`); the common rank falls, from `(2, 6)` to `(2, 4)`
  (`dec_round_lowers_commonRank`).
* **The pieces through the one solver**: a Miller permutation with incomparable codomains commits, a scope escape is
  refuted, the decomposition of arrow codes commits; a dependent Π type stays outside and pending (`dep_outside_mixed`).
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

/-! ## The solver in the tower -/

/-- **The mixed solver at the tower's facts.** -/
def towerMixedSolver : ContextualDependentWorklist.Solver setting.levels :=
  mixedSolver (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found)

/-- **Decided in the tower.** -/
theorem towerMixed_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMixed ExecutableTowerChoices.choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run towerMixedSolver original larger = run towerMixedSolver original fuel ∧
        ((∃ state finished, run towerMixedSolver original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run towerMixedSolver original larger = .refuted absent)) :=
  mixed_decided (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

/-! ## The blend store -/

theorem blend_inMixed : InMixed ExecutableTowerChoices.choices blendStore :=
  inMixed_of_B _ (by decide +kernel)

/-- **The blend store commits**: the Miller equation, then the equation between arrow codes. -/
theorem blend_mixed_committed : (run towerMixedSolver blendStore 4).readout = .commit := by decide +kernel
theorem blend_mixed_suspended_before : (run towerMixedSolver blendStore 3).readout = .suspended := by decide +kernel

/-- **In the other order too**: the Miller equation is put first. -/
theorem blendSwapped_committed : (run towerMixedSolver [blendArrow, blendFlex] 4).readout = .commit := by
  decide +kernel

/-- **The solver of arrow codes alone is stuck** on the blend store with its equation between arrow codes first. -/
theorem blendSwapped_arrows_suspended :
    (run arrowCodTowerSolver [blendArrow, blendFlex] 3).readout = .suspended := by decide +kernel

/-! ## An unknown shared by a Miller equation under a binder and an equation between arrow codes -/

def shF : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head U0) (.head U1)) (by decide +kernel)
abbrev ctxSh1 := extend (empty setting.R) shF
def shX : TypeOver ctxSh1 := formIn ctxSh1 (.head U1) (by decide +kernel)
/-- `F : U0 → U1, X : U1`. -/
abbrev ctxSh := extend ctxSh1 shX
def shFamType : TypeOver ctxSh := formIn ctxSh (.pi (.head U0) (.head U1)) (by decide +kernel)
def shUniType : TypeOver ctxSh := formIn ctxSh (.head U1) (by decide +kernel)

/-- `λ z. X ≐ λ z. F z` at `Π (z : U0). U1`. -/
def shFlex : Equation (TotalTerm ctxSh) :=
  (termIn ctxSh shFamType (.lam (.var 1)) (by decide +kernel),
    termIn ctxSh shFamType (.lam (.app (.var 2) (.var 0))) (by decide +kernel))

/-- `X ≐ Π (_ : U0). U0` at `U1`. -/
def shArrow : Equation (TotalTerm ctxSh) :=
  (termIn ctxSh shUniType (.var 0) (by decide +kernel),
    termIn ctxSh shUniType (.pi (.head U0) (.head U0)) (by decide +kernel))

def sharedStore : EquationStore (TotalTerm ctxSh) := [shFlex, shArrow]

/-- **In no piece of the earlier union**, inside the mixed fragment. -/
theorem shared_piece : towerClassify sharedStore = none := by decide +kernel
theorem shared_inMixed : InMixed ExecutableTowerChoices.choices sharedStore :=
  inMixed_of_B _ (by decide +kernel)

/-- **Committed**: `F` pruned to no parameter, the two unknowns of `U1` merged, then `X := Π (_ : U0). U0`. -/
theorem shared_committed : (run towerMixedSolver sharedStore 5).readout = .commit := by decide +kernel
theorem shared_suspended_before : (run towerMixedSolver sharedStore 4).readout = .suspended := by decide +kernel
theorem sharedSwapped_committed : (run towerMixedSolver [shArrow, shFlex] 5).readout = .commit := by
  decide +kernel

/-- **What the other order would leave**: `λ z. Π (_ : U0). U0 ≐ λ z. F z`, the equation between arrow codes solved
first. -/
def shLeft : Equation (TotalTerm ctxSh) :=
  (termIn ctxSh shFamType (.lam (.pi (.head U0) (.head U0))) (by decide +kernel),
    termIn ctxSh shFamType (.lam (.app (.var 2) (.var 0))) (by decide +kernel))

/-- **It lies outside the mixed fragment**: neither a Miller equation nor an equation at a universe. -/
theorem shLeft_outside : ¬ InMixed ExecutableTowerChoices.choices [shLeft] := by
  have notArrows : ¬ InArrowsCod ExecutableTowerChoices.choices [shLeft] := fun inside => by
    have h := Miller.inArrowsCodB_of (S := setting) ExecutableTowerChoices.choices (problem := [shLeft]) inside
    revert h
    decide +kernel
  have notView : ¬ Nonempty (Miller.EqView (S := setting) shLeft) := fun ⟨w⟩ => by
    have h := Miller.readEq_isSome_of_view w
    revert h
    decide +kernel
  rintro (arrows | mixed)
  · exact notArrows arrows
  · rcases mixed.each shLeft List.mem_cons_self with view | arrow
    · exact notView view
    · exact notArrows arrow

theorem shLeft_suspended : (run towerMixedSolver [shLeft] 3).readout = .suspended := by decide +kernel

/-- `F := λ z. Π (_ : U0). U0`, `X := Π (_ : U0). U0`. -/
def shLeftSolution : empty setting.R ⟶ ctxSh :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) shF (.lam (.pi (.head U0) (.head U0))) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxSh1 (termIn ctxSh1 shX (.pi (.head U0) (.head U0)) (by decide +kernel)).2

/-- **It is solvable**: the boundary is the order of the rounds, not a missing answer. -/
theorem shLeft_solvable : (frames setting.levels).Solvable [shLeft] :=
  ⟨_, shLeftSolution, models_by shLeftSolution shLeft.1.2 shLeft.2.2 (by decide +kernel)⟩

/-! ## One rank where the pieces' ranks disagree -/

theorem dec_inMixed : InMixed ExecutableTowerChoices.choices decStore := inMixed_of_B _ (by decide +kernel)

theorem dec_ranks : Miller.millerRank decStore = (2, 1) ∧ commonRank decStore = (2, 6) := by decide +kernel

/-- The ranks of the store after one round. -/
def decRanksAfterOne : Option ((Nat × Nat) × (Nat × Nat)) :=
  match run towerMixedSolver decStore 1 with
  | .cutoff state => some (Miller.millerRank state.remaining, commonRank state.remaining)
  | _ => none

/-- **One round (a decomposition) raises the Miller rank** from `(2, 1)` to `(2, 2)` **and lowers the common rank**
from `(2, 6)` to `(2, 4)`. -/
theorem dec_round_ranks : decRanksAfterOne = some ((2, 2), (2, 4)) := by decide +kernel

theorem dec_round_raises_millerRank : ¬ ContextualDependentWorklist.Below (2, 2) (2, 1) := by
  intro h
  rcases Prod.lex_def.mp h with lt | ⟨_, lt⟩ <;> omega

theorem dec_round_lowers_commonRank : ContextualDependentWorklist.Below (2, 4) (2, 6) :=
  Prod.Lex.right _ (by decide)

theorem dec_mixed_committed : (run towerMixedSolver decStore 4).readout = .commit := by decide +kernel

/-! ## The pieces through the one solver -/

theorem levelPerm_mixed_committed : (run towerMixedSolver Miller.Controls.levelPermStore 3).readout = .commit := by
  decide +kernel

theorem scope_mixed_refuted : (run towerMixedSolver Miller.Controls.scopeStore 1).readout = .refuted := by
  decide +kernel

/-- **A dependent Π type stays outside**: its equation is neither a Miller equation nor between arrow codes. -/
theorem dep_outside_mixed : inMixedB ExecutableTowerChoices.choices depStore = false := by decide +kernel
theorem dep_mixed_suspended : (run towerMixedSolver depStore 3).readout = .suspended := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
