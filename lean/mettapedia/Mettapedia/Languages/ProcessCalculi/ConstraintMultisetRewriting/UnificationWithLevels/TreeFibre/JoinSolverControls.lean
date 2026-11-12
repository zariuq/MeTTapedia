import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinControls

/-!
# Controls: the join solver in the tree's tower

* **The tower's join function** (`towerJoin`, `towerJoin_sound`, `towerJoin_total`): the formal maximum of two
  levels.
* **Twisted domains, decided** (`twist_insideJ`, `twist_committedJ`, `twist_principalJ`): the store of
  `X : U0 → U1 → U1` and `Y : U1 → U0 → U1` lies in the join fragment, outside the fragment of meet groups; the join
  solver commits after one join.
* **Two equations, re-reading and a second join** (`chain_insideJ`, `chain_committedJ`, `chain_principalJ`): with
  `W : U1 → U1 → U1` and the second equation `λ x y. Y x y ≐ λ x y. W x y` at `Π (x : U1) (y : U0). U1`, the first
  join re-reads the second equation's side of `Y` as a side of the joined unknown, and a second join solves it
  (`chain_second_join_needed`). The store lies outside the fragment of meet groups (`chain_not_meet_insideJ`).
* **Just outside: different codomains** (`cross_not_join_inside`, `cross_join_stuck`): the cross store, which has no
  principal answer, lies outside the join fragment and the join solver is stuck on it.
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

/-! ## The tower's join function -/

/-- The least upper bound of two universes of the tower: the larger one when they are comparable, the formal maximum
of their levels otherwise. -/
def towerJoin : Tower.Head → Tower.Head → Option Tower.Head
  | .sort l, .sort r =>
      if setting.R.cumulative (.sort r) (.sort l) then some (.sort l)
      else if setting.R.cumulative (.sort l) (.sort r) then some (.sort r)
      else some (.sort (.max l r))
  | _, _ => none

theorem towerJoin_sound :
    ∀ {u v w : Tower.Head}, towerJoin u v = some w → setting.R.isUniverse w ∧ IsLub setting.R w u v
  | .sort l, .sort r, _, h => by
      simp only [towerJoin] at h
      split_ifs at h with h1 h2
      · cases h
        exact ⟨LevelTower.IsUniverse.sort l, isLub_left (S := setting) (LevelTower.IsUniverse.sort l) h1⟩
      · cases h
        exact ⟨LevelTower.IsUniverse.sort r, isLub_right (S := setting) (LevelTower.IsUniverse.sort r) h2⟩
      · cases h
        exact ⟨LevelTower.IsUniverse.sort _, isLub_of_join (S := setting) TowerModel.algebra (LevelTower.Join.sorts l r)⟩
  | .legacyGround, _, _, h => by cases h
  | .sort _, .legacyGround, _, h => by cases h

theorem towerJoin_total :
    ∀ {u v : Tower.Head}, setting.R.isUniverse u → setting.R.isUniverse v → ∃ w, towerJoin u v = some w
  | .sort _, .sort _, _, _ => by
      simp only [towerJoin]
      split_ifs <;> exact ⟨_, rfl⟩
  | .legacyGround, _, hu, _ => absurd hu (by decide)
  | .sort _, .legacyGround, _, hv => absurd hv (by decide)

/-- The join solver at the tower's facts. -/
def joinTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  joinSolverK (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound

/-- Membership in the join fragment, decided. -/
def inJoinFragmentKB {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  decide (Miller.Families (S := setting) Θ) && problem.all fun e =>
    match readFlexK (S := setting) e with
    | some d => decide (d.cl = d.cr)
    | none => false

theorem inJoinFragmentK_of_B {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inJoinFragmentKB problem = true) : InJoinFragmentK problem := by
  simp only [inJoinFragmentKB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hfam, hall⟩ := h
  refine ⟨hfam, fun e member => ?_, fun e member w => ?_⟩
  · have he := List.all_eq_true.mp hall e member
    cases hd : readFlexK (S := setting) e with
    | none => rw [hd] at he; cases he
    | some d => exact ⟨viewOfK hd⟩
  · have he := List.all_eq_true.mp hall e member
    rw [readFlexK_complete w] at he
    exact of_decide_eq_true he

/-- **The join fragment is decided by the join solver in the tower.** -/
theorem joinTower_principal {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinFragmentK original) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), (frames setting.levels).Principal original answer :=
  principal_of_inJoinFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound towerJoin_total inside

/-! ## Twisted domains, decided -/

theorem twist_insideJ : InJoinFragmentK twistStore := inJoinFragmentK_of_B (by decide +kernel)

/-- **The join solver commits** on the twisted store, which the solver of meet groups is stuck on. -/
theorem twist_committedJ : (run joinTowerSolver twistStore 2).readout = .commit := by decide +kernel

theorem twist_principalJ :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTwist), (frames setting.levels).Principal twistStore answer :=
  joinTower_principal twist_insideJ

/-! ## Two equations: re-reading and a second join -/

def chainW : TypeOver ctxTwist := formIn ctxTwist (bin U1 U1 U1) (by decide +kernel)
/-- `X : U0 → U1 → U1, Y : U1 → U0 → U1, W : U1 → U1 → U1`. -/
abbrev ctxJoinChain := extend ctxTwist chainW
def chainFirstType : TypeOver ctxJoinChain := formIn ctxJoinChain (bin U0 U0 U1) (by decide +kernel)
def chainSecondType : TypeOver ctxJoinChain := formIn ctxJoinChain (bin U1 U0 U1) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U1`. -/
def chainFirst : Equation (TotalTerm ctxJoinChain) :=
  (termIn ctxJoinChain chainFirstType (etaBin 4) (by decide +kernel),
    termIn ctxJoinChain chainFirstType (etaBin 3) (by decide +kernel))

/-- `λ x y. Y x y ≐ λ x y. W x y` at `Π (x : U1) (y : U0). U1`. -/
def chainSecond : Equation (TotalTerm ctxJoinChain) :=
  (termIn ctxJoinChain chainSecondType (etaBin 3) (by decide +kernel),
    termIn ctxJoinChain chainSecondType (etaBin 2) (by decide +kernel))

def joinChainStore : EquationStore (TotalTerm ctxJoinChain) := [chainFirst, chainSecond]

theorem chain_insideJ : InJoinFragmentK joinChainStore := inJoinFragmentK_of_B (by decide +kernel)

theorem chainFirst_annotation : chainFirst.1.1.code = famCode [U0, U0] U1 := by decide +kernel
theorem chainFirst_left : chainFirst.1.2.code = etaExp 2 (.var (2 : Fin ctxJoinChain.arity)) := by decide +kernel
theorem chainFirst_right : chainFirst.2.2.code = etaExp 2 (.var (1 : Fin ctxJoinChain.arity)) := by decide +kernel
theorem chainX_declared : Ctx.lookup ctxJoinChain.raw 2 = famCode [U0, U1] U1 := by decide +kernel
theorem chainY_declared : Ctx.lookup ctxJoinChain.raw 1 = famCode [U1, U0] U1 := by decide +kernel

/-- **It lies outside the fragment of meet groups**: `X` and `Y` have incomparable domains. -/
theorem chain_not_meet_insideJ : ¬ InMeetFragmentK joinChainStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes chainFirst List.mem_cons_self
  have together := grouped chainFirst List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans chainFirst_annotation)
  have sl := v.side_left.symm.trans chainFirst_left
  have sr := v.side_right.symm.trans chainFirst_right
  rw [hps] at sl sr
  have hl : v.left = 2 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 1 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxJoinChain.raw v.left = famCode [U0, U1] U1 := by rw [hl]; exact chainX_declared
  have dr : Ctx.lookup ctxJoinChain.raw v.right = famCode [U1, U0] U1 := by rw [hr]; exact chainY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := comparable v.left v.right different together [U0, U1] U1 [U1, U0] U1 dl dr
  exact absurd compatible (by decide)

/-- **The join solver commits**: two joins, the second equation re-read after the first; the budget counts one more
step to read the empty store. -/
theorem chain_committedJ : (run joinTowerSolver joinChainStore 3).readout = .commit := by decide +kernel

/-- A budget that the twisted store needs is not enough: the second equation remains after the first join. -/
theorem chain_second_join_needed : (run joinTowerSolver joinChainStore 2).readout = .suspended := by decide +kernel

theorem chain_principalJ :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxJoinChain),
      (frames setting.levels).Principal joinChainStore answer :=
  joinTower_principal chain_insideJ

/-! ## Just outside: different codomains -/

/-- **The cross store lies outside the join fragment**: its two unknowns have the codomains `U0` and `U1`. -/
theorem cross_not_join_inside : ¬ InJoinFragmentK crossStore := by
  intro inside
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have codomains := inside.codomains crossEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans crossAnnotation_code)
  have sl := v.side_left.symm.trans crossLeft_code
  have sr := v.side_right.symm.trans crossRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxCross.raw v.left = famCode v.psl v.cl := v.declared_left
  have dr : Ctx.lookup ctxCross.raw v.right = famCode v.psr v.cr := v.declared_right
  rw [hl, crossX_declared] at dl
  rw [hr, crossY_declared] at dr
  have cl := (famCode_inj dl).2
  have cr := (famCode_inj dr).2
  rw [← cl, ← cr] at codomains
  exact absurd codomains (by decide)

theorem cross_join_stuck : isStuck (run joinTowerSolver crossStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
