import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TowerGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls

/-!
# Controls for the greatest-lower-bound rule inside a decided fragment, in the tree's tower

All stores are in the tree's cumulative tower, with the solver of glb groups at the tower's own facts and its
greatest lower bound (`glbTowerSolver`). Membership, greatest lower bounds and runs are evaluated by the kernel.

* **The tower's greatest lower bound** (`towerGlb_Ua_Ub`, `towerGlb_Ua_Ua1`, `towerGlb_U1_Ua`): `U_a ⊓ U_b = U0`
  for two level variables; `U_a ⊓ U_{a+1}` is `U_a` up to the order (its level reads `max 0 a`); `U1` is not below
  `U_a`, and `U1 ⊓ U_a = U0`.
* **Views below each other, positive and negative** (`below_level`, `not_compat_level`, `not_below_cross`).
* **Two level variables** (`level_glb_inside`, `level_not_meet_inside`, `level_meet_stuck`, `level_glb_committed`,
  `level_inside_principal`): over `X : U0 → U_a`, `Y : U0 → U_b`, the equation `λ x. X x ≐ λ x. Y x` at
  `Π (x : U0). U_{max a b}` lies outside the fragment of meet groups, whose solver is stuck on it; it lies in the
  fragment of glb groups, whose solver lowers both unknowns to `U0 → U0`, raises `X := λ x. Y x`, and commits; the
  answer is principal.
* **The closure at work** (`glbChain_inside`, `glbChain_committed`, `glbChain_principal`): adding
  `W : U0 → U1` and `λ x. Y x ≐ λ x. W x` at `Π (x : U0). U_{max b 1}`. `U_b` and `U1` are incomparable; after the
  first rule `Y` is `U0 → U0`, which the solver reads again and raises into `W`.
* **Just outside: the crossing is needed** (`cross_only_below_crossing_fails`, `below_crossing_needed`,
  `cross_not_glb_inside`, `cross_glb_stuck`): on the cross store (`X : U0 → U0`, `Y : U1 → U1`) the views fail only
  `U1` below `U0`; the store is solvable and has no principal answer; it lies outside the fragment and the solver is
  stuck on it.
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

/-! ## The tower's greatest lower bound -/

/-- **Two level variables**: `U_a ⊓ U_b = U0`. -/
theorem towerGlb_Ua_Ub : LevelGlb.towerGlb Ua Ub = some U0 := by decide +kernel

/-- `U_{a+1}`. -/
abbrev Ua1 : Tower.Head := .sort (.succ (.param 0))

/-- **One below the other**: `U_a ⊓ U_{a+1}` is `U_a` up to the order. -/
theorem towerGlb_Ua_Ua1 :
    LevelGlb.towerGlb Ua Ua1 = some (.sort (.max (.const 0) (.param 0))) ∧
      setting.R.cumulative (.sort (.max (.const 0) (.param 0))) Ua ∧
      setting.R.cumulative Ua (.sort (.max (.const 0) (.param 0))) := by
  decide +kernel

/-- **A universe not below a level variable**: `U1` is not below `U_a`, and `U1 ⊓ U_a = U0`. -/
theorem towerGlb_U1_Ua : ¬ setting.R.cumulative U1 Ua ∧ LevelGlb.towerGlb U1 Ua = some U0 := by decide +kernel

/-! ## Views below each other -/

/-- **Below each other**: `U0 → U_a` and `U0 → U_b`. -/
theorem below_level : BelowPair setting.R U0 Ua U0 Ub := by decide +kernel

/-- **Not compatible**: neither fits or meets the other. -/
theorem not_compat_level : ¬ Compat setting.R U0 Ua U0 Ub := by decide +kernel

/-- **Not below each other**: `U0 → U0` and `U1 → U1`, since `U1` is not below `U0`. -/
theorem not_below_cross : ¬ GlbCompat setting.R U0 U0 U1 U1 := by decide +kernel

/-! ## The solver -/

/-- The solver of glb groups at the tower's facts and its greatest lower bound. -/
def glbTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  glbGroupSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found)

/-! ## Two level variables -/

/-- **The store lies in the fragment of glb groups.** -/
theorem level_glb_inside : InGlbFragment levelStore := inGlbFragment_of_B (by decide +kernel)

/-- **It lies outside the fragment of meet groups.** -/
theorem level_not_meet_inside : ¬ InMeetFragment levelStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes levelEquation List.mem_cons_self
  have together := grouped levelEquation List.mem_cons_self v
  obtain ⟨hl, hr⟩ := FitFlex.unique v levelView
  have dl : Ctx.lookup ctxAB.raw v.left = famCode [U0] Ua := by rw [hl]; exact levelView.declared_left
  have dr : Ctx.lookup ctxAB.raw v.right = famCode [U0] Ub := by rw [hr]; exact levelView.declared_right
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  exact not_compat_level (comparable v.left v.right different together U0 Ua U0 Ub dl dr)

/-- **The solver of meet groups is stuck on it.** -/
theorem level_meet_stuck : isStuck (run meetTowerSolver levelStore 1) = true := by decide +kernel

/-- **The solver of glb groups commits on it**: both unknowns lowered to `U0 → U0`, then `X := λ x. Y x`. -/
theorem level_glb_committed : (run glbTowerSolver levelStore 2).readout = .commit := by decide +kernel

/-- **Its answer is principal.** -/
theorem level_inside_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB), (frames setting.levels).Principal levelStore answer :=
  principal_of_inGlbFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) (fun ha hb => LevelGlb.towerGlb_total ha hb) level_glb_inside

/-! ## The closure at work -/

/-- `U0 → U1`, over `X Y`. -/
def familyW : TypeOver ctxAB := formIn ctxAB (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `X : U0 → U_a, Y : U0 → U_b, W : U0 → U1`. -/
abbrev ctxABW := extend ctxAB familyW

/-- `U_{max b 1}`. -/
abbrev Ub1 : Tower.Head := .sort (.max (.param 1) (.succ Tower.zero))

/-- `Π (x : U0). U_{max a b}` and `Π (x : U0). U_{max b 1}`, over `X Y W`. -/
def abwType : TypeOver ctxABW := formIn ctxABW (.pi (.head U0) (.head Uab)) (by decide +kernel)
def bwType : TypeOver ctxABW := formIn ctxABW (.pi (.head U0) (.head Ub1)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`, and `λ x. Y x ≐ λ x. W x` at `Π (x : U0). U_{max b 1}`. -/
def glbChainStore : EquationStore (TotalTerm ctxABW) :=
  [(termIn ctxABW abwType (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
      termIn ctxABW abwType (.lam (.app (.var 2) (.var 0))) (by decide +kernel)),
    (termIn ctxABW bwType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
      termIn ctxABW bwType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))]

/-- **Inside**: the three views are pairwise below each other. -/
theorem glbChain_inside : InGlbFragment glbChainStore := inGlbFragment_of_B (by decide +kernel)

/-- **The solver commits**: `X`, `Y` lowered to `U0 → U0` and `X := λ x. Y x`; the second equation read again over
the lowered telescope, and `W := λ x. Y x`. -/
theorem glbChain_committed : (run glbTowerSolver glbChainStore 3).readout = .commit := by decide +kernel

theorem glbChain_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxABW), (frames setting.levels).Principal glbChainStore answer :=
  principal_of_inGlbFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) (fun ha hb => LevelGlb.towerGlb_total ha hb) glbChain_inside

/-! ## Just outside: the crossing is needed -/

/-- **On the cross store the views fail only the crossing**: comparable domains, `U0` below both codomains, `U1`
below its own codomain, and `U1` not below `U0`. -/
theorem cross_only_below_crossing_fails :
    setting.R.cumulative U0 U1 ∧ setting.R.cumulative U0 U0 ∧ setting.R.cumulative U0 U1 ∧
      setting.R.cumulative U1 U1 ∧ ¬ setting.R.cumulative U1 U0 := by decide +kernel

/-- **The crossing is needed**: the cross store fails only the crossing, it is solvable, and it has no principal
answer. -/
theorem below_crossing_needed :
    (setting.R.cumulative U0 U1 ∧ setting.R.cumulative U0 U0 ∧ setting.R.cumulative U0 U1 ∧
        setting.R.cumulative U1 U1 ∧ ¬ setting.R.cumulative U1 U0) ∧
      (frames setting.levels).Solvable crossStore ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer :=
  ⟨cross_only_below_crossing_fails, cross_identity, fun answer => cross_no_principal answer⟩

/-- **It lies outside the fragment of glb groups.** -/
theorem cross_not_glb_inside : ¬ InGlbFragment crossStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have together := grouped crossEquation List.mem_cons_self v
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans crossLeft_code))
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans crossRight_code))
  have dl : Ctx.lookup ctxCross.raw v.left = famCode [U0] U0 := by rw [hl]; exact crossX_declared
  have dr : Ctx.lookup ctxCross.raw v.right = famCode [U1] U1 := by rw [hr]; exact crossY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  exact not_below_cross (comparable v.left v.right different together U0 U0 U1 U1 dl dr)

/-- **The solver of glb groups is stuck on it.** -/
theorem cross_glb_stuck : isStuck (run glbTowerSolver crossStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
