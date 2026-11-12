import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetSolverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupControls

/-!
# Controls: the glb-join solver in the tree's tower

All stores are in the tree's cumulative tower; membership and runs are evaluated by the kernel.

* **Incomparable codomains together with incomparable domains** (`twin_*`): over `X : U0 → U1 → U_{a+1}` and
  `Y : U1 → U0 → U_{b+1}`, the equation `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U_{max (a+1) (b+1)}`. Every
  position is usable on both sides and crosses (`U0` and `U1` lie below both codomains). The store lies outside the
  join-meet fragment, whose solver is stuck on it; the glb-join solver declares `Y` again at
  `U1 → U1 → U_{(a+1) ⊓ (b+1)}` and commits; the answer is principal.
* **A position whose domain exceeds its codomain** (`spare_*`): over `X : U0 → U0` and `Y : U2 → U1`, at
  `Π (x : U0). U1`. The join with a meet's crossing fails (`U2` is neither `X`'s domain nor below `U0`), so the store lies
  outside the join-meet fragment and its solver is stuck; the position is not usable on `Y`'s side (`U2` is not below
  `U1`), so it crosses, and the glb-join solver commits with a principal answer.
* **Cumulatively equivalent, different codomains** (`equiv_*`): over `X : U0 → U_a` and `Y : U0 → U_{max 0 a}`. The
  join-meet fragment excludes the store by its condition that equivalent codomains are equal; the glb-join fragment
  contains it, and both solvers commit on it.
* **The earlier fragments' stores** (`*_insideGJ`, `*_committedGJ`): twisted domains of one and of two codomains, the
  chained store of three unknowns, the true meet, and the store of two level variables are inside and commit.
* **Just outside: the cross store** (`cross_not_glbJoin_inside`, `cross_glbJoin_stuck`): `X : U0 → U0`,
  `Y : U1 → U1` at `Π (x : U0). U1` fails the condition at its one position, which is usable on both sides; it is
  solvable and has no principal answer.
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

/-- The glb-join solver at the tower's facts, its join function and its greatest lower bound. -/
def glbJoinTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  glbJoinSolverK (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found)

/-- Of two different declared families, crossing well, decided. -/
def groupCrossB {n : Nat} (Γ : Tower.Ctx n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Γ i), readFam (Ctx.lookup Γ j) with
    | some a, some b => decide (CrossCompat setting.R a.1 a.2 b.1 b.2)
    | _, _ => true

theorem groupCross_of_B {Θ : Context setting.R} (h : groupCrossB Θ.raw = true) : GroupCross Θ (fun _ => 0) := by
  intro i j ne _ psi ci psj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  exact of_decide_eq_true hij

/-- **Membership in the glb-join fragment, decided**, with all unknowns in one group. -/
def inGlbJoinFragmentKB {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  decide (Miller.Families (S := setting) Θ) && problem.all (fun e => (readFlexK (S := setting) e).isSome) &&
    groupCrossB Θ.raw

theorem inGlbJoinFragmentK_of_B {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inGlbJoinFragmentKB problem = true) : InGlbJoinFragmentK problem := by
  simp only [inGlbJoinFragmentKB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfam, hshapes⟩, hcross⟩ := h
  refine ⟨hfam, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, groupCross_of_B hcross⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFlexK (S := setting) e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfK hd⟩

/-- **The glb-join fragment is decided in the tower.** -/
theorem glbJoinTower_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run glbJoinTowerSolver original larger = run glbJoinTowerSolver original fuel ∧
        ((∃ state finished, run glbJoinTowerSolver original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run glbJoinTowerSolver original larger = .refuted absent)) :=
  glbJoinK_decided TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerJoin_total (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

theorem glbJoinTower_principal {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), (frames setting.levels).Principal original answer :=
  principal_of_inGlbJoinFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerJoin_total (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

/-! ## Incomparable codomains together with incomparable domains -/

/-- `U_{b+1}` and `U_{max (a+1) (b+1)}`. -/
abbrev UbSucc : Tower.Head := .sort (.succ (.param 1))
abbrev UabSucc : Tower.Head := .sort (.max (.succ (.param 0)) (.succ (.param 1)))

def twinX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U1 Ua1) (by decide +kernel)
abbrev ctxTwin1 := extend (empty setting.R) twinX
def twinY : TypeOver ctxTwin1 := formIn ctxTwin1 (bin U1 U0 UbSucc) (by decide +kernel)
/-- `X : U0 → U1 → U_{a+1}, Y : U1 → U0 → U_{b+1}`. -/
abbrev ctxTwin := extend ctxTwin1 twinY
def twinType : TypeOver ctxTwin := formIn ctxTwin (bin U0 U0 UabSucc) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U_{max (a+1) (b+1)}`. -/
def twinEquation : Equation (TotalTerm ctxTwin) :=
  (termIn ctxTwin twinType (etaBin 3) (by decide +kernel), termIn ctxTwin twinType (etaBin 2) (by decide +kernel))

def twinStore : EquationStore (TotalTerm ctxTwin) := [twinEquation]

theorem twinAnnotation_code : twinEquation.1.1.code = famCode [U0, U0] UabSucc := by decide +kernel
theorem twinLeft_code : twinEquation.1.2.code = etaExp 2 (.var (1 : Fin ctxTwin.arity)) := by decide +kernel
theorem twinRight_code : twinEquation.2.2.code = etaExp 2 (.var (0 : Fin ctxTwin.arity)) := by decide +kernel
theorem twinX_declared : Ctx.lookup ctxTwin.raw 1 = famCode [U0, U1] Ua1 := by decide +kernel
theorem twinY_declared : Ctx.lookup ctxTwin.raw 0 = famCode [U1, U0] UbSucc := by decide +kernel

/-- **Neither the codomains nor the domains are comparable**, and every position is usable on both sides. -/
theorem twin_incomparable :
    ¬ setting.R.cumulative Ua1 UbSucc ∧ ¬ setting.R.cumulative UbSucc Ua1 ∧ ¬ setting.R.cumulative U1 U0 ∧
      setting.R.cumulative U0 Ua1 ∧ setting.R.cumulative U1 Ua1 ∧ setting.R.cumulative U0 UbSucc ∧
      setting.R.cumulative U1 UbSucc := by
  decide +kernel

/-- **The store lies in the glb-join fragment.** -/
theorem twin_inside : InGlbJoinFragmentK twinStore := inGlbJoinFragmentK_of_B (by decide +kernel)

/-- **It lies outside the join-meet fragment**: the codomains are incomparable. -/
theorem twin_not_joinMeet_inside : ¬ InJoinMeetFragmentK twinStore := by
  intro inside
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes twinEquation List.mem_cons_self
  have together := grouped twinEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans twinAnnotation_code)
  have sl := v.side_left.symm.trans twinLeft_code
  have sr := v.side_right.symm.trans twinRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxTwin.raw v.left = famCode [U0, U1] Ua1 := by rw [hl]; exact twinX_declared
  have dr : Ctx.lookup ctxTwin.raw v.right = famCode [U1, U0] UbSucc := by rw [hr]; exact twinY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := (compat v.left v.right different together [U0, U1] Ua1 [U1, U0] UbSucc dl dr).1
  exact absurd compatible (by decide +kernel)

/-- **The join-meet solver is stuck on it.** -/
theorem twin_joinMeet_stuck : isStuck (run joinMeetTowerSolver twinStore 1) = true := by decide +kernel

/-- **The glb-join solver commits**: `Y` declared again at the least upper bounds `U1 → U1` of the domains and the
greatest lower bound of the codomains, `X, Y := λ x y. Y x y`. -/
theorem twin_committed : (run glbJoinTowerSolver twinStore 2).readout = .commit := by decide +kernel

theorem twin_suspended_before : (run glbJoinTowerSolver twinStore 1).readout = .suspended := by decide +kernel

/-- **Its answer is principal.** -/
theorem twin_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTwin), (frames setting.levels).Principal twinStore answer :=
  glbJoinTower_principal twin_inside

/-! ## A position whose domain exceeds its codomain -/

def spareX : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.head U0)) (by decide +kernel)
abbrev ctxSpare1 := extend (empty setting.R) spareX
def spareY : TypeOver ctxSpare1 := formIn ctxSpare1 (.pi (.head U2) (.head U1)) (by decide +kernel)
/-- `X : U0 → U0, Y : U2 → U1`. -/
abbrev ctxSpare := extend ctxSpare1 spareY
def spareType : TypeOver ctxSpare := formIn ctxSpare (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1`. -/
def spareEquation : Equation (TotalTerm ctxSpare) :=
  (termIn ctxSpare spareType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxSpare spareType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def spareStore : EquationStore (TotalTerm ctxSpare) := [spareEquation]

theorem spareAnnotation_code : spareEquation.1.1.code = famCode [U0] U1 := by decide +kernel
theorem spareLeft_code : spareEquation.1.2.code = etaExp 1 (.var (1 : Fin ctxSpare.arity)) := by decide +kernel
theorem spareRight_code : spareEquation.2.2.code = etaExp 1 (.var (0 : Fin ctxSpare.arity)) := by decide +kernel
theorem spareX_declared : Ctx.lookup ctxSpare.raw 1 = famCode [U0] U0 := by decide +kernel
theorem spareY_declared : Ctx.lookup ctxSpare.raw 0 = famCode [U2] U1 := by decide +kernel

/-- **The join with a meet's crossing fails, and the position is not usable on `Y`'s side**: `U2` is neither `X`'s
domain nor below `U0`, and `U2` is not below `U1`. -/
theorem spare_crossing_fails :
    ¬ CrossOK setting.R U0 [U0] [U2] ∧ ¬ setting.R.cumulative U2 U1 ∧ CrossAt setting.R U0 U1 U0 U2 := by
  decide +kernel

theorem spare_inside : InGlbJoinFragmentK spareStore := inGlbJoinFragmentK_of_B (by decide +kernel)

/-- **It lies outside the join-meet fragment.** -/
theorem spare_not_joinMeet_inside : ¬ InJoinMeetFragmentK spareStore := by
  intro inside
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes spareEquation List.mem_cons_self
  have together := grouped spareEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans spareAnnotation_code)
  have sl := v.side_left.symm.trans spareLeft_code
  have sr := v.side_right.symm.trans spareRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxSpare.raw v.left = famCode [U0] U0 := by rw [hl]; exact spareX_declared
  have dr : Ctx.lookup ctxSpare.raw v.right = famCode [U2] U1 := by rw [hr]; exact spareY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := (compat v.left v.right different together [U0] U0 [U2] U1 dl dr).1
  exact absurd compatible (by decide +kernel)

theorem spare_joinMeet_stuck : isStuck (run joinMeetTowerSolver spareStore 1) = true := by decide +kernel

/-- **The glb-join solver commits**: `Y` declared again at `U2 → U0`. -/
theorem spare_committed : (run glbJoinTowerSolver spareStore 2).readout = .commit := by decide +kernel

theorem spare_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxSpare), (frames setting.levels).Principal spareStore answer :=
  glbJoinTower_principal spare_inside

/-! ## Cumulatively equivalent, different codomains -/

/-- `U_{max 0 a}`: the tower's greatest lower bound of `U_a` and `U_{a+1}`. -/
abbrev U0a : Tower.Head := .sort (.max (.const 0) (.param 0))

def equivX : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.head Ua)) (by decide +kernel)
abbrev ctxEquiv1 := extend (empty setting.R) equivX
def equivY : TypeOver ctxEquiv1 := formIn ctxEquiv1 (.pi (.head U0) (.head U0a)) (by decide +kernel)
/-- `X : U0 → U_a, Y : U0 → U_{max 0 a}`. -/
abbrev ctxEquiv := extend ctxEquiv1 equivY
def equivType : TypeOver ctxEquiv := formIn ctxEquiv (.pi (.head U0) (.head U0a)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max 0 a}`. -/
def equivEquation : Equation (TotalTerm ctxEquiv) :=
  (termIn ctxEquiv equivType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxEquiv equivType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def equivStore : EquationStore (TotalTerm ctxEquiv) := [equivEquation]

theorem equivAnnotation_code : equivEquation.1.1.code = famCode [U0] U0a := by decide +kernel
theorem equivLeft_code : equivEquation.1.2.code = etaExp 1 (.var (1 : Fin ctxEquiv.arity)) := by decide +kernel
theorem equivRight_code : equivEquation.2.2.code = etaExp 1 (.var (0 : Fin ctxEquiv.arity)) := by decide +kernel
theorem equivX_declared : Ctx.lookup ctxEquiv.raw 1 = famCode [U0] Ua := by decide +kernel
theorem equivY_declared : Ctx.lookup ctxEquiv.raw 0 = famCode [U0] U0a := by decide +kernel

/-- **The codomains are cumulatively equivalent and different.** -/
theorem equiv_codomains : setting.R.cumulative Ua U0a ∧ setting.R.cumulative U0a Ua ∧ Ua ≠ U0a := by
  decide +kernel

/-- **The join-meet fragment excludes the store**, by its condition that equivalent codomains are equal. -/
theorem equiv_not_joinMeet_inside : ¬ InJoinMeetFragmentK equivStore := by
  intro inside
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes equivEquation List.mem_cons_self
  have together := grouped equivEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans equivAnnotation_code)
  have sl := v.side_left.symm.trans equivLeft_code
  have sr := v.side_right.symm.trans equivRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxEquiv.raw v.left = famCode [U0] Ua := by rw [hl]; exact equivX_declared
  have dr : Ctx.lookup ctxEquiv.raw v.right = famCode [U0] U0a := by rw [hr]; exact equivY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have antisym := (compat v.left v.right different together [U0] Ua [U0] U0a dl dr).2
  exact equiv_codomains.2.2 (antisym equiv_codomains.1 equiv_codomains.2.1)

/-- **The glb-join fragment contains it**: its condition compares no codomains. -/
theorem equiv_inside : InGlbJoinFragmentK equivStore := inGlbJoinFragmentK_of_B (by decide +kernel)

theorem equiv_committed : (run glbJoinTowerSolver equivStore 2).readout = .commit := by decide +kernel

/-- The join-meet solver commits on it as well: the excluded condition was not needed by its rounds here. -/
theorem equiv_joinMeet_committed : (run joinMeetTowerSolver equivStore 2).readout = .commit := by decide +kernel

theorem equiv_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxEquiv), (frames setting.levels).Principal equivStore answer :=
  glbJoinTower_principal equiv_inside

/-! ## The earlier fragments' stores -/

theorem twist_insideGJ : InGlbJoinFragmentK twistStore := inGlbJoinFragmentK_of_joinMeet TowerModel.algebra twist_insideJM

theorem twist_committedGJ : (run glbJoinTowerSolver twistStore 2).readout = .commit := by decide +kernel

theorem meetTwist_insideGJ : InGlbJoinFragmentK meetTwistStore :=
  inGlbJoinFragmentK_of_joinMeet TowerModel.algebra meetTwist_insideJM

theorem meetTwist_committedGJ : (run glbJoinTowerSolver meetTwistStore 2).readout = .commit := by decide +kernel

theorem triple_insideGJ : InGlbJoinFragmentK tripleStore := inGlbJoinFragmentK_of_joinMeet TowerModel.algebra triple_inside

theorem triple_committedGJ : (run glbJoinTowerSolver tripleStore 3).readout = .commit := by decide +kernel

theorem binMeet_insideGJ : InGlbJoinFragmentK binMeetStore :=
  inGlbJoinFragmentK_of_joinMeet TowerModel.algebra binMeet_insideJM

theorem binMeet_committedGJ : (run glbJoinTowerSolver binMeetStore 2).readout = .commit := by decide +kernel

/-- The store of two level variables, decided by the solver of glb groups, is inside and commits. -/
theorem level_insideGJ : InGlbJoinFragmentK levelStore := inGlbJoinFragmentK_of_B (by decide +kernel)

theorem level_committedGJ : (run glbJoinTowerSolver levelStore 2).readout = .commit := by decide +kernel

/-! ## Just outside: the cross store -/

/-- **The cross store fails the condition at its one position**, usable on both sides: `U1` is not below `U0`. -/
theorem cross_not_crossAt : ¬ CrossAt setting.R U0 U1 U0 U1 := by decide +kernel

/-- **It lies outside the glb-join fragment; it is solvable and has no principal answer.** -/
theorem cross_not_glbJoin_inside : ¬ InGlbJoinFragmentK crossStore ∧ (frames setting.levels).Solvable crossStore ∧
    ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer := by
  refine ⟨fun inside => ?_, cross_identity, fun answer => cross_no_principal answer⟩
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have together := grouped crossEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans crossAnnotation_code)
  have sl := v.side_left.symm.trans crossLeft_code
  have sr := v.side_right.symm.trans crossRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxCross.raw v.left = famCode [U0] U0 := by rw [hl]; exact crossX_declared
  have dr : Ctx.lookup ctxCross.raw v.right = famCode [U1] U1 := by rw [hr]; exact crossY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have crossing := compat v.left v.right different together [U0] U0 [U1] U1 dl dr rfl
  cases crossing with
  | cons here _ => exact cross_not_crossAt here

theorem cross_glbJoin_stuck : isStuck (run glbJoinTowerSolver crossStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
