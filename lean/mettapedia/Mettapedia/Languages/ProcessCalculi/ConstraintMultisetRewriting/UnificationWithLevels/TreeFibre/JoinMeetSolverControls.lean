import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetControls

/-!
# Controls: the join-meet solver in the tree's tower

* **The tower's join function keeps the larger universe** (`towerJoin_bias`).
* **Twisted domains, decided** (`meetTwist_insideJM`, `meetTwist_committedJM`, `twist_insideJM`,
  `twist_committedJM`): the stores of `JoinMeetControls` (two codomains) and `JoinControls` (one codomain) commit.
* **Three unknowns, two codomains, chained** (`triple_*`): `X : U0 → U0 → U1`, `Y : U0 → U1 → U2`,
  `W : U1 → U0 → U2`, with `λ x y. X x y ≐ λ x y. Y x y` and `λ x y. Y x y ≐ λ x y. W x y` at `Π (x y : U0). U2`.
  The first join with a meet redeclares `Y` at `U0 → U1 → U1`; the second equation, re-read, redeclares `W` at
  `U1 → U1 → U1`. The store lies outside the fragment of meet groups (`Y`, `W` incomparable) and outside the join
  fragment (two codomains).
* **The true meet** (`binMeet_insideJM`, `binMeet_committedJM`): the store of the fragment of meet groups commits.
* **Just outside: the cross store** (`cross_not_joinMeet_inside`, `cross_joinMeet_stuck`).
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

/-- The tower's join function keeps the larger of two comparable universes. -/
theorem towerJoin_bias : ∀ {u v : Tower.Head}, setting.R.isUniverse u → setting.R.isUniverse v →
    setting.R.cumulative v u → towerJoin u v = some u
  | .sort _, .sort _, _, _, le => by
      simp only [towerJoin]
      rw [if_pos le]
  | .legacyGround, _, hu, _, _ => absurd hu (by decide)
  | .sort _, .legacyGround, _, hv, _ => absurd hv (by decide)

/-- The join-meet solver at the tower's facts. -/
def joinMeetTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  joinMeetSolverK (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound towerJoin_bias

/-- Of two different declared families, compatible and with equal codomains when equivalent, decided. -/
def groupCompatB {n : Nat} (Γ : Tower.Ctx n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    if i = j then true else
    match readFam (Ctx.lookup Γ i), readFam (Ctx.lookup Γ j) with
    | some a, some b => decide (CompatJ setting.R a.1 a.2 b.1 b.2) &&
        decide (setting.R.cumulative a.2 b.2 → setting.R.cumulative b.2 a.2 → a.2 = b.2)
    | _, _ => true

theorem groupCompat_of_B {Θ : Context setting.R} (h : groupCompatB Θ.raw = true) :
    GroupCompat Θ (fun _ => 0) := by
  intro i j ne _ psi ci psj cj hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  rw [if_neg ne, hi, hj, readFam_famCode, readFam_famCode] at hij
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
  exact hij

/-- **Membership in the join-meet fragment, decided**, with all unknowns in one group. -/
def inJoinMeetFragmentKB {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  decide (Miller.Families (S := setting) Θ) && problem.all (fun e => (readFlexK (S := setting) e).isSome) &&
    groupCompatB Θ.raw

theorem inJoinMeetFragmentK_of_B {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inJoinMeetFragmentKB problem = true) : InJoinMeetFragmentK problem := by
  simp only [inJoinMeetFragmentKB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfam, hshapes⟩, hcomp⟩ := h
  refine ⟨hfam, fun e member => ?_, ⟨fun _ => 0, fun _ _ _ => rfl, groupCompat_of_B hcomp⟩⟩
  have he := List.all_eq_true.mp hshapes e member
  cases hd : readFlexK (S := setting) e with
  | none => rw [hd] at he; cases he
  | some d => exact ⟨viewOfK hd⟩

/-- **The join-meet fragment is decided in the tower.** -/
theorem joinMeetTower_principal {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InJoinMeetFragmentK original) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), (frames setting.levels).Principal original answer :=
  principal_of_inJoinMeetFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound towerJoin_bias
    towerJoin_total inside

/-! ## Twisted domains with two codomains -/

theorem meetTwist_insideJM : InJoinMeetFragmentK meetTwistStore := inJoinMeetFragmentK_of_B (by decide +kernel)

theorem meetTwist_committedJM : (run joinMeetTowerSolver meetTwistStore 2).readout = .commit := by decide +kernel

/-- The twisted store of one codomain is inside as well, and commits. -/
theorem twist_insideJM : InJoinMeetFragmentK twistStore := inJoinMeetFragmentK_of_B (by decide +kernel)

theorem twist_committedJM : (run joinMeetTowerSolver twistStore 2).readout = .commit := by decide +kernel

/-! ## Three unknowns, two codomains, chained -/

def tripleX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U0 U1) (by decide +kernel)
abbrev ctxTriple1 := extend (empty setting.R) tripleX
def tripleY : TypeOver ctxTriple1 := formIn ctxTriple1 (bin U0 U1 U2) (by decide +kernel)
abbrev ctxTriple2 := extend ctxTriple1 tripleY
def tripleW : TypeOver ctxTriple2 := formIn ctxTriple2 (bin U1 U0 U2) (by decide +kernel)
/-- `X : U0 → U0 → U1, Y : U0 → U1 → U2, W : U1 → U0 → U2`. -/
abbrev ctxTriple := extend ctxTriple2 tripleW
def tripleType : TypeOver ctxTriple := formIn ctxTriple (bin U0 U0 U2) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U2`. -/
def tripleFirst : Equation (TotalTerm ctxTriple) :=
  (termIn ctxTriple tripleType (etaBin 4) (by decide +kernel),
    termIn ctxTriple tripleType (etaBin 3) (by decide +kernel))

/-- `λ x y. Y x y ≐ λ x y. W x y` at `Π (x y : U0). U2`. -/
def tripleSecond : Equation (TotalTerm ctxTriple) :=
  (termIn ctxTriple tripleType (etaBin 3) (by decide +kernel),
    termIn ctxTriple tripleType (etaBin 2) (by decide +kernel))

def tripleStore : EquationStore (TotalTerm ctxTriple) := [tripleFirst, tripleSecond]

theorem triple_inside : InJoinMeetFragmentK tripleStore := inJoinMeetFragmentK_of_B (by decide +kernel)

/-- **The join-meet solver commits**: two joins with a meet, the second equation re-read after the first. -/
theorem triple_committed : (run joinMeetTowerSolver tripleStore 3).readout = .commit := by decide +kernel

theorem triple_second_needed : (run joinMeetTowerSolver tripleStore 2).readout = .suspended := by decide +kernel

theorem triple_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTriple), (frames setting.levels).Principal tripleStore answer :=
  joinMeetTower_principal triple_inside

theorem tripleSecond_annotation : tripleSecond.1.1.code = famCode [U0, U0] U2 := by decide +kernel
theorem tripleSecond_left : tripleSecond.1.2.code = etaExp 2 (.var (1 : Fin ctxTriple.arity)) := by decide +kernel
theorem tripleSecond_right : tripleSecond.2.2.code = etaExp 2 (.var (0 : Fin ctxTriple.arity)) := by decide +kernel
theorem tripleY_declared : Ctx.lookup ctxTriple.raw 1 = famCode [U0, U1] U2 := by decide +kernel
theorem tripleW_declared : Ctx.lookup ctxTriple.raw 0 = famCode [U1, U0] U2 := by decide +kernel
theorem tripleFirst_annotation : tripleFirst.1.1.code = famCode [U0, U0] U2 := by decide +kernel
theorem tripleFirst_left : tripleFirst.1.2.code = etaExp 2 (.var (2 : Fin ctxTriple.arity)) := by decide +kernel
theorem tripleFirst_right : tripleFirst.2.2.code = etaExp 2 (.var (1 : Fin ctxTriple.arity)) := by decide +kernel
theorem tripleX_declared : Ctx.lookup ctxTriple.raw 2 = famCode [U0, U0] U1 := by decide +kernel

/-- **It lies outside the fragment of meet groups**: `Y` and `W` share an equation and their domains are not
comparable. -/
theorem triple_not_meet_inside : ¬ InMeetFragmentK tripleStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  have member : tripleSecond ∈ tripleStore := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨v⟩ := inside.shapes tripleSecond member
  have together := grouped tripleSecond member v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans tripleSecond_annotation)
  have sl := v.side_left.symm.trans tripleSecond_left
  have sr := v.side_right.symm.trans tripleSecond_right
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxTriple.raw v.left = famCode [U0, U1] U2 := by rw [hl]; exact tripleY_declared
  have dr : Ctx.lookup ctxTriple.raw v.right = famCode [U1, U0] U2 := by rw [hr]; exact tripleW_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := comparable v.left v.right different together [U0, U1] U2 [U1, U0] U2 dl dr
  exact absurd compatible (by decide)

/-- **It lies outside the join fragment**: `X` and `Y` have the codomains `U1` and `U2`. -/
theorem triple_not_join_inside : ¬ InJoinFragmentK tripleStore := by
  intro inside
  obtain ⟨v⟩ := inside.shapes tripleFirst List.mem_cons_self
  have codomains := inside.codomains tripleFirst List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans tripleFirst_annotation)
  have sl := v.side_left.symm.trans tripleFirst_left
  have sr := v.side_right.symm.trans tripleFirst_right
  rw [hps] at sl sr
  have hl : v.left = 2 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 1 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxTriple.raw v.left = famCode v.psl v.cl := v.declared_left
  have dr : Ctx.lookup ctxTriple.raw v.right = famCode v.psr v.cr := v.declared_right
  rw [hl, tripleX_declared] at dl
  rw [hr, tripleY_declared] at dr
  have cl := (famCode_inj dl).2
  have cr := (famCode_inj dr).2
  rw [← cl, ← cr] at codomains
  exact absurd codomains (by decide)

/-! ## The true meet -/

theorem binMeet_insideJM : InJoinMeetFragmentK binMeetStore := inJoinMeetFragmentK_of_B (by decide +kernel)

theorem binMeet_committedJM : (run joinMeetTowerSolver binMeetStore 2).readout = .commit := by decide +kernel

/-! ## Just outside: the cross store -/

/-- **The cross store lies outside**: its two unknowns are not compatible; it has no principal answer. -/
theorem cross_not_joinMeet_inside : ¬ InJoinMeetFragmentK crossStore ∧
    ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer := by
  refine ⟨fun inside => ?_, fun answer => crossing_needed.2.2 answer⟩
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
  have compatible := (compat v.left v.right different together [U0] U0 [U1] U1 dl dr).1
  exact absurd compatible (by decide)

theorem cross_joinMeet_stuck : isStuck (run joinMeetTowerSolver crossStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
