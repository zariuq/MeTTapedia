import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinSolverControls

/-!
# Controls: the join with a meet in the tree's tower

* **Twisted domains with two codomains** (`meetTwist_principal`): over `X : U0 → U1 → U1` and `Y : U1 → U0 → U2`,
  the store `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U2` has a principal answer: `Y` declared again at
  `U1 → U1 → U1`, and `X, Y := λ x y. Y x y`. The crossing holds: the first domain is raised to `U1`, below `X`'s
  codomain `U1`; the second is `X`'s own. The store lies outside the fragment of meet groups (incomparable domains) and
  outside the join fragment (two codomains).
* **The true meet is an instance** (`binMeet_joinMeet_principal`): the store of `X : U0 → U0 → U2` and
  `Y : U1 → U1 → U3`, decided by the solver of meet groups, is solved by the same rule.
* **The crossing cannot be dropped** (`cross_no_crossing`): the cross store fails it for every least upper bound of its
  domains, and has no principal answer (`crossing_needed`).
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

/-! ## Twisted domains with two codomains -/

def meetTwistX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U1 U1) (by decide +kernel)
abbrev ctxMeetTwist1 := extend (empty setting.R) meetTwistX
def meetTwistY : TypeOver ctxMeetTwist1 := formIn ctxMeetTwist1 (bin U1 U0 U2) (by decide +kernel)
/-- `X : U0 → U1 → U1, Y : U1 → U0 → U2`. -/
abbrev ctxMeetTwist := extend ctxMeetTwist1 meetTwistY
def meetTwistType : TypeOver ctxMeetTwist := formIn ctxMeetTwist (bin U0 U0 U2) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U2`. -/
def meetTwistEquation : Equation (TotalTerm ctxMeetTwist) :=
  (termIn ctxMeetTwist meetTwistType (etaBin 3) (by decide +kernel),
    termIn ctxMeetTwist meetTwistType (etaBin 2) (by decide +kernel))

def meetTwistStore : EquationStore (TotalTerm ctxMeetTwist) := [meetTwistEquation]

theorem meetTwistAnnotation_left : meetTwistEquation.1.1.code = famCode [U0, U0] U2 := by decide +kernel
theorem meetTwistAnnotation_right : meetTwistEquation.2.1.code = famCode [U0, U0] U2 := by decide +kernel
theorem meetTwistLeft_code : meetTwistEquation.1.2.code = etaExp 2 (.var (1 : Fin ctxMeetTwist.arity)) := by
  decide +kernel
theorem meetTwistRight_code : meetTwistEquation.2.2.code = etaExp 2 (.var (0 : Fin ctxMeetTwist.arity)) := by
  decide +kernel
theorem meetTwistX_declared : Ctx.lookup ctxMeetTwist.raw 1 = famCode [U0, U1] U1 := by decide +kernel
theorem meetTwistY_declared : Ctx.lookup ctxMeetTwist.raw 0 = famCode [U1, U0] U2 := by decide +kernel

/-- **The view**: `X` on the left with the smaller codomain `U1`, `Y` on the right with `U2`. -/
def meetTwistViewK : FlexK (S := setting) meetTwistEquation where
  ps := [U0, U0]
  q := U2
  left := 1
  right := 0
  psl := [U0, U1]
  cl := U1
  psr := [U1, U0]
  cr := U2
  annotation_left := meetTwistAnnotation_left
  annotation_right := meetTwistAnnotation_right
  side_left := meetTwistLeft_code
  side_right := meetTwistRight_code
  declared_left := meetTwistX_declared
  declared_right := meetTwistY_declared
  universes := by decide
  universes_left := by decide
  universes_right := by decide
  universe_q := by decide
  universe_cl := by decide
  universe_cr := by decide
  domain_left := .cons (by decide) (.cons (by decide) .nil)
  domain_right := .cons (by decide) (.cons (by decide) .nil)
  codomain_left := by decide
  codomain_right := by decide

theorem meetTwistFamilies : Miller.Families (S := setting) ctxMeetTwist := by decide +kernel

theorem meetTwist_low : setting.R.cumulative meetTwistViewK.cl meetTwistViewK.cr := by decide

/-- **The crossing**: the first domain is raised to `U1`, below `X`'s codomain `U1`; the second is `X`'s own. -/
theorem meetTwistCrosses : CrossesK setting.R U1 [U0, U1] [U1, U1] := .lower (by decide) (.keep .nil)

/-- **The answer**: `Y` declared again at `U1 → U1 → U1`, and `X, Y := λ x y. Y x y`. -/
abbrev meetTwistAnswer :=
  joinMKHom ctxMeetTwist meetTwistFamilies meetTwistViewK twistJoins meetTwistViewK.universe_cl
    (setting.levels.cumulative_refl meetTwistViewK.universe_cl) meetTwist_low

theorem meetTwist_joined :
    Ctx.lookup (joinedMK ctxMeetTwist meetTwistFamilies meetTwistViewK twistJoins meetTwistViewK.universe_cl).raw 0 =
      famCode [U1, U1] U1 :=
  joinedMK_self ctxMeetTwist meetTwistFamilies meetTwistViewK twistJoins meetTwistViewK.universe_cl

theorem meetTwist_value :
    meetTwistAnswer.substitution 1 = etaExp 2 (.var 0) ∧ meetTwistAnswer.substitution 0 = etaExp 2 (.var 0) :=
  ⟨rfl, rfl⟩

theorem meetTwist_exact : Exact (frames setting.levels) meetTwistStore meetTwistAnswer [] :=
  joinMeetK_exact TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique meetTwistFamilies meetTwistViewK meetTwist_low twistJoins
    meetTwistCrosses []

/-- **Twisted domains with two codomains have a principal answer.** -/
theorem meetTwist_principal : (frames setting.levels).Principal meetTwistStore meetTwistAnswer :=
  exact_nil_iff_principal.mp meetTwist_exact

/-- **It lies outside the fragment of meet groups**: the domains `U0, U1` and `U1, U0` are not comparable. -/
theorem meetTwist_not_meet_inside : ¬ InMeetFragmentK meetTwistStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes meetTwistEquation List.mem_cons_self
  have together := grouped meetTwistEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans meetTwistAnnotation_left)
  have sl := v.side_left.symm.trans meetTwistLeft_code
  have sr := v.side_right.symm.trans meetTwistRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxMeetTwist.raw v.left = famCode [U0, U1] U1 := by rw [hl]; exact meetTwistX_declared
  have dr : Ctx.lookup ctxMeetTwist.raw v.right = famCode [U1, U0] U2 := by rw [hr]; exact meetTwistY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := comparable v.left v.right different together [U0, U1] U1 [U1, U0] U2 dl dr
  exact absurd compatible (by decide)

/-- **It lies outside the join fragment**: the two codomains are `U1` and `U2`. -/
theorem meetTwist_not_join_inside : ¬ InJoinFragmentK meetTwistStore := by
  intro inside
  obtain ⟨v⟩ := inside.shapes meetTwistEquation List.mem_cons_self
  have codomains := inside.codomains meetTwistEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans meetTwistAnnotation_left)
  have sl := v.side_left.symm.trans meetTwistLeft_code
  have sr := v.side_right.symm.trans meetTwistRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxMeetTwist.raw v.left = famCode v.psl v.cl := v.declared_left
  have dr : Ctx.lookup ctxMeetTwist.raw v.right = famCode v.psr v.cr := v.declared_right
  rw [hl, meetTwistX_declared] at dl
  rw [hr, meetTwistY_declared] at dr
  have cl := (famCode_inj dl).2
  have cr := (famCode_inj dr).2
  rw [← cl, ← cr] at codomains
  exact absurd codomains (by decide)

/-! ## The true meet is an instance -/

theorem binMeetAnnotation_left : binMeetEquation.1.1.code = famCode [U0, U0] U3 := by decide +kernel
theorem binMeetAnnotation_right : binMeetEquation.2.1.code = famCode [U0, U0] U3 := by decide +kernel
theorem binMeetLeft_code : binMeetEquation.1.2.code = etaExp 2 (.var (1 : Fin ctxBinMeet.arity)) := by
  decide +kernel
theorem binMeetRight_code : binMeetEquation.2.2.code = etaExp 2 (.var (0 : Fin ctxBinMeet.arity)) := by
  decide +kernel
theorem binMeetX_declared : Ctx.lookup ctxBinMeet.raw 1 = famCode [U0, U0] U2 := by decide +kernel
theorem binMeetY_declared : Ctx.lookup ctxBinMeet.raw 0 = famCode [U1, U1] U3 := by decide +kernel

def binMeetViewK : FlexK (S := setting) binMeetEquation where
  ps := [U0, U0]
  q := U3
  left := 1
  right := 0
  psl := [U0, U0]
  cl := U2
  psr := [U1, U1]
  cr := U3
  annotation_left := binMeetAnnotation_left
  annotation_right := binMeetAnnotation_right
  side_left := binMeetLeft_code
  side_right := binMeetRight_code
  declared_left := binMeetX_declared
  declared_right := binMeetY_declared
  universes := by decide
  universes_left := by decide
  universes_right := by decide
  universe_q := by decide
  universe_cl := by decide
  universe_cr := by decide
  domain_left := .cons (by decide) (.cons (by decide) .nil)
  domain_right := .cons (by decide) (.cons (by decide) .nil)
  codomain_left := by decide
  codomain_right := by decide

theorem binMeet_comparable :
    (JoinsK setting.R [U0, U0] [U1, U1] [U1, U1] ∧ CrossesK setting.R U2 [U0, U0] [U1, U1]) :=
  joins_of_above (.cons (by decide) (.cons (by decide) .nil)) (by decide)
    (fun p member => by
      rcases List.mem_cons.mp member with rfl | member
      · decide
      · rcases List.mem_cons.mp member with rfl | member
        · decide
        · cases member)

theorem binMeet_low : setting.R.cumulative binMeetViewK.cl binMeetViewK.cr := by decide

theorem binMeetFamilies : Miller.Families (S := setting) ctxBinMeet := by decide +kernel

/-- **The true meet, by the join with a meet**: `Y` declared again at `U1 → U1 → U2`. -/
theorem binMeet_joinMeet_principal :
    (frames setting.levels).Principal binMeetStore
      (joinMKHom ctxBinMeet binMeetFamilies binMeetViewK binMeet_comparable.1 binMeetViewK.universe_cl
        (setting.levels.cumulative_refl binMeetViewK.universe_cl) binMeet_low) :=
  exact_nil_iff_principal.mp
    (joinMeetK_exact TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentNormalCheckingTower.head_typing_unique binMeetFamilies binMeetViewK binMeet_low
      binMeet_comparable.1 binMeet_comparable.2 [])

/-! ## The crossing cannot be dropped -/

/-- **The cross store fails the crossing** for every least upper bound of its domains `U0` and `U1`: the joined
domain is not `X`'s `U0`, and it does not lie below `X`'s codomain `U0`. It has no principal answer. -/
theorem cross_no_crossing :
    (∀ w, IsLub setting.R w U0 U1 → ¬ CrossesK setting.R U0 [U0] [w]) ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer := by
  refine ⟨fun w lub crosses => ?_, fun answer => crossing_needed.2.2 answer⟩
  cases crosses with
  | keep _ => exact absurd lub.2.1 (by decide)
  | lower below _ => exact absurd (TowerModel.algebra.trans lub.2.1 below) (by decide)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
