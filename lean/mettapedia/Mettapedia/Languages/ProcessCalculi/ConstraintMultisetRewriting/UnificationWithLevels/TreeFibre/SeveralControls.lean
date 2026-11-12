import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls

/-!
# Controls for several parameters, in the tree's tower

The solver of meet groups with several parameters at the tower's facts (`meetTowerSolverK`); membership, readings
and runs evaluated by the kernel.

* **Two parameters, raised** (`binFit_inside`, `binFit_unread`, `binFit_committed`, `binFit_principal`): over
  `X : U0 → U0 → U1` and `Y : U1 → U1 → U0`, `λ x y. X x y ≐ λ x y. Y x y`. `Y` fits `X`; the unary reader does
  not read the equation; the solver raises `X := λ x y. Y x y` and commits.
* **Two parameters, the true meet** (`binMeet_*`): `X : U0 → U0 → U2`, `Y : U1 → U1 → U3`. Neither fits; they meet at
  `U1 → U1 → U2`; the solver lowers `Y` and raises `X`, and commits.
* **Mixed domains** (`binMixed_*`): `X : U0 → U1 → U2`, `Y : U1 → U1 → U3`, at `Π (x : U0) (y : U1). U3`.
* **One parameter is the special case** (`meet_insideK`, `meet_committedK`): the unary store of the true meet is in
  the fragment and decided by the same solver.
* **Just outside: the crossing** (`cross_not_meet_insideK`, `cross_meet_stuckK`, `cross_postponed_by_meetK`): the
  cross store fails only the crossing, has no principal answer (`crossing_needed`), lies outside, the solver is
  stuck, and every run stops postponed.
* **Just outside: domains not pointwise comparable** (`twist_*`): `X : U0 → U1 → U1`, `Y : U1 → U0 → U1`. The store is
  solvable, lies outside, and the solver is stuck on it; whether it has a principal answer is not decided here.
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

/-- The solver of meet groups with several parameters at the tower's facts. -/
def meetTowerSolverK : ContextualDependentWorklist.Solver setting.levels :=
  meetGroupSolverK (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete

/-- `Π (x : a) (y : b). c`. -/
abbrev bin {n : Nat} (a b c : Tower.Head) : Tm Tower.Head n := .pi (.head a) (.pi (.head b) (.head c))

/-- `λ x y. Z x y`, for the unknown `Z` at index `i` under the two binders. -/
abbrev etaBin {n : Nat} (i : Fin (n + 2)) : Tm Tower.Head n := .lam (.lam (.app (.app (.var i) (.var 1)) (.var 0)))

/-! ## Two parameters, raised -/

def binFitX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U0 U1) (by decide +kernel)
abbrev ctxBinFit1 := extend (empty setting.R) binFitX
def binFitY : TypeOver ctxBinFit1 := formIn ctxBinFit1 (bin U1 U1 U0) (by decide +kernel)
/-- `X : U0 → U0 → U1, Y : U1 → U1 → U0`. -/
abbrev ctxBinFit := extend ctxBinFit1 binFitY
def binFitType : TypeOver ctxBinFit := formIn ctxBinFit (bin U0 U0 U1) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U1`. -/
def binFitEquation : Equation (TotalTerm ctxBinFit) :=
  (termIn ctxBinFit binFitType (etaBin 3) (by decide +kernel),
    termIn ctxBinFit binFitType (etaBin 2) (by decide +kernel))

def binFitStore : EquationStore (TotalTerm ctxBinFit) := [binFitEquation]

theorem binFit_inside : InMeetFragmentK binFitStore := inMeetFragmentK_of_B (by decide +kernel)

/-- **The unary reader does not read it.** -/
theorem binFit_unread : (readFitData (S := setting) binFitEquation).isNone = true := by decide +kernel

/-- **The solver commits**: `X := λ x y. Y x y`. -/
theorem binFit_committed : (run meetTowerSolverK binFitStore 2).readout = .commit := by decide +kernel

theorem binFit_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBinFit), (frames setting.levels).Principal binFitStore answer :=
  principal_of_inMeetFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete binFit_inside

/-! ## Two parameters, the true meet -/

def binMeetX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U0 U2) (by decide +kernel)
abbrev ctxBinMeet1 := extend (empty setting.R) binMeetX
def binMeetY : TypeOver ctxBinMeet1 := formIn ctxBinMeet1 (bin U1 U1 U3) (by decide +kernel)
/-- `X : U0 → U0 → U2, Y : U1 → U1 → U3`. -/
abbrev ctxBinMeet := extend ctxBinMeet1 binMeetY
def binMeetType : TypeOver ctxBinMeet := formIn ctxBinMeet (bin U0 U0 U3) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U3`. -/
def binMeetEquation : Equation (TotalTerm ctxBinMeet) :=
  (termIn ctxBinMeet binMeetType (etaBin 3) (by decide +kernel),
    termIn ctxBinMeet binMeetType (etaBin 2) (by decide +kernel))

def binMeetStore : EquationStore (TotalTerm ctxBinMeet) := [binMeetEquation]

theorem binMeet_inside : InMeetFragmentK binMeetStore := inMeetFragmentK_of_B (by decide +kernel)

/-- **Neither unknown fits the other**: `Y`'s codomain `U3` does not lie below `X`'s `U2`, and `Y`'s domains `U1`
do not lie below `X`'s `U0`. -/
theorem binMeet_no_fit : ¬ setting.R.cumulative U3 U2 ∧ ¬ setting.R.cumulative U1 U0 := by decide

/-- **The solver commits**: `Y` lowered to `U1 → U1 → U2`, then `X := λ x y. Y x y`. -/
theorem binMeet_committed : (run meetTowerSolverK binMeetStore 2).readout = .commit := by decide +kernel

theorem binMeet_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBinMeet), (frames setting.levels).Principal binMeetStore answer :=
  principal_of_inMeetFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete binMeet_inside

/-! ## Mixed domains -/

def binMixedX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U1 U2) (by decide +kernel)
abbrev ctxBinMixed1 := extend (empty setting.R) binMixedX
def binMixedY : TypeOver ctxBinMixed1 := formIn ctxBinMixed1 (bin U1 U1 U3) (by decide +kernel)
/-- `X : U0 → U1 → U2, Y : U1 → U1 → U3`. -/
abbrev ctxBinMixed := extend ctxBinMixed1 binMixedY
def binMixedType : TypeOver ctxBinMixed := formIn ctxBinMixed (bin U0 U1 U3) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x : U0) (y : U1). U3`. -/
def binMixedStore : EquationStore (TotalTerm ctxBinMixed) :=
  [(termIn ctxBinMixed binMixedType (etaBin 3) (by decide +kernel),
    termIn ctxBinMixed binMixedType (etaBin 2) (by decide +kernel))]

theorem binMixed_inside : InMeetFragmentK binMixedStore := inMeetFragmentK_of_B (by decide +kernel)

/-- **The solver commits**: `Y` lowered to `U1 → U1 → U2`, then `X := λ x y. Y x y`. -/
theorem binMixed_committed : (run meetTowerSolverK binMixedStore 2).readout = .commit := by decide +kernel

theorem binMixed_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBinMixed), (frames setting.levels).Principal binMixedStore answer :=
  principal_of_inMeetFragmentK TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete binMixed_inside

/-! ## One parameter is the special case -/

theorem meet_insideK : InMeetFragmentK meetStore := inMeetFragmentK_of_B (by decide +kernel)

theorem meet_committedK : (run meetTowerSolverK meetStore 2).readout = .commit := by decide +kernel

theorem chain_committedK : (run meetTowerSolverK chainStore 3).readout = .commit := by decide +kernel

/-! ## Just outside: the crossing -/

theorem crossAnnotation_code : crossEquation.1.1.code = famCode [U0] U1 := by decide +kernel

/-- **The cross store lies outside the fragment with several parameters.** -/
theorem cross_not_meet_insideK : ¬ InMeetFragmentK crossStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
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
  have compatible := comparable v.left v.right different together [U0] U0 [U1] U1 dl dr
  exact absurd compatible (by decide)

theorem cross_meet_stuckK : isStuck (run meetTowerSolverK crossStore 1) = true := by decide +kernel

theorem cross_postponed_by_meetK :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run meetTowerSolverK crossStore larger = run meetTowerSolverK crossStore fuel ∧
      ∃ state, run meetTowerSolverK crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames setting.levels) crossStore state.answer state.remaining ∧
        DependentFibre.NoPrincipal setting.levels state.remaining :=
  DependentFibre.cross_run_postponed meetTowerSolverK

/-! ## Just outside: domains not pointwise comparable -/

def twistX : TypeOver (empty setting.R) := formIn (empty setting.R) (bin U0 U1 U1) (by decide +kernel)
abbrev ctxTwist1 := extend (empty setting.R) twistX
def twistY : TypeOver ctxTwist1 := formIn ctxTwist1 (bin U1 U0 U1) (by decide +kernel)
/-- `X : U0 → U1 → U1, Y : U1 → U0 → U1`. -/
abbrev ctxTwist := extend ctxTwist1 twistY
def twistType : TypeOver ctxTwist := formIn ctxTwist (bin U0 U0 U1) (by decide +kernel)

/-- `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U1`. -/
def twistEquation : Equation (TotalTerm ctxTwist) :=
  (termIn ctxTwist twistType (etaBin 3) (by decide +kernel),
    termIn ctxTwist twistType (etaBin 2) (by decide +kernel))

def twistStore : EquationStore (TotalTerm ctxTwist) := [twistEquation]

/-- `X := λ x y. x, Y := λ x y. x`. -/
def twistFirst : empty setting.R ⟶ ctxTwist :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) twistX (.lam (.lam (.var 1))) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxTwist1 (termIn ctxTwist1 twistY (.lam (.lam (.var 1))) (by decide +kernel)).2

/-- **It is solvable**, by the first projections. -/
theorem twist_solvable : (frames setting.levels).Solvable twistStore :=
  solvable_by twistFirst twistEquation.1.2 twistEquation.2.2 (by decide +kernel)

theorem twistAnnotation_code : twistEquation.1.1.code = famCode [U0, U0] U1 := by decide +kernel
theorem twistLeft_code : twistEquation.1.2.code = etaExp 2 (.var (1 : Fin ctxTwist.arity)) := by decide +kernel
theorem twistRight_code : twistEquation.2.2.code = etaExp 2 (.var (0 : Fin ctxTwist.arity)) := by decide +kernel
theorem twistX_declared : Ctx.lookup ctxTwist.raw 1 = famCode [U0, U1] U1 := by decide +kernel
theorem twistY_declared : Ctx.lookup ctxTwist.raw 0 = famCode [U1, U0] U1 := by decide +kernel

/-- **It lies outside the fragment**: the domains `U0, U1` and `U1, U0` are not pointwise comparable. -/
theorem twist_not_inside : ¬ InMeetFragmentK twistStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes twistEquation List.mem_cons_self
  have together := grouped twistEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans twistAnnotation_code)
  have sl := v.side_left.symm.trans twistLeft_code
  have sr := v.side_right.symm.trans twistRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxTwist.raw v.left = famCode [U0, U1] U1 := by rw [hl]; exact twistX_declared
  have dr : Ctx.lookup ctxTwist.raw v.right = famCode [U1, U0] U1 := by rw [hr]; exact twistY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := comparable v.left v.right different together [U0, U1] U1 [U1, U0] U1 dl dr
  exact absurd compatible (by decide)

/-- **The solver is stuck on it.** -/
theorem twist_stuck : isStuck (run meetTowerSolverK twistStore 1) = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
