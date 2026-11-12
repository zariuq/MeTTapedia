import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitControls

/-!
# Controls for the true meet, in the tree's tower

All stores are in the tree's cumulative tower, with the solver of meet groups at the tower's own facts
(`meetTowerSolver`). Membership, readings and runs are evaluated by the kernel.

* **Neither unknown fits, and the meet decides** (`meet_inside`, `meet_not_fit`, `meet_fit_stuck`,
  `meet_committed`, `meet_principal`): over `X : U0 → U2` and `Y : U1 → U3`, the equation `λ x. X x ≐ λ x. Y x` at
  `Π (x : U0). U3`. `X` has the smaller domain and the smaller codomain, so neither fits the other: the store lies
  outside the fragment of fitting groups and that solver is stuck on it. `Y`'s domain `U1` lies below `X`'s
  codomain `U2`, so the two meet at `Π (x : U1). U2`: the store is in the fragment of meet groups, the solver lowers
  `Y` to the meet, raises `X := λ x. Y x`, and commits; the answer is principal.
* **Lowering below the meet loses a solution** (`overMeet_solution_models`, `over_meet_loses`): with `Y` declared
  at `U1 → U1`, one universe below the meet, the solution `X := λ x. U1, Y := λ x. U1` no longer factors.
* **Two meets in a chain** (`chain_inside`, `chain_committed`, `chain_principal`): adding `W : U2 → U4` and
  `λ x. Y x ≐ λ x. W x` at `Π (x : U1). U4`. After the first meet `Y` is `U1 → U2`, which meets `W` at `U2 → U2`.
* **Just outside: the crossing condition is needed** (`cross_only_crossing_fails`, `crossing_needed`,
  `cross_not_meet_inside`, `cross_meet_stuck`, `cross_postponed_by_meet`): on the cross store (`X : U0 → U0`,
  `Y : U1 → U1`) `X` has the smaller domain and the smaller codomain, and only the crossing fails, `U1` not below
  `U0`. The store is solvable and has no principal answer (the tree's `cross_no_principal`); it lies outside the
  fragment, the solver is stuck on it, and every run stops postponed.
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

/-- The solver of meet groups at the tower's facts. -/
def meetTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  meetGroupSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete

/-- `U3`, `U4`. -/
abbrev U3 : Tower.Head := .sort (.succ (.succ (.succ Tower.zero)))
abbrev U4 : Tower.Head := .sort (.succ (.succ (.succ (.succ Tower.zero))))

/-! ## Neither unknown fits, and the meet decides -/

/-- `U0 → U2`. -/
def familyLow : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.head U2)) (by decide +kernel)

/-- `X : U0 → U2`. -/
abbrev ctxLow := extend (empty setting.R) familyLow

/-- `U1 → U3`, over `X`. -/
def familyHigh : TypeOver ctxLow := formIn ctxLow (.pi (.head U1) (.head U3)) (by decide +kernel)

/-- `X : U0 → U2, Y : U1 → U3`. -/
abbrev ctxMeet := extend ctxLow familyHigh

/-- `Π (x : U0). U3`, over `X Y`. -/
def meetType : TypeOver ctxMeet := formIn ctxMeet (.pi (.head U0) (.head U3)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U3`. -/
def meetEquation : Equation (TotalTerm ctxMeet) :=
  (termIn ctxMeet meetType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxMeet meetType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def meetStore : EquationStore (TotalTerm ctxMeet) := [meetEquation]

/-- **The store is in the fragment of meet groups.** -/
theorem meet_inside : InMeetFragment meetStore := inMeetFragment_of_B (by decide +kernel)

theorem meetLeft_code : meetEquation.1.2.code = etaExp 1 (.var (1 : Fin ctxMeet.arity)) := by decide +kernel
theorem meetRight_code : meetEquation.2.2.code = etaExp 1 (.var (0 : Fin ctxMeet.arity)) := by decide +kernel
theorem meetX_declared : Ctx.lookup ctxMeet.raw 1 = famCode [U0] U2 := by decide +kernel
theorem meetY_declared : Ctx.lookup ctxMeet.raw 0 = famCode [U1] U3 := by decide +kernel

/-- **It lies outside the fragment of fitting groups**: its two unknowns share an equation and neither fits the
other. -/
theorem meet_not_fit : ¬ InFitFragment meetStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes meetEquation List.mem_cons_self
  have together := grouped meetEquation List.mem_cons_self v
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans meetLeft_code))
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans meetRight_code))
  have dl : Ctx.lookup ctxMeet.raw v.left = famCode [U0] U2 := by rw [hl]; exact meetX_declared
  have dr : Ctx.lookup ctxMeet.raw v.right = famCode [U1] U3 := by rw [hr]; exact meetY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have fits := comparable v.left v.right different together U0 U2 U1 U3 dl dr
  exact absurd fits (by decide)

/-- **The solver of fitting groups is stuck on it.** -/
theorem meet_fit_stuck : isStuck (run fitTowerSolver meetStore 1) = true := by decide +kernel

/-- **The solver of meet groups commits on it**: `Y` lowered to `U1 → U2`, then `X := λ x. Y x`. -/
theorem meet_committed : (run meetTowerSolver meetStore 2).readout = .commit := by decide +kernel

/-- **Its answer is principal.** -/
theorem meet_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxMeet), (frames setting.levels).Principal meetStore answer :=
  principal_of_inMeetFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete meet_inside

/-! ## Lowering below the meet loses a solution -/

/-- `X := λ x. U1, Y := λ x. U1`. -/
def overMeetSolution : empty setting.R ⟶ ctxMeet :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) familyLow (.lam (.head U1)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxLow (termIn ctxLow familyHigh (.lam (.head U1)) (by decide +kernel)).2

/-- **It is a solution.** -/
theorem overMeet_solution_models : (frames setting.levels).Models overMeetSolution meetStore := by
  intro e member
  rw [List.mem_singleton.mp member]
  exact e_of_codes rfl (by decide +kernel)

/-- `Y` declared at `U1 → U1`: one universe below the meet `U1 → U2`. -/
abbrev overMeetContext : Context setting.R where
  arity := ctxMeet.arity
  raw := setFamAt ctxMeet.raw 0 [U1] U1
  formed := setFamAt_formed ctxMeet.raw 0 ctxMeet.formed meetY_declared (by decide) (by decide) (by decide)
    (by decide)

/-- The identity on codes, from the telescope with `Y : U1 → U1`. -/
def overMeetHom : overMeetContext ⟶ ctxMeet where
  substitution := ids
  typed := setFamAt_substMor ctxMeet.raw 0 meetY_declared (by decide) (by decide) (by decide) (by decide)
    overMeetContext.formed

theorem u1_apart : ∀ above, setting.R.headTyping U1 above → ¬ setting.R.cumulative above U1 := by
  intro above typing
  change LevelTower.HeadTyping (.sort (.succ Tower.zero)) above at typing
  cases typing
  decide

/-- **Lowering `Y` below the meet loses a solution**: `X := λ x. U1, Y := λ x. U1` does not factor through the
telescope with `Y : U1 → U1`, since its value of `Y` returns `U1`, which is not a type of `U1`. -/
theorem over_meet_loses :
    ¬ ∃ τ : empty setting.R ⟶ overMeetContext, homTypedEquality setting.R overMeetSolution (τ ≫ overMeetHom) := by
  rintro ⟨τ, same⟩
  have equal := same.2 (0 : Fin ctxMeet.arity)
  have valueCode : overMeetSolution.substitution 0 = .lam (.head U1) := by decide +kernel
  have declaredCode : Presentation.subst overMeetSolution.substitution (Ctx.lookup ctxMeet.raw 0) =
      .pi (.head U1) (.head U3) := by decide +kernel
  change Equal setting.R (empty setting.R).raw (overMeetSolution.substitution 0)
    (τ.substitution (0 : Fin ctxMeet.arity))
    (Presentation.subst overMeetSolution.substitution (Ctx.lookup ctxMeet.raw 0)) at equal
  rw [valueCode, declaredCode] at equal
  have typed := τ.typed (0 : Fin ctxMeet.arity)
  change Typed setting.R (empty setting.R).raw (τ.substitution (0 : Fin ctxMeet.arity))
    (Presentation.subst τ.substitution (Ctx.lookup (setFamAt ctxMeet.raw 0 [U1] U1) 0)) at typed
  rw [lookup_setFamAt_self, famCode_subst] at typed
  have formed : CtxFormed setting.R (.snoc (empty setting.R).raw (.head U1)) :=
    (empty setting.R).formed.snoc (IsType.head_of_universe (by decide))
  have opened := ContextualDependentUniverseInjective.equal_of_lam_left TowerModel.facts (empty setting.R).formed
    equal
  have body : Typed setting.R (.snoc (empty setting.R).raw (.head U1))
      (.app (Presentation.rename wk (τ.substitution (0 : Fin ctxMeet.arity))) (.var 0)) (.head U1) :=
    open_typed typed (var_head_typed _ U1)
  exact ContextualDependentUniverseInjective.sort_not_small (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete formed
    (by decide) u1_apart body ⟨U3, by decide, .symm opened⟩

/-! ## Two meets in a chain -/

/-- `U2 → U4`, over `X Y`. -/
def familyTop : TypeOver ctxMeet := formIn ctxMeet (.pi (.head U2) (.head U4)) (by decide +kernel)

/-- `X : U0 → U2, Y : U1 → U3, W : U2 → U4`. -/
abbrev ctxChain := extend ctxMeet familyTop

/-- `Π (x : U0). U4` and `Π (x : U1). U4`, over `X Y W`. -/
def chainLow : TypeOver ctxChain := formIn ctxChain (.pi (.head U0) (.head U4)) (by decide +kernel)
def chainHigh : TypeOver ctxChain := formIn ctxChain (.pi (.head U1) (.head U4)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U4`, and `λ x. Y x ≐ λ x. W x` at `Π (x : U1). U4`. -/
def chainStore : EquationStore (TotalTerm ctxChain) :=
  [(termIn ctxChain chainLow (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
      termIn ctxChain chainLow (.lam (.app (.var 2) (.var 0))) (by decide +kernel)),
    (termIn ctxChain chainHigh (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
      termIn ctxChain chainHigh (.lam (.app (.var 1) (.var 0))) (by decide +kernel))]

theorem chain_inside : InMeetFragment chainStore := inMeetFragment_of_B (by decide +kernel)

/-- **The solver commits**: `Y` lowered to `U1 → U2` and `X := λ x. Y x`; then `W` lowered to `U2 → U2` and
`Y := λ x. W x`. -/
theorem chain_committed : (run meetTowerSolver chainStore 3).readout = .commit := by decide +kernel

theorem chain_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxChain), (frames setting.levels).Principal chainStore answer :=
  principal_of_inMeetFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete chain_inside

/-! ## Just outside: the crossing condition is needed -/

/-- **On the cross store only the crossing fails**: `X : U0 → U0` has the smaller domain and the smaller codomain,
and `Y`'s domain `U1` does not lie below `X`'s codomain `U0`. -/
theorem cross_only_crossing_fails :
    setting.R.cumulative U0 U1 ∧ setting.R.cumulative U0 U1 ∧ ¬ setting.R.cumulative U1 U0 := by decide

/-- **The crossing condition is needed**: the cross store fails only the crossing, it is solvable, and it has no
principal answer. -/
theorem crossing_needed :
    (setting.R.cumulative U0 U1 ∧ setting.R.cumulative U0 U1 ∧ ¬ setting.R.cumulative U1 U0) ∧
      (frames setting.levels).Solvable crossStore ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer :=
  ⟨cross_only_crossing_fails, cross_identity, fun answer => cross_no_principal answer⟩

/-- **It lies outside the fragment of meet groups.** -/
theorem cross_not_meet_inside : ¬ InMeetFragment crossStore := by
  intro inside
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have together := grouped crossEquation List.mem_cons_self v
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj 1 (v.side_left.symm.trans crossLeft_code))
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj 1 (v.side_right.symm.trans crossRight_code))
  have dl : Ctx.lookup ctxCross.raw v.left = famCode [U0] U0 := by rw [hl]; exact crossX_declared
  have dr : Ctx.lookup ctxCross.raw v.right = famCode [U1] U1 := by rw [hr]; exact crossY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have compatible := comparable v.left v.right different together U0 U0 U1 U1 dl dr
  exact absurd compatible (by decide)

/-- **The solver of meet groups is stuck on it.** -/
theorem cross_meet_stuck : isStuck (run meetTowerSolver crossStore 1) = true := by decide +kernel

/-- **Every run of it stops postponed**, at an exact residual without a principal answer. -/
theorem cross_postponed_by_meet :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run meetTowerSolver crossStore larger = run meetTowerSolver crossStore fuel ∧
      ∃ state, run meetTowerSolver crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames setting.levels) crossStore state.answer state.remaining ∧
        DependentFibre.NoPrincipal setting.levels state.remaining :=
  DependentFibre.cross_run_postponed meetTowerSolver

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
