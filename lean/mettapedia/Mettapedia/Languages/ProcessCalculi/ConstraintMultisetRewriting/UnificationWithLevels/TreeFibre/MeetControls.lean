import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilyControls

/-!
# Controls for meet narrowing, in the tree's tower

* **The rule fires and unlocks the tree's solver** (`narrow_meet_fires`, `narrowMeet_committed`,
  `narrow_principal_by_meet`): on the tree's `narrowStore`, `X ≐ Π (y : Y). Y` at `U1` over `A : U0, X : U0, Y : U1`,
  the reading finds `Y` at a domain position, lowers `Y` to `U0`, and the tree's top family `sortTower` commits on the
  lowered store at budget 16. So the store has a principal answer, reached through the rule.
* **Narrowing stops at the meet** (`over_meet_fires`, `over_solution_models`, `over_narrowing_loses`): over
  `X : U1, Y : U2`, the store `X ≐ Π (y : Y). Y` at `U2` is narrowed by the rule to `Y : U1`, the meet of `U2` and
  `U1`. Lowering `Y` one universe further, to `U0`, would lose the solution `X := Π (y : U0). U0, Y := U0`: `U0` is
  not equal to any type of `U0`.
* **The rule does not fire on the cross store** (`cross_no_meet`): its sides are abstractions, not an unknown at a
  universe.
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
open ContextualDependentEtaDepth ContextualDependentUniverseInjective

/-- The meet narrowing rule at the tower's facts. -/
def towerMeet {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Update setting.levels problem) :=
  meetRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete problem

/-! ## The rule fires and unlocks the tree's solver -/

/-- **The rule fires on `narrowStore`.** -/
theorem narrow_meet_fires : (towerMeet narrowStore).isSome = true := by decide +kernel

/-- The update the rule returns: `Y` lowered to `U0`. -/
def narrowMeet : Update setting.levels narrowStore := (towerMeet narrowStore).get narrow_meet_fires

/-- **The tree's top family commits on the lowered store**, at budget 16. -/
theorem narrowMeet_committed : (run (sortTower.solver 16) narrowMeet.remaining 2).readout = .commit := by
  decide +kernel

/-- **`narrowStore` has a principal answer, reached through the rule.** -/
theorem narrow_principal_by_meet :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAXY), (frames setting.levels).Principal narrowStore answer := by
  cases outcome : run (sortTower.solver 16) narrowMeet.remaining 2 with
  | solved state finished => exact ⟨_, _, (narrowMeet.then state).completed finished⟩
  | stuck _ =>
      have committed := narrowMeet_committed
      rw [outcome] at committed
      cases committed
  | refuted _ =>
      have committed := narrowMeet_committed
      rw [outcome] at committed
      cases committed
  | cutoff _ =>
      have committed := narrowMeet_committed
      rw [outcome] at committed
      cases committed

/-! ## Narrowing stops at the meet -/

/-- `U1`. -/
def universeOne : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)

/-- `X : U1`. -/
abbrev ctxOne := extend (empty setting.R) universeOne

/-- `U2`, over `X`. -/
def universeTwo : TypeOver ctxOne := formIn ctxOne (.head U2) (by decide +kernel)

/-- `X : U1, Y : U2`. -/
abbrev ctxOneTwo := extend ctxOne universeTwo

/-- `U2`, over `X Y`. -/
def typeTwo : TypeOver ctxOneTwo := formIn ctxOneTwo (.head U2) (by decide +kernel)

/-- `X ≐ Π (y : Y). Y` at `U2`. -/
def overEquation : Equation (TotalTerm ctxOneTwo) :=
  (termIn ctxOneTwo typeTwo (.var 1) (by decide +kernel),
    termIn ctxOneTwo typeTwo (.pi (.var 0) (.var 1)) (by decide +kernel))

def overStore : EquationStore (TotalTerm ctxOneTwo) := [overEquation]

/-- **The rule fires**: it lowers `Y` to `U1`, the meet of `U2` and `U1`. -/
theorem over_meet_fires : (towerMeet overStore).isSome = true := by decide +kernel

/-- `X := Π (y : U0). U0, Y := U0`. -/
def overSolution : empty setting.R ⟶ ctxOneTwo :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) universeOne (.pi (.head U0) (.head U0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxOne (termIn ctxOne universeTwo (.head U0) (by decide +kernel)).2

/-- **It is a solution.** -/
theorem over_solution_models : (frames setting.levels).Models overSolution overStore := by
  intro e member
  rw [List.mem_singleton.mp member]
  exact e_of_codes rfl (by decide +kernel)

/-- `Y` declared at `U0`: one universe below the meet. -/
theorem overDeclared : Ctx.lookup ctxOneTwo.raw 0 = .head U2 := by decide +kernel

def overLowering : Narrowing ctxOneTwo :=
  lowering ctxOneTwo 0 (u := U0) overDeclared (by decide) (by decide)

theorem u0_apart : ∀ above, setting.R.headTyping U0 above → ¬ setting.R.cumulative above U0 := by
  intro above typing
  change LevelTower.HeadTyping (.sort Tower.zero) above at typing
  cases typing
  decide

/-- **Lowering `Y` below the meet loses a solution**: the solution `X := Π (y : U0). U0, Y := U0` does not factor
through the telescope with `Y : U0`. -/
theorem over_narrowing_loses :
    ¬ ∃ τ : empty setting.R ⟶ overLowering.context, homTypedEquality setting.R overSolution (τ ≫ overLowering.hom) := by
  rintro ⟨τ, same⟩
  have equal := same.2 (0 : Fin ctxOneTwo.arity)
  have valueCode : overSolution.substitution 0 = .head U0 := by decide +kernel
  have declaredCode : Presentation.subst overSolution.substitution (Ctx.lookup ctxOneTwo.raw 0) = .head U2 := by
    decide +kernel
  change Equal setting.R (empty setting.R).raw (overSolution.substitution 0)
    (Presentation.subst τ.substitution (.var (0 : Fin ctxOneTwo.arity)))
    (Presentation.subst overSolution.substitution (Ctx.lookup ctxOneTwo.raw 0)) at equal
  rw [valueCode, declaredCode] at equal
  have typed := τ.typed (0 : Fin ctxOneTwo.arity)
  change Typed setting.R (empty setting.R).raw (τ.substitution (0 : Fin ctxOneTwo.arity)) (.head U0) at typed
  exact sort_not_small (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete (empty setting.R).formed (by decide) u0_apart
    typed ⟨U2, by decide, .symm equal⟩

/-! ## The rule does not fire on the cross store -/

/-- **The rule does not fire on the cross store.** -/
theorem cross_no_meet : (towerMeet crossStore).isNone = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
