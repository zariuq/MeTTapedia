import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTwins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexWakeup
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# Controls for the worklist driver, rigid refutation and wake-up

All runs below execute the actual step (rigid clash check, typed eta conversion scan,
newest-variable dispatcher) inside the actual driver, in the cumulative tower.

* **Clash.** `Ground ≐ U0`, whose endpoint types are the different universes `U0` and `U1`, is
  refuted by the first round; the refutation is certified. A flexible `X ≐ Ground` does not clash.
* **Wake-up.** With `X : U0`, the heterogeneous equation `snd (X, refl X) ≐ refl Ground` alone
  leaves the step stuck and is not refuted. Placed before `X ≐ Ground`, it is skipped, the type
  variable is solved, and the woken equation is discharged: the run solves the store with a
  principal answer, at which the type equation holds.
* **Pattern and non-pattern.** With `G, F : U0 → U0`, the store `λx. F x ≐ λx. G x`,
  `λx. F x ≐ λx. F (F x)` solves `F` and keeps the transported non-pattern equation as the only
  residual, stuck and not refuted, although the store has a solution.
* **Two rounds.** `λx. F x ≐ λx. G x`, `G ≐ λx. x` needs two solving rounds: at budget two it is
  cut off, at budget three it is solved, with a principal answer at every larger budget. The
  fragment-completeness theorem is instantiated on it through the executable check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWorklist.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ContextualDependentFlex.Controls.setting

theorem rigid : ∀ name, setting.roles name = .rigid := fun _ => rfl

/-- The actual step in the cumulative tower. -/
def step : Solver setting.levels :=
  solver (S := setting) rigid TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentFlex.Controls.declarations_formed
    ExecutableTowerChoices.choices ConversionControls.reducer 16

/-- Whether a run is stuck with a residual store of a given length. -/
def stuckWith {Γ : Context Tower.rules} {original : EquationStore (TotalTerm Γ)}
    (length : Nat) : Outcome setting.levels original → Bool
  | .stuck state => state.remaining.length == length
  | _ => false

def isCutoff {Γ : Context Tower.rules} {original : EquationStore (TotalTerm Γ)} :
    Outcome setting.levels original → Bool
  | .cutoff _ => true
  | _ => false

theorem solved_of_commit {Γ : Context Tower.rules} {original : EquationStore (TotalTerm Γ)}
    {outcome : Outcome setting.levels original} (committed : outcome.readout = .commit) :
    ∃ state finished, outcome = .solved state finished := by
  cases outcome with
  | solved state finished => exact ⟨state, finished, rfl⟩
  | refuted _ => cases committed
  | stuck _ => cases committed
  | cutoff _ => cases committed

/-! ## A rigid clash -/

def universeOne : TypeOver (empty Tower.rules) :=
  ⟨.head (.sort (.succ Tower.zero)), .sort (.succ (.succ Tower.zero)), .sort _, .headType (.sort _)⟩

def groundCode : TotalTerm (empty Tower.rules) :=
  ⟨ContextualDependentFlex.Wakeup.universeType, ⟨.head .legacyGround, .headType .legacyGround⟩⟩

def universeCode : TotalTerm (empty Tower.rules) :=
  ⟨universeOne, ⟨.head (.sort Tower.zero), .headType (.sort _)⟩⟩

def clash : EquationStore (TotalTerm (empty Tower.rules)) := [(groundCode, universeCode)]

theorem clash_detected : ContextualDependentRigid.storeClashes (S := setting) clash = true := by decide +kernel

theorem clash_refuted : ¬ (frames setting.levels).Solvable clash :=
  ContextualDependentRigid.not_solvable_of_storeClashes rigid TowerModel.facts TowerModel.complete
    clash_detected

theorem clash_run_refutes : (run step clash 1).readout = .refuted := by decide +kernel

abbrev wakeFrame := ContextualDependentFlex.Wakeup.frame

def typeDefinition : Equation (TotalTerm wakeFrame) :=
  ContextualDependentFlex.equation ContextualDependentFlex.Wakeup.unknownType
    ContextualDependentFlex.Wakeup.ground

theorem flexible_does_not_clash :
    ContextualDependentRigid.storeClashes (S := setting) [typeDefinition] = false := by decide +kernel

/-! ## Wake-up of a heterogeneous equation -/

theorem heterogeneous_alone_is_stuck :
    stuckWith 1 (run step [ContextualDependentFlex.Wakeup.pending] 4) = true := by decide +kernel

theorem heterogeneous_alone_is_not_refuted :
    (run step [ContextualDependentFlex.Wakeup.pending] 4).readout = .suspended := by decide +kernel

def twinStore : EquationStore (TotalTerm wakeFrame) :=
  [ContextualDependentFlex.Wakeup.pending, typeDefinition]

theorem woken_after_type_solution : (run step twinStore 2).readout = .commit := by decide +kernel

theorem twin_store_principal :
    ∃ state finished, run step twinStore 2 = .solved state finished ∧
      (frames setting.levels).Principal twinStore state.answer ∧
      ContextualDependentTwins.TypesAgree state.answer ContextualDependentFlex.Wakeup.pending := by
  obtain ⟨state, finished, solved⟩ := solved_of_commit woken_after_type_solution
  have principal := drive_solved_principal step solved
  exact ⟨state, finished, solved, principal,
    ContextualDependentTwins.typesAgree_of_solves setting.levels
      (principal.sound _ (List.mem_cons_self ..))⟩

/-! ## A pattern beside a non-pattern -/

abbrev flexFrame := ContextualDependentFlex.Controls.frame

def patternEquation : Equation (TotalTerm flexFrame) :=
  ContextualDependentFlex.equation ContextualDependentFlex.Controls.left
    ContextualDependentFlex.Controls.right

def recursiveEquation : Equation (TotalTerm flexFrame) :=
  ContextualDependentFlex.equation ContextualDependentFlex.Controls.left
    ContextualDependentFlex.Controls.recursiveRight

def mixedStore : EquationStore (TotalTerm flexFrame) := [patternEquation, recursiveEquation]

theorem pattern_solved_residual_kept : stuckWith 1 (run step mixedStore 4) = true := by
  decide +kernel

theorem residual_not_refuted : (run step mixedStore 4).readout = .suspended := by decide +kernel

/-! ## Two solving rounds -/

def twoRounds : EquationStore (TotalTerm flexFrame) :=
  [patternEquation, ContextualDependentFlex.Controls.sideCondition]

theorem two_rounds_cut_at_two : isCutoff (run step twoRounds 2) = true := by decide +kernel

theorem two_rounds_solved_at_three : (run step twoRounds 3).readout = .commit := by decide +kernel

theorem two_rounds_decided : decidesWithin step 2 flexFrame twoRounds = true := by decide +kernel

/-- **Fragment completeness, instantiated**: the store lies in the decided fragment of the step,
so from some budget on every run reaches the same principal answer or refutation. -/
theorem two_rounds_fragment :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run step twoRounds larger = run step twoRounds fuel ∧
      ((∃ state finished, run step twoRounds larger = .solved state finished ∧
          (frames setting.levels).Principal twoRounds state.answer) ∨
        (∃ absent, run step twoRounds larger = .refuted absent)) :=
  (decidedFragment rigid TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentFlex.Controls.declarations_formed
    ExecutableTowerChoices.choices ConversionControls.reducer 16).decided
    (Reaches.of_decidesWithin step 2 flexFrame twoRounds two_rounds_decided)

theorem two_rounds_principal :
    ∃ state finished, run step twoRounds 3 = .solved state finished ∧
      (frames setting.levels).Principal twoRounds state.answer := by
  obtain ⟨state, finished, solved⟩ := solved_of_commit two_rounds_solved_at_three
  exact ⟨state, finished, solved, drive_solved_principal step solved⟩

/-! ## Constants in any rigid-constant profile -/

/-- **Distinct constants clash** at any annotations: `c ≐ d` has no solution in any later
context. -/
theorem constants_clash {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
    [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
    (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
    (complete : AlgorithmicComplete S.R S.roles) {Γ : Context S.R} (left right : TotalTerm Γ)
    {c d : DeclName} (leftCode : left.2.code = .const c) (rightCode : right.2.code = .const d)
    (distinct : c ≠ d) : ¬ (frames S.levels).Solvable [(left, right)] := by
  apply ContextualDependentRigid.not_solvable_of_storeClashes rigid facts complete
  simp [ContextualDependentRigid.storeClashes, ContextualDependentRigid.equationClashes,
    ContextualDependentRigid.spineClashes, leftCode, rightCode, spineConst, distinct]

/-- One constant on both sides does not clash. -/
theorem same_constant_does_not_clash {Head : Type} {n : Nat} (c : DeclName) :
    ContextualDependentRigid.spineClashes (.const c : Tm Head n) (.const c) = false := by
  simp [ContextualDependentRigid.spineClashes, spineConst]

end ContextualDependentWorklist.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
