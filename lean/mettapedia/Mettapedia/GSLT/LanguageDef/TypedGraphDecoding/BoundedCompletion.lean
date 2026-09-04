import Mathlib.Tactic

/-!
# Exact bounded completion for semantic decoding

Cheap arity or sort-cost checks are only sufficient pruning tests.  For a
finite action enumeration and finite fuel, however, completion is decidable
exactly.  This module defines the executable search and proves both witness
directions.  The action enumeration is part of the semantic authority: a
transition available outside that enumeration is intentionally irrelevant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.BoundedCompletion

universe uState uAction uWitness

/-- Finite deterministic transition system used by a bounded prefix oracle. -/
structure FiniteMachine where
  State : Type uState
  Action : Type uAction
  actions : List Action
  step? : State → Action → Option State
  accepting : State → Bool

namespace FiniteMachine

variable (machine : FiniteMachine)

def run : List machine.Action → machine.State → Option machine.State
  | [], state => some state
  | action :: actions, state => do
      let next ← machine.step? state action
      run actions next

/-- Every action in a witness belongs to the checker-owned finite support. -/
def EnumeratedTrace (trace : List machine.Action) : Prop :=
  ∀ action, action ∈ trace → action ∈ machine.actions

/-- Propositional specification of completion within a finite action budget. -/
def CompletesWithin (fuel : Nat) (state : machine.State) : Prop :=
  ∃ trace finalState,
    trace.length ≤ fuel ∧
      machine.EnumeratedTrace trace ∧
      machine.run trace state = some finalState ∧
      machine.accepting finalState = true

/-- Exact finite search.  Acceptance at the current state represents the
empty completion; otherwise one enumerated action consumes one unit of fuel. -/
def canComplete : Nat → machine.State → Bool
  | 0, state => machine.accepting state
  | fuel + 1, state =>
      machine.accepting state ||
        machine.actions.any fun action =>
          match machine.step? state action with
          | none => false
          | some next => canComplete fuel next

theorem canComplete_sound :
    ∀ fuel state, machine.canComplete fuel state = true →
      machine.CompletesWithin fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state complete
      exact ⟨[], state, by simp, by simp [EnumeratedTrace], rfl, complete⟩
  | succ fuel inductionHypothesis =>
      intro state complete
      simp only [canComplete, Bool.or_eq_true] at complete
      rcases complete with accepting | progresses
      · exact ⟨[], state, by simp, by simp [EnumeratedTrace], rfl, accepting⟩
      · rw [List.any_eq_true] at progresses
        rcases progresses with ⟨action, actionMember, branch⟩
        cases step : machine.step? state action with
        | none => simp [step] at branch
        | some next =>
            simp only [step] at branch
            rcases inductionHypothesis next branch with
              ⟨trace, finalState, lengthBound, enumerated, traceRun,
                accepting⟩
            refine
              ⟨action :: trace, finalState, ?_, ?_, ?_, accepting⟩
            · simpa using Nat.succ_le_succ lengthBound
            · intro candidate candidateMember
              simp only [List.mem_cons] at candidateMember
              rcases candidateMember with equality | member
              · simpa [equality] using actionMember
              · exact enumerated candidate member
            · simp [run, step, traceRun]

theorem canComplete_complete :
    ∀ fuel state, machine.CompletesWithin fuel state →
      machine.canComplete fuel state = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro state completion
      rcases completion with
        ⟨trace, finalState, lengthBound, _enumerated, traceRun, accepting⟩
      have traceEmpty : trace = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero lengthBound)
      subst trace
      simp only [run, Option.some.injEq] at traceRun
      subst finalState
      exact accepting
  | succ fuel inductionHypothesis =>
      intro state completion
      rcases completion with
        ⟨trace, finalState, lengthBound, enumerated, traceRun, accepting⟩
      cases trace with
      | nil =>
          simp only [run, Option.some.injEq] at traceRun
          subst finalState
          simp [canComplete, accepting]
      | cons action trace =>
          have actionMember : action ∈ machine.actions :=
            enumerated action (by simp)
          have restEnumerated : machine.EnumeratedTrace trace := by
            intro candidate member
            exact enumerated candidate (by simp [member])
          have restLength : trace.length ≤ fuel := by
            simpa using lengthBound
          simp only [run] at traceRun
          cases step : machine.step? state action with
          | none =>
              rw [step] at traceRun
              contradiction
          | some next =>
              rw [step] at traceRun
              have restCompletion : machine.CompletesWithin fuel next :=
                ⟨trace, finalState, restLength, restEnumerated, traceRun,
                  accepting⟩
              have restSearch := inductionHypothesis next restCompletion
              have branch :
                  (match machine.step? state action with
                    | none => false
                    | some next => machine.canComplete fuel next) = true := by
                simp [step, restSearch]
              have someBranch :
                  machine.actions.any (fun candidate =>
                    match machine.step? state candidate with
                    | none => false
                    | some next => machine.canComplete fuel next) = true :=
                List.any_eq_true.mpr ⟨action, actionMember, branch⟩
              change
                (machine.accepting state ||
                  machine.actions.any (fun candidate =>
                    match machine.step? state candidate with
                    | none => false
                    | some next => machine.canComplete fuel next)) = true
              rw [Bool.or_eq_true]
              exact Or.inr someBranch

/-- The executable oracle has neither false positives nor false negatives at
the declared finite horizon. -/
theorem canComplete_eq_true_iff (fuel : Nat) (state : machine.State) :
    machine.canComplete fuel state = true ↔
      machine.CompletesWithin fuel state :=
  ⟨machine.canComplete_sound fuel state,
    machine.canComplete_complete fuel state⟩

end FiniteMachine

/-! ## Structural lower bounds are one-way certificates -/

/-- Abstract completion evidence used to state a safe lower-bound pruning
rule without pretending that the lower bound decides semantic completion. -/
structure BudgetedProblem (Witness : Type uWitness) where
  remaining : Nat
  requiredLowerBound : Nat
  completes : Witness → Prop
  witnessCost : Witness → Nat
  lowerBound_sound : ∀ witness, completes witness →
    requiredLowerBound ≤ witnessCost witness

/-- Exceeding a sound structural lower bound rules out every completion that
fits the remaining budget. -/
theorem no_fitting_completion_of_remaining_lt_lowerBound
    {Witness : Type uWitness} (problem : BudgetedProblem Witness)
    (tooSmall : problem.remaining < problem.requiredLowerBound) :
    ¬ ∃ witness,
      problem.completes witness ∧
        problem.witnessCost witness ≤ problem.remaining := by
  rintro ⟨witness, completes, fits⟩
  have lower := problem.lowerBound_sound witness completes
  omega

/-- The converse is invalid: a lower bound may fit while a semantic
obligation makes completion impossible. -/
theorem lowerBound_fit_does_not_imply_completion :
    ∃ problem : BudgetedProblem Unit,
      problem.requiredLowerBound ≤ problem.remaining ∧
        ¬ ∃ witness, problem.completes witness := by
  let problem : BudgetedProblem Unit :=
    { remaining := 1
      requiredLowerBound := 1
      completes := fun _ => False
      witnessCost := fun _ => 1
      lowerBound_sound := by
        intro witness impossible
        contradiction }
  exact ⟨problem, by decide, by simp [problem]⟩

/-! ## Executable controls -/

private abbrev countdown : FiniteMachine where
  State := Nat
  Action := Unit
  actions := [()]
  step? := fun state _ => if state = 0 then none else some (state - 1)
  accepting := fun state => state == 0

/-- Two steps suffice to finish a countdown from two. -/
theorem countdown_two_steps : countdown.canComplete 2 2 = true := by
  decide

/-- One step does not suffice. -/
theorem countdown_one_step_is_insufficient :
    countdown.canComplete 1 2 = false := by
  decide

private abbrev unenumeratedShortcut : FiniteMachine where
  State := Bool
  Action := Bool
  actions := [false]
  step? := fun state action =>
    if state then none else if action then some true else none
  accepting := id

/-- A physical transition outside the authenticated action enumeration cannot
be smuggled into the completion oracle. -/
theorem unenumerated_transition_is_not_a_completion :
    unenumeratedShortcut.canComplete 1 false = false := by
  decide

#print axioms FiniteMachine.canComplete_sound
#print axioms FiniteMachine.canComplete_complete
#print axioms FiniteMachine.canComplete_eq_true_iff
#print axioms no_fitting_completion_of_remaining_lt_lowerBound
#print axioms lowerBound_fit_does_not_imply_completion
#print axioms countdown_two_steps
#print axioms countdown_one_step_is_insufficient
#print axioms unenumerated_transition_is_not_a_completion

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.BoundedCompletion
