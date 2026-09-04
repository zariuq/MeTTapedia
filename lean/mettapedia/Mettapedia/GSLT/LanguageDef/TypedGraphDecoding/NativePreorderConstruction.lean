import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec
import Mathlib.Tactic

/-!
# Native preorder construction contract

This module models the language-independent construction machine beneath the
typed decoder.  It accounts for the root/program distinction, open holes,
task-local references, canonical variable introduction, per-top-level-form
variable reset, and the exact remaining-action bound.

The source-derived language refinement is intentionally separate.  A native
action must pass both machines: this file establishes that it is a faithful
bounded tree action, while the language refinement establishes that the tree
position is admitted by the selected language presentation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.NativePreorderConstruction

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec

structure Config where
  maxProgramForms : Nat
  maxListArity : Nat
  maxSymbols : Nat
  maxVariables : Nat
  maxActions : Nat
  deriving Repr, DecidableEq

inductive HoleClass where
  | root
  | topForm
  | nested
  deriving Repr, DecidableEq

structure State where
  holes : List HoleClass
  actionsUsed : Nat
  variableCount : Nat
  deriving Repr, DecidableEq

def initial : State :=
  { holes := [.root], actionsUsed := 0, variableCount := 0 }

def actionArity : Action → Nat
  | .program count => count
  | .list count => count
  | .reference _ => 0
  | .var _ => 0

def budgetAllows (config : Config) (state : State)
    (action : Action) : Prop :=
  state.actionsUsed < config.maxActions ∧
    state.holes.tail.length + actionArity action ≤
      config.maxActions - state.actionsUsed - 1

def budgetAllows? (config : Config) (state : State)
    (action : Action) : Bool :=
  state.actionsUsed < config.maxActions &&
    state.holes.tail.length + actionArity action ≤
      config.maxActions - state.actionsUsed - 1

theorem budgetAllows?_eq_true_iff (config : Config) (state : State)
    (action : Action) :
    budgetAllows? config state action = true ↔
      budgetAllows config state action := by
  simp [budgetAllows?, budgetAllows]

/-- Declarative legality of one native action. -/
def Allowed (config : Config) (symbolCount : Nat)
    (state : State) (action : Action) : Prop :=
  symbolCount ≤ config.maxSymbols ∧
    budgetAllows config state action ∧
    match state.holes with
    | [] => False
    | .root :: _ =>
        match action with
        | .program count => 0 < count ∧ count ≤ config.maxProgramForms
        | _ => False
    | .topForm :: _ =>
        match action with
        | .program _ => False
        | .list arity => arity ≤ config.maxListArity
        | .reference index => index < symbolCount
        | .var index =>
            index < state.variableCount ∨
              (index = state.variableCount ∧
                state.variableCount < config.maxVariables)
    | .nested :: _ =>
        match action with
        | .program _ => False
        | .list arity => arity ≤ config.maxListArity
        | .reference index => index < symbolCount
        | .var index =>
            index < state.variableCount ∨
              (index = state.variableCount ∧
                state.variableCount < config.maxVariables)

/-- Executable legality test, defined independently of `Allowed`. -/
def allowed? (config : Config) (symbolCount : Nat)
    (state : State) (action : Action) : Bool :=
  if symbolCount > config.maxSymbols then false
  else if !budgetAllows? config state action then false
  else
    match state.holes with
    | [] => false
    | .root :: _ =>
        match action with
        | .program count => 0 < count && count ≤ config.maxProgramForms
        | _ => false
    | .topForm :: _ =>
        match action with
        | .program _ => false
        | .list arity => arity ≤ config.maxListArity
        | .reference index => index < symbolCount
        | .var index =>
            index < state.variableCount ||
              (index == state.variableCount &&
                state.variableCount < config.maxVariables)
    | .nested :: _ =>
        match action with
        | .program _ => false
        | .list arity => arity ≤ config.maxListArity
        | .reference index => index < symbolCount
        | .var index =>
            index < state.variableCount ||
              (index == state.variableCount &&
                state.variableCount < config.maxVariables)

theorem allowed?_eq_true_iff (config : Config) (symbolCount : Nat)
    (state : State) (action : Action) :
    allowed? config symbolCount state action = true ↔
      Allowed config symbolCount state action := by
  cases state with
  | mk holes actionsUsed variableCount =>
      cases holes with
      | nil => simp [allowed?, Allowed]
      | cons hole rest =>
          cases hole <;> cases action <;>
            simp [allowed?, Allowed, budgetAllows?_eq_true_iff,
              Bool.or_eq_true, Bool.and_eq_true]

def childHoles (current : HoleClass) (action : Action) : List HoleClass :=
  match current, action with
  | .root, .program count => List.replicate count .topForm
  | .topForm, .list arity => List.replicate arity .nested
  | .nested, .list arity => List.replicate arity .nested
  | _, _ => []

def countAfterAction (state : State) (action : Action) : Nat :=
  match action with
  | .var index => if index = state.variableCount then state.variableCount + 1
      else state.variableCount
  | _ => state.variableCount

def resetAtTopForm (holes : List HoleClass) (count : Nat) : Nat :=
  match holes with
  | .topForm :: _ => 0
  | _ => count

def advance (state : State) (action : Action) : State :=
  match state.holes with
  | [] => state
  | current :: rest =>
      let holes := childHoles current action ++ rest
      { holes := holes
        actionsUsed := state.actionsUsed + 1
        variableCount := resetAtTopForm holes (countAfterAction state action) }

def step? (config : Config) (symbolCount : Nat)
    (state : State) (action : Action) : Option State :=
  if allowed? config symbolCount state action then
    some (advance state action)
  else none

/-- Independent relational account of a successful native transition. -/
structure Steps (config : Config) (symbolCount : Nat)
    (state : State) (action : Action) (next : State) : Prop where
  allowed : Allowed config symbolCount state action
  exactNext : next = advance state action

theorem step?_eq_some_iff (config : Config) (symbolCount : Nat)
    (state next : State) (action : Action) :
    step? config symbolCount state action = some next ↔
      Steps config symbolCount state action next := by
  unfold step?
  by_cases legal : allowed? config symbolCount state action = true
  · simp only [legal, if_true, Option.some.injEq]
    constructor
    · intro exactNext
      exact ⟨(allowed?_eq_true_iff config symbolCount state action).mp legal,
        exactNext.symm⟩
    · intro steps
      exact steps.exactNext.symm
  · have falseLegal : allowed? config symbolCount state action = false :=
      Bool.eq_false_of_not_eq_true legal
    rw [falseLegal]
    simp only [Bool.false_eq_true, if_false]
    constructor
    · intro impossible
      cases impossible
    · intro steps
      exfalso
      exact legal
        ((allowed?_eq_true_iff config symbolCount state action).mpr steps.allowed)

def run? (config : Config) (symbolCount : Nat) :
    State → List Action → Option State
  | state, [] => some state
  | state, action :: actions => do
      let next ← step? config symbolCount state action
      run? config symbolCount next actions

theorem run?_append (config : Config) (symbolCount : Nat)
    (state : State) (first second : List Action) :
    run? config symbolCount state (first ++ second) =
      (run? config symbolCount state first).bind fun middle =>
        run? config symbolCount middle second := by
  induction first generalizing state with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.cons_append, run?]
      cases stepped : step? config symbolCount state action with
      | none => simp
      | some next => simpa [stepped] using induction next

structure Admission (config : Config) (symbolCount : Nat)
    (actions : List Action) where
  finalState : State
  runExact : run? config symbolCount initial actions = some finalState
  complete : finalState.holes = []

theorem admitted_prefix_non_stranding {config : Config} {symbolCount : Nat}
    {actions leading : List Action}
    (admission : Admission config symbolCount actions)
    (isPrefix : leading <+: actions) :
    ∃ state, run? config symbolCount initial leading = some state := by
  rcases isPrefix with ⟨suffix, rfl⟩
  have whole := admission.runExact
  rw [run?_append] at whole
  cases prefixRun : run? config symbolCount initial leading with
  | none => simp [prefixRun] at whole
  | some state => exact ⟨state, rfl⟩

private def fixtureConfig : Config :=
  { maxProgramForms := 2, maxListArity := 4, maxSymbols := 3,
    maxVariables := 3, maxActions := 12 }

theorem root_requires_nonempty_program_fixture :
    allowed? fixtureConfig 2 initial (.program 0) = false := by
  decide +kernel

theorem absent_reference_is_rejected_fixture :
    allowed? fixtureConfig 2
      { holes := [.nested], actionsUsed := 1, variableCount := 0 }
      (.reference 2) = false := by
  decide +kernel

theorem next_canonical_variable_is_admitted_fixture :
    allowed? fixtureConfig 2
      { holes := [.nested], actionsUsed := 1, variableCount := 1 }
      (.var 1) = true := by
  decide +kernel

theorem skipped_canonical_variable_is_rejected_fixture :
    allowed? fixtureConfig 2
      { holes := [.nested], actionsUsed := 1, variableCount := 1 }
      (.var 2) = false := by
  decide +kernel

/-- Completing one top-level form resets the variable namespace before the
next top-level form, matching canonical per-form encoding. -/
theorem top_form_boundary_resets_variables_fixture :
    (advance
      { holes := [.nested, .topForm], actionsUsed := 4, variableCount := 2 }
      (.reference 0)).variableCount = 0 := by
  rfl

theorem insufficient_remaining_budget_rejects_list_fixture :
    allowed? fixtureConfig 2
      { holes := [.nested], actionsUsed := 11, variableCount := 0 }
      (.list 1) = false := by
  decide +kernel

#print axioms budgetAllows?_eq_true_iff
#print axioms allowed?_eq_true_iff
#print axioms step?_eq_some_iff
#print axioms run?_append
#print axioms admitted_prefix_non_stranding
#print axioms root_requires_nonempty_program_fixture
#print axioms absent_reference_is_rejected_fixture
#print axioms next_canonical_variable_is_admitted_fixture
#print axioms skipped_canonical_variable_is_rejected_fixture
#print axioms top_form_boundary_resets_variables_fixture
#print axioms insufficient_remaining_budget_rejects_list_fixture

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.NativePreorderConstruction
