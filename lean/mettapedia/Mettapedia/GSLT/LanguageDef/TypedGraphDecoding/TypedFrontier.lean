import Mathlib.Tactic

/-!
# Typed frontier transitions

The type judgment belongs in the graph transition, not merely in a terminal
validator.  A policy action selects one open hole and one constructor head.
The checker admits it only when the head synthesizes the hole's expected sort
and the resulting child frontier can still fit the declared structural budget.

This module is signature-parametric.  PeTTa, MM2, and future GSLT languages
instantiate the same transition rather than selecting language modes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier

universe uSort uHead

/-- Typed constructor signature projected from an authored presentation. -/
structure Signature where
  SortType : Type uSort
  Head : Type uHead
  resultSort : Head → SortType
  childSorts : Head → List SortType

/-- One policy action: refine the indexed open hole with a constructor head. -/
structure Action (signature : Signature) where
  holeIndex : Nat
  head : signature.Head

/-- Open typed obligations plus the number of remaining constructor actions. -/
structure State (signature : Signature) where
  holes : List signature.SortType
  remaining : Nat

namespace Signature

variable (signature : Signature)

/-- Replace one indexed hole by the selected head's ordered child holes. -/
def nextHoles (state : State signature) (action : Action signature) :
    List signature.SortType :=
  state.holes.take action.holeIndex ++
    signature.childSorts action.head ++
    state.holes.drop (action.holeIndex + 1)

/-- Sum of per-sort completion lower bounds over the current frontier. -/
def required (sortCost : signature.SortType → Nat)
    (holes : List signature.SortType) : Nat :=
  (holes.map sortCost).sum

/-- Exact policy-visible legality for the typed structural layer. -/
def Legal (sortCost : signature.SortType → Nat)
    (state : State signature) (action : Action signature) : Prop :=
  ∃ expected,
    state.holes[action.holeIndex]? = some expected ∧
      signature.resultSort action.head = expected ∧
      1 + signature.required sortCost
        (signature.nextHoles state action) ≤ state.remaining

/-- Checker-owned transition.  The proof-bearing `if` branches are erased at
runtime; their proposition is reflected by `refine?_isSome_iff_legal`. -/
def refine? [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (state : State signature) (action : Action signature) :
    Option (State signature) :=
  match state.holes[action.holeIndex]? with
  | none => none
  | some expected =>
      if signature.resultSort action.head = expected then
        let holes := signature.nextHoles state action
        if 1 + signature.required sortCost holes ≤ state.remaining then
          some { holes := holes, remaining := state.remaining - 1 }
        else none
      else none

theorem refine?_isSome_iff_legal [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (state : State signature) (action : Action signature) :
    (∃ next, signature.refine? sortCost state action = some next) ↔
      signature.Legal sortCost state action := by
  constructor
  · rintro ⟨next, refined⟩
    unfold refine? at refined
    cases expectedLookup : state.holes[action.holeIndex]? with
    | none => simp [expectedLookup] at refined
    | some expected =>
        by_cases sortMatches : signature.resultSort action.head = expected
        · by_cases budgetFits :
            1 + signature.required sortCost
              (signature.nextHoles state action) ≤ state.remaining
          · exact ⟨expected, expectedLookup, sortMatches, budgetFits⟩
          · simp [expectedLookup, sortMatches, budgetFits] at refined
        · simp [expectedLookup, sortMatches] at refined
  · rintro ⟨expected, expectedLookup, sortMatches, budgetFits⟩
    refine
      ⟨{ holes := signature.nextHoles state action
         remaining := state.remaining - 1 }, ?_⟩
    simp [refine?, expectedLookup, sortMatches, budgetFits]

/-- Every successful transition is sort-correct and leaves a frontier whose
declared lower bound fits the remaining budget. -/
theorem refine?_some_typed_and_budget_safe [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (state next : State signature) (action : Action signature)
    (refined : signature.refine? sortCost state action = some next) :
    ∃ expected,
      state.holes[action.holeIndex]? = some expected ∧
        signature.resultSort action.head = expected ∧
        next.holes = signature.nextHoles state action ∧
        next.remaining = state.remaining - 1 ∧
        signature.required sortCost next.holes ≤ next.remaining := by
  have legal : signature.Legal sortCost state action :=
    (signature.refine?_isSome_iff_legal sortCost state action).mp
      ⟨next, refined⟩
  rcases legal with ⟨expected, expectedLookup, sortMatches, budgetFits⟩
  have refinedCopy := refined
  simp [refine?, expectedLookup, sortMatches, budgetFits] at refinedCopy
  have nextEquality :
      ({ holes := signature.nextHoles state action
         remaining := state.remaining - 1 } : State signature) = next :=
    refinedCopy
  cases nextEquality
  refine ⟨expected, expectedLookup, sortMatches, rfl, rfl, ?_⟩
  dsimp only
  omega

/-- A head of the wrong result sort is absent from typed legal support. -/
theorem wrong_result_sort_illegal [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (state : State signature) (action : Action signature)
    {expected : signature.SortType}
    (lookup : state.holes[action.holeIndex]? = some expected)
    (wrong : signature.resultSort action.head ≠ expected) :
    ¬ signature.Legal sortCost state action := by
  rintro ⟨other, otherLookup, resultMatches, _budget⟩
  rw [lookup] at otherLookup
  have equality : other = expected := Option.some.inj otherLookup.symm
  exact wrong (resultMatches.trans equality)

/-- A structurally fitting head is still rejected when its child obligations
cannot fit the remaining action budget. -/
theorem insufficient_budget_illegal [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (state : State signature) (action : Action signature)
    (tooLarge : state.remaining <
      1 + signature.required sortCost
        (signature.nextHoles state action)) :
    ¬ signature.Legal sortCost state action := by
  rintro ⟨expected, _lookup, _sort, fits⟩
  omega

end Signature

/-! ## Executable positive and negative controls -/

private inductive FixtureSort where
  | expr
  | nat
  deriving DecidableEq, Repr

private inductive FixtureHead where
  | add
  | literal
  | successor
  deriving DecidableEq, Repr

private abbrev fixtureSignature : Signature where
  SortType := FixtureSort
  Head := FixtureHead
  resultSort
    | .add | .literal => .expr
    | .successor => .nat
  childSorts
    | .add => [.expr, .expr]
    | .literal => []
    | .successor => [.nat]

private def unitSortCost : FixtureSort → Nat := fun _ => 1

private def expressionState (remaining : Nat) : State fixtureSignature :=
  { holes := [.expr], remaining := remaining }

private def addAction : Action fixtureSignature :=
  { holeIndex := 0, head := .add }

private def successorAction : Action fixtureSignature :=
  { holeIndex := 0, head := .successor }

/-- The binary expression head is legal with one action plus two child slots. -/
theorem typed_add_is_legal_with_three_actions :
    fixtureSignature.Legal unitSortCost (expressionState 3) addAction := by
  exact ⟨.expr, rfl, rfl, by decide⟩

/-- The same structurally well-shaped action is rejected at an expression
hole because its result sort is `nat`. -/
theorem typed_wrong_sort_is_rejected :
    ¬ fixtureSignature.Legal unitSortCost
      (expressionState 3) successorAction := by
  simp [Signature.Legal, expressionState, successorAction,
    fixtureSignature]

/-- Sort correctness does not override the completion budget. -/
theorem typed_add_is_rejected_with_two_actions :
    ¬ fixtureSignature.Legal unitSortCost (expressionState 2) addAction := by
  simp [Signature.Legal, Signature.required, Signature.nextHoles,
    expressionState, addAction, fixtureSignature, unitSortCost]

/-- The successful transition exposes exactly the two typed child holes and
the decremented budget. -/
theorem typed_add_transition_exact :
    fixtureSignature.refine? unitSortCost (expressionState 3) addAction =
      some { holes := [.expr, .expr], remaining := 2 } := by
  simp [Signature.refine?, Signature.required, Signature.nextHoles,
    expressionState, addAction, fixtureSignature, unitSortCost]

#print axioms Signature.refine?_isSome_iff_legal
#print axioms Signature.refine?_some_typed_and_budget_safe
#print axioms Signature.wrong_result_sort_illegal
#print axioms Signature.insufficient_budget_illegal
#print axioms typed_add_is_legal_with_three_actions
#print axioms typed_wrong_sort_is_rejected
#print axioms typed_add_is_rejected_with_two_actions
#print axioms typed_add_transition_exact

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier
