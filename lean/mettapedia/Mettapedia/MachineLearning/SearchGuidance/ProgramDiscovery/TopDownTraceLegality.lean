import Mathlib

/-!
# Top-down TGAD traces and current-state legality

TGAD search emits a preorder action stream while some older decoders expose a
postfix token stream.  Valid traces are isomorphic, but their online legality
states are not interchangeable.  This module makes both facts explicit.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

/-- A small ranked action signature sufficient to expose traversal order and
open-hole legality. -/
inductive TGADAction where
  | atom (token : Nat)
  | unary (token : Nat)
  | binary (token : Nat)
  deriving DecidableEq, Repr

namespace TGADAction

def token : TGADAction → Nat
  | .atom value | .unary value | .binary value => value

def arity : TGADAction → Nat
  | .atom _ => 0
  | .unary _ => 1
  | .binary _ => 2

end TGADAction

/-- A valid top-down action trace.  Constructor order is emission order. -/
inductive TopDownTrace where
  | atom (token : Nat)
  | unary (token : Nat) (child : TopDownTrace)
  | binary (token : Nat) (left right : TopDownTrace)
  deriving DecidableEq, Repr

/-- A valid postfix trace.  Children occur structurally before their parent. -/
inductive PostfixTrace where
  | atom (token : Nat)
  | unary (child : PostfixTrace) (token : Nat)
  | binary (left right : PostfixTrace) (token : Nat)
  deriving DecidableEq, Repr

def TopDownTrace.toPostfix : TopDownTrace → PostfixTrace
  | .atom token => .atom token
  | .unary token child => .unary child.toPostfix token
  | .binary token left right => .binary left.toPostfix right.toPostfix token

def PostfixTrace.toTopDown : PostfixTrace → TopDownTrace
  | .atom token => .atom token
  | .unary child token => .unary token child.toTopDown
  | .binary left right token => .binary token left.toTopDown right.toTopDown

/-- Flatten a valid trace into the actual preorder action order. -/
def TopDownTrace.actions : TopDownTrace → List TGADAction
  | .atom token => [.atom token]
  | .unary token child => .unary token :: child.actions
  | .binary token left right =>
      .binary token :: (left.actions ++ right.actions)

/-- Flatten a valid trace into postfix action order. -/
def PostfixTrace.actions : PostfixTrace → List TGADAction
  | .atom token => [.atom token]
  | .unary child token => child.actions ++ [.unary token]
  | .binary left right token =>
      left.actions ++ right.actions ++ [.binary token]

/-- Top-down to postfix and back preserves the complete valid trace. -/
@[simp] theorem PostfixTrace.toTopDown_toPostfix (trace : TopDownTrace) :
    trace.toPostfix.toTopDown = trace := by
  induction trace with
  | atom => rfl
  | unary token child ih => simp [TopDownTrace.toPostfix, PostfixTrace.toTopDown, ih]
  | binary token left right ihLeft ihRight =>
      simp [TopDownTrace.toPostfix, PostfixTrace.toTopDown, ihLeft, ihRight]

/-- Postfix to top-down and back preserves the complete valid trace. -/
@[simp] theorem TopDownTrace.toPostfix_toTopDown (trace : PostfixTrace) :
    trace.toTopDown.toPostfix = trace := by
  induction trace with
  | atom => rfl
  | unary child token ih => simp [PostfixTrace.toTopDown, TopDownTrace.toPostfix, ih]
  | binary left right token ihLeft ihRight =>
      simp [PostfixTrace.toTopDown, TopDownTrace.toPostfix, ihLeft, ihRight]

/-- Conversion changes traversal order, not the multiset of action tokens. -/
theorem TopDownTrace.actions_toPostfix_perm (trace : TopDownTrace) :
    trace.toPostfix.actions.Perm trace.actions := by
  induction trace with
  | atom => simp [TopDownTrace.toPostfix, PostfixTrace.actions, TopDownTrace.actions]
  | unary token child ih =>
      simpa [TopDownTrace.toPostfix, PostfixTrace.actions, TopDownTrace.actions] using
        (ih.append_right [TGADAction.unary token]).trans List.perm_append_comm
  | binary token left right ihLeft ihRight =>
      simp only [TopDownTrace.toPostfix, PostfixTrace.actions, TopDownTrace.actions]
      exact ((ihLeft.append ihRight).append_right [TGADAction.binary token]).trans
        List.perm_append_comm

/-! ## Runtime construction state -/

inductive HoleRole where
  | term
  | atomOnly
  deriving DecidableEq, Repr

/-- One live construction obligation. -/
structure OpenHole where
  role : HoleRole
  parentToken : Option Nat
  argumentId : Nat
  depth : Nat
  deriving DecidableEq, Repr

/-- The online state used by top-down search. -/
structure TGADConstructionState where
  openHoles : List OpenHole
  position : Nat
  deriving DecidableEq, Repr

/-- Role-sensitive legality.  An atom-only hole cannot be filled by a
compound action. -/
def actionLegalForRole : HoleRole → TGADAction → Bool
  | .term, _ => true
  | .atomOnly, .atom _ => true
  | .atomOnly, _ => false

/-- Legality is decided against the head hole of the current state. -/
def actionLegalAt (state : TGADConstructionState) (action : TGADAction) : Bool :=
  match state.openHoles with
  | [] => false
  | hole :: _ => actionLegalForRole hole.role action

private def childHoles (hole : OpenHole) (action : TGADAction) : List OpenHole :=
  let parent := some action.token
  let depth := hole.depth + 1
  match action with
  | .atom _ => []
  | .unary _ => [⟨.term, parent, 0, depth⟩]
  | .binary _ =>
      [⟨.atomOnly, parent, 0, depth⟩, ⟨.term, parent, 1, depth⟩]

/-- Execute one legal top-down construction action. -/
def advanceConstruction
    (state : TGADConstructionState) (action : TGADAction) :
    Option TGADConstructionState :=
  match state.openHoles with
  | [] => none
  | hole :: remaining =>
      if actionLegalForRole hole.role action then
        some ⟨childHoles hole action ++ remaining, state.position + 1⟩
      else none

theorem advanceConstruction_position
    {state next : TGADConstructionState} {action : TGADAction}
    (advanced : advanceConstruction state action = some next) :
    next.position = state.position + 1 := by
  cases holesEquation : state.openHoles with
  | nil => simp [advanceConstruction, holesEquation] at advanced
  | cons hole remaining =>
      by_cases legal : actionLegalForRole hole.role action = true
      · simp [advanceConstruction, holesEquation, legal] at advanced
        subst next
        rfl
      · have illegal : actionLegalForRole hole.role action = false := by
          exact Bool.eq_false_of_not_eq_true legal
        simp [advanceConstruction, holesEquation, illegal] at advanced

/-- Retrieved evidence carries its source state for provenance, but admission
is evaluated against the current construction state. -/
structure RetrievedActionEvidence where
  sourceState : TGADConstructionState
  action : TGADAction
  weight : ℚ
  deriving DecidableEq, Repr

def transportedActionWeight
    (current : TGADConstructionState) (evidence : RetrievedActionEvidence) : ℚ :=
  if actionLegalAt current evidence.action then evidence.weight else 0

/-- Illegal actions receive exactly zero transported support. -/
theorem transportedActionWeight_eq_zero_of_current_illegal
    (current : TGADConstructionState) (evidence : RetrievedActionEvidence)
    (illegal : actionLegalAt current evidence.action = false) :
    transportedActionWeight current evidence = 0 := by
  simp [transportedActionWeight, illegal]

def termStateAtOne : TGADConstructionState :=
  ⟨[⟨.term, some 7, 1, 2⟩], 1⟩

def atomStateAtOne : TGADConstructionState :=
  ⟨[⟨.atomOnly, some 7, 1, 2⟩], 1⟩

/-- Equal token positions do not identify the construction state. -/
theorem equal_position_unequal_tree_state_fixture :
    termStateAtOne.position = atomStateAtOne.position ∧
      termStateAtOne ≠ atomStateAtOne ∧
      actionLegalAt termStateAtOne (.unary 9) = true ∧
      actionLegalAt atomStateAtOne (.unary 9) = false := by
  decide

def sourceLegalCurrentIllegalEvidence : RetrievedActionEvidence where
  sourceState := termStateAtOne
  action := .unary 9
  weight := 3

/-- Source-state legality cannot resurrect an action illegal in the current
state. -/
theorem source_legal_current_illegal_has_zero_support :
    actionLegalAt sourceLegalCurrentIllegalEvidence.sourceState
        sourceLegalCurrentIllegalEvidence.action = true ∧
      actionLegalAt atomStateAtOne sourceLegalCurrentIllegalEvidence.action = false ∧
      transportedActionWeight atomStateAtOne
        sourceLegalCurrentIllegalEvidence = 0 := by
  decide

/-- A postfix stack mask checks operand availability, not preorder hole role. -/
def postfixStackLegal (stackDepth : Nat) : TGADAction → Bool
  | .atom _ => true
  | .unary _ => decide (1 ≤ stackDepth)
  | .binary _ => decide (2 ≤ stackDepth)

/-- Applying a postfix mask to preorder construction admits a compound action
that the current atom-only hole rejects. -/
theorem postfix_mask_admits_preorder_illegal_fixture :
    postfixStackLegal 2 (.binary 11) = true ∧
      actionLegalAt atomStateAtOne (.binary 11) = false ∧
      advanceConstruction atomStateAtOne (.binary 11) = none := by
  decide

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
