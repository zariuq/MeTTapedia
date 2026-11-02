import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldAdmission
import Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary

/-!
# Joining operand receipts to retained source callback pages

The existing operand boundary evaluates list and initial value once. A callback
refusal retains that captured entrance and its actual resulting world. Accepted
source callback pages refine the independent host-fold judgment, and source
completion retains the outer operand effects. This is an explicit adapter for
the declared host profile, not a modification of the older Eval primitive table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldSourceBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def capturedRequest (request : FoldSourceBoundary.Request)
    (captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before) :
    PagedFoldAdmission.Request :=
  ⟨request.program, request.code.callback request.caller, captured.after, captured.items, captured.initial⟩

structure Session where
  request : FoldSourceBoundary.Request
  captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before
  execution : PagedFoldAdmission.Session
  linked : execution.request = capturedRequest request captured

def advance (allowance : Nat) (session : Session) : Session × Nat :=
  let page := PagedFoldAdmission.advance allowance session.execution
  (⟨session.request, session.captured, page.1,
    (PagedFoldAdmission.advance_keeps_source allowance session.execution).trans session.linked⟩, page.2)

theorem advance_retains_outer_boundary (allowance : Nat) (session : Session) :
    (advance allowance session).1.request = session.request ∧
      (advance allowance session).1.captured = session.captured := ⟨rfl, rfl⟩

theorem completed_source_return (session : Session) (world : Effects.State) (value : Atom)
    (completed : session.execution.current.phase = .done world value) :
    world = session.captured.after ∧
      FoldSourceBoundary.Evaluates session.request.program session.request.caller session.request.code
        session.request.before world value := by
  have source := PagedFoldAdmission.completed_page_is_source_value session.execution world value completed
  rw [session.linked] at source
  change world = session.captured.after ∧ _ at source
  refine ⟨source.1, ?_⟩
  rw [source.1]
  exact session.captured.finish value source.2

theorem callbacks_eventually_complete (session : Session) :
    ∃ allowance value, (advance allowance session).1.execution.current.phase = .done session.captured.after value := by
  obtain ⟨allowance, value, completed⟩ := PagedFoldAdmission.every_retained_page_can_finish session.execution
  refine ⟨allowance, value, ?_⟩
  simpa only [advance, session.linked, capturedRequest] using completed

inductive Result (request : FoldSourceBoundary.Request)
  | reference
  | operandHandoff (saved : FoldSourceBoundary.Handoff)
  | referenceFold (captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before)
  | admitted (session : Session) (source : session.request = request)

def resolve (budget : Nat) (request : FoldSourceBoundary.Request)
    (captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before) : Result request :=
  match FoldCallbackExtraction.prepare budget request.program (request.code.callback request.caller)
      captured.items captured.initial with
  | none => .referenceFold captured
  | some prepared =>
      .admitted ⟨request, captured,
        PagedFoldAdmission.begin (capturedRequest request captured) ⟨prepared.result, prepared.returns captured.after⟩, rfl⟩ rfl

def enter (listFuel initialFuel callbackBudget : Nat) (request : FoldSourceBoundary.Request) : Result request :=
  match FoldSourceBoundary.prepare listFuel initialFuel request.program request.caller request.code request.before with
  | .reference => .reference
  | .handoff saved => .operandHandoff saved
  | .ready captured => resolve callbackBudget request captured

theorem callback_refusal_keeps_captured_world (budget : Nat) (request : FoldSourceBoundary.Request)
    (captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before)
    (refused : FoldCallbackExtraction.prepare budget request.program (request.code.callback request.caller)
      captured.items captured.initial = none) :
    resolve budget request captured = .referenceFold captured := by simp [resolve, refused]

theorem callback_refusal_never_replays_operands (budget : Nat) (request : FoldSourceBoundary.Request)
    (captured : FoldSourceBoundary.Captured request.program request.caller request.code request.before) :
    resolve budget request captured ≠ .reference := by unfold resolve; split <;> simp

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldSourceBoundary
