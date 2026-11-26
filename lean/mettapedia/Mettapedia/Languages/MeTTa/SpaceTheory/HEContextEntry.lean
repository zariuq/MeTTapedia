import Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

/-!
# The source reading of explicit context instructions

Context handles are payloads, not necessarily injective names. Entry
chooses a context whose payload matches the request and saves the
parent's identity. Reading the current context gives its payload,
not the atoms that happen to be in it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEContextEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup Frame Policy Result WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual
  (Control Continuation Task UnscopedControl managedContextControl)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldLocalStepWith LocalStepWith)
open HEFocused (Focus Parent)

inductive Instruction where
  | evalc (operand : Entry.Value) (handle : GroundedValue)
  | metta (operand expected : Entry.Value) (handle : GroundedValue)
  | contextSpace

structure Request where
  live : List Atom
  scope : List String
  caller : Option Atom
  status : Entry.Status
  instruction : Instruction
  frame : Frame

def Instruction.syntax : Instruction → List Entry.Value
  | .evalc operand handle => [.symbol "evalc", operand, .grounded handle]
  | .metta operand expected handle => [.symbol "metta", operand, expected, .grounded handle]
  | .contextSpace => [.symbol "context-space"]

def Request.task (request : Request) : Task :=
  .minimal request.live request.scope request.caller
    (.expression request.status request.instruction.syntax) request.frame

def Request.recognize : Task → Option Request
  | .minimal live scope caller (.expression status [.symbol "evalc", operand, .grounded handle]) frame =>
    some ⟨live, scope, caller, status, .evalc operand handle, frame⟩
  | .minimal live scope caller (.expression status [.symbol "metta", operand, expected, .grounded handle]) frame =>
    some ⟨live, scope, caller, status, .metta operand expected handle, frame⟩
  | .minimal live scope caller (.expression status [.symbol "context-space"]) frame =>
    some ⟨live, scope, caller, status, .contextSpace, frame⟩
  | _ => none

@[simp] theorem Request.recognize_task (request : Request) : recognize request.task = some request := by
  rcases request with ⟨_, _, _, _, instruction, _⟩
  cases instruction <;> rfl

theorem Request.recognize_exact {task : Task} {request : Request}
    (recognized : recognize task = some request) : request.task = task := by
  unfold recognize at recognized
  split at recognized
  all_goals cases recognized
  all_goals rfl

@[simp] theorem not_native (request : Request) : HEFocused.NativeRequest.recognize request.task = none := by
  rcases request with ⟨_, _, _, _, instruction, _⟩
  cases instruction <;> rfl

@[simp] theorem not_scope (request : HEFocused.NativeRequest) : Request.recognize request.task = none := by
  cases request
  rfl

variable {Context World : Type}

/-- The part of entering a child that does not inspect a space or execute
its contents. Reading the operand bindings does not evaluate the operand. -/
def Request.childTask (policy : Policy) (request : Request) : Option (GroundedValue × Task) :=
  match request.instruction with
  | .evalc operand handle =>
    some (handle, .invocation request.live request.scope request.caller (request.frame.read policy operand) request.frame)
  | .metta operand expected handle =>
    some (handle, .atom request.live request.scope operand expected.erase request.frame)
  | .contextSpace => none

def Resulting (services : WorldServices Context World) (policy : Policy)
    (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (next : Focus Context World) : Prop :=
  match request.childTask policy with
  | some (handle, task) =>
    ∃ child, services.contextPayload child = handle ∧
      next = ⟨world, child, .work task, [], ⟨scope, stack⟩ :: parents, emitted⟩
  | none =>
    next = ⟨world, scope, .returning [(.grounded (services.contextPayload scope), request.frame)],
      stack, parents, emitted⟩

/-- The legal child entries are in bijection with the fibre of the
presented handle. There is no additional branch from the contents of a
space at this boundary, nor can equal contents identify two members. -/
def entryFibre (services : WorldServices Context World) (policy : Policy)
    (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (handle : GroundedValue) (task : Task)
    (prepared : request.childTask policy = some (handle, task)) :
    { child : Context // services.contextPayload child = handle } ≃
      { next : Focus Context World // Resulting services policy request world scope stack parents emitted next } where
  toFun child := ⟨⟨world, child.1, .work task, [], ⟨scope, stack⟩ :: parents, emitted⟩, by
    rw [Resulting, prepared]
    exact ⟨child.1, child.2, rfl⟩⟩
  invFun next := ⟨next.1.scope, by
    rcases next with ⟨reached, accepted⟩
    simp only [Resulting, prepared] at accepted
    obtain ⟨child, named, rfl⟩ := accepted
    exact named⟩
  left_inv _ := Subtype.ext rfl
  right_inv next := by
    rcases next with ⟨reached, accepted⟩
    apply Subtype.ext
    have result := accepted
    simp only [Resulting, prepared] at result
    obtain ⟨child, _, rfl⟩ := result
    rfl

/-- Entry has at most one successor exactly when its matching identities
are subsingleton. This is a local statement; a provider need not make all
handles injective to justify a single target for one inhabited search. -/
theorem entry_has_at_most_one_iff (services : WorldServices Context World) (policy : Policy)
    (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (handle : GroundedValue) (task : Task)
    (prepared : request.childTask policy = some (handle, task)) :
    Subsingleton { next : Focus Context World // Resulting services policy request world scope stack parents emitted next } ↔
      Subsingleton { child : Context // services.contextPayload child = handle } := by
  let entered := entryFibre services policy request world scope stack parents emitted handle task prepared
  exact ⟨fun unique => ⟨fun a b => entered.injective (unique.allEq _ _)⟩,
    fun unique => ⟨fun a b => entered.symm.injective (unique.allEq _ _)⟩⟩

section Steps

variable {admission : ArgumentService} {view : World → Context → Space}
  {services : WorldServices Context World} {dispatch : GroundedDispatch}
  {lookup : CastLookup} {policy : Policy}

private theorem no_flat_scope {world : World} {scope : Context} {request : Request}
    {stack remaining : List Continuation} {target : Control}
    (unmanaged : managedContextControl (Control.work request.task : Control Context) = false)
    (step : LocalStepWith admission (view world scope) dispatch lookup policy
      (.work request.task, stack) (target, remaining))
    (unscoped : ∃ source : Control Context, UnscopedControl source target) : False := by
  rcases request with ⟨live, names, caller, ready, instruction, frame⟩
  cases instruction with
  | contextSpace => cases unmanaged
  | evalc operand handle =>
    generalize shape : (Control.work (Request.task ⟨live, names, caller, ready, .evalc operand handle, frame⟩),
      stack) = input at step
    cases step <;> simp [Request.task, Instruction.syntax] at shape
    · obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := shape
      have falseHead : Minimal.embeddedInstruction
          (Entry.Value.expression ready [.symbol "evalc", operand, .grounded handle]).erase = false := by assumption
      simp [Entry.Value.erase, Minimal.embeddedInstruction] at falseHead
    · obtain ⟨_, notAChild⟩ := unscoped
      cases notAChild
  | metta operand expected handle =>
    generalize shape : (Control.work (Request.task ⟨live, names, caller, ready, .metta operand expected handle, frame⟩),
      stack) = input at step
    cases step <;> simp [Request.task, Instruction.syntax] at shape
    · obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := shape
      have falseHead : Minimal.embeddedInstruction
          (Entry.Value.expression ready [.symbol "metta", operand, expected, .grounded handle]).erase = false :=
        by assumption
      simp [Entry.Value.erase, Minimal.embeddedInstruction] at falseHead
    · obtain ⟨_, notAChild⟩ := unscoped
      cases notAChild

/-- Exact in the live source, including hosts whose context payloads
collide. The equations here do not identify those contexts. -/
theorem step_iff (request : Request) (world : World) (scope : Context) (stack : List Continuation)
    (parents : List (Parent Context)) (emitted : List Result) (next : Focus Context World) :
    HEFocused.Move admission view services dispatch lookup policy
      ⟨world, scope, .work request.task, stack, parents, emitted⟩ next ↔
      Resulting services policy request world scope stack parents emitted next := by
  constructor
  · intro moved
    cases moved with
    | perform step =>
      change WorldLocalStepWith admission view services dispatch lookup policy world scope
        (.work request.task, stack) _ _ at step
      generalize shape : (Control.work request.task, stack) = input at step
      cases step with
      | core incoming unmanaged performed outgoing =>
        cases incoming with
        | work task =>
          have fields := Prod.mk.inj shape
          obtain rfl := Control.work.inj fields.1
          cases fields.2
          exact (no_flat_scope unmanaged performed ⟨_, outgoing⟩).elim
        | returning => cases shape
      | evalc | metta | contextSpace =>
        rcases request with ⟨live, names, caller, ready, instruction, frame⟩
        cases instruction <;> simp [Request.task, Instruction.syntax] at shape
        all_goals
          rcases shape with ⟨⟨rfl, rfl, rfl, h, rfl⟩, rfl⟩
          first
          | obtain ⟨rfl, rfl, e⟩ := h; exact ⟨_, e.symm, rfl⟩
          | obtain ⟨rfl, rfl, rfl, e⟩ := h; exact ⟨_, e.symm, rfl⟩
          | cases h; rfl
      | _ =>
        rcases request with ⟨_, _, _, _, instruction, _⟩
        cases instruction <;> simp [Request.task, Instruction.syntax] at shape
  · rcases request with ⟨live, names, caller, ready, instruction, frame⟩
    cases instruction with
    | evalc operand handle =>
      rintro ⟨child, identified, rfl⟩
      cases identified
      exact HEFocused.Move.perform (before := ⟨world, scope, .work
        (Request.task ⟨live, names, caller, ready, .evalc operand (services.contextPayload child), frame⟩),
        stack, parents, emitted⟩) (WorldLocalStepWith.evalc (childLabel := child))
    | metta operand expected handle =>
      rintro ⟨child, identified, rfl⟩
      cases identified
      exact HEFocused.Move.perform (before := ⟨world, scope, .work
        (Request.task ⟨live, names, caller, ready, .metta operand expected (services.contextPayload child), frame⟩),
        stack, parents, emitted⟩) (WorldLocalStepWith.metta (childLabel := child))
    | contextSpace =>
      intro result
      cases result
      exact HEFocused.Move.perform (before := ⟨world, scope, .work
        (Request.task ⟨live, names, caller, ready, .contextSpace, frame⟩),
        stack, parents, emitted⟩) WorldLocalStepWith.contextSpace

end Steps

end Mettapedia.Languages.MeTTa.SpaceTheory.HEContextEntry
