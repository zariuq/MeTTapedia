import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic

/-!
# Scoped outcomes and resolved expected-error tests

Returning an error-shaped payload and raising an exception are distinct
constructors. This finite computation language has exhaustive occurrence choice
and branch-local scoped handlers that may recover, discard, or re-raise a fault.
An independent relational semantics specifies the observable occurrences. The
executor instead carries a handler stack and resolves each leaf immediately;
its correspondence preserves multiplicity, not merely membership.

The expected-error policy here is explicit and exhaustive: there must be at
least one raised occurrence, every raised fault must be accepted, and no value
occurrence may remain. It does not select one convenient error. Answer tests
inspect a bag of values and require the absence of unhandled raises. Each test
resolves locally to a Boolean verdict; later handling cannot rewrite a verdict
already resolved in another scope. Reporting these independent verdicts imposes
no first-error ordering requirement.

This is a semantic component and handler-stack algorithm, not native CeTTa
refinement or a specification of a particular surface `catch` or assertion.
In particular branch-local handling differs from an ordered search cutoff.
Choice, selection and exception handlers may not be interchanged without a
separate law. There is no recursion, mutable state, IO, interruption, resource
finalization, or test-plan discovery in this finite model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.ScopedOutcome

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

inductive Outcome (α : Type u) (ε : Type v) where
  | value (payload : α)
  | raised (fault : ε)
  deriving DecidableEq, Repr

abbrev Handler (α : Type u) (ε : Type v) := ε → Option (Outcome α ε)

inductive Computation (α : Type u) (ε : Type v) where
  | pure (payload : α)
  | raise (fault : ε)
  | empty
  | choice (left right : Computation α ε)
  | handle (body : Computation α ε) (handler : Handler α ε)

/-- A handler only inspects raised control; values are transparent. -/
def handleOne (handler : Handler α ε) : Outcome α ε → Option (Outcome α ε)
  | .value value => some (.value value)
  | .raised fault => handler fault

/-- Bottom-up denotation. Handler scope covers the body occurrences, not
siblings of the handled computation. -/
def denote : Computation α ε → List (Outcome α ε)
  | .pure value => [.value value]
  | .raise fault => [.raised fault]
  | .empty => []
  | .choice left right => denote left ++ denote right
  | .handle body handler => (denote body).filterMap (handleOne handler)

/-- Independent handler judgment: returned values are never offered to an
exception handler, and a handler result is not handled again by that handler. -/
inductive Handles (handler : Handler α ε) : List (Outcome α ε) → List (Outcome α ε) → Prop
  | nil : Handles handler [] []
  | value (value : α) {input output} (tail : Handles handler input output) :
      Handles handler (.value value :: input) (.value value :: output)
  | discard (fault : ε) {input output} (dropped : handler fault = none)
      (tail : Handles handler input output) :
      Handles handler (.raised fault :: input) output
  | recover (fault : ε) (result : Outcome α ε) {input output}
      (recovered : handler fault = some result) (tail : Handles handler input output) :
      Handles handler (.raised fault :: input) (result :: output)

inductive Observes : Computation α ε → List (Outcome α ε) → Prop
  | pure (value : α) : Observes (.pure value) [.value value]
  | raise (fault : ε) : Observes (.raise fault) [.raised fault]
  | empty : Observes .empty []
  | choice {left right first second}
      (earlier : Observes left first) (later : Observes right second) :
      Observes (.choice left right) (first ++ second)
  | handle {body handler input output} (evaluated : Observes body input)
      (handled : Handles handler input output) :
      Observes (.handle body handler) output

theorem Handles.sound {handler : Handler α ε} {input output : List (Outcome α ε)}
    (proof : Handles handler input output) : input.filterMap (handleOne handler) = output := by
  induction proof with
  | nil => rfl
  | value value tail ih => simp [handleOne, ih]
  | discard fault dropped tail ih => simp [handleOne, dropped, ih]
  | recover fault result recovered tail ih => simp [handleOne, recovered, ih]

theorem Handles.complete (handler : Handler α ε) (input : List (Outcome α ε)) :
    Handles handler input (input.filterMap (handleOne handler)) := by
  induction input with
  | nil => exact .nil
  | cons head tail ih =>
      cases head with
      | value value => exact .value value ih
      | raised fault =>
          cases found : handler fault with
          | none => simpa [handleOne, found] using Handles.discard fault found ih
          | some result => simpa [handleOne, found] using Handles.recover fault result found ih

theorem Observes.sound {program : Computation α ε} {output : List (Outcome α ε)}
    (proof : Observes program output) : denote program = output := by
  induction proof with
  | pure value => rfl
  | raise fault => rfl
  | empty => rfl
  | choice earlier later ih₁ ih₂ => simp [denote, ih₁, ih₂]
  | handle evaluated handled ih => simpa [denote, ih] using handled.sound

theorem Observes.complete (program : Computation α ε) : Observes program (denote program) := by
  induction program with
  | pure value => exact .pure value
  | raise fault => exact .raise fault
  | empty => exact .empty
  | choice left right ih₁ ih₂ => exact .choice ih₁ ih₂
  | handle body handler ih => exact .handle ih (Handles.complete handler _)

/-- Nearest handler first. A recovered value crosses remaining frames as a
value; a re-raised fault reaches the next surrounding handler. -/
def route : List (Handler α ε) → Outcome α ε → Option (Outcome α ε)
  | [], outcome => some outcome
  | handler :: rest, outcome => (handleOne handler outcome).bind (route rest)

/-- Top-down execution fuses scope handling into leaf publication. It does
not materialize the unhandled result collection at each handler boundary. -/
def execute (handlers : List (Handler α ε)) : Computation α ε → List (Outcome α ε)
  | .pure value => (route handlers (.value value)).toList
  | .raise fault => (route handlers (.raised fault)).toList
  | .empty => []
  | .choice left right => execute handlers left ++ execute handlers right
  | .handle body handler => execute (handler :: handlers) body

theorem execute_eq_denote (program : Computation α ε) (handlers : List (Handler α ε)) :
    execute handlers program = (denote program).filterMap (route handlers) := by
  induction program generalizing handlers with
  | pure value =>
      cases h : route handlers (.value value) <;> simp [execute, denote, h]
  | raise fault =>
      cases h : route handlers (.raised fault) <;> simp [execute, denote, h]
  | empty => rfl
  | choice left right ih₁ ih₂ => simp [execute, denote, ih₁, ih₂]
  | handle body handler ih =>
      simp only [execute, denote, ih, List.filterMap_filterMap]
      rfl

/-- The executable resolver agrees with the independently given scoped
derivations, including every duplicate answer or raised occurrence. -/
theorem execute_iff (program : Computation α ε) (output : List (Outcome α ε)) :
    execute [] program = output ↔ Observes program output := by
  have eq : execute [] program = denote program := by simp [execute_eq_denote, route]
  constructor
  · intro result
    rw [eq] at result
    exact result ▸ Observes.complete program
  · intro proof
    exact eq.trans proof.sound

theorem execute_bag (program : Computation α ε) (output : List (Outcome α ε))
    (proof : Observes program output) :
    (execute [] program : Multiset (Outcome α ε)) = (output : Multiset (Outcome α ε)) := by
  rw [(execute_iff program output).mpr proof]

def Outcome.value? : Outcome α ε → Option α
  | .value payload => some payload
  | .raised _ => none

def Outcome.isValue : Outcome α ε → Bool
  | .value _ => true
  | .raised _ => false

def Outcome.acceptedError (accepts : ε → Bool) : Outcome α ε → Bool
  | .value _ => false
  | .raised fault => accepts fault

inductive Expectation (α : Type u) (ε : Type v) where
  | answers (accepts : Multiset α → Bool)
  | raises (accepts : ε → Bool)

/-- A semantic value observation names all value occurrences explicitly. -/
inductive Values : List (Outcome α ε) → List α → Prop
  | nil : Values [] []
  | cons (value : α) {input output} (tail : Values input output) :
      Values (.value value :: input) (value :: output)

/-- A resolved expectation concerns the entire finite scope. Error tests
require a nonempty observation consisting exclusively of accepted raises. -/
def Satisfies : Expectation α ε → List (Outcome α ε) → Prop
  | .answers accepts, observations =>
      ∃ values, Values observations values ∧ accepts (values : Multiset α) = true
  | .raises accepts, observations =>
      observations ≠ [] ∧ ∀ outcome ∈ observations,
        ∃ fault, outcome = .raised fault ∧ accepts fault = true

/-- Executable test-boundary check. Ordinary value spelling never determines
whether an outcome is an outstanding exception. -/
def resolveObserved : Expectation α ε → List (Outcome α ε) → Bool
  | .answers accepts, observations =>
      observations.all Outcome.isValue &&
        accepts ((observations.filterMap Outcome.value?) : Multiset α)
  | .raises accepts, observations =>
      !observations.isEmpty && observations.all (Outcome.acceptedError accepts)

theorem Values.sound {observations : List (Outcome α ε)} {values : List α}
    (proof : Values observations values) :
    observations.all Outcome.isValue = true ∧ observations.filterMap Outcome.value? = values := by
  induction proof with
  | nil => simp
  | cons value tail ih => simpa [Outcome.isValue, Outcome.value?] using ih

theorem Values.complete (observations : List (Outcome α ε))
    (allValues : observations.all Outcome.isValue = true) :
    Values observations (observations.filterMap Outcome.value?) := by
  induction observations with
  | nil => exact .nil
  | cons head tail ih =>
      cases head with
      | value value =>
          have rest : tail.all Outcome.isValue = true := by
            simpa [Outcome.isValue] using allValues
          exact .cons value (ih rest)
      | raised fault => simp [Outcome.isValue] at allValues

theorem resolveObserved_correct (expectation : Expectation α ε)
    (observations : List (Outcome α ε)) :
    resolveObserved expectation observations = true ↔ Satisfies expectation observations := by
  cases expectation with
  | answers accepts =>
      simp only [resolveObserved, Satisfies, Bool.and_eq_true]
      constructor
      · rintro ⟨allValues, accepted⟩
        exact ⟨_, Values.complete observations allValues, accepted⟩
      · rintro ⟨values, proof, accepted⟩
        obtain ⟨allValues, same⟩ := proof.sound
        exact ⟨allValues, same ▸ accepted⟩
  | raises accepts =>
      simp only [resolveObserved, Satisfies, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
        List.isEmpty_eq_false_iff, List.all_eq_true]
      constructor
      · rintro ⟨nonempty, allAccepted⟩
        refine ⟨nonempty, ?_⟩
        intro outcome member
        have accepted := allAccepted outcome member
        cases outcome with
        | value value => simp [Outcome.acceptedError] at accepted
        | raised fault => exact ⟨fault, rfl, accepted⟩
      · rintro ⟨nonempty, allAccepted⟩
        refine ⟨nonempty, ?_⟩
        intro outcome member
        obtain ⟨fault, same, accepted⟩ := allAccepted outcome member
        simpa [same, Outcome.acceptedError] using accepted

def resolve (expectation : Expectation α ε) (program : Computation α ε) : Bool :=
  resolveObserved expectation (execute [] program)

/-- Adapter consumed by test-plan checking: identity plus a scoped, resolved
verdict, without leaking raw intermediate raises into a sticky global flag. -/
def resolved (id : Id) (expectation : Expectation α ε) (program : Computation α ε) : Id × Bool :=
  (id, resolve expectation program)

theorem resolve_correct (expectation : Expectation α ε) (program : Computation α ε) :
    resolve expectation program = true ↔
      ∃ observations, Observes program observations ∧ Satisfies expectation observations := by
  rw [resolve, resolveObserved_correct]
  constructor
  · intro satisfied
    exact ⟨_, (execute_iff program _).mp rfl, satisfied⟩
  · rintro ⟨observations, observed, satisfied⟩
    rwa [(execute_iff program observations).mpr observed]

theorem resolveObserved_perm (expectation : Expectation α ε)
    {left right : List (Outcome α ε)} (permutation : left.Perm right) :
    resolveObserved expectation left = resolveObserved expectation right := by
  cases expectation with
  | answers accepts =>
      have sameValues :
          (left.filterMap Outcome.value? : Multiset α) =
            (right.filterMap Outcome.value? : Multiset α) := by
        exact Quot.sound (permutation.filterMap _)
      simp only [resolveObserved, permutation.all_eq, sameValues]
  | raises accepts =>
      have sameEmpty : left.isEmpty = right.isEmpty := by
        cases left <;> cases right <;> simp_all
      simp only [resolveObserved, sameEmpty, permutation.all_eq]

/-- Appending another independently resolved scope cannot clear a previous
false verdict. Test identity/discovery obligations belong to the plan checker. -/
theorem resolved_failure_persists (id : Id) (earlier later : List (Id × Bool)) :
    ((earlier ++ (id, false) :: later).all Prod.snd) = false := by
  simp

namespace Controls

inductive Payload where
  | number (value : Nat)
  | errorData (message : String)
  deriving DecidableEq, Repr

def acceptsValues : Expectation Payload String := .answers (fun _ => true)
def expectsBoom : Expectation Payload String := .raises (· == "boom")
def recoverAsData : Handler Payload String := fun fault => some (.value (.errorData fault))
def discardFault : Handler Payload String := fun _ => none

theorem error_data_is_not_raise :
    resolve acceptsValues (.pure (.errorData "boom")) = true ∧
    resolve expectsBoom (.pure (.errorData "boom")) = false ∧
    resolve acceptsValues (.raise "boom") = false ∧
    resolve expectsBoom (.raise "boom") = true := by decide

theorem empty_and_false_payloads_are_values :
    resolve (.answers (fun _ => true) : Expectation Bool String) .empty = true ∧
    resolve (.answers (fun _ => true) : Expectation Bool String) (.pure false) = true ∧
    resolve expectsBoom .empty = false := by decide

theorem recovery_is_local :
    execute [] (.choice (.handle (.raise "boom") recoverAsData) (.raise "other")) =
      [.value (.errorData "boom"), .raised "other"] ∧
    resolve acceptsValues
      (.choice (.handle (.raise "boom") recoverAsData) (.raise "other")) = false := by decide

theorem unexpected_sibling_fault_cannot_pass :
    resolve expectsBoom (.choice (.raise "boom") (.raise "other")) = false ∧
    resolve expectsBoom (.choice (.raise "boom") (.pure (.number 1))) = false := by decide

theorem expected_error_does_not_clear_resolved_failure :
    ([((3 : Nat), false), resolved 4 expectsBoom (.raise "boom")].all Prod.snd) = false ∧
    (resolved 4 expectsBoom (.raise "boom")).2 = true := by decide

theorem duplicate_occurrences_survive :
    execute [] (.handle (.choice (.raise "boom") (.raise "boom")) recoverAsData) =
      [.value (.errorData "boom"), .value (.errorData "boom")] ∧
    (execute [] (.handle (.choice (.raise "boom") (.raise "boom")) recoverAsData)).length = 2 := by
  decide

def rethrowOther : Handler Payload String := fun _ => some (.raised "other")

/-- Re-raising reaches the surrounding handler, not the same frame again.
Reversing these handler scopes changes the returned payload. -/
theorem nested_handler_order_matters :
    execute [] (.handle (.handle (.raise "boom") rethrowOther) recoverAsData) =
      [.value (.errorData "other")] ∧
    execute [] (.handle (.handle (.raise "boom") recoverAsData) rethrowOther) =
      [.value (.errorData "boom")] := by decide

/-- Taking an explored prefix before recovery differs from taking it after
recovery. A branch-local handler is not permission to move selection. -/
theorem selection_and_recovery_do_not_commute :
    let paths : List (Outcome Payload String) := [.raised "boom", .value (.number 7)]
    ((paths.take 1).filterMap (handleOne discardFault)) = [] ∧
    ((paths.filterMap (handleOne discardFault)).take 1) = [.value (.number 7)] := by decide

/-- Ordered cutoff is a different observer: a fault can abandon later paths. -/
def cutoff : List (Outcome α ε) → List α
  | [] => []
  | .value value :: rest => value :: cutoff rest
  | .raised _ :: _ => []

theorem branch_recovery_is_not_cutoff :
    cutoff [.raised "boom", .value (Payload.number 7)] = [] ∧
    execute [] (.handle (.choice (.raise "boom") (.pure (.number 7))) discardFault) =
      [.value (.number 7)] := by decide

end Controls

end Mettapedia.Machines.RunContracts.ScopedOutcome
