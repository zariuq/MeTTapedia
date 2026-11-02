import Mettapedia.Machines.HEInstructionSource

/-!
# HE instruction completion at a saved caller

The native completion decision selects omission, refusal readback, ordinary
typed evaluation or a tail carrier. The independent reference is the maintained
HE call-return judgment, with public instructions removing raw Empty events.
Both use the reached binding frame and the caller's actual expected type.

Tail eligibility is supplied by the existing type-demand service; this model
checks its use and the additional function-delimiter exclusion. Native source
charging, profile-specific refusal images and C pointer ownership remain separate
correspondence obligations. This is not an alternative HE evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEInstructionCompletion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval

inductive Action where
  | omit | refusal | interpret | tail
  deriving DecidableEq, Repr

def isFunction : Atom → Bool
  | .expression (.symbol "function" :: _) => true
  | _ => false

def plan (publicInstruction allowTail interpretDemand : Bool) (value : Atom) : Action :=
  if publicInstruction && decide (value = Atom.empty) then .omit
  else if value = Atom.notReducible then .refusal
  else if allowTail && !isFunction value && interpretDemand then .tail
  else .interpret

variable {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
  {protectedScope : List String} {typing : EvalTypeService}
  {original expected value : Atom} {bindings : BindingFrame} {result : FrameResult}

theorem stopped_evaluation_iff (stopped : IsEmptyOrErrorRel value) :
    EvalAtomRawRel space dispatch live value expected bindings result
      (protectedScope := protectedScope) (typing := typing) ↔
      result = (value, bindings) := by
  constructor
  · intro ran
    cases ran with
    | emptyOrError => rfl
    | typePass _ _ _ _ notStopped => exact False.elim (notStopped stopped)
    | cast _ _ _ _ _ notStopped => exact False.elim (notStopped stopped)
    | interpretSuccess _ _ _ _ _ notStopped => exact False.elim (notStopped stopped)
    | interpretError _ _ _ _ _ notStopped => exact False.elim (notStopped stopped)
  · rintro rfl
    exact .emptyOrError value expected bindings stopped

/-- Away from the raw refusal marker, the source protocol agrees with typed
evaluation. Stopped values use the existing source passthrough rule. -/
theorem nonrefusal_completion_iff (notRefused : value ≠ Atom.notReducible) :
    CallReturnRel space dispatch live original expected value bindings result
      (protectedScope := protectedScope) (typing := typing) ↔
    EvalAtomRawRel space dispatch live value expected bindings result
      (protectedScope := protectedScope) (typing := typing) := by
  constructor
  · intro completed
    cases completed with
    | notReducible => exact False.elim (notRefused rfl)
    | stopped _ _ _ _ stopped => exact .emptyOrError _ _ _ stopped
    | evaluate _ _ _ _ _ _ _ evaluated => exact evaluated
  · intro evaluated
    by_cases stopped : IsEmptyOrErrorRel value
    · have same := stopped_evaluation_iff stopped |>.mp evaluated
      subst result
      exact .stopped original expected value bindings stopped
    · exact .evaluate original expected value bindings result notRefused stopped evaluated

theorem refusal_completion_iff :
    CallReturnRel space dispatch live original expected Atom.notReducible bindings result
      (protectedScope := protectedScope) (typing := typing) ↔
      result = (original, bindings) := by
  constructor
  · intro completed
    cases completed with
    | notReducible => rfl
    | stopped _ _ _ _ stopped =>
        simp [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty] at stopped
    | evaluate _ _ _ _ _ notRefused => exact False.elim (notRefused rfl)
  · rintro rfl
    exact .notReducible original expected bindings

/-- The source completes one raw occurrence before its public boundary removes
Empty. It has no tail-carrier decision and reads no instruction-array layout. -/
def reference (publicInstruction : Bool) (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (protectedScope : List String) (typing : EvalTypeService)
    (original expected value : Atom) (bindings : BindingFrame)
    (answer : Option FrameResult) : Prop :=
  if publicInstruction && decide (value = Atom.empty) then answer = none
  else ∃ result, CallReturnRel space dispatch live original expected value bindings result
    (protectedScope := protectedScope) (typing := typing) ∧ answer = some result

/-- The selected action is consumed by either continuation implementation.
Every entered computation uses the same reached bindings and expected type. -/
def target (publicInstruction allowTail interpretDemand : Bool)
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (protectedScope : List String) (typing : EvalTypeService)
    (original expected value : Atom) (bindings : BindingFrame)
    (answer : Option FrameResult) : Prop :=
  match plan publicInstruction allowTail interpretDemand value with
  | .omit => answer = none
  | .refusal => answer = some (original, bindings)
  | .interpret | .tail =>
      ∃ result, EvalAtomRawRel space dispatch live value expected bindings result
        (protectedScope := protectedScope) (typing := typing) ∧ answer = some result

theorem completion_refines (publicInstruction allowTail interpretDemand : Bool)
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (protectedScope : List String) (typing : EvalTypeService)
    (original expected value : Atom) (bindings : BindingFrame)
    (answer : Option FrameResult) :
    target publicInstruction allowTail interpretDemand space dispatch live protectedScope
        typing original expected value bindings answer ↔
      reference publicInstruction space dispatch live protectedScope typing
        original expected value bindings answer := by
  by_cases omitted : (publicInstruction && decide (value = Atom.empty)) = true
  · simp [target, reference, plan, omitted]
  · by_cases refused : value = Atom.notReducible
    · subst value
      simp [target, reference, plan, omitted, refusal_completion_iff]
    · by_cases tail : (allowTail && !isFunction value && interpretDemand) = true
      <;> simp [target, reference, plan, omitted, refused, tail,
        nonrefusal_completion_iff refused]

theorem tail_requires_demand (publicInstruction allowTail interpretDemand : Bool)
    (value : Atom) (chosen : plan publicInstruction allowTail interpretDemand value = .tail) :
    allowTail = true ∧ isFunction value = false ∧ interpretDemand = true ∧
      value ≠ Atom.notReducible := by
  unfold plan at chosen
  split at chosen
  · contradiction
  · split at chosen
    · contradiction
    · rename_i notRefused
      split at chosen
      · rename_i eligible
        simp only [Bool.and_eq_true] at eligible
        exact ⟨eligible.1.1, by simpa using eligible.1.2, eligible.2, notRefused⟩
      · contradiction

/-- A function returned by an instruction remains a fresh public invocation;
its own codomain cannot be replaced by the surrounding tail carrier. -/
theorem returned_function_never_tails (publicInstruction allowTail interpretDemand : Bool)
    (body : List Atom) :
    plan publicInstruction allowTail interpretDemand
        (.expression (.symbol "function" :: body)) = .interpret := by
  simp [plan, isFunction, Atom.empty, Atom.notReducible]

theorem omission_does_not_evaluate (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (protectedScope : List String) (typing : EvalTypeService)
    (original expected : Atom) (bindings : BindingFrame) (allowTail interpretDemand : Bool) :
    target true allowTail interpretDemand space dispatch live protectedScope typing
      original expected Atom.empty bindings none := by
  simp [target, plan]

/-- Producer-completed provenance has a different source judgment. Even a
payload spelling the refusal marker stays data under Undefined demand. -/
theorem completed_marker_stays_data (space : Space) (typing : EvalTypeService)
    (bindings : BindingFrame) (protectedScope : List String) :
    CompletedNativeReturnRel space typing Atom.notReducible Atom.undefinedType
      bindings (Atom.notReducible, bindings) (protectedScope := protectedScope) :=
  .keep (Or.inr (Or.inl rfl))

theorem public_empty_and_delimiter_empty_differ :
    plan true true true Atom.empty = .omit ∧
      plan false false true Atom.empty = .interpret := by
  simp [plan, Atom.empty, Atom.notReducible]

theorem private_data_shape_does_not_authorize_tail :
    plan true true false (.expression [.symbol "run", .symbol "payload"]) = .interpret := by
  simp [plan, Atom.empty, Atom.notReducible]

end Mettapedia.Machines.HEInstructionCompletion

#print axioms Mettapedia.Machines.HEInstructionCompletion.stopped_evaluation_iff
#print axioms Mettapedia.Machines.HEInstructionCompletion.nonrefusal_completion_iff
#print axioms Mettapedia.Machines.HEInstructionCompletion.refusal_completion_iff
#print axioms Mettapedia.Machines.HEInstructionCompletion.completion_refines
#print axioms Mettapedia.Machines.HEInstructionCompletion.tail_requires_demand
#print axioms Mettapedia.Machines.HEInstructionCompletion.returned_function_never_tails
#print axioms Mettapedia.Machines.HEInstructionCompletion.omission_does_not_evaluate
#print axioms Mettapedia.Machines.HEInstructionCompletion.completed_marker_stays_data
#print axioms Mettapedia.Machines.HEInstructionCompletion.public_empty_and_delimiter_empty_differ
#print axioms Mettapedia.Machines.HEInstructionCompletion.private_data_shape_does_not_authorize_tail
