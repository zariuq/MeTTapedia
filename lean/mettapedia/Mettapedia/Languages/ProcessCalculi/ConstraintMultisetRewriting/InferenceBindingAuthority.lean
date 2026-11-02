import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution

/-!
# Binding authorization for actual scoped inference receipts

An execution receipt records a successful worklist return. Publication through
this adapter additionally requires the returned assignment to agree with the
pure capture inclusion on the dependencies of the caller's protected values.
Fresh names and an accepted proof do not establish that permission.

Protected values are an external parameter of the adapter, not a policy chosen
by the execution being authorized. They denote current resolved observations;
raw triangular binding tables require their separate dereferencing contract.
The underlying firing, solver receipt and source proof projection are unchanged.
The native publication path has a separate obligation to enforce this check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBindingAuthority

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open ScopedInferenceValues (base)

variable {Local Shared : Type}
  {locals : Local → MetaArity base} {captures : Shared → MetaArity base}
  [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]
  {definition : ValidatedCalculusLanguageDef}

def captureInclusion (execution : InferenceScopedExecution.Receipt definition locals captures) :
    Assignment captures
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures)
        execution.update.declaration) :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource execution.update)
    (ContextualSelectionViews.capturedTarget locals captures)

/-- The same dependency condition is used at every object context and sort. -/
def Permits (execution : InferenceScopedExecution.Receipt definition locals captures)
    (protectedValues : List (Observation base captures)) : Prop :=
  ∀ observation ∈ protectedValues, ∀ name ∈ support observation.2.2,
    execution.capturedAnswer name = captureInclusion execution name

theorem Permits.preserves
    {execution : InferenceScopedExecution.Receipt definition locals captures}
    {protectedValues : List (Observation base captures)} (authorized : Permits execution protectedValues)
    (observation : Observation base captures) (member : observation ∈ protectedValues) :
    instantiateObservation execution.capturedAnswer observation =
      instantiateObservation (captureInclusion execution) observation := by
  rcases observation with ⟨context, sort, term⟩
  exact congrArg observe (instantiate_congr execution.capturedAnswer (captureInclusion execution)
    term (fun name inside => authorized _ member name inside))

theorem Permits.restrict
    {execution : InferenceScopedExecution.Receipt definition locals captures}
    {all smaller : List (Observation base captures)} (authorized : Permits execution all)
    (subset : ∀ observation ∈ smaller, observation ∈ all) : Permits execution smaller :=
  fun observation member => authorized observation (subset observation member)

theorem empty_policy (execution : InferenceScopedExecution.Receipt definition locals captures) :
    Permits execution [] := by
  intro observation member
  cases member

structure AuthorizedReceipt (definition : ValidatedCalculusLanguageDef)
    (locals : Local → MetaArity base) (captures : Shared → MetaArity base)
    [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]
    (protectedValues : List (Observation base captures)) where
  execution : InferenceScopedExecution.Receipt definition locals captures
  permitted : Permits execution protectedValues

namespace AuthorizedReceipt

variable {protectedValues : List (Observation base captures)}
  (receipt : AuthorizedReceipt definition locals captures protectedValues)

theorem protected_observation_unchanged (observation : Observation base captures)
    (member : observation ∈ protectedValues) :
    instantiateObservation receipt.execution.capturedAnswer observation =
      instantiateObservation (captureInclusion receipt.execution) observation :=
  receipt.permitted.preserves observation member

/-- Authorization adds no replacement source, selection or proof derivation. -/
def firing := receipt.execution.firing

theorem source_inputs_selection :
    receipt.firing.source = .inl receipt.execution.id ∧
      receipt.firing.inputs = .inl receipt.execution.arguments ∧
      receipt.firing.picked = receipt.execution.selection :=
  receipt.execution.source_inputs_selection

theorem answer_still_solves_external_frame :
    ContextualFrameUnifier.Models receipt.execution.capturedAnswer receipt.execution.extraFrame :=
  receipt.execution.captured_answer_solves_external_frame

end AuthorizedReceipt

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBindingAuthority
