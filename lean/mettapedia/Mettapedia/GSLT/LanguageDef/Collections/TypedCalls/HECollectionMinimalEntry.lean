import Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEArgumentMetatypeRole

/-!
# Explicit eval in the collection macro does not admit a typed call

The foldl and minimal-foldl invocations occur beneath explicit eval. The
existing world worker enters InvocationRel with the caller-read operand;
this step needs neither an operator type query nor argument inference.
It does not assert that an arbitrary invoked host operation succeeds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMinimalEntry

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed

theorem eval_entry {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (caller : Option Atom) (operand : Entry.Value) (before : Frame)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    RecursiveMachine.Contextual.WorldStep environment.view environment.services environment.dispatch environment.lookup policy
      ⟨world, label, .work (.minimal live scope caller (.expression .active [.symbol "eval", operand]) before), stack, emitted⟩
      ⟨world, label, .work (.invocation live scope caller (before.read policy operand) before), stack, emitted⟩
      (admission := environment.arguments) := by
  exact .internal (.core (by constructor) rfl .minimalEval (by constructor))

/-- Even an unavailable typing service does not block this actual phase
edge. Subsequent invocation/host validation is deliberately not elided. -/
theorem eval_entry_without_type_answers {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (caller : Option Atom) (operand : Entry.Value) (before : Frame)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    let current := { environment with lookup := fun _ _ _ _ _ _ => False }
    RecursiveMachine.Contextual.WorldStep current.view current.services current.dispatch current.lookup policy
      ⟨world, label, .work (.minimal live scope caller (.expression .active [.symbol "eval", operand]) before), stack, emitted⟩
      ⟨world, label, .work (.invocation live scope caller (before.read policy operand) before), stack, emitted⟩
      (admission := current.arguments) :=
  eval_entry _ policy label world live scope caller operand before stack emitted

theorem typed_entry_is_a_different_phase (live : List Atom) (scope : List String)
    (caller : Option Atom) (operand : Entry.Value) (before : Frame) (expected : Atom) :
    RecursiveTasks.Contextual.Task.atom live scope operand expected before ≠
      RecursiveTasks.Contextual.Task.invocation live scope caller operand before := by
  intro impossible
  cases impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMinimalEntry
