import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ReadyConstructorBoundary

/-!
# Selected constructor execution and its completed-value boundary

An actual selected arrow, its operator interpretation and its argument
delivery lead to the no-equation constructor return. Open and shared formal
variables remain in the reached frames; no closed-arrow restriction or
whole-body execution equality is imposed. Expression-subject annotations
are not excluded: applicability is a source derivation, not a positive count
of unrelated whole-expression typings.

The result is read and published once at that source boundary. A later
producer-completed type gate is separate and does not reinterpret fields.
It uses the requested type reader, not the public diagnostic type vector.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type
open Mettapedia.Machines.OrderedProtocol.Completion

def assembled (head : String) (arguments : List Entry.Value) : Entry.Value :=
  .expression .active (.symbol head :: arguments)

def published (policy : Policy) (original : Atom) (head : String)
    (arguments : List Entry.Value) (frame : Frame) : Result :=
  publishResult policy original (readResult policy (assembled head arguments, frame))

theorem assembled_erase (head : String) (arguments : List Entry.Value) :
    (assembled head arguments).erase = .expression (.symbol head :: arguments.map Entry.Value.erase) := by
  simp [assembled, Entry.Value.erase]

theorem assembled_read_clean (policy : Policy) (head : String) (arguments : List Entry.Value)
    (frame : Frame) (notError : head ≠ "Error") :
    isErrorAtom (frame.read policy (assembled head arguments)).erase = false := by
  simp [Frame.read, Entry.Value.erase_substitute_environment, assembled_erase,
    Spec.Type.Presentation.TypeSubst.apply, isErrorAtom, notError]

/-- Syntactic equation absence earns the complete source frontier after
argument delivery, independently of every expression typing annotation. -/
theorem absent_call {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (head : String) (arguments : List Entry.Value) (expected : Atom) (frame : Frame)
    (notError : head ≠ "Error")
    (ordinary : NonGroundedCallRel environment.dispatch (assembled head arguments).erase)
    (absent : HEConstructorAdmission.headAbsent (environment.view world label) head = true) :
    Stateful.CallRel environment label world live scope (assembled head arguments) expected frame
      [(assembled head arguments, frame)] world (policy := policy) := by
  apply Stateful.CallRel.absent
  · simp [assembled_erase, IsErrorRel, notError]
  · exact ordinary
  · rw [assembled_erase]
    exact ReadyConstructorBoundary.headAbsent_frontier absent _ (expected :: live) frame.bindings

/-- A constructor's single function row is selected from the actual source
applicability derivation, never from a typing count on the whole expression. -/
theorem selection_of_checks (space : Space) (lookup : CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (original operator expected : Atom)
    (signature : SelectedTypePolicy) (before after : Frame)
    (queried : lookup (invocationTypeScope scope live original expected before.bindings) space
      before.bindings operator Atom.undefinedType [signature.functionType])
    (checked : ApplicationChecksRel space
      (lookup (invocationTypeScope scope live original expected before.bindings) space)
      policy original expected signature before [after] []) :
    InvocationSelectionRel space lookup policy live scope original operator expected before
      (.selected signature [after]) :=
  ⟨[signature.functionType], queried, .selected checked (by simp)⟩

/-- Compose actual local source phases into the constructor's full source
interpretation. The signature may contain shared open formals. Its selection
must have succeeded; the argument run must deliver its actual reached packet. -/
theorem source_from_parts {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (beforeWorld headWorld argumentsWorld : World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (before selectedFrame headFrame argumentsFrame : Frame) (readiness : Entry.Status)
    (operator : Entry.Value) (head : String) (arguments delivered : List Entry.Value)
    (signature : SelectedTypePolicy)
    (entry : Entry.Rel policy.reentry (before.read policy value).status
      (before.read policy value).erase expected .interpret)
    (shape : before.read policy value = .expression readiness (operator :: arguments))
    (selection : environment.arguments.selection (environment.view beforeWorld label) environment.lookup policy live scope
      (before.read policy value).erase operator.erase expected before (.selected signature [selectedFrame]))
    (arity : arguments.length = signature.argumentTypes.length)
    (operatorRun : Stateful.AtomRel environment label beforeWorld
      (signature.functionType :: arguments.map Entry.Value.erase ++ invocationReturnType signature :: live)
      (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
      operator signature.functionType selectedFrame [(.symbol head, headFrame)] headWorld (policy := policy))
    (headContinues : ¬IsEmptyOrErrorRel (.symbol head))
    (argumentsRun : Stateful.ArgumentsRel environment label headWorld
      (.symbol head :: invocationReturnType signature :: live) scope
      (arguments.zip signature.argumentTypes) headFrame
      [(Entry.Value.argumentPacket delivered, argumentsFrame)] argumentsWorld (policy := policy))
    (notError : head ≠ "Error")
    (ordinary : NonGroundedCallRel environment.dispatch (assembled head delivered).erase)
    (absent : HEConstructorAdmission.headAbsent (environment.view argumentsWorld label) head = true) :
    Stateful.AtomRel environment label beforeWorld live scope value expected before
      [published policy (before.read policy value).erase head delivered argumentsFrame]
      argumentsWorld (policy := policy) := by
  have call := absent_call environment policy label argumentsWorld live scope head delivered
    (invocationReturnType signature) argumentsFrame notError ordinary absent
  have calls : Stateful.CallsRel environment label argumentsWorld live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket delivered, argumentsFrame)].map (functionAssemble (.symbol head)))
      [(assembled head delivered, argumentsFrame)] argumentsWorld (policy := policy) := by
    simpa only [List.map_cons, List.map_nil, functionAssemble, Entry.Value.unpackArguments_packet,
      List.append_nil, assembled] using Stateful.CallsRel.cons call Stateful.CallsRel.nil
  have clean := assembled_read_clean policy head delivered argumentsFrame notError
  have priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ([(assembled head delivered, argumentsFrame)].map (readResult policy))
      [readResult policy (assembled head delivered, argumentsFrame)] := by
    simpa only [List.map_cons, List.map_nil, List.filter_cons, readResult, clean,
      Bool.not_false, if_true, List.filter_nil] using
      (SuccessPriorityRel.successes (isError := fun result : Result => isErrorAtom result.1.erase)
        (raw := [readResult policy (assembled head delivered, argumentsFrame)])
        ⟨readResult policy (assembled head delivered, argumentsFrame), by simp, clean⟩)
  simpa only [List.map_cons, List.map_nil, published, Entry.Value.erase] using
    HEStatefulSelectedComposition.selected_of_parts environment policy label beforeWorld headWorld
      argumentsWorld argumentsWorld live scope value expected before selectedFrame headFrame readiness
      operator (.symbol head) arguments signature _ _ _ entry shape selection arity operatorRun
      (by simpa only [Entry.Value.erase] using headContinues)
      (by simpa only [Entry.Value.erase] using argumentsRun) calls priority

theorem published_frame (policy : Policy) (original : Atom) (head : String)
    (arguments : List Entry.Value) (frame : Frame) :
    (published policy original head arguments frame).2 = frame := rfl

theorem published_erase (policy : Policy) (original : Atom) (head : String)
    (arguments : List Entry.Value) (frame : Frame) :
    (published policy original head arguments frame).1.erase =
      (frame.read policy (assembled head arguments)).erase := by
  exact publishResult_erase policy original _

/-- The completed boundary never runs the constructor or its fields again;
its required check is the existing type service with earned result frames. -/
theorem completed_from_cast (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (value : Entry.Value) (expected : Atom) (frame : Frame) (raw : ResultSet)
    (notKeep : ¬CompletedNativeKeepRel value.erase expected)
    (checked : TypeCastBatchRel space value.erase expected frame.bindings raw
      (lookup := lookup) (matching := policy.matching.Rel))
    (models : ∀ result ∈ raw, ∃ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation result.2) :
    ∃ results, NativeCompletedReturnRel space lookup policy value expected frame results := by
  obtain ⟨results, related⟩ := CastResultRel.lift_modelled_batch checked models
  exact ⟨results, .cast notKeep checked related⟩

theorem completed_undefined (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (value : Entry.Value) (frame : Frame) :
    NativeCompletedReturnRel space lookup policy value Atom.undefinedType frame [(value, frame)] :=
  .keep (Or.inr (Or.inl rfl))

/-- A required completed-value gate is first-success over its actual reader.
Repeated typings after the selected range do not duplicate the value. This
query is not inferred from constructor applicability or diagnostic get-type. -/
theorem completed_at_closed_range (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (value : Entry.Value) (range : Atom) (frame : Frame) (earlier later : List Atom)
    (closed : Spec.Type.Presentation.TypeSubst.typeVars range = [])
    (queried : lookup frame.bindings value.erase range (earlier ++ range :: later))
    (rejected : ∀ prior ∈ earlier, ∀ output, ¬policy.matching.Rel range prior frame.bindings output) :
    NativeCompletedReturnRel space lookup policy value range frame [(value, frame)] := by
  by_cases keep : CompletedNativeKeepRel value.erase range
  · exact .keep keep
  · have matched := frame.preserved_type_match policy
      (FirstSuccessSourceApplicability.closed_type_match range frame.bindings
        (sizeOf range + sizeOf range + 2) closed (Nat.le_refl _)).2
    have checked : TypeCastBatchRel space value.erase range frame.bindings [(value.erase, frame.bindings)]
        (lookup := lookup) (matching := policy.matching.Rel) :=
      .success queried rfl rejected matched
    apply NativeCompletedReturnRel.cast keep checked
    exact .cons ⟨rfl, .same frame, by simp⟩ .nil

/-- Parent publication preserves every delivered child's full annotated
read. It changes only the newly assembled root's status. -/
theorem published_successes (policy : Policy) (marked : policy.marking = .successes)
    (original : Atom) (head : String) (arguments : List Entry.Value) (frame : Frame)
    (notError : head ≠ "Error") :
    (published policy original head arguments frame).1 =
      .expression .held (.symbol head :: arguments.map (frame.read policy)) := by
  simp [published, publishResult, readResult, Frame.read, assembled, Entry.Value.substitute,
    Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase, marked, isErrorAtom, notError]

theorem published_unchanged (policy : Policy) (marked : policy.marking = .unchanged)
    (original : Atom) (head : String) (arguments : List Entry.Value) (frame : Frame)
    (notError : head ≠ "Error") :
    (published policy original head arguments frame).1 =
      .expression (if (frame.read policy (assembled head arguments)).erase == original then .held else .active)
        (.symbol head :: arguments.map (frame.read policy)) := by
  simp [published, publishResult, readResult, Frame.read, assembled, Entry.Value.substitute,
    Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase, marked, isErrorAtom, notError]

theorem published_unmarked (policy : Policy) (marked : policy.marking = .none)
    (original : Atom) (head : String) (arguments : List Entry.Value) (frame : Frame)
    (notError : head ≠ "Error") :
    (published policy original head arguments frame).1 =
      .expression .active (.symbol head :: arguments.map (frame.read policy)) := by
  by_cases error : head = "Error"
  · exact (notError error).elim
  simp [published, publishResult, readResult, Frame.read, assembled, Entry.Value.substitute,
    Entry.Value.publish, Entry.publish, Entry.Value.withStatus, Entry.Value.erase, marked]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorSource
