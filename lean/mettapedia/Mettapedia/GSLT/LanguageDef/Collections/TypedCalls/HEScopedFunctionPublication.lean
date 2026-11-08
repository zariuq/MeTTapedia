import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypeContinuationScope

/-!
# Scoped publication of the pending function-argument program

The packet below is the actual chain/call-native/unify/cons-atom/return
program emitted for successful operator interpretation. It retains complete
annotated operands. Selective substitution acts on this packet at publication,
not separately at every operand-entry rule. Static applicability still uses
the authored function type before this operation.

The proved retirement fragment is an isolated fresh closed type assignment.
The full native alias-class projection is not identified with this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEScopedFunctionPublication

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEPrivateTypePublication

def nativeCall (name : String) (callback : GroundedValue) (arguments : List Entry.Value) : Entry.Value :=
  .expression .active [.symbol "function", .expression .active
    [.symbol "call-native", .symbol name, .grounded callback, .expression .active arguments]]

theorem nativeCall_erase (name : String) (callback : GroundedValue) (arguments : List Entry.Value) :
    (nativeCall name callback arguments).erase =
      HETypeContinuationScope.nativeCall name callback (arguments.map Entry.Value.erase) := by
  simp [nativeCall, HETypeContinuationScope.nativeCall, Entry.Value.erase]

/-- The type vector includes the final range, just as the actual
interpret_function packet removes only the leading arrow symbol. -/
def pending (callback : GroundedValue) (subject : Entry.Value)
    (arguments parameterAndRange : List Entry.Value) (expected context operator : Entry.Value)
    (answers unpacked result : String) : Entry.Value :=
  .expression .active [.symbol "chain",
    nativeCall "interpret_args" callback
      [subject, .expression .active arguments, .expression .active parameterAndRange, expected, context],
    .var answers,
    .expression .active [.symbol "unify", .expression .active [.symbol "Ok", .var unpacked], .var answers,
      .expression .active [.symbol "chain",
        .expression .active [.symbol "cons-atom", operator, .var unpacked], .var result,
        .expression .active [.symbol "return", .var result]],
      .expression .active [.symbol "return", .var answers]]]

/-- The full operator-evaluation emission, including the native
return-on-error wrapper. The pending packet is not run on an error result. -/
def functionBody (argsCallback errorCallback : GroundedValue) (operator : Entry.Value)
    (arguments parameterAndRange : List Entry.Value) (expected context : Entry.Value)
    (reduced answers unpacked result : String) : Entry.Value :=
  let subject := Entry.Value.expression .active (operator :: arguments)
  let functionType := Entry.Value.expression .active (.symbol "->" :: parameterAndRange)
  .expression .active [.symbol "chain",
    .expression .active [.symbol "metta", operator, functionType, context], .var reduced,
    nativeCall "return_on_error" errorCallback
      [.var reduced, pending argsCallback subject arguments parameterAndRange expected context
        (.var reduced) answers unpacked result]]

theorem substitute_nativeCall (valuation : String → Entry.Value) (name : String)
    (callback : GroundedValue) (arguments : List Entry.Value) :
    Entry.Value.substitute .preserve valuation (nativeCall name callback arguments) =
      nativeCall name callback (arguments.map (Entry.Value.substitute .preserve valuation)) := by
  simp [nativeCall, Entry.Value.substitute, Entry.Value.rebuildStatus]

/-- One publication substitutes the entire emitted packet coherently. The
generated instruction variables are fixed; operand values keep all marks. -/
theorem substitute_pending (valuation : String → Entry.Value) (callback : GroundedValue)
    (subject : Entry.Value) (arguments parameterAndRange : List Entry.Value)
    (expected context operator : Entry.Value) (answers unpacked result : String)
    (answersFixed : valuation answers = .var answers)
    (unpackedFixed : valuation unpacked = .var unpacked)
    (resultFixed : valuation result = .var result) :
    Entry.Value.substitute .preserve valuation
      (pending callback subject arguments parameterAndRange expected context operator answers unpacked result) =
      pending callback (Entry.Value.substitute .preserve valuation subject)
        (arguments.map (Entry.Value.substitute .preserve valuation))
        (parameterAndRange.map (Entry.Value.substitute .preserve valuation))
        (Entry.Value.substitute .preserve valuation expected)
        (Entry.Value.substitute .preserve valuation context)
        (Entry.Value.substitute .preserve valuation operator) answers unpacked result := by
  simp [pending, nativeCall, Entry.Value.substitute, Entry.Value.rebuildStatus,
    answersFixed, unpackedFixed, resultFixed]

theorem substitute_functionBody (valuation : String → Entry.Value)
    (argsCallback errorCallback : GroundedValue) (operator : Entry.Value)
    (arguments parameterAndRange : List Entry.Value) (expected context : Entry.Value)
    (reduced answers unpacked result : String)
    (reducedFixed : valuation reduced = .var reduced)
    (answersFixed : valuation answers = .var answers)
    (unpackedFixed : valuation unpacked = .var unpacked)
    (resultFixed : valuation result = .var result) :
    Entry.Value.substitute .preserve valuation
      (functionBody argsCallback errorCallback operator arguments parameterAndRange expected context
        reduced answers unpacked result) =
      functionBody argsCallback errorCallback (Entry.Value.substitute .preserve valuation operator)
        (arguments.map (Entry.Value.substitute .preserve valuation))
        (parameterAndRange.map (Entry.Value.substitute .preserve valuation))
        (Entry.Value.substitute .preserve valuation expected)
        (Entry.Value.substitute .preserve valuation context) reduced answers unpacked result := by
  simp [functionBody, pending, nativeCall, Entry.Value.substitute, Entry.Value.rebuildStatus,
    reducedFixed, answersFixed, unpackedFixed, resultFixed]

/-- This singleton operation is admitted only for the independently proved
isolated-assignment fragment. Keeping the name does not read its value. -/
def publishIsolated (retained : List String) (name : String) (frame : Frame)
    (payload : Entry.Value) : Entry.Value :=
  if name ∈ retained then payload else exposeName name frame payload

theorem publish_kept (retained : List String) (name : String) (frame : Frame)
    (payload : Entry.Value) (kept : name ∈ retained) :
    publishIsolated retained name frame payload = payload := by
  simp [publishIsolated, kept]

theorem publish_fresh_pending (policy : Policy) (before : Frame) (name : String)
    (actual : Atom) (closed : TypeSubst.typeVars actual = [])
    (notUndefined : actual ≠ Atom.undefinedType) (notAtom : actual ≠ Atom.atomType)
    (fresh : name ∉ specBindingVars before.bindings)
    (callback : GroundedValue) (subject : Entry.Value) (arguments parameterAndRange : List Entry.Value)
    (expected context operator : Entry.Value) (answers unpacked result : String)
    (answersDifferent : answers ≠ name) (unpackedDifferent : unpacked ≠ name) (resultDifferent : result ≠ name) :
    ∃ selected : Frame,
      Frame.TypeRenewRel policy actual (.var name) before selected ∧
      dropAssignment name selected.bindings = before.bindings ∧
      dropEnvironment name selected.environment = before.environment ∧
      exposeName name selected
        (pending callback subject arguments parameterAndRange expected context operator answers unpacked result) =
      let read := Entry.Value.substitute .preserve (Entry.Value.resolve [(name, Entry.Value.ofAtom actual)])
      pending callback (read subject) (arguments.map read) (parameterAndRange.map read)
        (read expected) (read context) (read operator) answers unpacked result := by
  obtain ⟨selected, renewed, _, _, bindings, environment, payload⟩ :=
    fresh_closed_type_publication policy before name actual closed notUndefined notAtom fresh
  refine ⟨selected, renewed, bindings, environment, ?_⟩
  rw [payload]
  apply substitute_pending
  · simp only [Entry.Value.resolve, List.lookup_cons,
      beq_eq_false_iff_ne.mpr answersDifferent, List.lookup_nil, Option.getD_none]
  · simp only [Entry.Value.resolve, List.lookup_cons,
      beq_eq_false_iff_ne.mpr unpackedDifferent, List.lookup_nil, Option.getD_none]
  · simp only [Entry.Value.resolve, List.lookup_cons,
      beq_eq_false_iff_ne.mpr resultDifferent, List.lookup_nil, Option.getD_none]

namespace Controls

def activeOperand : Entry.Value :=
  .expression .active [.symbol "ExprBox", .expression .active [.symbol "completion-number"]]

def heldOperand : Entry.Value :=
  .expression .held [.symbol "Keep", .expression .held [.symbol "payload"]]

/-- Both formal positions are exposed together at publication, while both
operand trees retain their original (and different) readiness statuses. -/
theorem private_two_argument_packet (policy : Policy) (before : Frame) (name : String)
    (fresh : name ∉ specBindingVars before.bindings) (callback : GroundedValue)
    (answersDifferent : "answers" ≠ name) (unpackedDifferent : "unpacked" ≠ name)
    (resultDifferent : "result" ≠ name) :
    ∃ selected : Frame,
      Frame.TypeRenewRel policy Atom.expressionType (.var name) before selected ∧
      dropAssignment name selected.bindings = before.bindings ∧
      dropEnvironment name selected.environment = before.environment ∧
      exposeName name selected
        (pending callback (.expression .active [.symbol "Coupled", activeOperand, heldOperand])
          [activeOperand, heldOperand] [.var name, .var name, .symbol "Result"]
          (.symbol "%Undefined%") (.symbol "context") (.symbol "Coupled") "answers" "unpacked" "result") =
      pending callback (.expression .active [.symbol "Coupled", activeOperand, heldOperand])
          [activeOperand, heldOperand] [.symbol "Expression", .symbol "Expression", .symbol "Result"]
          (.symbol "%Undefined%") (.symbol "context") (.symbol "Coupled") "answers" "unpacked" "result" := by
  obtain ⟨selected, renewed, bindings, environment, payload⟩ :=
    publish_fresh_pending policy before name Atom.expressionType rfl (by decide) (by decide) fresh callback
      (.expression .active [.symbol "Coupled", activeOperand, heldOperand]) [activeOperand, heldOperand]
      [.var name, .var name, .symbol "Result"] (.symbol "%Undefined%") (.symbol "context") (.symbol "Coupled")
      "answers" "unpacked" "result" answersDifferent unpackedDifferent resultDifferent
  refine ⟨selected, renewed, bindings, environment, ?_⟩
  simpa [activeOperand, heldOperand, Entry.Value.substitute, Entry.Value.rebuildStatus,
    Entry.Value.resolve, Entry.Value.ofAtom, Atom.expressionType] using payload

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEScopedFunctionPublication
