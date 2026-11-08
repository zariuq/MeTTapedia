import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedFields

/-!
# Marked-ready provenance joined to actual compiled field recovery

The source field is selected from the caller's real materialized value.
The native-pattern model recovers that same origin from the emitted match
program, including its EXPR/BIND/SAME operations. Its lowered SLOT result
then agrees with the independently constructed source capture and body
return. No successful body execution or nominal field typing is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedSlots

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open Mettapedia.Machines
open HEPatternSlotOrigins HEPatternSlotReadback HECompletionEntry

theorem marked_whole_capture {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (world : World) (policy : Policy) (reuse : policy.reentry = .reuse)
    (live : List Atom) (scope : List String) (before : Frame) (input : Entry.Value)
    (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool) (fields : List Entry.Value)
    (materialized : before.read policy input = .expression .held fields)
    (admitted : readyOperand symbolAllowed normalForm (.expression .held fields) = value)
    (name : String) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars (Entry.Value.expression .held fields).erase) (expected : Atom) :
    finish false (structural (template (readyOperand symbolAllowed normalForm (.expression .held fields)))) = some true ∧
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (.expression .held fields) (.var name) after.environment ∧
      after.read policy (.var name) = .expression .held fields ∧
      Stateful.AtomRel environment label world live scope (.var name) expected after
        [(.expression .held fields, after)] world (policy := policy) := by
  refine ⟨by rw [admitted]; rfl, ?_⟩
  apply HECompletionMarkedFields.held_capture_source environment label world policy reuse live scope before fields
  · have unassigned := FrameUnassignedOn.after_read policy before input
    simpa only [materialized] using unassigned
  · exact fresh
  · exact absent

theorem compiled_field_capture {Context World L O P H : Type}
    (environment : WorldEnvironment Context World) (label : Context) (world : World)
    (policy : Policy) (reuse : policy.reentry = .reuse) (live : List Atom) (scope : List String)
    (before : Frame) (input : Entry.Value) (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool)
    (fields : List Entry.Value) (fieldIndex : Nat) (status : Entry.Status) (head : Entry.Value) (tail : List Entry.Value)
    (materialized : before.read policy input = .expression .held fields)
    (admitted : readyOperand symbolAllowed normalForm (.expression .held fields) = value)
    (selected : fields[fieldIndex]? = some (.expression status (head :: tail)))
    (name : String) (fresh : name ∉ specBindingVars before.bindings)
    (absent : name ∉ TypeSubst.typeVars (Entry.Value.expression status (head :: tail)).erase) (expected : Atom)
    (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (slots : String → Option Nat) (patterns : List Atom) (output : Emitted)
    (emitted : compile slots patterns = some output) (compare : Atom → Atom → Bool)
    (arguments : List Entry.Value) (lengths : arguments.length = patterns.length)
    (source : Nat) (argumentAt : arguments[source]? = some (.expression .held fields))
    (locals finalRegisters finalLocals : RegisterCode.Regs Entry.Value) (slot destination next : Nat)
    (recovered : recoverSlot slot output.code (initialOrigins arguments.length) = some (source, some fieldIndex))
    (matched : run compare output.code (fun index => arguments[index]?) locals = some (finalRegisters, finalLocals)) :
    ∃ after : Frame,
      Entry.Value.UnifyRel policy.rebuilding before.environment (.expression status (head :: tail)) (.var name) after.environment ∧
      after.read policy (.var name) = .expression status (head :: tail) ∧
      Stateful.AtomRel environment label world live scope (.var name) expected after
        [(.expression status (head :: tail), after)] world (policy := policy) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot slot) true destination next).1 finalLocals =
        some (.ret (.expression status (head :: tail))) := by
  obtain ⟨after, unified, read, sourceBody⟩ := HECompletionMarkedFields.admitted_marked_field_capture
    environment label world policy reuse live scope before input symbolAllowed normalForm fields fieldIndex
    status head tail materialized admitted selected name fresh absent expected
  refine ⟨after, unified, read, sourceBody, ?_⟩
  apply compiled_slot_returns sem answer fuses slots patterns output emitted compare arguments lengths
    locals finalRegisters finalLocals slot destination next (source, some fieldIndex)
    (.expression status (head :: tail)) recovered matched
  simp only [readOrigin, HEShownSlotReturn.readBinding, argumentAt, Option.bind_some, selected]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionMarkedSlots
