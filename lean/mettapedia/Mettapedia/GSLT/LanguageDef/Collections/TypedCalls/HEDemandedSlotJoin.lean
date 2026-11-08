import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedWholeProgram

/-!
# The checked consumer's whole-parameter SLOT return

The consumer's one formal is exactly its return type. Its authored variable
pattern earns the slot binding, and the already proved producer supplies the
completed annotated value. Both compact entry and the ordinary emitted BIND
read that same value. The existing register lowering returns it without a new
type query. Native pointer/mark encoding and whole-program C correspondence
are not inferred from this value-level join.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedSlotJoin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed
open Mettapedia.Machines
open HEPatternSlotOrigins HEPatternSlotReadback
open HEDemandedConstructorEdge (space heldResult consumerSignature)
open HEDemandedConstructorInferred (environment rangeDemand)

def slots (name : String) : Option Nat := if name == "value" then some 0 else none
def generated : Emitted := ⟨[.bind 0 0], 1, [0]⟩
def arguments : List Entry.Value := [heldResult]
def inputRegisters : RegisterCode.Regs Entry.Value := fun index => arguments[index]?
def emptyRegisters : RegisterCode.Regs Entry.Value := fun _ => none
def localRegisters : RegisterCode.Regs Entry.Value := Function.update emptyRegisters 0 (some heldResult)

theorem formal_is_the_shown_range : consumerSignature.argumentTypes[0]? = some consumerSignature.returnType := rfl

theorem source_pattern_emits_slot : compile slots [.var "value"] = some generated := by cbv

theorem ordinary_entry_keeps_ready_value :
    run (fun left right => left == right) generated.code inputRegisters emptyRegisters =
      some (inputRegisters, localRegisters) := rfl

theorem compact_entry_is_the_same :
    HEShownSlotReturn.install arguments [⟨0, 0, none⟩] emptyRegisters = some localRegisters := rfl

/-- This is the nontrivial successful source producer paired with the
consumer's actual emitted pattern and lowered SLOT body, not an assumed
value in an arbitrary register. -/
theorem source_and_slot_agree_of_reads {L O P H : Type}
    (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving) (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () [] [] HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot 0) true destination next).1 localRegisters =
        some (.ret heldResult) := by
  obtain ⟨after, source⟩ := HEDemandedWholeProgram.source_call_with_marking_of_reads reads minimal marking supported [] []
  refine ⟨after, source, ?_⟩
  exact compiled_slot_returns sem answer fuses slots [.var "value"] generated source_pattern_emits_slot
    (fun left right => left == right) arguments rfl emptyRegisters inputRegisters localRegisters
    0 destination next (0, none) heldResult rfl ordinary_entry_keeps_ready_value rfl

theorem source_and_slot_agree_with_marking {L O P H : Type}
    (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving) (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () [] [] HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot 0) true destination next).1 localRegisters =
        some (.ret heldResult) :=
  source_and_slot_agree_of_reads HEDemandedConstructorInferred.historicalReads minimal marking supported sem answer fuses destination next

theorem source_and_slot_agree {L O P H : Type}
    (minimal : Minimal.Services) (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () [] [] HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot 0) true destination next).1 localRegisters =
        some (.ret heldResult) :=
  source_and_slot_agree_with_marking minimal .successes (Or.inl rfl) sem answer fuses destination next

theorem source_and_slot_agree_preserving {L O P H : Type}
    (minimal : Minimal.Services) (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () [] [] HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot 0) true destination next).1 localRegisters =
        some (.ret heldResult) :=
  source_and_slot_agree_with_marking minimal .unchangedPreserving (Or.inr rfl) sem answer fuses destination next

/-- An absent compiled input cannot be promoted to a completed result. -/
theorem absent_input_does_not_bind :
    run (fun left right => left == right) generated.code emptyRegisters emptyRegisters = none := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedSlotJoin
