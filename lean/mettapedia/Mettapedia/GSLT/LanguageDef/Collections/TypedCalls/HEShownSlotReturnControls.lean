import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownBuildCounterexample
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

/-! # Compact-slot provenance and completed-return controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type
open Mettapedia.Machines

def wholeBind : CodeBind := ⟨3, 0, none⟩
def fieldBind : CodeBind := ⟨1, 1, some 1⟩
def occurrences : List CodeBind := [wholeBind, fieldBind]
def heldField : Entry.Value := .expression .held [.symbol "Stored", .grounded (.int 7)]
def arguments : List Entry.Value :=
  [.symbol "caller-value", .expression .held [.symbol "Box", heldField]]
def emptyRegisters : RegisterCode.Regs Entry.Value := fun _ => none
def enteredRegisters : RegisterCode.Regs Entry.Value :=
  Function.update (Function.update emptyRegisters 1 (some heldField)) 3 (some (.symbol "caller-value"))

theorem fresh_occurrences_are_compact : compact (emitUses [] occurrences) = true := by decide

theorem field_first_is_a_real_reordering : fieldFirst occurrences = [fieldBind, wholeBind] := by decide

theorem exact_compact_entry : install arguments (fieldFirst occurrences) emptyRegisters = some enteredRegisters := by
  rfl

theorem both_values_and_marks_survive :
    enteredRegisters 1 = some heldField ∧ enteredRegisters 3 = some (.symbol "caller-value") := by
  simp [enteredRegisters]

def repeatBind : CodeBind := ⟨1, 0, none⟩

theorem repeated_variable_emits_same_not_write :
    emitUses [] [fieldBind, repeatBind] = [.bind fieldBind, .same repeatBind] ∧
    compact (emitUses [] [fieldBind, repeatBind]) = false ∧
    writes (emitUses [] [fieldBind, repeatBind]) = [fieldBind] := by decide

/-- If SAME were changed to a second BIND, first-record static lookup would
describe the old field but the installed register would contain a new value. -/
theorem duplicate_write_breaks_static_lookup :
    [fieldBind, repeatBind].find? (fun entry => entry.slot == 1) = some fieldBind ∧
    readBinding arguments fieldBind = some heldField ∧
    ((install arguments [fieldBind, repeatBind] emptyRegisters).bind fun registers => registers 1) =
      some (.symbol "caller-value") := ⟨rfl, rfl, rfl⟩

theorem metadata_does_not_make_a_scalar_have_fields :
    readBinding arguments ⟨4, 0, some 1⟩ = none := rfl

theorem field_zero_is_the_constructor_head :
    readBinding arguments ⟨4, 1, some 0⟩ = some (.symbol "Box") := rfl

def range : Atom := .symbol "StoredRange"
def space : Space := Space.ofList
  [HEShownBuildCounterexample.declaration (.symbol "Stored")
    (CompletedDelivery.arrowType [.symbol "Number"] range)]

def source : NativeTypeSourcePorts.Source :=
  ⟨space.atoms, [], fun _ _ => id, 4, "subtype", fun first second => first == second⟩

/-- A concrete completed observation from the existing recursive source
driver. Missing or exhausted work cannot be read as an empty typing list. -/
def reader : TypeLookupRel := fun _ value _ types =>
  NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate HEConstructorDeclarationGuard.Controls.sourceOps source
      (fun tag key => .grounded (.custom tag key)) 6 (.infer true value) ⟨[], 0⟩).1 = some types

theorem actual_return_reader (frame : Frame) :
    reader frame.bindings heldField.erase range [range] := by cbv

/-- The ordinary lowered slot and the actual source completed-value gate
return one identical marked value. The reader evidence is computed from
the stored arrow declaration, not supplied as a typing assertion. -/
theorem lowered_slot_and_actual_gate {L O P H : Type}
    (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) (policy : Policy) (frame : Frame) :
    RegisterCode.exec sem answer
      (RegisterCode.compile fuses (.slot 1) true destination next).1 enteredRegisters = some (.ret heldField) ∧
    NativeCompletedReturnRel space reader policy heldField range frame [(heldField, frame)] := by
  exact compact_slot_completed sem answer fuses [] occurrences fresh_occurrences_are_compact arguments
    emptyRegisters enteredRegisters 1 destination next fieldBind heldField (by decide) exact_compact_entry rfl
    space reader policy frame range [] [] rfl (actual_return_reader frame) (by simp)

theorem replacing_marked_field_with_raw_syntax_changes_it : Entry.Value.ofAtom heldField.erase ≠ heldField := by
  simp [heldField, Entry.Value.ofAtom, Entry.Value.erase]

def pendingCall : Atom := .expression [.symbol "slot-compute"]
def pendingSpace : Space := Space.ofList
  [HEShownBuildCounterexample.declaration (.symbol "slot-compute")
    (CompletedDelivery.arrowType [] (.symbol "Number")),
   HEShownBuildCounterexample.equation pendingCall (.grounded (.int 7))]

/-- A declared range is not proof that pending syntax is producer-completed.
The ordinary source interpreter really runs this call. -/
theorem pending_source_is_not_completed_data :
    evalAtom pendingSpace Mettapedia.Languages.MeTTa.HE.GroundedDispatch.none pendingCall
      Atom.undefinedType Bindings.empty 32 = [(.grounded (.int 7), Bindings.empty)] ∧
    pendingCall ≠ .grounded (.int 7) := by decide +kernel

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn.Controls
