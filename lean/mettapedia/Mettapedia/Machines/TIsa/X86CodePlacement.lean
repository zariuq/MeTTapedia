import Mettapedia.Machines.TIsa.NativeImage
import Mettapedia.Machines.TIsa.X86Execution
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Native code-byte placement in the actual Sail memory map

Placed relates a raw native image view to the bytes stored at its base
address. A successful range read transfers the checked byte sequence to
the existing codeLoaded predicate after signed-address rebasing. It assumes
no instruction execution or compiler correctness. Installing executable
memory and the external ABI remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86CodePlacement
open X86RegisterRefinement NativeImage

theorem mapM_option_nth {α β : Type} (f : α → Option β) (inputs : List α) (outputs : List β)
    (mapped : inputs.mapM f = some outputs) (index : Nat) (value : β)
    (present : outputs[index]? = some value) : (inputs[index]?).bind f = some value := by
  induction inputs generalizing outputs index with
  | nil =>
    have same : [] = outputs := by simpa using mapped
    subst outputs
    simp at present
  | cons head later ih =>
    cases first : f head with
    | none => simp [List.mapM_cons, first] at mapped
    | some current =>
      cases rest : later.mapM f with
      | none => simp [List.mapM_cons, first, rest] at mapped
      | some remaining =>
        have same : current :: remaining = outputs := by
          simpa [List.mapM_cons, first, rest] using mapped
        subst outputs
        cases index with
        | zero => simpa only [List.getElem?_cons_zero, Option.bind_some, first] using present
        | succ index =>
          simpa only [List.getElem?_cons_succ] using ih remaining rest index
            (by simpa only [List.getElem?_cons_succ] using present)

theorem read_range_byte (view : View) (offset count : Nat) (bytes : List Byte)
    (read : readRange? view offset count = some bytes) (index : Nat) (byte : Byte)
    (within : index < count) (present : bytes[index]? = some byte) :
    view.read (offset + index) = some byte := by
  have one := mapM_option_nth (fun index => view.read (offset + index)) (List.range count) bytes read index byte present
  simpa only [List.getElem?_range within, Option.bind_some] using one

def Placed (state : State) (base : Int) (view : View) : Prop :=
  ∀ index byte, view.read index = some byte →
    state.mem.get? ((X86Execution.address base index).signExtend 52).toNat = some byte

theorem Placed.preserved {before after : State} {registers : Finset _root_.X86Registers.Register}
    {written : Finset Nat} (base : Int) (view : View)
    (placed : Placed before base view) (frame : X86StateFrame.Frame registers written before after)
    (outside : ∀ index byte, view.read index = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉ written) :
    Placed after base view := by
  intro index byte present
  rw [frame.memory _ (outside index byte present)]
  exact placed index byte present

theorem range_code (state : State) (base : Int) (view : View) (offset : Nat) (bytes : List Nat)
    (placed : Placed state base view)
    (read : readRange? view offset bytes.length = some (bytes.map (BitVec.ofNat 8))) :
    X86Execution.codeLoaded state (base + offset) bytes := by
  intro index byte present
  have within : index < bytes.length := (List.getElem?_eq_some_iff.mp present).choose
  have readByte := read_range_byte view offset bytes.length (bytes.map (BitVec.ofNat 8)) read
    index (BitVec.ofNat 8 byte) within (by simp only [List.getElem?_map, present, Option.map_some])
  have memory := placed (offset + index) _ readByte
  have address : X86Execution.address base (offset + index) = X86Execution.address (base + offset) index := by
    simp only [X86Execution.address, Int.natCast_add, Int.add_assoc]
  simpa only [address] using memory

theorem code_of_read_range (state : State) (base : Int) (view : View) (offset : Nat)
    (start : BitVec 48) (bytes : List Nat)
    (location : start.toInt = base + offset) (placed : Placed state base view)
    (read : readRange? view offset bytes.length = some (bytes.map (BitVec.ofNat 8))) :
    X86Execution.codeLoaded state start.toInt bytes := by
  rw [location]
  exact range_code state base view offset bytes placed read

namespace Controls

private def state : State :=
  ⟨∅, (), ((∅ : Std.ExtHashMap Nat Byte).insert 4096 (0x4c#8)).insert 4097 (0x8b#8), (), 0, #[]⟩

private def view : View :=
  ⟨2, fun index => match index with | 0 => some (0x4c#8) | 1 => some (0x8b#8) | _ => none⟩

theorem correct_base : Placed state 4096 view := by
  intro index byte present
  cases index with
  | zero =>
    have same : (0x4c#8) = byte := Option.some.inj present
    subst byte
    simp [state, X86Execution.address, Std.ExtHashMap.getElem_insert]
  | succ index =>
    cases index with
    | zero =>
      have same : (0x8b#8) = byte := Option.some.inj present
      subst byte
      simp [state, X86Execution.address]
    | succ index => cases present

theorem shifted_base_refused : ¬Placed state 4097 view := by
  intro placed
  have wrong := placed 0 (0x4c#8) rfl
  simp [state, X86Execution.address] at wrong

private def changed : View :=
  ⟨2, fun index => match index with | 0 => some (0x4c#8) | 1 => some (0x8a#8) | _ => none⟩

theorem changed_byte_refused : ¬Placed state 4096 changed := by
  intro placed
  have wrong := placed 1 (0x8a#8) rfl
  simp [state, X86Execution.address] at wrong

private def afterData : State := { state with mem := state.mem.insert 8192 (42#8) }

private theorem data_frame : X86StateFrame.Frame ∅ {8192} state afterData where
  registers _ _ := rfl
  memory index outside := by
    have different : 8192 ≠ index := by
      intro same
      exact outside (Finset.mem_singleton.mpr same.symm)
    change (state.mem.insert 8192 (42#8))[index]? = state.mem[index]?
    simp only [Std.ExtHashMap.getElem?_insert, beq_eq_false_iff_ne.mpr different,
      Bool.false_eq_true, ite_false]
  choices := rfl
  tags := rfl
  cycles := rfl
  output := rfl

theorem disjoint_data_write_preserves_image : Placed afterData 4096 view := by
  apply correct_base.preserved 4096 view data_frame
  intro index byte present
  cases index with
  | zero => change (4096 : Nat) ∉ ({8192} : Finset Nat); decide
  | succ index =>
    cases index with
    | zero => change (4097 : Nat) ∉ ({8192} : Finset Nat); decide
    | succ index => cases present

private def afterTail : State := { state with mem := state.mem.insert 4097 (0x8a#8) }

theorem leaf_byte_preserved : afterTail.mem.get? 4096 = some (0x4c#8) := by
  simp [afterTail, state, Std.ExtHashMap.getElem_insert]

theorem whole_image_exclusion_required : ¬Placed afterTail 4096 view := by
  intro placed
  have wrong := placed 1 (0x8b#8) rfl
  simp [afterTail, state, X86Execution.address] at wrong

end Controls
end Mettapedia.Machines.TIsa.X86CodePlacement

#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.read_range_byte
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.code_of_read_range
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Placed.preserved
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.shifted_base_refused
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.changed_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.disjoint_data_write_preserves_image
#print axioms Mettapedia.Machines.TIsa.X86CodePlacement.Controls.whole_image_exclusion_required
