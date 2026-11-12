import Mettapedia.Machines.TIsa.X86Execution

/-!
# Register and byte footprints on the actual Sail state

This frame relation allows explicit register and memory writes while
preserving every other location and the model's remaining state fields.
It extends the existing register-only frame, and composes footprints by
union. Code-byte preservation follows from disjointness with the writes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86StateFrame

open _root_.X86Registers X86RegisterRefinement

structure Frame (registerWrites : Finset Register) (byteWrites : Finset Nat)
    (before after : State) : Prop where
  registers : ∀ register, register ∉ registerWrites → after.regs.get? register = before.regs.get? register
  memory : ∀ address, address ∉ byteWrites → after.mem.get? address = before.mem.get? address
  choices : after.choiceState = before.choiceState
  tags : after.tags = before.tags
  cycles : after.cycleCount = before.cycleCount
  output : after.sailOutput = before.sailOutput

theorem Frame.refl (registerWrites : Finset Register) (byteWrites : Finset Nat) (state : State) :
    Frame registerWrites byteWrites state state := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.mono {smallRegisters largeRegisters : Finset Register} {smallBytes largeBytes : Finset Nat}
    {before after : State} (frame : Frame smallRegisters smallBytes before after)
    (registers : smallRegisters ⊆ largeRegisters) (bytes : smallBytes ⊆ largeBytes) :
    Frame largeRegisters largeBytes before after :=
  { frame with
    registers := fun register outside => frame.registers register (fun member => outside (registers member))
    memory := fun address outside => frame.memory address (fun member => outside (bytes member)) }

theorem Frame.trans {leftRegisters rightRegisters : Finset Register} {leftBytes rightBytes : Finset Nat}
    {before middle after : State} (first : Frame leftRegisters leftBytes before middle)
    (second : Frame rightRegisters rightBytes middle after) :
    Frame (leftRegisters ∪ rightRegisters) (leftBytes ∪ rightBytes) before after where
  registers register outside :=
    (second.registers register (fun member => outside (Finset.mem_union_right _ member))).trans
      (first.registers register (fun member => outside (Finset.mem_union_left _ member)))
  memory address outside :=
    (second.memory address (fun member => outside (Finset.mem_union_right _ member))).trans
      (first.memory address (fun member => outside (Finset.mem_union_left _ member)))
  choices := second.choices.trans first.choices
  tags := second.tags.trans first.tags
  cycles := second.cycles.trans first.cycles
  output := second.output.trans first.output

theorem registerOnly {registers : Finset Register} {before after : State}
    (frame : X86Execution.RegisterFrame registers before after) : Frame registers ∅ before after where
  registers := frame.registers
  memory address _ := by rw [frame.memory]
  choices := frame.choices
  tags := frame.tags
  cycles := frame.cycles
  output := frame.output

theorem Frame.registers_equal {bytes : Finset Nat} {before after : State}
    (frame : Frame ∅ bytes before after) : after.regs = before.regs := by
  apply Std.ExtDHashMap.ext_get?
  intro register
  exact frame.registers register (by simp)

theorem Frame.lookup {registers : Finset Register} {bytes : Finset Nat} {before after : State}
    (frame : Frame registers bytes before after) (index : Fin 16) (outside : key index ∉ registers) :
    lookup after index = lookup before index := by
  unfold X86RegisterRefinement.lookup
  rw [frame.registers (key index) outside]

def rebase {registers : Finset Register} {bytes : Finset Nat}
    (before after : State) (origin : X86LegacyFetch.Basis before)
    (frame : Frame registers bytes before after) (dataOnly : registers ⊆ X86Execution.dataRegisters)
    {extent : Nat} (upper : origin.address.toInt + extent < (2 ^ 47 : Int))
    (offset : Nat) (within : offset + 3 ≤ extent)
    (rip : after.regs.get? .rip = some ((X86Execution.address origin.address.toInt offset).signExtend 64)) :
    X86LegacyFetch.Basis after :=
  let lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let at0 := X86Execution.address_toInt origin.address.toInt lower upper offset (by omega)
  let at1 := X86Execution.address_toInt origin.address.toInt lower upper (offset + 1) (by omega)
  let at2 := X86Execution.address_toInt origin.address.toInt lower upper (offset + 2) (by omega)
  let at3 := X86Execution.address_toInt origin.address.toInt lower upper (offset + 3) (by omega)
  let unchanged (register : Register) (outside : register ∉ X86Execution.dataRegisters) :
      after.regs.get? register = before.regs.get? register :=
    frame.registers register (fun member => outside (dataOnly member))
  { address := X86Execution.address origin.address.toInt offset
    opcodeAddress := X86Execution.address origin.address.toInt (offset + 1)
    modrmAddress := X86Execution.address origin.address.toInt (offset + 2)
    next := X86Execution.address origin.address.toInt (offset + 3)
    control := origin.control
    attributes := origin.attributes
    step1 := by rw [at0, at1]; omega
    step2 := by rw [at0, at2]; omega
    step3 := by rw [at2, at3]; omega
    status := (unchanged .ms_reg (by decide)).trans origin.status
    fault := (unchanged .fault_reg (by decide)).trans origin.fault
    msrs := (unchanged .msrs (by decide)).trans origin.msrs
    segments := (unchanged .seg_hidden_attrs (by decide)).trans origin.segments
    longMode := origin.longMode
    codeMode := origin.codeMode
    application := (unchanged .app_view (by decide)).trans origin.application
    rip := rip }

theorem Frame.codeLoaded {registers : Finset Register} {written : Finset Nat} {before after : State}
    (frame : Frame registers written before after) (base : Int) (bytes : List Nat)
    (loaded : X86Execution.codeLoaded before base bytes)
    (outside : ∀ index byte, bytes[index]? = some byte →
      ((X86Execution.address base index).signExtend 52).toNat ∉ written) :
    X86Execution.codeLoaded after base bytes := by
  intro index byte present
  rw [frame.memory _ (outside index byte present)]
  exact loaded index byte present

/-- Carry architectural fetch facts to a canonical target reached by a framed block. -/
def basisAt {registers : Finset Register} {bytes : Finset Nat}
    (before after : State) (origin : X86LegacyFetch.Basis before)
    (frame : Frame registers bytes before after) (dataOnly : registers ⊆ X86Execution.dataRegisters)
    (entry : BitVec 48) (upper : entry.toInt + 3 < (2 ^ 47 : Int))
    (rip : after.regs.get? .rip = some (entry.signExtend 64)) : X86LegacyFetch.Basis after :=
  let lower : -(2 ^ 47 : Int) ≤ entry.toInt := by simpa using BitVec.le_toInt entry
  let at1 := X86Execution.address_toInt entry.toInt lower upper 1 (by decide : 1 ≤ 3)
  let at2 := X86Execution.address_toInt entry.toInt lower upper 2 (by decide : 2 ≤ 3)
  let at3 := X86Execution.address_toInt entry.toInt lower upper 3 (by decide : 3 ≤ 3)
  let unchanged (register : Register) (outside : register ∉ X86Execution.dataRegisters) :
      after.regs.get? register = before.regs.get? register :=
    frame.registers register (fun member => outside (dataOnly member))
  { address := entry
    opcodeAddress := X86Execution.address entry.toInt 1
    modrmAddress := X86Execution.address entry.toInt 2
    next := X86Execution.address entry.toInt 3
    control := origin.control
    attributes := origin.attributes
    step1 := by rw [at1]; omega
    step2 := by rw [at2]; omega
    step3 := by rw [at2, at3]; omega
    status := (unchanged .ms_reg (by decide)).trans origin.status
    fault := (unchanged .fault_reg (by decide)).trans origin.fault
    msrs := (unchanged .msrs (by decide)).trans origin.msrs
    segments := (unchanged .seg_hidden_attrs (by decide)).trans origin.segments
    longMode := origin.longMode
    codeMode := origin.codeMode
    application := (unchanged .app_view (by decide)).trans origin.application
    rip := rip }

end Mettapedia.Machines.TIsa.X86StateFrame

#print axioms Mettapedia.Machines.TIsa.X86StateFrame.Frame.trans
#print axioms Mettapedia.Machines.TIsa.X86StateFrame.Frame.codeLoaded
#print axioms Mettapedia.Machines.TIsa.X86StateFrame.basisAt
