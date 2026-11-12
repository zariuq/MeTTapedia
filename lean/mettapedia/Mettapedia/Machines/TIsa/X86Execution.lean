import Mettapedia.Machines.TIsa.X86Arithmetic
import Mathlib.Logic.Relation

/-!
# Concrete state frames and fetched instruction composition

RegisterFrame describes changes to the actual Sail state, preserving memory
and every register outside a declared clobber set. Address rebasing carries
the protected fetch inputs through such a frame. Loaded code bytes then
construct the next input window without an execution hypothesis.

Step is the original fetch/decode/execute function's successful result;
Steps uses the existing reflexive-transitive closure.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Execution

open _root_.X86Registers X86RegisterRefinement

structure RegisterFrame (clobbers : Finset Register) (before after : State) : Prop where
  registers : ∀ register, register ∉ clobbers → after.regs.get? register = before.regs.get? register
  memory : after.mem = before.mem
  choices : after.choiceState = before.choiceState
  tags : after.tags = before.tags
  cycles : after.cycleCount = before.cycleCount
  output : after.sailOutput = before.sailOutput

theorem RegisterFrame.refl (clobbers : Finset Register) (state : State) :
    RegisterFrame clobbers state state := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RegisterFrame.mono {small large : Finset Register} {before after : State}
    (frame : RegisterFrame small before after) (included : small ⊆ large) :
    RegisterFrame large before after :=
  { frame with registers := fun register apart => frame.registers register (fun member => apart (included member)) }

theorem RegisterFrame.trans {left right : Finset Register} {before middle after : State}
    (first : RegisterFrame left before middle) (second : RegisterFrame right middle after) :
    RegisterFrame (left ∪ right) before after where
  registers register apart := (second.registers register (fun member => apart (Finset.mem_union_right _ member))).trans
    (first.registers register (fun member => apart (Finset.mem_union_left _ member)))
  memory := second.memory.trans first.memory
  choices := second.choices.trans first.choices
  tags := second.tags.trans first.tags
  cycles := second.cycles.trans first.cycles
  output := second.output.trans first.output

theorem RegisterFrame.lookup {clobbers : Finset Register} {before after : State}
    (frame : RegisterFrame clobbers before after) (index : Fin 16)
    (apart : key index ∉ clobbers) : lookup after index = lookup before index := by
  unfold X86RegisterRefinement.lookup
  rw [frame.registers (key index) apart]

theorem put_frame (state : State) (index : Fin 16) (value : Word) :
    RegisterFrame {key index} state (put state index value) where
  registers register apart := by
    apply put_other_register
    intro same
    exact apart (Finset.mem_singleton.mpr same.symm)
  memory := rfl
  choices := rfl
  tags := rfl
  cycles := rfl
  output := rfl

theorem flags_frame (state : State) (flags : BitVec 32) :
    RegisterFrame {.rflags} state (X86Flags.putFlags state flags) where
  registers register apart := by
    apply X86Flags.putFlags_other
    intro same
    exact apart (Finset.mem_singleton.mpr same.symm)
  memory := rfl
  choices := rfl
  tags := rfl
  cycles := rfl
  output := rfl

theorem pointer_frame (state : State) (pointer : BitVec 48) :
    RegisterFrame {.rip} state (X86Move.putPointer state pointer) where
  registers register apart := by
    have different : Register.rip ≠ register := by
      intro same
      exact apart (Finset.mem_singleton.mpr same.symm)
    simp [X86Move.putPointer, Std.ExtDHashMap.get?_insert, different]
  memory := rfl
  choices := rfl
  tags := rfl
  cycles := rfl
  output := rfl

def dataRegisters : Finset Register := (Finset.univ.image key) ∪ {.rflags, .rip}

abbrev DataFrame (before after : State) := RegisterFrame dataRegisters before after

theorem data_key (index : Fin 16) : key index ∈ dataRegisters := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)

theorem data_put (state : State) (index : Fin 16) (value : Word) :
    DataFrame state (put state index value) :=
  (put_frame state index value).mono (Finset.singleton_subset_iff.mpr (data_key index))

theorem data_flags (state : State) (flags : BitVec 32) :
    DataFrame state (X86Flags.putFlags state flags) :=
  (flags_frame state flags).mono (by simp [dataRegisters])

theorem data_pointer (state : State) (pointer : BitVec 48) :
    DataFrame state (X86Move.putPointer state pointer) :=
  (pointer_frame state pointer).mono (by simp [dataRegisters])

theorem data_trans {before middle after : State}
    (first : DataFrame before middle) (second : DataFrame middle after) : DataFrame before after := by
  simpa only [Finset.union_self] using first.trans second

def address (base : Int) (offset : Nat) : BitVec 48 := BitVec.ofInt 48 (base + offset)

theorem address_toInt (base : Int) {extent : Nat} (lower : -(2 ^ 47 : Int) ≤ base)
    (upper : base + extent < (2 ^ 47 : Int)) (offset : Nat) (within : offset ≤ extent) :
    (address base offset).toInt = base + offset := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · omega
  · omega

def rebase (before after : State) (origin : X86LegacyFetch.Basis before)
    (frame : DataFrame before after) {extent : Nat}
    (upper : origin.address.toInt + extent < (2 ^ 47 : Int))
    (offset : Nat) (within : offset + 3 ≤ extent)
    (rip : after.regs.get? .rip = some ((address origin.address.toInt offset).signExtend 64)) :
    X86LegacyFetch.Basis after :=
  let lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let at0 := address_toInt origin.address.toInt lower upper offset (by omega)
  let at1 := address_toInt origin.address.toInt lower upper (offset + 1) (by omega)
  let at2 := address_toInt origin.address.toInt lower upper (offset + 2) (by omega)
  let at3 := address_toInt origin.address.toInt lower upper (offset + 3) (by omega)
  { address := address origin.address.toInt offset
    opcodeAddress := address origin.address.toInt (offset + 1)
    modrmAddress := address origin.address.toInt (offset + 2)
    next := address origin.address.toInt (offset + 3)
    control := origin.control
    attributes := origin.attributes
    step1 := by rw [at0, at1]; omega
    step2 := by rw [at0, at2]; omega
    step3 := by rw [at2, at3]; omega
    status := (frame.registers .ms_reg (by decide)).trans origin.status
    fault := (frame.registers .fault_reg (by decide)).trans origin.fault
    msrs := (frame.registers .msrs (by decide)).trans origin.msrs
    segments := (frame.registers .seg_hidden_attrs (by decide)).trans origin.segments
    longMode := origin.longMode
    codeMode := origin.codeMode
    application := (frame.registers .app_view (by decide)).trans origin.application
    rip := rip }

def codeLoaded (state : State) (base : Int) (bytes : List Nat) : Prop :=
  ∀ index byte, bytes[index]? = some byte →
    state.mem.get? ((address base index).signExtend 52).toNat = some (BitVec.ofNat 8 byte)

theorem RegisterFrame.code_preserved {clobbers : Finset Register} {before after : State}
    (frame : RegisterFrame clobbers before after) (base : Int) (bytes : List Nat)
    (loaded : codeLoaded before base bytes) : codeLoaded after base bytes := by
  intro index byte present
  rw [frame.memory]
  exact loaded index byte present

def windowAt (before after : State) (origin : X86LegacyFetch.Basis before)
    (frame : DataFrame before after) {extent : Nat}
    (upper : origin.address.toInt + extent < (2 ^ 47 : Int))
    (offset : Nat) (within : offset + 3 ≤ extent)
    (rip : after.regs.get? .rip = some ((address origin.address.toInt offset).signExtend 64))
    (bytes : List Nat) (loaded : codeLoaded after origin.address.toInt bytes)
    (source destination : Fin 16) (opcode : BitVec 8)
    (prefixByte : bytes[offset]? = some (X86RegisterEncoding.rex true source destination).toNat)
    (opcodeByte : bytes[offset + 1]? = some opcode.toNat)
    (modrmByte : bytes[offset + 2]? = some (X86RegisterEncoding.modRM source destination).toNat) :
    X86LegacyFetch.Window after opcode true source destination :=
  { toBasis := rebase before after origin frame upper offset within rip
    prefixByte := by simpa only [rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ prefixByte
    opcodeByte := by simpa only [rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ opcodeByte
    modrmByte := by simpa only [rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ modrmByte }

def Step [MemoryPrimitives] [OtherOpcodeHandlers] [VectorOpcodeHandlers] (before after : State) : Prop :=
  (Functions.x86_fetch_decode_execute ()).run before = .ok () after

theorem Step.deterministic [MemoryPrimitives] [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {before left right : State} (first : Step before left) (second : Step before right) : left = right :=
  (EStateM.Result.ok.inj (first.symm.trans second)).2

abbrev Steps [MemoryPrimitives] [OtherOpcodeHandlers] [VectorOpcodeHandlers] := Relation.ReflTransGen Step

theorem three_steps [MemoryPrimitives] [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {start first second finish : State}
    (one : Step start first) (two : Step first second) (three : Step second finish) : Steps start finish :=
  (Relation.ReflTransGen.single one).tail two |>.tail three

theorem three_steps_deterministic [MemoryPrimitives] [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {start left right : State}
    (first : ∃ a b, Step start a ∧ Step a b ∧ Step b left)
    (second : ∃ a b, Step start a ∧ Step a b ∧ Step b right) : left = right := by
  obtain ⟨a, b, one, two, three⟩ := first
  obtain ⟨c, d, otherOne, otherTwo, otherThree⟩ := second
  have sameFirst := one.deterministic otherOne
  subst c
  have sameSecond := two.deterministic otherTwo
  subst d
  exact three.deterministic otherThree

namespace Controls

private def before : State :=
  ⟨((∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false).insert .rax (0#64),
    (), ∅, (), 0, #[]⟩

theorem declared_write_frames : RegisterFrame {key 0} before (put before 0 (1#64)) :=
  put_frame before 0 (1#64)

theorem omitted_write_refused : ¬RegisterFrame ∅ before (put before 0 (1#64)) := by
  intro frame
  have same := frame.lookup 0 (by simp)
  rw [lookup_put_same] at same
  have original : lookup before 0 = some (0#64) := by
    change (before.regs.get? .rax).map (fun value : Word => value) = _
    simp [before]
  rw [original] at same
  exact (by decide : (1#64) ≠ (0#64)) (Option.some.inj same)

private def corrupted : State := { before with regs := before.regs.insert .ms_reg true }

theorem changed_control_refused : ¬DataFrame before corrupted := by
  intro frame
  have same := frame.registers .ms_reg (by decide)
  simp [before, corrupted, Std.ExtDHashMap.get?_insert] at same

end Controls
end Mettapedia.Machines.TIsa.X86Execution

#print axioms Mettapedia.Machines.TIsa.X86Execution.rebase
#print axioms Mettapedia.Machines.TIsa.X86Execution.three_steps
