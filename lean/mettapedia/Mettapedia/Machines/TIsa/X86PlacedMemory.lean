import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86SibQword

/-! # Placed qword stores and preservation of executable bytes -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 330000

namespace Mettapedia.Machines.TIsa.X86PlacedMemory

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev footprint (atAddress : BitVec 48) : Finset Nat :=
  X86WriteWords.written atAddress (List.range 8)

def Reads (state : State) (atAddress : BitVec 48) (value : Word) : Prop :=
  ∀ index < 8, state.mem.get? (X86WriteWords.physicalAddress atAddress index) =
    some (value.extractLsb' (8 * index) 8)

theorem footprint_byte (atAddress : BitVec 48) (index : Nat) (inside : index < 8) :
    X86WriteWords.physicalAddress atAddress index ∈ footprint atAddress := by
  simp only [footprint, X86WriteWords.written, List.mem_toFinset, List.mem_map]
  exact ⟨index, List.mem_range.mpr inside, rfl⟩

theorem Reads.preserved {before after : State} {atAddress : BitVec 48} {value : Word}
    {registers : Finset Register} {bytes : Finset Nat}
    (read : Reads before atAddress value) (frame : X86StateFrame.Frame registers bytes before after)
    (apart : Disjoint (footprint atAddress) bytes) : Reads after atAddress value := by
  intro index inside
  rw [frame.memory _ (fun member => Finset.disjoint_left.mp apart (footprint_byte _ _ inside) member)]
  exact read index inside

def CodeApart (image : NativeImage.View) (base : BitVec 48) (bytes : Finset Nat) : Prop :=
  ∀ index byte, image.read index = some byte → ((address base.toInt index).signExtend 52).toNat ∉ bytes

theorem CodeApart.mono {image : NativeImage.View} {base : BitVec 48} {small large : Finset Nat}
    (apart : CodeApart image base large) (subset : small ⊆ large) : CodeApart image base small :=
  fun index byte found member => apart index byte found (subset member)

def advance {image : NativeImage.View} {base : BitVec 48} {start offset : Nat} {before after : State}
    {registers : Finset Register} {bytes : Finset Nat}
    (point : At image before base start) (frame : X86StateFrame.Frame registers bytes before after)
    (dataOnly : registers ⊆ dataRegisters) (apart : CodeApart image base bytes)
    (rip : after.regs.get? .rip = some ((address base.toInt offset).signExtend 64))
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags) : At image after base offset :=
  let kept (register : Register) (outside : register ∉ dataRegisters) :=
    frame.registers register (fun member => outside (dataOnly member))
  { mode := { point.mode with
      status := (kept .ms_reg (by decide)).trans point.mode.status
      fault := (kept .fault_reg (by decide)).trans point.mode.fault
      msrs := (kept .msrs (by decide)).trans point.mode.msrs
      segments := (kept .seg_hidden_attrs (by decide)).trans point.mode.segments
      application := (kept .app_view (by decide)).trans point.mode.application }
    placed := X86CodePlacement.Placed.preserved _ _ point.placed frame apart
    upper := point.upper
    rip := rip
    flags := flags
    knownFlags := flagsKnown
    quiet := (kept .log_register_writes (by decide)).trans point.quiet }

structure Cell (base : Word) (displacement : BitVec 32) where
  address : BitVec 48
  effective : base + displacement.signExtend 64 = address.signExtend 64
  upper : address.toInt + 8 ≤ (2^47 : Int)
  aligned : address &&& (7#48) = (0#48)

structure Controls (state : State) where
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  visibleKnown : state.regs.get? .seg_visibles = some visible
  controlsKnown : state.regs.get? .ctrs = some controls

def Controls.transport {before after : State} {registers : Finset Register} {bytes : Finset Nat}
    (known : Controls before) (frame : X86StateFrame.Frame registers bytes before after)
    (dataOnly : registers ⊆ dataRegisters) : Controls after :=
  { known with
    visibleKnown := (frame.registers .seg_visibles (fun member =>
      (by decide : Register.seg_visibles ∉ dataRegisters) (dataOnly member))).trans known.visibleKnown
    controlsKnown := (frame.registers .ctrs (fun member =>
      (by decide : Register.ctrs ∉ dataRegisters) (dataOnly member))).trans known.controlsKnown }

inductive Encoding where
  | direct (base : Fin 16) (noSib : base.val % 8 ≠ 4) (noStack : base.val % 8 ≠ 5)
  | r12

def Encoding.base : Encoding → Fin 16
  | .direct base _ _ => base
  | .r12 => 12

def Encoding.length : Encoding → Nat
  | .direct .. => 7
  | .r12 => 8

def Encoding.bytes (encoding : Encoding) (source : Fin 16) (displacement : BitVec 32) : List Nat :=
  match encoding with
  | .direct base _ _ => X86DataStore.code true source base displacement
  | .r12 => X86SibQword.code .store source displacement

theorem stores (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (controls : Controls state)
    (encoding : Encoding) (source : Fin 16) (displacement : BitVec 32)
    (baseValue value : Word) (cell : Cell baseValue displacement)
    (baseKnown : lookup state encoding.base = some baseValue) (sourceKnown : lookup state source = some value)
    (extent : offset + encoding.length ≤ image.size)
    (code : Code image offset (encoding.bytes source displacement))
    (apart : CodeApart image base (footprint cell.address)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      X86StateFrame.Frame {.rip} (footprint cell.address) state after ∧ Reads after cell.address value ∧
      Nonempty (At image after base (offset + encoding.length)) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  have enough : 3 ≤ encoding.length := by cases encoding <;> simp [Encoding.length]
  let origin := point.basis (by omega)
  have upper : origin.address.toInt + encoding.length < (2^47 : Int) := by
    change (address base.toInt offset).toInt + encoding.length < (2^47 : Int)
    rw [point.location offset (by omega)]
    have := point.upper
    omega
  have loaded := point.bytes _ (by omega) _ code
  let finish := address base.toInt (offset + encoding.length)
  let after := X86Move.putPointer (X86WriteWords.storeBytes 8 state cell.address value) finish
  have ran : (X86FuelPrefix.fetches 1).run state = .ok () after := by
    cases encoding with
    | direct baseRegister noSib noStack =>
      let input : X86DataStore.Inputs state true source baseRegister displacement :=
        { toBasis := origin
          noSib := noSib
          noStack := noStack
          visible := controls.visible
          controls := controls.controls
          baseValue := baseValue
          value := value
          flags := point.flags
          dataAddress := cell.address
          baseKnown := baseKnown
          sourceKnown := sourceKnown
          controlKnown := controls.controlsKnown
          flagsKnown := point.knownFlags
          visibleKnown := controls.visibleKnown
          quiet := point.quiet
          upper := upper
          dataUpper := cell.upper
          effective := cell.effective
          aligned := cell.aligned
          loaded := loaded }
      have one := (X86DataStore.executes other vector state true source baseRegister displacement input).1
      change (X86FuelPrefix.fetches 1).run state =
        .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 state cell.address value)
          (address (address base.toInt offset).toInt 7)) at one
      rw [point.relative_address offset 7 (by omega)] at one
      exact one
    | r12 =>
      let input : X86SibQword.Inputs state displacement :=
        { toBasis := origin
          controls := controls.controls
          visible := controls.visible
          flags := point.flags
          baseValue := baseValue
          target := cell.address
          controlsRead := controls.controlsKnown
          visibleRead := controls.visibleKnown
          flagsRead := point.knownFlags
          quiet := point.quiet
          baseKnown := baseKnown
          effective := cell.effective
          upper := upper
          dataUpper := cell.upper
          aligned := cell.aligned }
      have one := X86SibQword.fetched_store other vector state source displacement input loaded value sourceKnown
      change (Functions.x86_fetch_decode_execute ()).run state = .ok ()
        (X86Move.putPointer (X86WriteWords.storeBytes 8 state cell.address value)
          (address (address base.toInt offset).toInt 8)) at one
      rw [point.relative_address offset 8 (by omega)] at one
      exact X86FuelPrefix.fetches_one _ _ one
  have frame : X86StateFrame.Frame {.rip} (footprint cell.address) state after := by
    simpa only [after, Finset.empty_union, Finset.union_empty] using
      (X86WriteWords.storeBytes_frame 8 state cell.address value).trans
        (X86StateFrame.registerOnly (pointer_frame _ finish))
  have stored : Reads after cell.address value := by
    intro index inside
    change (X86Move.putPointer _ _).mem.get? _ = _
    rw [(pointer_frame _ _).memory]
    exact X86WriteWords.store_word_byte _ _ _ cell.upper index inside
  exact ⟨after, ran, frame, stored, ⟨advance point frame (by decide) apart
    (X86FuelPrefix.pointer_rip _ _) point.flags ((frame.registers .rflags (by decide)).trans point.knownFlags)⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedMemory
