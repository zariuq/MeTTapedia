import Mettapedia.Machines.TIsa.X86PlainFetch
import Mettapedia.Machines.TIsa.X86CodePlacement

/-!
# A placed instruction boundary

This view uses an arbitrary checked byte image. Register-only segments
transport the placement and mode facts to their next instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PlacedInstruction

open _root_.X86Registers X86RegisterRefinement X86Execution

structure At (image : NativeImage.View) (state : State) (base : BitVec 48) (offset : Nat) where
  mode : X86PlainFetch.Facts state
  placed : X86CodePlacement.Placed state base.toInt image
  upper : base.toInt + image.size < (2^47 : Int)
  rip : state.regs.get? .rip = some ((address base.toInt offset).signExtend 64)
  flags : BitVec 32
  knownFlags : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

theorem At.location {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (site : Nat) (inside : site ≤ image.size) :
    (address base.toInt site).toInt = base.toInt + site :=
  address_toInt _ (BitVec.le_toInt base) point.upper site inside

theorem At.relative_address {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (start later : Nat) (inside : start ≤ image.size) :
    address (address base.toInt start).toInt later = address base.toInt (start + later) := by
  rw [point.location start inside]
  simp [address, Int.add_assoc]

def At.basis {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (inside : offset + 3 ≤ image.size) : X86LegacyFetch.Basis state where
  address := address base.toInt offset
  opcodeAddress := address base.toInt (offset + 1)
  modrmAddress := address base.toInt (offset + 2)
  next := address base.toInt (offset + 3)
  control := point.mode.control
  attributes := point.mode.attributes
  step1 := by rw [point.location _ (by omega), point.location _ (by omega)]; omega
  step2 := by rw [point.location _ (by omega), point.location _ (by omega)]; omega
  step3 := by rw [point.location _ (by omega), point.location _ inside]; omega
  status := point.mode.status
  fault := point.mode.fault
  msrs := point.mode.msrs
  segments := point.mode.segments
  longMode := point.mode.longMode
  codeMode := point.mode.codeMode
  application := point.mode.application
  rip := point.rip

theorem At.bytes {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (site : Nat) (inside : site ≤ image.size)
    (code : List Nat) (found : NativeImage.readRange? image site code.length = some (code.map (.ofNat 8))) :
    codeLoaded state (address base.toInt site).toInt code :=
  X86CodePlacement.code_of_read_range state base.toInt image site _ code
    (point.location site inside) point.placed found

def At.advance {image : NativeImage.View} {before after : State} {base : BitVec 48} {start offset : Nat}
    {written : Finset Register} (point : At image before base start) (frame : RegisterFrame written before after)
    (data : written ⊆ dataRegisters) (rip : after.regs.get? .rip = some ((address base.toInt offset).signExtend 64))
    (flags : BitVec 32) (known : after.regs.get? .rflags = some flags) : At image after base offset :=
  let unchanged (register : Register) (outside : register ∉ dataRegisters) :=
    frame.registers register (fun hit => outside (data hit))
  { mode := { point.mode with
      status := (unchanged .ms_reg (by decide)).trans point.mode.status
      fault := (unchanged .fault_reg (by decide)).trans point.mode.fault
      msrs := (unchanged .msrs (by decide)).trans point.mode.msrs
      segments := (unchanged .seg_hidden_attrs (by decide)).trans point.mode.segments
      application := (unchanged .app_view (by decide)).trans point.mode.application }
    placed := X86CodePlacement.Placed.preserved _ _ point.placed (X86StateFrame.registerOnly frame) (by simp)
    upper := point.upper
    rip := rip
    flags := flags
    knownFlags := known
    quiet := (unchanged .log_register_writes (by decide)).trans point.quiet }

end Mettapedia.Machines.TIsa.X86PlacedInstruction
