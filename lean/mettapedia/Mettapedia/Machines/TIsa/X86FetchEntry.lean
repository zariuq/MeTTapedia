import Mettapedia.Machines.TIsa.X86BareFetch
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Instruction-entry facts independent of instruction length

Mode facts and the current RIP can be transported through an actual state
frame. Bare ModRM and REX windows are then built using their own exact lengths.
These structures contain observations and address geometry, not execution laws.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86FetchEntry
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

structure Entry (state : State) extends X86PlainFetch.Facts state where
  address : BitVec 48
  rip : state.regs.get? .rip = some (address.signExtend 64)

def Entry.ofBasis {state : State} (origin : X86LegacyFetch.Basis state) : Entry state :=
  ⟨X86PlainFetch.Facts.ofBasis origin,origin.address,origin.rip⟩

def Entry.transport {registers : Finset Register} {written : Finset Nat} {before after : State}
    (origin : Entry before) (frame : X86StateFrame.Frame registers written before after)
    (dataOnly : registers ⊆ dataRegisters) (target : BitVec 48)
    (rip : after.regs.get? .rip = some (target.signExtend 64)) : Entry after :=
  let unchanged (register : Register) (outside : register ∉ dataRegisters) :
      after.regs.get? register = before.regs.get? register :=
    frame.registers register (fun member => outside (dataOnly member))
  { control := origin.control
    attributes := origin.attributes
    status := (unchanged .ms_reg (by decide)).trans origin.status
    fault := (unchanged .fault_reg (by decide)).trans origin.fault
    msrs := (unchanged .msrs (by decide)).trans origin.msrs
    segments := (unchanged .seg_hidden_attrs (by decide)).trans origin.segments
    longMode := origin.longMode
    codeMode := origin.codeMode
    application := (unchanged .app_view (by decide)).trans origin.application
    address := target
    rip := rip }

theorem address_zero (base : BitVec 48) : address base.toInt 0 = base := by simp [address]

theorem codeLoaded_left (state : State) (base : Int) (left right : List Nat)
    (loaded : codeLoaded state base (left ++ right)) : codeLoaded state base left := by
  intro index byte found
  apply loaded index byte
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem codeLoaded_right (state : State) (base : Int) (left right : List Nat)
    (loaded : codeLoaded state base (left ++ right)) : codeLoaded state (base + left.length) right := by
  intro index byte found
  have present : (left ++ right)[left.length + index]? = some byte := by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact found
  have read := loaded (left.length + index) byte present
  simpa only [address,Int.natCast_add,Int.add_assoc] using read

def Entry.bareWindow {state : State} (origin : Entry state) (opcode modrm : BitVec 8)
    (upper : origin.address.toInt + 2 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt [opcode.toNat,modrm.toNat]) :
    X86BareFetch.Window state opcode modrm :=
  let lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let at1 := address_toInt origin.address.toInt lower upper 1 (by decide : 1 ≤ 2)
  let at2 := address_toInt origin.address.toInt lower upper 2 (by decide : 2 ≤ 2)
  { toFacts := origin.toFacts
    address := origin.address
    modrmAddress := X86Execution.address origin.address.toInt 1
    next := X86Execution.address origin.address.toInt 2
    step1 := at1.symm
    step2 := by rw [at1,at2]; omega
    rip := origin.rip
    opcodeByte := by
      simpa only [address_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using loaded 0 opcode.toNat (by rfl)
    modrmByte := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using loaded 1 modrm.toNat (by rfl) }

def Entry.rexBasis {state : State} (origin : Entry state)
    (upper : origin.address.toInt + 3 < (2 ^ 47 : Int)) : X86LegacyFetch.Basis state :=
  let lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let at1 := address_toInt origin.address.toInt lower upper 1 (by decide : 1 ≤ 3)
  let at2 := address_toInt origin.address.toInt lower upper 2 (by decide : 2 ≤ 3)
  let at3 := address_toInt origin.address.toInt lower upper 3 (by decide : 3 ≤ 3)
  { address := origin.address
    opcodeAddress := X86Execution.address origin.address.toInt 1
    modrmAddress := X86Execution.address origin.address.toInt 2
    next := X86Execution.address origin.address.toInt 3
    step1 := at1.symm
    step2 := at2.symm
    step3 := by rw [at2,at3]; omega
    control := origin.control
    attributes := origin.attributes
    status := origin.status
    fault := origin.fault
    msrs := origin.msrs
    segments := origin.segments
    longMode := origin.longMode
    codeMode := origin.codeMode
    application := origin.application
    rip := origin.rip }

def Entry.rexWindow {state : State} (origin : Entry state) (opcode : BitVec 8)
    (wide : Bool) (source destination : Fin 16)
    (upper : origin.address.toInt + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt
      [(X86RegisterEncoding.rex wide source destination).toNat,opcode.toNat,
        (X86RegisterEncoding.modRM source destination).toNat]) :
    X86LegacyFetch.Window state opcode wide source destination :=
  { toBasis := origin.rexBasis upper
    prefixByte := by
      simpa only [Entry.rexBasis,address_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        loaded 0 (X86RegisterEncoding.rex wide source destination).toNat (by rfl)
    opcodeByte := by
      simpa only [Entry.rexBasis,BitVec.ofNat_toNat,BitVec.setWidth_eq] using loaded 1 opcode.toNat (by rfl)
    modrmByte := by
      simpa only [Entry.rexBasis,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
        loaded 2 (X86RegisterEncoding.modRM source destination).toNat (by rfl) }

#print axioms Entry.transport
#print axioms codeLoaded_left
#print axioms codeLoaded_right
#print axioms Entry.bareWindow
#print axioms Entry.rexWindow
end Mettapedia.Machines.TIsa.X86FetchEntry
