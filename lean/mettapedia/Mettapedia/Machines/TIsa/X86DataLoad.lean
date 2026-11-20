import Mettapedia.Machines.TIsa.X86QwordLoad
import Mettapedia.Machines.TIsa.X86FetchEntry

/-!
# Width-parameterized original-model data loads

The seven-byte REX-prefixed no-SIB/default-data-segment MOV template retains checked
alignment, arbitrary signed displacement and partial register initialization.
Both widths share one interface; the dword result is explicitly zero-extended.
Capability checks are composed separately with this actual fetched execution.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86DataLoad
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

def byteCount (wide : Bool) : Nat := if wide then 8 else 4
def value (wide : Bool) (word : Word) : Word := if wide then word else (word.extractLsb' 0 32).zeroExtend 64
def code (wide : Bool) (destination base : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(loadRex wide destination base).toNat,0x8b,(loadModRM destination base).toNat] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

theorem code_length (wide : Bool) (destination base : Fin 16) (displacement : BitVec 32) :
    (code wide destination base displacement).length = 7 := by simp [code]

structure Inputs (state : State) (wide : Bool) (destination base : Fin 16) (displacement : BitVec 32)
    extends X86LegacyFetch.Basis state where
  noSib : base.val % 8 ≠ 4
  noStack : base.val % 8 ≠ 5
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  baseValue : Word
  word : Word
  flags : BitVec 32
  dataAddress : BitVec 48
  baseKnown : lookup state base = some baseValue
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 7 < (2 ^ 47 : Int)
  dataUpper : dataAddress.toInt + byteCount wide ≤ (2 ^ 47 : Int)
  effective : baseValue + displacement.signExtend 64 = dataAddress.signExtend 64
  safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨
    dataAddress &&& BitVec.ofNat 48 (byteCount wide - 1) = (0#48)
  loaded : codeLoaded state address.toInt (code wide destination base displacement)
  dataPresent : ∀ index < byteCount wide,
    state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat = some (word.extractLsb' (8 * index) 8)

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (wide : Bool) (destination base : Fin 16) (displacement : BitVec 32)
    (input : Inputs state wide destination base displacement) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination,.rip} state after ∧
      lookup after destination = some (value wide input.word) ∧
      after.regs.get? .rip = some ((address input.address.toInt 7).signExtend 64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let site := rebase state state input.toBasis (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) (by simpa [address] using input.rip)
  let finish := address input.address.toInt 7
  have at3 : site.next.toInt = input.address.toInt + 3 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 3 (by decide)
  have at7 : finish.toInt = input.address.toInt + 7 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 7 (by decide)
  have present : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8) := by
    intro index within
    rw [at3]
    have shift : address (input.address.toInt + 3) index = address input.address.toInt (3 + index) := by
      simp [address,Int.add_assoc]
    rw [shift]
    have byte : (code wide destination base displacement)[3 + index]? =
        some (displacement.extractLsb' (8 * index) 8).toNat := by interval_cases index <;> rfl
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using input.loaded _ _ byte
  have prefixByte : state.mem.get? (site.address.signExtend 52).toNat = some (loadRex wide destination base) := by
    simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 0 (loadRex wide destination base).toNat (by simp [code])
  have opcodeByte := input.loaded 1 0x8b (by simp [code])
  have modrmByte : state.mem.get? (site.modrmAddress.signExtend 52).toNat = some (loadModRM destination base) := by
    simpa only [site,rebase,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      input.loaded 2 (loadModRM destination base).toNat (by simp [code])
  have run : (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination (value wide input.word)) finish) := by
    cases wide with
    | true =>
        exact X86QwordLoad.fetched_qword_checked other vector state destination base input.noSib input.noStack
          site finish input.dataAddress input.visible input.controls input.baseValue input.word input.flags displacement
          (by omega) input.dataUpper input.baseKnown input.controlKnown input.flagsKnown input.visibleKnown input.quiet
          input.effective input.safe prefixByte opcodeByte modrmByte present input.dataPresent
    | false =>
        apply X86DwordLoad.fetched_dword_checked other vector state destination base input.noSib input.noStack
          site finish input.dataAddress input.visible input.controls input.baseValue (input.word.extractLsb' 0 32)
          input.flags displacement (by omega) input.dataUpper input.baseKnown input.controlKnown input.flagsKnown
          input.visibleKnown input.quiet input.effective input.safe prefixByte opcodeByte modrmByte present
        intro index within
        rw [BitVec.extractLsb'_extractLsb'_of_le (by omega : 8 * index + 8 ≤ 32)]
        exact input.dataPresent index within
  let after := X86Move.putPointer (put state destination (value wide input.word)) finish
  refine ⟨after,X86FuelPrefix.fetches_one state after run,X86QwordLoad.result_frame _ _ _ _,?_,?_⟩
  · rw [X86Move.lookup_putPointer,lookup_put_same]
  · simp only [after,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    rfl

#print axioms executes
end Mettapedia.Machines.TIsa.X86DataLoad
