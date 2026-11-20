import Mettapedia.Machines.TIsa.X86Bounds
import Mettapedia.Machines.TIsa.X86P1QwordLoadCapture

/-!
# The premise field used by output construction

The actual LOAD at 260..316 composes the parameterized bounds constructor
with the original full-word MOV contract. The complete image supplies all
56 bytes. A successful ten-instruction run preserves memory and the image
and returns the full 64-bit premise field in R10. The finer contract retains
the protected flag mask from bounds through the final load. Source admission and the
surrounding output sequence remain separate composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1FieldLoadCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
noncomputable abbrev image := X86P1LoadCapture.propImage
def layout : X86Bounds.Layout := ⟨6,0,⟨8,by decide⟩,8,330⟩

theorem source_instruction : image.source.body.atPath ([1,1,1,1] ++ List.replicate 7 0 ++ [1]) =
    some (.instruction (.load .u64 .word64 0 6 1 (8#32))) := by kernel_reflexivity

theorem prefix_bytes (byte : Fin 49) : image.view.read (260 + byte.val) =
    ((X86Bounds.code layout)[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases byte <;> kernel_reflexivity

theorem tail_bytes (byte : Fin 7) : image.view.read (309 + byte.val) =
    ((X86QwordLoad.code 10 6 (8#32))[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases byte <;> kernel_reflexivity

def context (base : Int) (start : BitVec 48) (placed : start.toInt = base + 260)
    (upper : base + 647 < (2 ^ 47 : Int)) : X86Bounds.Context layout start where
  extent := 387
  upper := by rw [placed]; omega
  codeWithin := by decide
  rejectWithin := by decide
  overflowDelta := by decide
  shortDelta := by decide
  rangeDelta := by decide

theorem prefix_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 260) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86Bounds.code layout) := by
  intro byte value present
  have within : byte < 49 := by
    simpa only [X86Bounds.code_length,show X86Bounds.exitAt layout = 49 from rfl] using (List.getElem?_eq_some_iff.mp present).1
  have captured := prefix_bytes ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (260 + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (260 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

theorem tail_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 309) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86QwordLoad.code 10 6 (8#32)) := by
  intro byte value present
  have within : byte < 7 := by simpa only [X86QwordLoad.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := tail_bytes ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (309 + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (309 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

def input (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86Bounds.Facts layout state) (placed : origin.address.toInt = base + 260)
    (upper : base + 647 < (2 ^ 47 : Int)) (loaded : X86P1LoadCapture.Loaded image state base) :
    X86Bounds.Inputs layout state origin :=
  { facts with geometry := context base origin.address placed upper
               loaded := prefix_loaded state base origin placed loaded }

theorem load_executes_control (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86Bounds.Facts layout state) (placed : origin.address.toInt = base + 260)
    (upper : base + 647 < (2 ^ 47 : Int)) (loaded : X86P1LoadCapture.Loaded image state base)
    (value : Word) (dataAddress : BitVec 48)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (effective : facts.pointer + (8#32).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (bytes : ∀ index < 8, state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8))
    (fits : (facts.pointer - facts.base).toNat + 16 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 10).run state = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) state after ∧ lookup after 10 = some value ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some ((address base 316).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  let prepared := input state base origin facts placed upper loaded
  have fitsPrepared : (prepared.pointer - prepared.base).toNat + layout.offset.val + layout.count.val ≤ prepared.length.toNat := fits
  obtain ⟨middle,flags,first,firstFrame,flagsRead,firstRip,control⟩ :=
    X86Bounds.succeeds_control other extraHandlers vector layout state origin prepared fitsPrepared
  let nextOrigin := rebase state middle origin (firstFrame.mono X86Bounds.writes_data) prepared.geometry.upper 49
    (by change 49 + 3 ≤ 387; decide) firstRip
  have nextPlaced : nextOrigin.address.toInt = base + 309 := by
    change (address origin.address.toInt 49).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) prepared.geometry.upper 49
      (by change 49 ≤ 387; decide)]
    omega
  have middleImage : X86P1LoadCapture.Loaded image middle base := by
    intro index within
    rw [firstFrame.memory]
    exact loaded index within
  let readInput : X86QwordLoad.Inputs middle 10 6 (8#32) := { nextOrigin with
    noSib := by decide
    noStack := by decide
    visible := facts.visible
    controls := facts.controls
    baseValue := facts.pointer
    value := value
    flags := flags
    dataAddress := dataAddress
    baseKnown := (firstFrame.lookup 6 (by decide)).trans facts.pointerKnown
    controlKnown := (firstFrame.registers .ctrs (by decide)).trans facts.controlKnown
    flagsKnown := flagsRead
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans facts.visibleKnown
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet
    upper := by rw [nextPlaced]; omega
    dataUpper := dataUpper
    effective := effective
    aligned := aligned
    loaded := tail_loaded middle base nextOrigin nextPlaced middleImage
    dataPresent := by intro index within; rw [firstFrame.memory]; exact bytes index within }
  obtain ⟨after,last,lastFrame,valueRead,rip⟩ := X86QwordLoad.executes (X86Bounds.handlers other extraHandlers) vector middle 10 6 (8#32) readInput
  refine ⟨after,flags,?_,(firstFrame.trans lastFrame).mono (by decide),valueRead,
    (lastFrame.registers .rflags (by decide)).trans flagsRead,?_,?_,?_⟩
  · exact X86FuelPrefix.fetches_then 9 1 state middle after first last
  · have point : address readInput.address.toInt 7 = address base 316 := by
      change address nextOrigin.address.toInt 7 = _
      unfold address
      rw [nextPlaced]
      congr 1
      omega
    rw [point] at rip
    exact rip
  · intro index within
    rw [lastFrame.memory,firstFrame.memory]
    exact loaded index within
  · exact control.trans (X86ControlFlags.of_register_frame lastFrame (by decide))

theorem load_executes (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86Bounds.Facts layout state) (placed : origin.address.toInt = base + 260)
    (upper : base + 647 < (2 ^ 47 : Int)) (loaded : X86P1LoadCapture.Loaded image state base)
    (value : Word) (dataAddress : BitVec 48)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (effective : facts.pointer + (8#32).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (bytes : ∀ index < 8, state.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8))
    (fits : (facts.pointer - facts.base).toNat + 16 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 10).run state = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) state after ∧ lookup after 10 = some value ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some ((address base 316).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,result,flagsRead,rip,imageLoaded,_control⟩ :=
    load_executes_control other extraHandlers vector state base origin facts placed upper loaded value dataAddress
      dataUpper effective aligned bytes fits
  exact ⟨after,flags,run,frame,result,flagsRead,rip,imageLoaded⟩

#print axioms prefix_bytes
#print axioms load_executes

end Mettapedia.Machines.TIsa.X86P1FieldLoadCapture
