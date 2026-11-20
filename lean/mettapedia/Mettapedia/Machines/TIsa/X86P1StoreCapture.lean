import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.X86Bounds

/-!
# The five output-store instructions in the actual consumer image

Each STORE span ends in the same proved REX-prefixed MOV form. The source
nodes, span metadata and all seven instruction bytes are checked for both
dword and all three qword writes. The loaded complete image supplies the
bytes, and the generic store contract supplies execution and exact effects.
Image preservation requires explicit separation from the written bytes.

The parameterized bounds constructor checks every captured prefix byte and
composes with the store contract for the complete individual STORE spans.
The output-construction sequence and complete consumer/source/ABI composition
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1StoreCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev image := X86P1LoadCapture.propImage

structure Site where
  start : Nat
  length : Nat
  wide : Bool
  displacement : BitVec 32

def site : Fin 5 → Site
  | ⟨0,_⟩ => ⟨155,43,false,0⟩
  | ⟨1,_⟩ => ⟨204,56,false,4⟩
  | ⟨2,_⟩ => ⟨316,56,true,8⟩
  | ⟨3,_⟩ => ⟨378,56,true,16⟩
  | ⟨4,_⟩ => ⟨440,56,true,24⟩

def path (index : Fin 5) : List Nat := [1,1,1,1] ++ List.replicate (10 - 2 * index.val) 0 ++ [1]
def tail (index : Fin 5) : Nat := (site index).start + (site index).length - 7
def finish (index : Fin 5) : Nat := (site index).start + (site index).length

theorem tail_finish : ∀ index : Fin 5, tail index + 7 = finish index := by decide
theorem finish_bound : ∀ index : Fin 5, finish index ≤ 647 := by decide

theorem source_instruction (index : Fin 5) : image.source.body.atPath (path index) =
    some (.instruction (.store (if (site index).wide then .word64 else .word32) 1 2 (site index).displacement 6)) := by
  fin_cases index <;> kernel_reflexivity

theorem containing_span (index : Fin 5) : image.spans.any (fun span =>
    span.offset == (site index).start && span.length == (site index).length && span.kind == "STORE" &&
      span.path == some (path index)) = true := by
  fin_cases index <;> kernel_reflexivity

theorem tail_bytes (index : Fin 5) (byte : Fin 7) : image.view.read (tail index + byte.val) =
    ((X86DataStore.code (site index).wide 10 2 (site index).displacement)[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> fin_cases byte <;> kernel_reflexivity

theorem tail_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (placed : origin.address.toInt = base + tail index) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86DataStore.code (site index).wide 10 2 (site index).displacement) := by
  intro byte value present
  have within : byte < 7 := by simpa only [X86DataStore.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := tail_bytes index ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (tail index + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have bounded : tail index + byte < image.size := by
    rw [X86P1LoadCapture.byte_extent]
    have := tail_finish index
    have := finish_bound index
    omega
  simpa only [shifted] using (loaded (tail index + byte) bounded).trans captured

def input (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (pointer value : Word) (dataAddress : BitVec 48) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (placed : origin.address.toInt = base + tail index) (upper : base + 647 < (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + X86DataStore.byteCount (site index).wide ≤ (2 ^ 47 : Int))
    (pointerKnown : lookup state 2 = some pointer) (valueKnown : lookup state 10 = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer + (site index).displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& BitVec.ofNat 48 (X86DataStore.byteCount (site index).wide - 1) = (0#48))
    (loaded : X86P1LoadCapture.Loaded image state base) :
    X86DataStore.Inputs state (site index).wide 10 2 (site index).displacement := {
  origin with
  noSib := by decide
  noStack := by decide
  visible := visible
  controls := controls
  baseValue := pointer
  value := value
  flags := flags
  dataAddress := dataAddress
  baseKnown := pointerKnown
  sourceKnown := valueKnown
  controlKnown := controlKnown
  flagsKnown := flagsKnown
  visibleKnown := visibleKnown
  quiet := quiet
  upper := by rw [placed]; have := tail_finish index; have := finish_bound index; omega
  dataUpper := dataUpper
  effective := effective
  aligned := aligned
  loaded := tail_loaded state base origin index placed loaded }

theorem tail_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (pointer value : Word) (dataAddress : BitVec 48) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (placed : origin.address.toInt = base + tail index) (upper : base + 647 < (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + X86DataStore.byteCount (site index).wide ≤ (2 ^ 47 : Int))
    (pointerKnown : lookup state 2 = some pointer) (valueKnown : lookup state 10 = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : pointer + (site index).displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& BitVec.ofNat 48 (X86DataStore.byteCount (site index).wide - 1) = (0#48))
    (loaded : X86P1LoadCapture.Loaded image state base)
    (apart : ∀ offset < image.size, ((address base offset).signExtend 52).toNat ∉
      X86DataStore.writes (site index).wide dataAddress) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      X86StateFrame.Frame {.rip} (X86DataStore.writes (site index).wide dataAddress) state after ∧
      after.regs.get? .rip = some ((address base (finish index)).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ lookup after 10 = some value ∧ lookup after 2 = some pointer ∧
      (∀ byte < X86DataStore.byteCount (site index).wide,
        after.mem.get? (X86WriteWords.physicalAddress dataAddress byte) =
          some ((X86DataStore.payload (site index).wide value).extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after base := by
  let prepared := input state base origin index pointer value dataAddress flags visible controls placed upper dataUpper
    pointerKnown valueKnown controlKnown flagsKnown visibleKnown quiet effective aligned loaded
  obtain ⟨run,frame⟩ := X86DataStore.executes other vector state (site index).wide 10 2 (site index).displacement prepared
  have addressValue : prepared.dataAddress = dataAddress := rfl
  have sourceValue : prepared.value = value := rfl
  rw [addressValue,sourceValue] at run frame
  let next := address prepared.address.toInt 7
  let after := X86DataStore.result (site index).wide state dataAddress next value
  refine ⟨after,run,frame,?_,(frame.registers .rflags (by decide)).trans flagsKnown,
    (frame.lookup 10 (by decide)).trans valueKnown,(frame.lookup 2 (by decide)).trans pointerKnown,?_,?_⟩
  · have shifted : next = address base (finish index) := by
      change address origin.address.toInt 7 = _
      unfold address
      rw [placed]
      congr 1
      have := tail_finish index
      omega
    simp only [after,X86DataStore.result,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]
    exact congrArg (fun point : BitVec 48 => some (point.signExtend 64)) shifted
  · intro byte within
    exact X86DataStore.byte_readback state (site index).wide dataAddress next value dataUpper byte within
  · intro offset within
    exact (frame.memory _ (apart offset within)).trans (loaded offset within)

def boundsLayout (index : Fin 5) : X86Bounds.Layout where
  pointer := 2
  region := 1
  offset := ⟨(site index).displacement.toNat,by fin_cases index <;> decide⟩
  count := ⟨X86DataStore.byteCount (site index).wide,by fin_cases index <;> decide⟩
  reject := 590 - (site index).start

theorem bounds_length : ∀ index : Fin 5, X86Bounds.exitAt (boundsLayout index) + 7 = (site index).length := by decide
theorem bounds_finish : ∀ index : Fin 5, (site index).start + X86Bounds.exitAt (boundsLayout index) = tail index := by decide
theorem bounds_reject : ∀ index : Fin 5, (site index).start + (boundsLayout index).reject = 590 := by decide
theorem bounds_offset : ∀ index : Fin 5,
    X86PositiveImmediate.immediate32 (boundsLayout index).offset = (site index).displacement := by decide

theorem bounds_bytes (index : Fin 5) (byte : Fin (X86Bounds.exitAt (boundsLayout index))) :
    image.view.read ((site index).start + byte.val) =
      ((X86Bounds.code (boundsLayout index))[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> fin_cases byte <;> kernel_reflexivity

theorem bounds_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (placed : origin.address.toInt = base + (site index).start) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86Bounds.code (boundsLayout index)) := by
  intro byte value present
  have within : byte < X86Bounds.exitAt (boundsLayout index) := by
    simpa only [X86Bounds.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := bounds_bytes index ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base ((site index).start + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have bounded : (site index).start + byte < image.size := by
    rw [X86P1LoadCapture.byte_extent]
    have := bounds_finish index
    have := tail_finish index
    have := finish_bound index
    omega
  simpa only [shifted] using (loaded ((site index).start + byte) bounded).trans captured

def boundsContext (base : Int) (start : BitVec 48) (index : Fin 5)
    (placed : start.toInt = base + (site index).start) (upper : base + 647 < (2 ^ 47 : Int)) :
    X86Bounds.Context (boundsLayout index) start where
  extent := 647 - (site index).start
  upper := by
    rw [placed]
    have small : (site index).start ≤ 647 := by fin_cases index <;> decide
    omega
  codeWithin := by fin_cases index <;> decide
  rejectWithin := by fin_cases index <;> decide
  overflowDelta := by fin_cases index <;> decide
  shortDelta := by fin_cases index <;> decide
  rangeDelta := by fin_cases index <;> decide

def boundsInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (facts : X86Bounds.Facts (boundsLayout index) state)
    (placed : origin.address.toInt = base + (site index).start) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded image state base) : X86Bounds.Inputs (boundsLayout index) state origin :=
  { facts with geometry := boundsContext base origin.address index placed upper
               loaded := bounds_loaded state base origin index placed loaded }

theorem bounds_position (start : BitVec 48) (base : Int) (index : Fin 5)
    (placed : start.toInt = base + (site index).start) (offset : Nat) :
    X86Bounds.position start offset = address base ((site index).start + offset) := by
  unfold X86Bounds.position address
  rw [placed]
  congr 1
  omega

theorem bounds_classifies (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (facts : X86Bounds.Facts (boundsLayout index) state)
    (placed : origin.address.toInt = base + (site index).start) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded image state base)
    (rangeFits : facts.base.toNat + facts.length.toNat < 2 ^ 64)
    (pointerLower : facts.base.toNat ≤ facts.pointer.toNat) (pointerUpper : facts.pointer.toNat ≤ facts.base.toNat + facts.length.toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86Bounds.boundsSteps (boundsLayout index) facts.base facts.pointer facts.length)).run state = .ok () after ∧
      RegisterFrame X86Bounds.writes state after ∧ after.regs.get? .rip = some
        ((if Memory.access? facts.base facts.length facts.pointer (site index).displacement.toInt
          (X86DataStore.byteCount (site index).wide) = some (facts.pointer.toNat + (site index).displacement.toNat)
          then address base (tail index) else address base 590).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  let prepared := boundsInput state base origin index facts placed upper loaded
  obtain ⟨after,run,frame,rip⟩ := X86Bounds.source_classifies other extraHandlers vector (boundsLayout index) state origin prepared
    rangeFits pointerLower pointerUpper
  have baseValue : prepared.base = facts.base := rfl
  have pointerValue : prepared.pointer = facts.pointer := rfl
  have lengthValue : prepared.length = facts.length := rfl
  rw [baseValue,pointerValue,lengthValue] at rip
  have offsetValue : (boundsLayout index).offset.val = (site index).displacement.toNat := rfl
  have countValue : (boundsLayout index).count.val = X86DataStore.byteCount (site index).wide := rfl
  rw [bounds_offset,offsetValue,countValue,bounds_position origin.address base index placed,
    bounds_position origin.address base index placed,bounds_finish,bounds_reject] at rip
  refine ⟨after,run,frame,rip,?_⟩
  intro offset within
  rw [frame.memory]
  exact loaded offset within

theorem store_span_executes (other : OtherOpcodeHandlers) (extraHandlers : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (index : Fin 5)
    (facts : X86Bounds.Facts (boundsLayout index) state)
    (placed : origin.address.toInt = base + (site index).start) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded image state base) (value : Word) (valueKnown : lookup state 10 = some value)
    (dataAddress : BitVec 48)
    (dataUpper : dataAddress.toInt + X86DataStore.byteCount (site index).wide ≤ (2 ^ 47 : Int))
    (effective : facts.pointer + (site index).displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& BitVec.ofNat 48 (X86DataStore.byteCount (site index).wide - 1) = (0#48))
    (fits : (facts.pointer - facts.base).toNat + (site index).displacement.toNat +
      X86DataStore.byteCount (site index).wide ≤ facts.length.toNat)
    (apart : ∀ offset < image.size, ((address base offset).signExtend 52).toNat ∉ X86DataStore.writes (site index).wide dataAddress) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (X86Bounds.offsetSteps (boundsLayout index) + 6)).run state = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes (site index).wide dataAddress) state after ∧
      after.regs.get? .rip = some ((address base (finish index)).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ lookup after 10 = some value ∧ lookup after 2 = some facts.pointer ∧
      (∀ byte < X86DataStore.byteCount (site index).wide,
        after.mem.get? (X86WriteWords.physicalAddress dataAddress byte) =
          some ((X86DataStore.payload (site index).wide value).extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extraHandlers
  let : VectorOpcodeHandlers := vector
  let prepared := boundsInput state base origin index facts placed upper loaded
  have fitsPrepared : (prepared.pointer - prepared.base).toNat + (boundsLayout index).offset.val +
      (boundsLayout index).count.val ≤ prepared.length.toNat := fits
  obtain ⟨middle,flags,first,firstFrame,flagsRead,firstRip⟩ :=
    X86Bounds.succeeds other extraHandlers vector (boundsLayout index) state origin prepared fitsPrepared
  have tailWithin : X86Bounds.exitAt (boundsLayout index) + 3 ≤ prepared.geometry.extent := by
    change X86Bounds.exitAt (boundsLayout index) + 3 ≤ 647 - (site index).start
    fin_cases index <;> decide
  let nextOrigin := rebase state middle origin (firstFrame.mono X86Bounds.writes_data) prepared.geometry.upper
    (X86Bounds.exitAt (boundsLayout index)) tailWithin firstRip
  have nextPlaced : nextOrigin.address.toInt = base + tail index := by
    change (address origin.address.toInt (X86Bounds.exitAt (boundsLayout index))).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) prepared.geometry.upper
      (X86Bounds.exitAt (boundsLayout index)) (by omega)]
    rw [placed]
    have finishPosition := bounds_finish index
    omega
  have middleImage : X86P1LoadCapture.Loaded image middle base := by
    intro offset within
    rw [firstFrame.memory]
    exact loaded offset within
  obtain ⟨after,last,lastFrame,rip,lastFlags,lastValue,lastPointer,bytes,image⟩ :=
    tail_executes (X86Bounds.handlers other extraHandlers) vector middle base nextOrigin index facts.pointer value dataAddress flags
      facts.visible facts.controls nextPlaced upper dataUpper
      ((firstFrame.lookup 2 (by decide)).trans facts.pointerKnown) ((firstFrame.lookup 10 (by decide)).trans valueKnown)
      ((firstFrame.registers .ctrs (by decide)).trans facts.controlKnown) flagsRead
      ((firstFrame.registers .seg_visibles (by decide)).trans facts.visibleKnown)
      ((firstFrame.registers .log_register_writes (by decide)).trans facts.quiet) effective aligned middleImage apart
  refine ⟨after,flags,?_,?_,rip,lastFlags,lastValue,lastPointer,bytes,image⟩
  · simpa only [Nat.add_assoc] using X86FuelPrefix.fetches_then (X86Bounds.offsetSteps (boundsLayout index) + 5) 1 state middle after first last
  · exact ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono (by decide) (by simp)

#print axioms store_span_executes
#print axioms bounds_bytes
#print axioms bounds_classifies
#print axioms source_instruction
#print axioms tail_bytes
#print axioms tail_executes

end Mettapedia.Machines.TIsa.X86P1StoreCapture
