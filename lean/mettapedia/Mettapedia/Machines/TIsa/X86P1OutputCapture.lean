import Mettapedia.Machines.TIsa.X86P1StoreCapture
import Mettapedia.Machines.TIsa.X86P1FieldLoadCapture
import Mettapedia.Machines.TIsa.X86Immediate32
import Mettapedia.Machines.TIsa.X86FailureHandler

/-!
# Output construction and successful completion in the actual p1 image

Generic immediate, bounds, load and store contracts compose through every
output stage in R_DERIVE_IS_PROP. The 62-instruction path produces all 32 row
bytes; later stores preserve the prefixes already written. Separate descriptor,
premise and code footprints carry the required inputs between stages.

The actual success block extends this to 66 instructions, both FIRED receipt
words and the epilogue boundary. Public ABI and source/admission joins remain
separate obligations. Inputs contain physical data and geometry, never a
native execution or output-correctness premise.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1OutputCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
noncomputable abbrev image := X86P1LoadCapture.propImage
abbrev clobbers : Finset Register := {.rip,.rflags,.r10,.r14,.r15}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def transferFacts {layout : X86Bounds.Layout} {before after : State} {written : Finset Nat}
    (facts : X86Bounds.Facts layout before) (frame : X86StateFrame.Frame clobbers written before after)
    (pointerKept : key layout.pointer ∉ clobbers) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags)
    (baseApart : ∀ byte < 8, ((address facts.baseAddress.toInt byte).signExtend 52).toNat ∉ written)
    (lengthApart : ∀ byte < 8, ((address facts.lengthAddress.toInt byte).signExtend 52).toNat ∉ written) :
    X86Bounds.Facts layout after :=
  X86Bounds.Facts.transport facts frame clobbers_data (by decide) pointerKept flags flagsKnown baseApart lengthApart

def storeFacts {state : State} (index : Fin 5)
    (facts : X86Bounds.Facts (X86P1StoreCapture.boundsLayout 0) state) :
    X86Bounds.Facts (X86P1StoreCapture.boundsLayout index) state := {
  facts with
  pointerKnown := facts.pointerKnown
  baseEffective := facts.baseEffective
  lengthEffective := facts.lengthEffective }

def start : Fin 5 → Nat
  | ⟨0,_⟩ => 149
  | ⟨1,_⟩ => 198
  | ⟨2,_⟩ => 260
  | ⟨3,_⟩ => 372
  | ⟨4,_⟩ => 434

def immediate (index : Fin 5) : BitVec 32 := if index.val = 0 then 7173 else 0
def value (index : Fin 5) (field : Word) : Word :=
  if index.val = 2 then field else (immediate index).zeroExtend 64

theorem immediate_bytes (index : Fin 5) (notLoad : index ≠ 2) (byte : Fin 6) :
    image.view.read (start index + byte.val) =
      ((X86Immediate32.code 10 (immediate index))[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> fin_cases byte <;>
    first | exact False.elim (notLoad rfl) | kernel_reflexivity

theorem immediate_finish : ∀ index : Fin 5, index ≠ 2 → start index + 6 = (X86P1StoreCapture.site index).start := by decide
theorem starts_within : ∀ index : Fin 5, start index + 6 < 647 := by decide

theorem immediate_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (index : Fin 5) (notLoad : index ≠ 2) (placed : origin.address.toInt = base + start index)
    (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt (X86Immediate32.code 10 (immediate index)) := by
  intro byte encoded present
  have within : byte < 6 := by simpa only [X86Immediate32.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := immediate_bytes index notLoad ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (start index + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have bounded : start index + byte < image.size := by
    rw [X86P1LoadCapture.byte_extent]
    have := starts_within index
    omega
  simpa only [shifted] using (loaded (start index + byte) bounded).trans captured

theorem immediate_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (index : Fin 5) (notLoad : index ≠ 2) (placed : origin.address.toInt = base + start index)
    (upper : base + 647 < (2 ^ 47 : Int)) (loaded : X86P1LoadCapture.Loaded image state base)
    (quiet : state.regs.get? .log_register_writes = some false) (flags : BitVec 32)
    (flagsKnown : state.regs.get? .rflags = some flags) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame clobbers state after ∧ lookup after 10 = some (value index 0) ∧
      after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((address base (X86P1StoreCapture.site index).start).signExtend 64) ∧
      X86P1LoadCapture.Loaded image after base := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : X86Immediate32.Inputs state 10 (immediate index) := { origin with
    quiet := quiet
    upper := by have := starts_within index; omega
    loaded := immediate_loaded state base origin index notLoad placed loaded }
  obtain ⟨after,run,frame,readback,rip⟩ :=
    X86Immediate32.executes (X86Bounds.handlers other extra) vector state 10 (immediate index) input
  refine ⟨after,run,frame.mono (by decide),?_,(frame.registers .rflags (by decide)).trans flagsKnown,?_,?_⟩
  · have different : index.val ≠ 2 := by intro same; exact notLoad (Fin.ext same)
    simpa only [value,if_neg different] using readback
  · have point : address input.address.toInt 6 = address base (X86P1StoreCapture.site index).start := by
      change address origin.address.toInt 6 = _
      unfold address
      rw [placed]
      congr 1
      have := immediate_finish index notLoad
      omega
    rw [point] at rip
    exact rip
  · intro byte within
    rw [frame.memory]
    exact loaded byte within

def outputWrites (output : BitVec 48) : Finset Nat := X86WriteWords.written output (List.range 32)
def displacement : Fin 5 → Nat
  | ⟨0,_⟩ => 0
  | ⟨1,_⟩ => 4
  | ⟨2,_⟩ => 8
  | ⟨3,_⟩ => 16
  | ⟨4,_⟩ => 24
theorem displacement_nat : ∀ index : Fin 5, (X86P1StoreCapture.site index).displacement.toNat = displacement index := by decide
def outputAt (output : BitVec 48) (index : Fin 5) : BitVec 48 :=
  address output.toInt (X86P1StoreCapture.site index).displacement.toNat

theorem store_within : ∀ index : Fin 5,
    (X86P1StoreCapture.site index).displacement.toNat + X86DataStore.byteCount (X86P1StoreCapture.site index).wide ≤ 32 := by decide

theorem outputAt_toInt (output : BitVec 48) (upper : output.toInt + 32 ≤ (2 ^ 47 : Int)) (index : Fin 5) :
    (outputAt output index).toInt = output.toInt + (X86P1StoreCapture.site index).displacement.toNat := by
  apply address_toInt output.toInt (extent := 31) (by simpa using BitVec.le_toInt output)
    (show output.toInt + 31 < (2 ^ 47 : Int) by omega)
  have := store_within index
  have positive : 1 ≤ X86DataStore.byteCount (X86P1StoreCapture.site index).wide := by
    fin_cases index <;> decide
  omega

theorem physical_shift (output : BitVec 48) (upper : output.toInt + 32 ≤ (2 ^ 47 : Int))
    (index : Fin 5) (byte : Nat) :
    X86WriteWords.physicalAddress (outputAt output index) byte =
      X86WriteWords.physicalAddress output ((X86P1StoreCapture.site index).displacement.toNat + byte) := by
  unfold X86WriteWords.physicalAddress
  rw [outputAt_toInt output upper index]
  simp only [address, Nat.cast_add, Int.add_assoc]

theorem store_writes_subset (output : BitVec 48) (upper : output.toInt + 32 ≤ (2 ^ 47 : Int)) (index : Fin 5) :
    X86DataStore.writes (X86P1StoreCapture.site index).wide (outputAt output index) ⊆ outputWrites output := by
  intro location member
  simp only [X86DataStore.writes,X86WriteWords.written,List.mem_toFinset,List.mem_map,List.mem_range] at member
  obtain ⟨byte,within,rfl⟩ := member
  rw [physical_shift output upper index byte]
  simp only [outputWrites,X86WriteWords.written,List.mem_toFinset,List.mem_map,List.mem_range]
  refine ⟨(X86P1StoreCapture.site index).displacement.toNat + byte,?_,rfl⟩
  have := store_within index
  omega

theorem outputAt_add (output : BitVec 48) (index : Fin 5) :
    outputAt output index = output + BitVec.ofNat 48 (X86P1StoreCapture.site index).displacement.toNat := by
  simp only [outputAt,address,BitVec.ofInt_add,BitVec.ofInt_toInt,BitVec.ofInt_natCast]

theorem output_alignment (output : BitVec 48) (aligned : output &&& (7#48) = (0#48)) (index : Fin 5) :
    outputAt output index &&& BitVec.ofNat 48 (X86DataStore.byteCount (X86P1StoreCapture.site index).wide - 1) = (0#48) := by
  have mod8 : output.toNat % 8 = 0 := by
    have known := congrArg BitVec.toNat aligned
    simpa only [BitVec.toNat_and,show (7#48).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_zero] using known
  rw [outputAt_add,displacement_nat index]
  fin_cases index <;> apply BitVec.eq_of_toNat_eq
  all_goals
    simp only [BitVec.toNat_and,BitVec.toNat_add,BitVec.toNat_ofNat]
    norm_num [X86P1StoreCapture.site,X86DataStore.byteCount,displacement,BitVec.ofNat_eq_ofNat,BitVec.toNat_ofNat]
    first
    | rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]; norm_num; omega
    | rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]; norm_num; omega

theorem signExtend_ofInt (word : BitVec 48) : word.signExtend 64 = BitVec.ofInt 64 word.toInt := by
  have h : BitVec.ofInt 64 (word.signExtend 64).toInt = word.signExtend 64 := BitVec.ofInt_toInt
  rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] at h
  exact h.symm

theorem output_effective (output : BitVec 48) (upper : output.toInt + 32 ≤ (2 ^ 47 : Int)) (index : Fin 5) :
    output.signExtend 64 + (X86P1StoreCapture.site index).displacement.signExtend 64 =
      (outputAt output index).signExtend 64 := by
  have displacement : (X86P1StoreCapture.site index).displacement.signExtend 64 =
      BitVec.ofInt 64 ((X86P1StoreCapture.site index).displacement.toNat : Int) := by
    fin_cases index <;> rfl
  rw [signExtend_ofInt,displacement,← BitVec.ofInt_add,signExtend_ofInt,outputAt_toInt output upper index]

structure DataFacts (state : State) where
  base : Int
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + 647 < (2 ^ 47 : Int)
  loaded : X86P1LoadCapture.Loaded image state base
  outputFacts : X86Bounds.Facts (X86P1StoreCapture.boundsLayout 0) state
  premiseFacts : X86Bounds.Facts X86P1FieldLoadCapture.layout state
  output : BitVec 48
  outputUpper : output.toInt + 32 ≤ (2 ^ 47 : Int)
  outputEffective : outputFacts.pointer = output.signExtend 64
  outputAligned : output &&& (7#48) = (0#48)
  outputFits : (outputFacts.pointer - outputFacts.base).toNat + 32 ≤ outputFacts.length.toNat
  field : Word
  fieldAddress : BitVec 48
  fieldUpper : fieldAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  fieldEffective : premiseFacts.pointer + (8#32).signExtend 64 = fieldAddress.signExtend 64
  fieldAligned : fieldAddress &&& (7#48) = (0#48)
  fieldBytes : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress fieldAddress byte) =
    some (field.extractLsb' (8 * byte) 8)
  premiseFits : (premiseFacts.pointer - premiseFacts.base).toNat + 16 ≤ premiseFacts.length.toNat
  codeApart : ∀ byte < image.size, ((address base byte).signExtend 52).toNat ∉ outputWrites output
  outputBaseApart : ∀ byte < 8, X86WriteWords.physicalAddress outputFacts.baseAddress byte ∉ outputWrites output
  outputLengthApart : ∀ byte < 8, X86WriteWords.physicalAddress outputFacts.lengthAddress byte ∉ outputWrites output
  premiseBaseApart : ∀ byte < 8, X86WriteWords.physicalAddress premiseFacts.baseAddress byte ∉ outputWrites output
  premiseLengthApart : ∀ byte < 8, X86WriteWords.physicalAddress premiseFacts.lengthAddress byte ∉ outputWrites output
  fieldApart : ∀ byte < 8, X86WriteWords.physicalAddress fieldAddress byte ∉ outputWrites output

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends DataFacts state where
  placed : origin.address.toInt = base + 149

def DataFacts.transport {before after : State} {registers : Finset Register} {written : Finset Nat}
    (facts : DataFacts before) (frame : X86StateFrame.Frame registers written before after)
    (dataOnly : registers ⊆ dataRegisters) (frameKept : key 7 ∉ registers)
    (outputKept : key 2 ∉ registers) (premiseKept : key 6 ∉ registers)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags)
    (codeApart : ∀ byte < image.size, ((address facts.base byte).signExtend 52).toNat ∉ written)
    (outputBaseApart : ∀ byte < 8, X86WriteWords.physicalAddress facts.outputFacts.baseAddress byte ∉ written)
    (outputLengthApart : ∀ byte < 8, X86WriteWords.physicalAddress facts.outputFacts.lengthAddress byte ∉ written)
    (premiseBaseApart : ∀ byte < 8, X86WriteWords.physicalAddress facts.premiseFacts.baseAddress byte ∉ written)
    (premiseLengthApart : ∀ byte < 8, X86WriteWords.physicalAddress facts.premiseFacts.lengthAddress byte ∉ written)
    (fieldApart : ∀ byte < 8, X86WriteWords.physicalAddress facts.fieldAddress byte ∉ written) : DataFacts after := {
  facts with
  loaded := fun byte within => (frame.memory _ (codeApart byte within)).trans (facts.loaded byte within)
  outputFacts := X86Bounds.Facts.transport facts.outputFacts frame dataOnly frameKept outputKept flags flagsKnown outputBaseApart outputLengthApart
  premiseFacts := X86Bounds.Facts.transport facts.premiseFacts frame dataOnly frameKept premiseKept flags flagsKnown premiseBaseApart premiseLengthApart
  fieldBytes := fun byte within => (frame.memory _ (fieldApart byte within)).trans (facts.fieldBytes byte within) }

def outputFactsAt {before after : State} {origin : X86LegacyFetch.Basis before}
    (input : Inputs before origin) (frame : X86StateFrame.Frame clobbers (outputWrites input.output) before after)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags) :
    X86Bounds.Facts (X86P1StoreCapture.boundsLayout 0) after :=
  transferFacts input.outputFacts frame (by decide) flags flagsKnown input.outputBaseApart input.outputLengthApart

def premiseFactsAt {before after : State} {origin : X86LegacyFetch.Basis before}
    (input : Inputs before origin) (frame : X86StateFrame.Frame clobbers (outputWrites input.output) before after)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags) :
    X86Bounds.Facts X86P1FieldLoadCapture.layout after :=
  transferFacts input.premiseFacts frame (by decide) flags flagsKnown input.premiseBaseApart input.premiseLengthApart

theorem imageAt {before after : State} {origin : X86LegacyFetch.Basis before}
    (input : Inputs before origin) (frame : X86StateFrame.Frame clobbers (outputWrites input.output) before after) :
    X86P1LoadCapture.Loaded image after input.base := by
  intro byte within
  exact (frame.memory _ (input.codeApart byte within)).trans (input.loaded byte within)

def basisAt {before after : State} {origin : X86LegacyFetch.Basis before}
    (input : Inputs before origin) (frame : X86StateFrame.Frame clobbers (outputWrites input.output) before after)
    (position : Nat) (within : position + 3 < 647)
    (rip : after.regs.get? .rip = some ((address input.base position).signExtend 64)) :
    X86LegacyFetch.Basis after :=
  X86StateFrame.basisAt before after origin frame clobbers_data (address input.base position)
    (by rw [address_toInt input.base (extent := 647) input.lower input.upper position (by omega)]; have := input.upper; omega) rip

def preambleSteps (index : Fin 5) : Nat := if index.val = 2 then 10 else 1
def stageSteps (index : Fin 5) : Nat := preambleSteps index + X86Bounds.offsetSteps (X86P1StoreCapture.boundsLayout index) + 6
def stageWrites (output : BitVec 48) (index : Fin 5) : Finset Nat :=
  X86DataStore.writes (X86P1StoreCapture.site index).wide (outputAt output index)

theorem preamble_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (initial current : State) (origin : X86LegacyFetch.Basis initial)
    (input : Inputs initial origin) (index : Fin 5)
    (frame : X86StateFrame.Frame clobbers (outputWrites input.output) initial current)
    (flags : BitVec 32) (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((address input.base (start index)).signExtend 64)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (preambleSteps index)).run current = .ok () after ∧
      RegisterFrame clobbers current after ∧ lookup after 10 = some (value index input.field) ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((address input.base (X86P1StoreCapture.site index).start).signExtend 64) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  let here := basisAt input frame (start index) (by have := starts_within index; omega) rip
  have placed : here.address.toInt = input.base + start index :=
    address_toInt input.base (extent := 647) input.lower input.upper (start index) (by have := starts_within index; omega)
  by_cases loading : index = 2
  · subst index
    let facts := premiseFactsAt input frame flags flagsKnown
    obtain ⟨after,nextFlags,run,effect,readback,nextFlagsKnown,nextRip,_⟩ :=
      X86P1FieldLoadCapture.load_executes other extra vector current input.base here facts placed input.upper
        (imageAt input frame) input.field input.fieldAddress input.fieldUpper input.fieldEffective input.fieldAligned
        (fun byte within => (frame.memory _ (input.fieldApart byte within)).trans (input.fieldBytes byte within)) input.premiseFits
    exact ⟨after,nextFlags,run,effect.mono (by decide),readback,nextFlagsKnown,nextRip⟩
  · have different : index.val ≠ 2 := by intro same; exact loading (Fin.ext same)
    obtain ⟨after,run,effect,readback,nextFlagsKnown,nextRip,_⟩ := immediate_executes other extra vector current input.base here
      index loading placed input.upper (imageAt input frame)
      ((frame.registers .log_register_writes (by decide)).trans input.outputFacts.quiet) flags flagsKnown
    refine ⟨after,flags,?_,effect,?_,nextFlagsKnown,nextRip⟩
    · simpa only [preambleSteps,if_neg different] using run
    · simpa only [value,if_neg different] using readback

theorem stage_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (initial current : State) (origin : X86LegacyFetch.Basis initial)
    (input : Inputs initial origin) (index : Fin 5)
    (frame : X86StateFrame.Frame clobbers (outputWrites input.output) initial current)
    (flags : BitVec 32) (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((address input.base (start index)).signExtend 64)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (stageSteps index)).run current = .ok () after ∧
      X86StateFrame.Frame clobbers (stageWrites input.output index) current after ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((address input.base (X86P1StoreCapture.finish index)).signExtend 64) ∧
      (∀ byte < X86DataStore.byteCount (X86P1StoreCapture.site index).wide,
        after.mem.get? (X86WriteWords.physicalAddress (outputAt input.output index) byte) =
          some ((X86DataStore.payload (X86P1StoreCapture.site index).wide (value index input.field)).extractLsb' (8 * byte) 8)) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,middleFlags,first,firstFrame,readback,middleFlagsKnown,middleRip⟩ :=
    preamble_executes other extra vector initial current origin input index frame flags flagsKnown rip
  have cumulative : X86StateFrame.Frame clobbers (outputWrites input.output) initial middle :=
    (frame.trans (X86StateFrame.registerOnly firstFrame)).mono (by simp) (by simp)
  have storeWithin : (X86P1StoreCapture.site index).start + 3 < 647 := by fin_cases index <;> decide
  let here := basisAt input cumulative (X86P1StoreCapture.site index).start storeWithin middleRip
  let facts := storeFacts index (outputFactsAt input cumulative middleFlags middleFlagsKnown)
  have placed : here.address.toInt = input.base + (X86P1StoreCapture.site index).start :=
    address_toInt input.base (extent := 647) input.lower input.upper (X86P1StoreCapture.site index).start (by omega)
  have dataUpper : (outputAt input.output index).toInt +
      X86DataStore.byteCount (X86P1StoreCapture.site index).wide ≤ (2 ^ 47 : Int) := by
    rw [outputAt_toInt input.output input.outputUpper index]
    have := store_within index
    have := input.outputUpper
    omega
  have effective : facts.pointer + (X86P1StoreCapture.site index).displacement.signExtend 64 =
      (outputAt input.output index).signExtend 64 := by
    change input.outputFacts.pointer + _ = _
    rw [input.outputEffective]
    exact output_effective input.output input.outputUpper index
  have fits : (facts.pointer - facts.base).toNat + (X86P1StoreCapture.site index).displacement.toNat +
      X86DataStore.byteCount (X86P1StoreCapture.site index).wide ≤ facts.length.toNat := by
    change (input.outputFacts.pointer - input.outputFacts.base).toNat + _ + _ ≤ input.outputFacts.length.toNat
    have := store_within index
    have := input.outputFits
    omega
  have apart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ stageWrites input.output index := by
    intro byte within member
    exact input.codeApart byte within (store_writes_subset input.output input.outputUpper index member)
  obtain ⟨after,nextFlags,last,lastFrame,lastRip,lastFlags,_,_,bytes,_⟩ :=
    X86P1StoreCapture.store_span_executes other extra vector middle input.base here index facts placed input.upper
      (imageAt input cumulative) (value index input.field) readback (outputAt input.output index) dataUpper effective
      (output_alignment input.output input.outputAligned index) fits apart
  refine ⟨after,nextFlags,?_,?_,lastFlags,lastRip,bytes⟩
  · simpa only [stageSteps,Nat.add_assoc] using X86FuelPrefix.fetches_then (preambleSteps index)
      (X86Bounds.offsetSteps (X86P1StoreCapture.boundsLayout index) + 6) current middle after first last
  · exact ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono (by decide) (by simp [stageWrites])

theorem extendFrame {initial before after : State} {origin : X86LegacyFetch.Basis initial}
    (input : Inputs initial origin) (index : Fin 5)
    (first : X86StateFrame.Frame clobbers (outputWrites input.output) initial before)
    (last : X86StateFrame.Frame clobbers (stageWrites input.output index) before after) :
    X86StateFrame.Frame clobbers (outputWrites input.output) initial after := by
  apply (first.trans last).mono (by simp)
  exact Finset.union_subset (fun _ member => member) (store_writes_subset input.output input.outputUpper index)

def encoded (field : Word) (byte : Nat) : BitVec 8 :=
  if byte < 4 then (7173#32).extractLsb' (8 * byte) 8
  else if byte < 8 then 0
  else if byte < 16 then field.extractLsb' (8 * (byte - 8)) 8
  else 0

def Prefix (state : State) (output : BitVec 48) (field : Word) (count : Nat) : Prop :=
  ∀ byte < count, state.mem.get? (X86WriteWords.physicalAddress output byte) = some (encoded field byte)

theorem encoded_stage (index : Fin 5) (field : Word) (byte : Nat)
    (within : byte < X86DataStore.byteCount (X86P1StoreCapture.site index).wide) :
    (X86DataStore.payload (X86P1StoreCapture.site index).wide (value index field)).extractLsb' (8 * byte) 8 =
      encoded field (displacement index + byte) := by
  fin_cases index <;> norm_num [X86P1StoreCapture.site,X86DataStore.byteCount] at within <;> interval_cases byte
  all_goals
    dsimp [X86P1StoreCapture.site,X86DataStore.byteCount,X86DataStore.payload,low32,value,immediate,encoded,displacement]

theorem previous_bytes_apart (output : BitVec 48) (upper : output.toInt + 32 ≤ (2 ^ 47 : Int))
    (index : Fin 5) (byte : Nat) (earlier : byte < displacement index) :
    X86WriteWords.physicalAddress output byte ∉ stageWrites output index := by
  intro member
  simp only [stageWrites,X86DataStore.writes,X86WriteWords.written,List.mem_toFinset,List.mem_map,List.mem_range] at member
  obtain ⟨offset,within,same⟩ := member
  rw [physical_shift output upper index offset,displacement_nat index] at same
  have bound := store_within index
  rw [displacement_nat index] at bound
  have equal := X86WriteWords.physicalAddress_injective 32 output upper (displacement index + offset) byte
    (by omega) (by omega) same
  omega

theorem prefix_extend {before after : State} (output : BitVec 48) (field : Word)
    (upper : output.toInt + 32 ≤ (2 ^ 47 : Int)) (index : Fin 5)
    (frame : X86StateFrame.Frame clobbers (stageWrites output index) before after)
    (previous : Prefix before output field (displacement index))
    (bytes : ∀ byte < X86DataStore.byteCount (X86P1StoreCapture.site index).wide,
      after.mem.get? (X86WriteWords.physicalAddress (outputAt output index) byte) =
        some ((X86DataStore.payload (X86P1StoreCapture.site index).wide (value index field)).extractLsb' (8 * byte) 8)) :
    Prefix after output field (displacement index + X86DataStore.byteCount (X86P1StoreCapture.site index).wide) := by
  intro byte within
  by_cases earlier : byte < displacement index
  · exact (frame.memory _ (previous_bytes_apart output upper index byte earlier)).trans (previous byte earlier)
  · have localBound : byte - displacement index < X86DataStore.byteCount (X86P1StoreCapture.site index).wide := by omega
    have next := bytes (byte - displacement index) localBound
    rw [physical_shift output upper index,displacement_nat index,
      encoded_stage index field _ localBound,show displacement index + (byte - displacement index) = byte by omega] at next
    exact next

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (initial : State) (origin : X86LegacyFetch.Basis initial) (input : Inputs initial origin) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 62).run initial = .ok () after ∧
      X86StateFrame.Frame clobbers (outputWrites input.output) initial after ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some ((address input.base 496).signExtend 64) ∧
      Prefix after input.output input.field 32 ∧ X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  have initialRip : initial.regs.get? .rip = some ((address input.base 149).signExtend 64) := by
    have point : address input.base 149 = origin.address := by
      unfold address
      change BitVec.ofInt 48 (input.base + 149) = origin.address
      rw [← input.placed]
      exact BitVec.ofInt_toInt
    rw [point]
    exact origin.rip
  have initialFrame := X86StateFrame.Frame.refl clobbers (outputWrites input.output) initial
  obtain ⟨a,f0,r0,e0,h0,p0,b0⟩ := stage_executes other extra vector initial initial origin input 0 initialFrame
    input.outputFacts.flags input.outputFacts.flagsKnown initialRip
  have c0 := extendFrame input 0 initialFrame e0
  have q0 : Prefix a input.output input.field 4 := prefix_extend input.output input.field input.outputUpper 0 e0 (by intro byte within; exact False.elim (Nat.not_lt_zero _ within)) b0
  obtain ⟨b,f1,r1,e1,h1,p1,b1⟩ := stage_executes other extra vector initial a origin input 1 c0 f0 h0 p0
  have c1 := extendFrame input 1 c0 e1
  have q1 : Prefix b input.output input.field 8 := prefix_extend input.output input.field input.outputUpper 1 e1 q0 b1
  obtain ⟨c,f2,r2,e2,h2,p2,b2⟩ := stage_executes other extra vector initial b origin input 2 c1 f1 h1 p1
  have c2 := extendFrame input 2 c1 e2
  have q2 : Prefix c input.output input.field 16 := prefix_extend input.output input.field input.outputUpper 2 e2 q1 b2
  obtain ⟨d,f3,r3,e3,h3,p3,b3⟩ := stage_executes other extra vector initial c origin input 3 c2 f2 h2 p2
  have c3 := extendFrame input 3 c2 e3
  have q3 : Prefix d input.output input.field 24 := prefix_extend input.output input.field input.outputUpper 3 e3 q2 b3
  obtain ⟨after,flags,r4,e4,h4,p4,b4⟩ := stage_executes other extra vector initial d origin input 4 c3 f3 h3 p3
  have c4 := extendFrame input 4 c3 e4
  have q4 : Prefix after input.output input.field 32 := prefix_extend input.output input.field input.outputUpper 4 e4 q3 b4
  have r01 := X86FuelPrefix.fetches_then 9 11 initial a b r0 r1
  have r012 := X86FuelPrefix.fetches_then 20 20 initial b c r01 r2
  have r0123 := X86FuelPrefix.fetches_then 40 11 initial c d r012 r3
  exact ⟨after,flags,X86FuelPrefix.fetches_then 51 11 initial d after r0123 r4,c4,h4,p4,q4,imageAt input c4⟩

def completionCode : List Nat := X86FailureHandler.expected (1#32) (95#32)
theorem completion_bytes (byte : Fin 28) : image.view.read (496 + byte.val) =
    (completionCode[byte.val]?).map (BitVec.ofNat 8) := by fin_cases byte <;> kernel_reflexivity

theorem completion_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 496) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state origin.address.toInt completionCode := by
  intro byte encoded present
  have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
  have captured := completion_bytes ⟨byte,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (496 + byte) = address origin.address.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using (loaded (496 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

def receiptWrites {state : State} (facts : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written facts.statusAddress (List.range 8) ∪ X86WriteWords.written facts.resultAddress (List.range 8)

def receiptAt {before after : State} {origin : X86LegacyFetch.Basis before}
    (input : Inputs before origin) (facts : X86FailureHandler.FrameFacts before)
    (frame : X86StateFrame.Frame clobbers (outputWrites input.output) before after)
    (flags : BitVec 32) (flagsKnown : after.regs.get? .rflags = some flags) : X86FailureHandler.FrameFacts after := {
  facts with
  flags := flags
  frameKnown := (frame.lookup 7 (by decide)).trans facts.frameKnown
  controlsKnown := (frame.registers .ctrs (by decide)).trans facts.controlsKnown
  visibleKnown := (frame.registers .seg_visibles (by decide)).trans facts.visibleKnown
  flagsKnown := flagsKnown
  quiet := (frame.registers .log_register_writes (by decide)).trans facts.quiet }

noncomputable abbrev completeHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86Bounds.handlers (X86FailureHandler.linkedHandlers other) extra
theorem completion_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FailureHandler.linkedHandlers (completeHandlers other extra) = completeHandlers other extra := rfl

theorem completes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (initial : State) (origin : X86LegacyFetch.Basis initial) (input : Inputs initial origin)
    (receipt : X86FailureHandler.FrameFacts initial)
    (codeApart : ∀ byte < image.size, ((address input.base byte).signExtend 52).toNat ∉ receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ receiptWrites receipt) :
    letI : OtherOpcodeHandlers := completeHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 66).run initial = .ok () after ∧
      X86StateFrame.Frame (insert .rax clobbers) (outputWrites input.output ∪ receiptWrites receipt) initial after ∧
      after.regs.get? .rflags = some flags ∧
      lookup after 0 = some (1#64) ∧ after.regs.get? .rip = some ((address input.base 619).signExtend 64) ∧
      Prefix after input.output input.field 32 ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some ((1#64).extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded image after input.base := by
  let : OtherOpcodeHandlers := completeHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,flags,first,firstFrame,flagsKnown,firstRip,outputPrefix,middleImage⟩ :=
    executes (X86FailureHandler.linkedHandlers other) extra vector initial origin input
  let here := basisAt input firstFrame 496 (by decide) firstRip
  have placed : here.address.toInt = input.base + 496 := address_toInt input.base (extent := 647) input.lower input.upper 496 (by decide)
  let facts := receiptAt input receipt firstFrame flags flagsKnown
  let finish : X86FailureHandler.Inputs middle (1#32) := {
    here with
    toFrameFacts := facts
    displacement := 95#32
    epilogue := address input.base 619
    upper := by rw [placed]; have := input.upper; omega
    jump := by
      rw [address_toInt input.base (extent := 647) input.lower input.upper 619 (by decide),placed]
      change input.base + 619 = input.base + 496 + 28 + 95
      omega
    loaded := completion_loaded middle input.base here placed middleImage
    codeOutside := by
      intro byte encoded present
      have within : byte < 28 := (List.getElem?_eq_some_iff.mp present).1
      have shifted : address here.address.toInt byte = address input.base (496 + byte) := by
        unfold address
        rw [placed]
        congr 1
        omega
      rw [shifted]
      exact codeApart (496 + byte) (by rw [X86P1LoadCapture.byte_extent]; omega) }
  have last := X86FailureHandler.executes (completeHandlers other extra) vector middle (1#32) finish
  rw [completion_installed] at last
  let after := X86FailureHandler.finished middle finish
  have correct := X86FailureHandler.finished_result middle (1#32) finish
  refine ⟨after,flags,X86FuelPrefix.fetches_then 62 4 initial middle after first last,
    (firstFrame.trans correct.frame).mono (by decide) (by simp [X86FailureHandler.writes,receiptWrites,finish,facts,receiptAt]),
    correct.flags,correct.rax,correct.pointer,?_,?_,?_,?_⟩
  · intro byte within
    exact (correct.frame.memory _ (outputApart byte within)).trans (outputPrefix byte within)
  · exact correct.status
  · exact correct.result
  · intro byte within
    exact (correct.frame.memory _ (codeApart byte within)).trans (middleImage byte within)

namespace Controls
private def modeControl : Vector (BitVec 64) 7 := Vector.ofFn (fun index => if index.val = 0 then 0x400 else 0)
private def attributes : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then 0x200 else 0)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 0
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 0
private def descriptor (byte : Nat) : BitVec 8 :=
  if byte < 8 then (12288#64).extractLsb' (8 * byte) 8
  else if byte < 16 then (32#64).extractLsb' (8 * (byte - 8)) 8
  else if byte < 24 then (16384#64).extractLsb' (8 * (byte - 16)) 8
  else (32#64).extractLsb' (8 * (byte - 24)) 8
private def premise (field : Word) (byte : Nat) : BitVec 8 :=
  if byte < 4 then (6661#32).extractLsb' (8 * byte) 8
  else if byte < 8 then 0
  else if byte < 16 then field.extractLsb' (8 * (byte - 8)) 8
  else 0
/-- The allowance budget `0x1000` at `frame + 0xa0` and the prior receipt `0x10` at `frame + 0xa8`. -/
def fuelWord (byte : Nat) : BitVec 8 :=
  if byte < 8 then (0x1000#64).extractLsb' (8 * byte) 8 else (0x10#64).extractLsb' (8 * (byte - 8)) 8
private noncomputable def cells (field : Word) : List (Nat × BitVec 8) :=
  (List.range 647).map (fun byte => (4096 + byte, BitVec.ofNat 8 (Lean.RArray.get image.data byte))) ++
  (List.range 32).map (fun byte => (8192 + byte,descriptor byte)) ++
  (List.range 24).map (fun byte => (12288 + byte,premise field byte)) ++
  [(16383,0x5a#8)] ++ [(16416,0xa5#8)] ++
  (List.range 8).map (fun byte => (32768 + byte,(0x9000#64).extractLsb' (8 * byte) 8)) ++
  (List.range 16).map (fun byte => (8352 + byte,fuelWord byte))
private def rangeKeys (base count : Nat) : List Nat := (List.range count).map (fun byte => base + byte)
private theorem range_nodup (base count : Nat) : (rangeKeys base count).Nodup := by
  apply List.Nodup.map (f := fun byte => base + byte)
  · intro left right same; dsimp only at same; omega
  · exact List.nodup_range
private theorem range_apart (left size right count : Nat) (apart : left + size ≤ right) :
    ∀ x ∈ rangeKeys left size, ∀ y ∈ rangeKeys right count, x ≠ y := by
  intro x hx y hy same
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
  have := List.mem_range.mp hi
  have := List.mem_range.mp hj
  omega
private theorem range_apart_below (left size right count : Nat) (apart : right + count ≤ left) :
    ∀ x ∈ rangeKeys left size, ∀ y ∈ rangeKeys right count, x ≠ y := by
  intro x hx y hy same
  exact range_apart right count left size apart y hy x hx same.symm
private theorem distinct (field : Word) : (cells field).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells field).map Prod.fst).Nodup := by
    simp only [cells,List.map_append,List.map_map,Function.comp_def]
    change (rangeKeys 4096 647 ++ rangeKeys 8192 32 ++ rangeKeys 12288 24 ++ rangeKeys 16383 1 ++ rangeKeys 16416 1 ++
      rangeKeys 32768 8 ++ rangeKeys 8352 16).Nodup
    simp only [List.nodup_append,range_nodup,true_and,List.mem_append,or_imp,forall_and]
    repeat' constructor
    all_goals first
      | exact range_apart _ _ _ _ (by decide)
      | exact range_apart_below _ _ _ _ (by decide)
  simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map,beq_eq_false_iff_ne] using keys
private noncomputable def before (field : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4245#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi (12288#64)
  let registers := registers.insert .rdx (16384#64)
  let registers := registers.insert .rsp (32768#64)
  let registers := registers.insert .rax (0#64)
  let registers := registers.insert .rbx (0x1000#64)
  let registers := registers.insert .rcx (0#64)
  let registers := registers.insert .rbp (0#64)
  let registers := registers.insert .r8 (0#64)
  let registers := registers.insert .r9 (0#64)
  let registers := registers.insert .r10 (0#64)
  let registers := registers.insert .r11 (0#64)
  let registers := registers.insert .r12 (0x1001#64)
  let registers := registers.insert .r13 (0x1002#64)
  let registers := registers.insert .r14 (0x1003#64)
  let registers := registers.insert .r15 (0x1004#64)
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells field),(),0,#[]⟩
private theorem cell (field : Word) (location : Nat) (byte : BitVec 8) (member : (location,byte) ∈ cells field) :
    (before field).mem.get? location = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct field) member

private theorem end_not_contains (field : Word) : ((cells field).map Prod.fst).contains 12320 = false := by
  have missing : 12320 ∉ (cells field).map Prod.fst := by
    simp only [cells,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil]
    intro member
    simp only [List.mem_append,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil] at member
    rcases member with ((((((hit | hit) | hit) | hit) | hit) | hit) | hit)
    all_goals
      rcases hit with ⟨index,within,same⟩
      omega
  simpa only [List.contains_eq_mem,decide_eq_false_iff_not] using missing

private theorem control_end_unmapped (field : Word) : (before field).mem.get? 12320 = none :=
  Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (l := cells field) (k := 12320) (end_not_contains field)

private theorem descriptor_cell (field : Word) (byte : Fin 32) :
    (before field).mem.get? (8192 + byte.val) = some (descriptor byte.val) := by
  apply cell
  simp only [cells,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨byte.val,List.mem_range.mpr byte.isLt,rfl⟩))))))
private theorem premise_cell (field : Word) (byte : Fin 24) :
    (before field).mem.get? (12288 + byte.val) = some (premise field byte.val) := by
  apply cell
  simp only [cells,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨byte.val,List.mem_range.mpr byte.isLt,rfl⟩)))))
private theorem premise_field (field : Word) (byte : Fin 8) :
    premise field (8 + byte.val) = field.extractLsb' (8 * byte.val) 8 := by
  unfold premise
  have bounded := byte.isLt
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
theorem positive_address (base offset : Nat) (within : base + offset < 2 ^ 47) :
    ((address (base : Int) offset).signExtend 52).toNat = base + offset := by
  let bits := (address (base : Int) offset).signExtend 52
  have signed : bits.toInt = ((base + offset : Nat) : Int) := by
    dsimp only [bits]
    rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 52),
      address_toInt (extent := offset) (base : Int) (by omega) (by exact_mod_cast within) offset (by omega)]
    simp
  have nonnegative : 0 ≤ bits.toInt := by rw [signed]; omega
  have unsigned := BitVec.toInt_eq_toNat_of_lt (BitVec.toInt_pos_iff.mp nonnegative)
  rw [signed] at unsigned
  exact_mod_cast unsigned.symm
private def controlOrigin (field : Word) : X86LegacyFetch.Basis (before field) where
  address := 4245#48
  opcodeAddress := 4246#48
  modrmAddress := 4247#48
  next := 4248#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]
private def controlLayout (output : Bool) : X86Bounds.Layout :=
  if output then X86P1StoreCapture.boundsLayout 0 else X86P1FieldLoadCapture.layout
private def controlBase (output : Bool) : Word := if output then 16384 else 12288
private def baseAddress (output : Bool) : BitVec 48 := if output then 8208 else 8192
private def lengthAddress (output : Bool) : BitVec 48 := if output then 8216 else 8200
private theorem base_descriptor : ∀ output : Bool, ∀ byte : Fin 8,
    descriptor ((if output then 16 else 0) + byte.val) = (controlBase output).extractLsb' (8 * byte.val) 8 := by decide
private theorem length_descriptor : ∀ output : Bool, ∀ byte : Fin 8,
    descriptor ((if output then 24 else 8) + byte.val) = (32#64).extractLsb' (8 * byte.val) 8 := by decide
private def controlFacts (field : Word) (output : Bool) : X86Bounds.Facts (controlLayout output) (before field) where
  frame := 8192#64
  base := controlBase output
  pointer := controlBase output
  length := 32#64
  baseAddress := baseAddress output
  lengthAddress := lengthAddress output
  controls := controls
  visible := visible
  flags := 0x200#32
  frameKnown := by simp [lookup,key,before,Std.ExtDHashMap.get?_insert]; rfl
  pointerKnown := by cases output <;> simp [controlLayout,X86P1StoreCapture.boundsLayout,X86P1FieldLoadCapture.layout,controlBase,lookup,key,before,Std.ExtDHashMap.get?_insert] <;> rfl
  baseEffective := by cases output <;> decide
  lengthEffective := by cases output <;> decide
  baseUpper := by cases output <;> decide
  lengthUpper := by cases output <;> decide
  baseAligned := by cases output <;> decide
  lengthAligned := by cases output <;> decide
  controlKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  baseBytes := by
    intro byte within
    have point : ((address (baseAddress output).toInt byte).signExtend 52).toNat = 8192 + ((if output then 16 else 0) + byte) := by
      cases output
      · change ((address 8192 byte).signExtend 52).toNat = 8192 + (0 + byte)
        have h := positive_address 8192 byte (by omega)
        change ((address 8192 byte).signExtend 52).toNat = 8192 + byte at h
        simpa only [Nat.zero_add] using h
      · change ((address 8208 byte).signExtend 52).toNat = 8192 + (16 + byte)
        have h := positive_address 8208 byte (by omega)
        change ((address 8208 byte).signExtend 52).toNat = 8208 + byte at h
        omega
    rw [point]
    exact (descriptor_cell field ⟨(if output then 16 else 0) + byte,by cases output <;> simp <;> omega⟩).trans
      (congrArg some (base_descriptor output ⟨byte,within⟩))
  lengthBytes := by
    intro byte within
    have point : ((address (lengthAddress output).toInt byte).signExtend 52).toNat = 8192 + ((if output then 24 else 8) + byte) := by
      cases output
      · change ((address 8200 byte).signExtend 52).toNat = 8192 + (8 + byte)
        have h := positive_address 8200 byte (by omega)
        change ((address 8200 byte).signExtend 52).toNat = 8200 + byte at h
        omega
      · change ((address 8216 byte).signExtend 52).toNat = 8192 + (24 + byte)
        have h := positive_address 8216 byte (by omega)
        change ((address 8216 byte).signExtend 52).toNat = 8216 + byte at h
        omega
    rw [point]
    exact (descriptor_cell field ⟨(if output then 24 else 8) + byte,by cases output <;> simp <;> omega⟩).trans
      (congrArg some (length_descriptor output ⟨byte,within⟩))
private theorem byte_bounds : (List.range 647).all (fun byte => decide (Lean.RArray.get image.data byte ≤ 255)) = true := by kernel_reflexivity
private theorem loaded (field : Word) : X86P1LoadCapture.Loaded image (before field) 4096 := by
  intro byte within
  have bounded : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
  have member : (4096 + byte,BitVec.ofNat 8 (Lean.RArray.get image.data byte)) ∈ cells field := by
    simp only [cells,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨byte,List.mem_range.mpr bounded,rfl⟩))))))
  have point := positive_address 4096 byte (by omega)
  change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
  rw [point,cell field _ _ member]
  simp only [P1Capture.Program.view,if_pos within]
  rw [show Nat.ble (Lean.RArray.get image.data byte) 255 = true from Nat.ble_eq.mpr
    (of_decide_eq_true (List.all_eq_true.mp byte_bounds byte (List.mem_range.mpr bounded)))]
  rfl
private theorem outside (location : Nat) (below : location < 16384) : location ∉ outputWrites (16384#48) := by
  intro member
  obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have bounded : byte < 32 := List.mem_range.mp within
  have points : ∀ i : Fin 32, X86WriteWords.physicalAddress (16384#48) i.val = 16384 + i.val := by decide
  rw [← same,points ⟨byte,bounded⟩] at below
  omega
private def controlInput (field : Word) : Inputs (before field) (controlOrigin field) where
  base := 4096
  lower := by decide
  upper := by decide
  placed := by change (4245#48).toInt = 4096 + 149; decide
  loaded := loaded field
  outputFacts := controlFacts field true
  premiseFacts := controlFacts field false
  output := 16384#48
  outputUpper := by decide
  outputEffective := by change (16384#64) = (16384#48).signExtend 64; decide
  outputAligned := by decide
  outputFits := by change (16384#64 - (16384#64)).toNat + 32 ≤ (32#64).toNat; decide
  field := field
  fieldAddress := 12296#48
  fieldUpper := by decide
  fieldEffective := by change (12288#64) + (8#32).signExtend 64 = (12296#48).signExtend 64; decide
  fieldAligned := by decide
  fieldBytes := by
    intro byte within
    rw [show X86WriteWords.physicalAddress (12296#48) byte = 12296 + byte from positive_address 12296 byte (by omega)]
    have got := premise_cell field ⟨8 + byte,by omega⟩
    rw [premise_field field ⟨byte,within⟩] at got
    rw [show 12288 + (8 + byte) = 12296 + byte by omega] at got
    exact got
  premiseFits := by change (12288#64 - (12288#64)).toNat + 16 ≤ (32#64).toNat; decide
  codeApart := by
    intro byte within
    have bounded : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
    have point := positive_address 4096 byte (by omega)
    change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
    rw [point]
    exact outside _ (by omega)
  outputBaseApart := by
    intro byte within
    change X86WriteWords.physicalAddress (8208#48) byte ∉ outputWrites (16384#48)
    rw [show X86WriteWords.physicalAddress (8208#48) byte = 8208 + byte from positive_address 8208 byte (by omega)]
    exact outside _ (by omega)
  outputLengthApart := by
    intro byte within
    change X86WriteWords.physicalAddress (8216#48) byte ∉ outputWrites (16384#48)
    rw [show X86WriteWords.physicalAddress (8216#48) byte = 8216 + byte from positive_address 8216 byte (by omega)]
    exact outside _ (by omega)
  premiseBaseApart := by
    intro byte within
    change X86WriteWords.physicalAddress (8192#48) byte ∉ outputWrites (16384#48)
    rw [show X86WriteWords.physicalAddress (8192#48) byte = 8192 + byte from positive_address 8192 byte (by omega)]
    exact outside _ (by omega)
  premiseLengthApart := by
    intro byte within
    change X86WriteWords.physicalAddress (8200#48) byte ∉ outputWrites (16384#48)
    rw [show X86WriteWords.physicalAddress (8200#48) byte = 8200 + byte from positive_address 8200 byte (by omega)]
    exact outside _ (by omega)
  fieldApart := by
    intro byte within
    rw [show X86WriteWords.physicalAddress (12296#48) byte = 12296 + byte from positive_address 12296 byte (by omega)]
    exact outside _ (by omega)

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) (field : Word) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 62).run (before field) = .ok () after ∧
      Prefix after (16384#48) field 32 ∧ after.regs.get? .rsp = some (32768#64) ∧
      after.mem.get? 16383 = some (0x5a#8) ∧ after.mem.get? 16416 = some (0xa5#8) := by
  obtain ⟨after,_,run,frame,_,_,bytes,_⟩ := executes other extra vector (before field) (controlOrigin field) (controlInput field)
  refine ⟨after,run,bytes,(frame.registers .rsp (by decide)).trans (by simp [before,Std.ExtDHashMap.get?_insert]),?_,?_⟩
  · rw [frame.memory 16383 (by change 16383 ∉ outputWrites (16384#48); decide)]
    apply cell
    simp only [cells,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr True.intro)))
  · rw [frame.memory 16416 (by change 16416 ∉ outputWrites (16384#48); decide)]
    apply cell
    simp only [cells,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr True.intro))

theorem high_word_retained : encoded (0x100000000#64) 12 = (1#8) := by kernel_reflexivity
theorem cannot_truncate_high_word (state : State) (output : BitVec 48) (correct : Prefix state output (0x100000000#64) 32) :
    ¬ Prefix state output 0 32 := by
  intro truncated
  have full := correct 12 (by decide)
  have lost := truncated 12 (by decide)
  rw [full] at lost
  have different : encoded (0x100000000#64) 12 ≠ encoded 0 12 := by decide
  exact different (Option.some.inj lost)

private def controlReceipt (field : Word) : X86FailureHandler.FrameFacts (before field) where
  frame := 8192#64
  statusAddress := 8336#48
  resultAddress := 8344#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := visible
  controls := controls
  flags := 0x200#32
  frameKnown := by simp [lookup,key,before,Std.ExtDHashMap.get?_insert]; rfl
  controlsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  statusOutside := by
    intro byte within
    exact (show ∀ i : Fin 8, X86WriteWords.physicalAddress (8336#48) i.val ∉
      X86WriteWords.written (8344#48) (List.range 8) from by decide) ⟨byte,within⟩

private theorem receipt_bounds (field : Word) (location : Nat) (member : location ∈ receiptWrites (controlReceipt field)) :
    8336 ≤ location ∧ location < 8352 := by
  rcases Finset.mem_union.mp member with left | right
  · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp left)
    have bounded : byte < 8 := List.mem_range.mp within
    have points : ∀ i : Fin 8, X86WriteWords.physicalAddress (8336#48) i.val = 8336 + i.val := by decide
    change X86WriteWords.physicalAddress (8336#48) byte = location at same
    rw [points ⟨byte,bounded⟩] at same
    omega
  · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp right)
    have bounded : byte < 8 := List.mem_range.mp within
    have points : ∀ i : Fin 8, X86WriteWords.physicalAddress (8344#48) i.val = 8344 + i.val := by decide
    change X86WriteWords.physicalAddress (8344#48) byte = location at same
    rw [points ⟨byte,bounded⟩] at same
    omega

theorem control_completes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) (field : Word) :
    letI : OtherOpcodeHandlers := completeHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 66).run (before field) = .ok () after ∧
      Prefix after (16384#48) field 32 ∧ lookup after 0 = some (1#64) ∧
      after.regs.get? .rsp = some (32768#64) ∧ after.mem.get? 8336 = some (1#8) ∧ after.mem.get? 8344 = some (1#8) ∧
      after.mem.get? 16383 = some (0x5a#8) ∧ after.mem.get? 16416 = some (0xa5#8) := by
  have codeApart : ∀ byte < image.size, ((address 4096 byte).signExtend 52).toNat ∉ receiptWrites (controlReceipt field) := by
    intro byte within member
    have bounded : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
    have bounds := receipt_bounds field _ member
    have point := positive_address 4096 byte (by omega)
    change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
    rw [point] at bounds
    omega
  have outputApart : ∀ byte < 32, X86WriteWords.physicalAddress (16384#48) byte ∉ receiptWrites (controlReceipt field) := by
    intro byte within member
    have bounds := receipt_bounds field _ member
    have points : ∀ i : Fin 32, X86WriteWords.physicalAddress (16384#48) i.val = 16384 + i.val := by decide
    rw [points ⟨byte,within⟩] at bounds
    omega
  obtain ⟨after,_,run,frame,_,rax,_,bytes,status,result,_⟩ := completes other extra vector
    (before field) (controlOrigin field) (controlInput field) (controlReceipt field) codeApart outputApart
  refine ⟨after,run,bytes,rax,(frame.registers .rsp (by decide)).trans (by simp [before,Std.ExtDHashMap.get?_insert]),
    status 0 (by decide),result 0 (by decide),?_,?_⟩
  · have apart : 16383 ∉ outputWrites (16384#48) ∪ receiptWrites (controlReceipt field) := by
      intro member
      rcases Finset.mem_union.mp member with output | receipt
      · exact outside 16383 (by decide) output
      · have := receipt_bounds field 16383 receipt; omega
    rw [frame.memory 16383 apart]
    apply cell
    simp only [cells,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr True.intro)))
  · have apart : 16416 ∉ outputWrites (16384#48) ∪ receiptWrites (controlReceipt field) := by
      intro member
      rcases Finset.mem_union.mp member with output | receipt
      · obtain ⟨byte,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp output)
        have bounded : byte < 32 := List.mem_range.mp within
        have points : ∀ i : Fin 32, X86WriteWords.physicalAddress (16384#48) i.val = 16384 + i.val := by decide
        rw [points ⟨byte,bounded⟩] at same
        omega
      · have := receipt_bounds field 16416 receipt; omega
    rw [frame.memory 16416 apart]
    apply cell
    simp only [cells,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr True.intro))

theorem changed_completion_rejected (field : Word) :
    ¬ codeLoaded (X86WriteWords.putByte (before field) 4593 (0#8)) 4592 completionCode := by
  intro loaded
  have byte := loaded 1 1 (by kernel_reflexivity)
  change (X86WriteWords.putByte (before field) 4593 (0#8)).mem.get? 4593 = some (1#8) at byte
  simp [X86WriteWords.putByte] at byte

structure Fixture (field : Word) where
  state : State
  endUnmapped : state.mem.get? 12320 = none
  origin : X86LegacyFetch.Basis state
  data : DataFacts state
  receipt : X86FailureHandler.FrameFacts state
  baseValue : data.base = 4096
  outputValue : data.output = (16384#48)
  fieldValue : data.field = field
  outputBaseValue : data.outputFacts.baseAddress = (8208#48)
  outputLengthValue : data.outputFacts.lengthAddress = (8216#48)
  premiseBaseValue : data.premiseFacts.baseAddress = (8192#48)
  premiseLengthValue : data.premiseFacts.lengthAddress = (8200#48)
  fieldAddressValue : data.fieldAddress = (12296#48)
  statusAddressValue : receipt.statusAddress = (8336#48)
  resultAddressValue : receipt.resultAddress = (8344#48)
  tag : X86P1LoadBounds.Readable state data.premiseFacts.pointer (6661#32)
  zero : X86P1QwordBounds.Readable state data.premiseFacts.pointer (0#64)
  tagAddress : tag.dataAddress = (12288#48)
  zeroAddress : zero.dataAddress = (12304#48)
  fits : (data.premiseFacts.pointer - data.premiseFacts.base).toNat + 24 ≤ data.premiseFacts.length.toNat
  oldKnown : lookup state 11 = some (0#64)
  stackKnown : lookup state 4 = some (32768#64)
  wordsKnown : ∀ index : Fin 16, ∃ value, lookup state index = some value
  returnBytes : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress (32768#48) byte) =
    some ((0x9000#64).extractLsb' (8 * byte) 8)
  budgetBytes : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress (8352#48) byte) =
    some ((0x1000#64).extractLsb' (8 * byte) 8)
  receiptBytes : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress (8360#48) byte) =
    some ((0x10#64).extractLsb' (8 * byte) 8)
  codeApart : ∀ byte < image.size, ((address data.base byte).signExtend 52).toNat ∉ receiptWrites receipt
  outputApart : ∀ byte < 32, X86WriteWords.physicalAddress data.output byte ∉ receiptWrites receipt

private theorem premise_zero (field : Word) (byte : Fin 8) :
    premise field (16 + byte.val) = (0#64).extractLsb' (8 * byte.val) 8 := by
  unfold premise
  have bound := byte.isLt
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  simp

noncomputable def fixture (field : Word) : Fixture field where
  state := before field
  endUnmapped := control_end_unmapped field
  origin := controlOrigin field
  data := (controlInput field).toDataFacts
  receipt := controlReceipt field
  baseValue := rfl
  outputValue := rfl
  fieldValue := rfl
  outputBaseValue := rfl
  outputLengthValue := rfl
  premiseBaseValue := rfl
  premiseLengthValue := rfl
  fieldAddressValue := rfl
  statusAddressValue := rfl
  resultAddressValue := rfl
  tag := {
    dataAddress := 12288#48
    effective := by change (12288#64) = (12288#48).signExtend 64; decide
    upper := by decide
    aligned := by decide
    bytes := by
      intro byte within
      change (before field).mem.get? (X86WriteWords.physicalAddress (12288#48) byte) = some ((6661#32).extractLsb' (8 * byte) 8)
      rw [show X86WriteWords.physicalAddress (12288#48) byte = 12288 + byte from positive_address 12288 byte (by omega)]
      have got := premise_cell field ⟨byte,by omega⟩
      have tagByte : premise field byte = (6661#32).extractLsb' (8 * byte) 8 := by unfold premise; rw [if_pos within]
      exact got.trans (congrArg some tagByte) }
  zero := {
    dataAddress := 12304#48
    effective := by change (12288#64) + (16#32).signExtend 64 = (12304#48).signExtend 64; decide
    upper := by decide
    aligned := by decide
    bytes := by
      intro byte within
      change (before field).mem.get? (X86WriteWords.physicalAddress (12304#48) byte) = some ((0#64).extractLsb' (8 * byte) 8)
      rw [show X86WriteWords.physicalAddress (12304#48) byte = 12304 + byte from positive_address 12304 byte (by omega)]
      have got := premise_cell field ⟨16 + byte,by omega⟩
      rw [premise_zero field ⟨byte,within⟩,show 12288 + (16 + byte) = 12304 + byte by omega] at got
      exact got }
  tagAddress := rfl
  zeroAddress := rfl
  fits := by change (12288#64 - (12288#64)).toNat + 24 ≤ (32#64).toNat; decide
  oldKnown := by simp [lookup,key,before,Std.ExtDHashMap.get?_insert]; rfl
  stackKnown := by simp [lookup,key,before,Std.ExtDHashMap.get?_insert]; rfl
  wordsKnown := by intro index; fin_cases index <;> simp [lookup,key,before,Std.ExtDHashMap.get?_insert]
  returnBytes := by
    intro byte within
    rw [show X86WriteWords.physicalAddress (32768#48) byte = 32768 + byte from positive_address 32768 byte (by omega)]
    apply cell
    simp only [cells,List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩))
  budgetBytes := by
    intro byte within
    rw [show X86WriteWords.physicalAddress (8352#48) byte = 8352 + byte from positive_address 8352 byte (by omega)]
    apply cell
    simp only [cells,List.mem_append]
    refine Or.inr (List.mem_map.mpr ⟨byte,List.mem_range.mpr (by omega),?_⟩)
    simp only [fuelWord,if_pos within]
  receiptBytes := by
    intro byte within
    rw [show X86WriteWords.physicalAddress (8360#48) byte = 8352 + (8 + byte) from by
      have point : X86WriteWords.physicalAddress (8360#48) byte = 8360 + byte := positive_address 8360 byte (by omega)
      rw [point]; omega]
    apply cell
    simp only [cells,List.mem_append]
    refine Or.inr (List.mem_map.mpr ⟨8 + byte,List.mem_range.mpr (by omega),?_⟩)
    simp only [fuelWord,if_neg (show ¬ 8 + byte < 8 by omega),Nat.add_sub_cancel_left]
  codeApart := by
    intro byte within member
    have bound : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
    have limits := receipt_bounds field _ member
    change 8336 ≤ ((address 4096 byte).signExtend 52).toNat ∧ ((address 4096 byte).signExtend 52).toNat < 8352 at limits
    have point := positive_address 4096 byte (by omega)
    change ((address 4096 byte).signExtend 52).toNat = 4096 + byte at point
    rw [point] at limits
    omega
  outputApart := by
    intro byte within member
    have limits := receipt_bounds field _ member
    change 8336 ≤ X86WriteWords.physicalAddress (16384#48) byte ∧ X86WriteWords.physicalAddress (16384#48) byte < 8352 at limits
    have points : ∀ i : Fin 32, X86WriteWords.physicalAddress (16384#48) i.val = 16384 + i.val := by decide
    rw [points ⟨byte,within⟩] at limits
    omega
theorem fixture_end_unmapped (field : Word) : (fixture field).state.mem.get? 12320 = none := by
  exact (fixture field).endUnmapped

def fixturePremiseByte (field : Word) (byte : Fin 24) : BitVec 8 := premise field byte.val

theorem fixture_premise_byte (field : Word) (byte : Fin 24) :
    (fixture field).state.mem.get? (12288 + byte.val) = some (fixturePremiseByte field byte) :=
  premise_cell field byte

private theorem buffers_not_contains (field : Word) (location : Nat)
    (range : (12312 ≤ location ∧ location < 12320) ∨ (16384 ≤ location ∧ location < 16416)) :
    ((cells field).map Prod.fst).contains location = false := by
  have missing : location ∉ (cells field).map Prod.fst := by
    simp only [cells,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil]
    intro member
    simp only [List.mem_append,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil] at member
    rcases member with ((((((hit | hit) | hit) | hit) | hit) | hit) | hit)
    all_goals
      rcases hit with ⟨index,within,same⟩
      rcases range with range | range <;> omega
    all_goals contradiction
  simpa only [List.contains_eq_mem,decide_eq_false_iff_not] using missing

theorem fixture_premise_suffix_unobserved (field : Word) (byte : Fin 8) :
    (fixture field).state.mem.get? (12312 + byte.val) = none :=
  Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (l := cells field) (k := 12312 + byte.val)
    (buffers_not_contains field _ (Or.inl ⟨by omega,by have := byte.isLt; omega⟩))

theorem fixture_output_unobserved (field : Word) (byte : Fin 32) :
    (fixture field).state.mem.get? (16384 + byte.val) = none :=
  Std.ExtHashMap.getElem?_ofList_of_contains_eq_false (l := cells field) (k := 16384 + byte.val)
    (buffers_not_contains field _ (Or.inr ⟨by omega,by have := byte.isLt; omega⟩))

end Controls

#print axioms immediate_executes
#print axioms store_writes_subset
#print axioms output_alignment
#print axioms stage_executes
#print axioms executes
#print axioms completes
#print axioms Controls.control
#print axioms Controls.cannot_truncate_high_word
#print axioms Controls.control_completes
#print axioms Controls.changed_completion_rejected
#print axioms Controls.fixture
#print axioms Controls.fixture_end_unmapped
end Mettapedia.Machines.TIsa.X86P1OutputCapture
