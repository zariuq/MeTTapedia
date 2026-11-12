import Mettapedia.Machines.TIsa.X86FrameIncrement
import Mettapedia.Machines.TIsa.X86EscapeFetch
import Mettapedia.Machines.TIsa.Fuel

/-!
# Complete fetched execution of the native fuel prefix

The fixed forty-byte prefix loads the budget, tests its zero sentinel,
compares the used count when bounded, and either branches to exhaustion or
increments the frame counter. A single linked dispatcher supplies the actual
Sail handlers throughout. All instruction inputs and loaded bytes are derived
from the initial state and preserved frames.

The proof covers four, six or seven original fetch/decode/execute calls,
including unlimited-counter wraparound and exact memory preservation on
exhaustion. Determinism reflects every successful run of that length into
the same result contract. Native image placement, the exhaustion handler,
source admission, ABI and complete emitter composition remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86FuelPrefix
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86TwoByteDispatch

local instance : MemoryPrimitives := X86Memory.ordinary

@[instance_reducible] def baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameIncrement.linkedHandlers (X86FrameLoad.linkedHandlers (X86Arithmetic.linkedHandlers other))

noncomputable abbrev linkedHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (baseHandlers other) extra

theorem arithmetic_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Arithmetic.linkedHandlers (linkedHandlers other extra) = linkedHandlers other extra := by rfl

theorem load_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FrameLoad.linkedHandlers (linkedHandlers other extra) = linkedHandlers other extra := by rfl

theorem increment_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FrameIncrement.linkedHandlers (linkedHandlers other extra) = linkedHandlers other extra := by rfl

def expected (displacement : BitVec 32) : List Nat :=
  [0x4c, 0x8b, 0xb7, 0xa0, 0, 0, 0, 0x4d, 0x85, 0xf6, 0x0f, 0x84, 16, 0, 0, 0,
    0x4c, 0x8b, 0xbf, 0xa8, 0, 0, 0, 0x4d, 0x39, 0xf7, 0x0f, 0x83,
    (displacement.extractLsb' 0 8).toNat, (displacement.extractLsb' 8 8).toNat,
    (displacement.extractLsb' 16 8).toNat, (displacement.extractLsb' 24 8).toNat,
    0x48, 0x83, 0x87, 0xa8, 0, 0, 0, 1]

theorem expected_length (displacement : BitVec 32) : (expected displacement).length = 40 := rfl

theorem data_status (state : State) (flags : BitVec 32) (next : BitVec 48) :
    DataFrame state (X86Move.putPointer (X86Flags.putFlags state flags) next) :=
  data_trans (data_flags state flags) (data_pointer _ next)

theorem pointer_rip (state : State) (next : BitVec 48) :
    (X86Move.putPointer state next).regs.get? .rip = some (next.signExtend 64) := by
  simp [X86Move.putPointer]

structure FrameFacts (state : State) where
  frame : Word
  budget : Word
  used : Word
  budgetAddress : BitVec 48
  usedAddress : BitVec 48
  budgetUpper : budgetAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  usedUpper : usedAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  budgetEffective : frame + (0xa0#32).signExtend 64 = budgetAddress.signExtend 64
  usedEffective : frame + (0xa8#32).signExtend 64 = usedAddress.signExtend 64
  budgetAligned : budgetAddress &&& (7#48) = (0#48)
  usedAligned : usedAddress &&& (7#48) = (0#48)
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  frameKnown : lookup state 7 = some frame
  controlsKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  budgetPresent : ∀ index < 8,
    state.mem.get? ((X86Execution.address budgetAddress.toInt index).signExtend 52).toNat =
      some (budget.extractLsb' (8 * index) 8)
  usedPresent : ∀ index < 8,
    state.mem.get? ((X86Execution.address usedAddress.toInt index).signExtend 52).toNat =
      some (used.extractLsb' (8 * index) 8)

structure Inputs (state : State) extends X86LegacyFetch.Basis state, FrameFacts state where
  displacement : BitVec 32
  exhausted : BitVec 48
  upper : address.toInt + 40 < (2 ^ 47 : Int)
  jump : exhausted.toInt = address.toInt + 32 + displacement.toInt
  loaded : codeLoaded state address.toInt (expected displacement)

theorem offset_int {state : State} (input : Inputs state) (offset : Nat) (within : offset ≤ 40) :
    (address input.address.toInt offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

def loadResult (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) : State :=
  X86Move.putPointer (put state destination value) next

theorem loadResult_frame (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) :
    RegisterFrame {key destination, .rip} state (loadResult state destination value next) := by
  simpa only [loadResult, Finset.singleton_union] using
    (put_frame state destination value).trans (pointer_frame (put state destination value) next)

theorem loadResult_data (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) :
    DataFrame state (loadResult state destination value next) :=
  data_trans (data_put state destination value) (data_pointer _ next)

theorem loadResult_rip (state : State) (destination : Fin 16) (value : Word) (next : BitVec 48) :
    (loadResult state destination value next).regs.get? .rip = some (next.signExtend 64) :=
  pointer_rip _ _

theorem load_at (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (before current : State) (input : Inputs before) (frame : DataFrame before current)
    (offset : Nat) (within : offset + 7 ≤ 40) (destination : Fin 16)
    (value : Word) (dataAddress : BitVec 48) (flags : BitVec 32) (displacement : BitVec 32)
    (currentRip : current.regs.get? .rip = some ((address input.address.toInt offset).signExtend 64))
    (frameKnown : lookup current 7 = some input.frame)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (effective : input.frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (dataPresent : ∀ index < 8,
      before.mem.get? ((address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8))
    (prefixByte : (expected input.displacement)[offset]? = some (X86FrameLoad.frameRex destination).toNat)
    (opcodeByte : (expected input.displacement)[offset + 1]? = some 0x8b)
    (modrmByte : (expected input.displacement)[offset + 2]? = some (X86FrameLoad.frameModRM destination).toNat)
    (displacementBytes : ∀ index < 4, (expected input.displacement)[offset + 3 + index]? =
      some (displacement.extractLsb' (8 * index) 8).toNat) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    Step current (loadResult current destination value (address input.address.toInt (offset + 7))) := by
  let site := rebase before current input.toBasis frame (extent := 40) input.upper offset
    (by omega) currentRip
  have result := X86FrameLoad.fetched_frame (linkedHandlers other extra) vector current destination site
    (address input.address.toInt (offset + 7)) dataAddress input.visible input.controls input.frame value flags
    displacement
    (by dsimp only [site, rebase]; rw [offset_int input (offset + 3) (by omega), offset_int input (offset + 7) within]; omega)
    dataUpper frameKnown
    ((frame.registers .ctrs (by decide)).trans input.controlsKnown) flagsKnown
    ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet) effective aligned
    (by simpa only [site, rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      frame.code_preserved _ _ input.loaded offset _ prefixByte)
    (by simpa only [site, rebase] using frame.code_preserved _ _ input.loaded (offset + 1) _ opcodeByte)
    (by simpa only [site, rebase, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      frame.code_preserved _ _ input.loaded (offset + 2) _ modrmByte)
    (by
      intro index less
      have baseIndex : address (address input.address.toInt (offset + 3)).toInt index =
          address input.address.toInt (offset + 3 + index) := by
        rw [offset_int input (offset + 3) (by omega)]
        simp only [address, Int.add_assoc, Int.natCast_add]
      dsimp only [site, rebase]
      rw [baseIndex]
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        frame.code_preserved _ _ input.loaded (offset + 3 + index) _ (displacementBytes index less))
    (by intro index less; rw [frame.memory]; exact dataPresent index less)
  simpa only [load_installed, Step, loadResult] using result

theorem nested_address {state : State} (input : Inputs state) (offset index : Nat) (within : offset ≤ 40) :
    address (address input.address.toInt offset).toInt index = address input.address.toInt (offset + index) := by
  rw [offset_int input offset within]
  simp only [address, Int.natCast_add, Int.add_assoc]

theorem branch_at (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (before current : State) (input : Inputs before) (frame : DataFrame before current)
    (offset : Nat) (within : offset + 6 ≤ 40) (condition : X86BranchCondition.Condition)
    (flags : BitVec 32) (displacement : BitVec 32) (target : BitVec 48)
    (currentRip : current.regs.get? .rip = some ((address input.address.toInt offset).signExtend 64))
    (flagsKnown : current.regs.get? .rflags = some flags)
    (jump : target.toInt = (address input.address.toInt (offset + 6)).toInt + displacement.toInt)
    (escapeByte : (expected input.displacement)[offset]? = some 15)
    (opcodeByte : (expected input.displacement)[offset + 1]? = some (X86BranchCondition.opcode condition).toNat)
    (displacementBytes : ∀ index < 4, (expected input.displacement)[offset + 2 + index]? =
      some (displacement.extractLsb' (8 * index) 8).toNat) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    Step current (X86Move.putPointer current
      (if X86BranchCondition.value condition flags then target else address input.address.toInt (offset + 6))) := by
  apply X86EscapeFetch.fetched_branch (baseHandlers other) extra vector condition current
    (address input.address.toInt offset) (address input.address.toInt (offset + 1))
    (address input.address.toInt (offset + 2)) (address input.address.toInt (offset + 6))
    target input.control input.attributes flags displacement
  · rw [offset_int input offset (by omega), offset_int input (offset + 1) (by omega)]
    omega
  · rw [offset_int input (offset + 1) (by omega), offset_int input (offset + 2) (by omega)]
    omega
  · rw [offset_int input (offset + 2) (by omega), offset_int input (offset + 6) within]
    omega
  · exact jump
  · exact (frame.registers .ms_reg (by decide)).trans input.status
  · exact (frame.registers .fault_reg (by decide)).trans input.fault
  · exact (frame.registers .msrs (by decide)).trans input.msrs
  · exact (frame.registers .seg_hidden_attrs (by decide)).trans input.segments
  · exact input.longMode
  · exact input.codeMode
  · exact (frame.registers .app_view (by decide)).trans input.application
  · exact currentRip
  · exact flagsKnown
  · exact (frame.registers .log_register_writes (by decide)).trans input.quiet
  · exact frame.code_preserved _ _ input.loaded offset _ escapeByte
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      frame.code_preserved _ _ input.loaded (offset + 1) _ opcodeByte
  · intro index less
    rw [nested_address input (offset + 2) index (by omega)]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      frame.code_preserved _ _ input.loaded (offset + 2 + index) _ (displacementBytes index less)

theorem zero_word (word : Word) : decide (word.toNat = 0) = (word == (0#64)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · exact fun h => BitVec.eq_of_toNat_eq h
  · rintro rfl
    rfl

def budgetLoaded (state : State) (input : Inputs state) : State :=
  loadResult state 14 input.budget (address input.address.toInt 7)

def budgetTested (state : State) (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer (X86Flags.putFlags (budgetLoaded state input)
    (X86LogicalFlags.merged input.flags output (0#1))) (address input.address.toInt 10)

def frontResult (state : State) (input : Inputs state) (output : BitVec 32) : State :=
  X86Move.putPointer (budgetTested state input output)
    (address input.address.toInt (if input.budget == (0#64) then 32 else 16))

theorem budgetLoaded_data (state : State) (input : Inputs state) : DataFrame state (budgetLoaded state input) :=
  loadResult_data state 14 input.budget _

theorem budgetTested_data (state : State) (input : Inputs state) (output : BitVec 32) :
    DataFrame state (budgetTested state input output) :=
  data_trans (budgetLoaded_data state input) (data_status _ _ _)

theorem frontResult_data (state : State) (input : Inputs state) (output : BitVec 32) :
    DataFrame state (frontResult state input output) :=
  data_trans (budgetTested_data state input output) (data_pointer _ _)

theorem tested_flags (state : State) (input : Inputs state) (output : BitVec 32) :
    (budgetTested state input output).regs.get? .rflags =
      some (X86LogicalFlags.merged input.flags output (0#1)) := by
  simp [budgetTested, X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]

theorem front_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      Step state (budgetLoaded state input) ∧
      Step (budgetLoaded state input) (budgetTested state input output) ∧
      Step (budgetTested state input output) (frontResult state input output) := by
  let : OtherOpcodeHandlers := linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  have first : Step state (budgetLoaded state input) :=
    load_at other extra vector state state input (RegisterFrame.refl dataRegisters state) 0 (by decide)
      14 input.budget input.budgetAddress input.flags (0xa0#32)
      (by simpa [address] using input.rip) input.frameKnown input.flagsKnown input.budgetUpper
      input.budgetEffective input.budgetAligned input.budgetPresent
      (by change some 76 = some (X86FrameLoad.frameRex 14).toNat; decide)
      rfl (by change some 183 = some (X86FrameLoad.frameModRM 14).toNat; decide)
      (by intro index less; interval_cases index <;> rfl)
  have loadedFlags : (budgetLoaded state input).regs.get? .rflags = some input.flags :=
    ((loadResult_frame state 14 input.budget _).registers .rflags (by decide)).trans input.flagsKnown
  have budgetKnown : lookup (budgetLoaded state input) 14 = some input.budget := by
    simp only [budgetLoaded, loadResult, X86Move.lookup_putPointer, lookup_put_same]
  let window := windowAt state (budgetLoaded state input) input.toBasis (budgetLoaded_data state input)
    (extent := 40) input.upper 7 (by decide) (loadResult_rip _ _ _ _)
    (expected input.displacement) ((budgetLoaded_data state input).code_preserved _ _ input.loaded)
    14 14 (0x85#8)
    (by change some 77 = some (X86RegisterEncoding.rex true 14 14).toNat; decide)
    rfl (by change some 246 = some (X86RegisterEncoding.modRM 14 14).toNat; decide)
  have test := X86Comparison.fetched_test64 (linkedHandlers other extra) vector (budgetLoaded state input)
    14 14 window input.budget input.budget input.flags budgetKnown budgetKnown loadedFlags
    (((budgetLoaded_data state input).registers .log_register_writes (by decide)).trans input.quiet)
  rw [arithmetic_installed] at test
  obtain ⟨output, tested, _, zero⟩ := test
  have second : Step (budgetLoaded state input) (budgetTested state input output) := tested
  have sense : X86BranchCondition.value .zero (X86LogicalFlags.merged input.flags output (0#1)) =
      (input.budget == (0#64)) := by
    simp only [X86BranchCondition.value, X86LogicalFlags.merged_zero, zero, BitVec.and_self,
      X86BranchCondition.zero_sense, zero_word]
  have third := branch_at other extra vector state (budgetTested state input output) input
    (budgetTested_data state input output) 10 (by decide) .zero
    (X86LogicalFlags.merged input.flags output (0#1)) (16#32) (address input.address.toInt 32)
    (pointer_rip _ _) (tested_flags state input output)
    (by rw [offset_int input 32 (by decide), offset_int input 16 (by decide)]; change _ + 32 = _ + 16 + (16 : Int); omega)
    rfl rfl (by intro index less; interval_cases index <;> rfl)
  rw [sense] at third
  refine ⟨output, first, second, ?_⟩
  simpa only [frontResult, apply_ite] using third

theorem frontResult_frame (state : State) (input : Inputs state) (output : BitVec 32) :
    RegisterFrame {.r14, .rflags, .rip} state (frontResult state input output) := by
  have first := loadResult_frame state 14 input.budget (address input.address.toInt 7)
  have second := X86Comparison.status_frame (budgetLoaded state input)
    (X86LogicalFlags.merged input.flags output (0#1)) (address input.address.toInt 10)
  have third := pointer_frame (budgetTested state input output)
    (address input.address.toInt (if input.budget == (0#64) then 32 else 16))
  apply (first.trans (second.trans third)).mono
  intro register member
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, key] at member ⊢
  tauto

theorem frontResult_rip (state : State) (input : Inputs state) (output : BitVec 32) :
    (frontResult state input output).regs.get? .rip =
      some ((address input.address.toInt (if input.budget == (0#64) then 32 else 16)).signExtend 64) :=
  pointer_rip _ _

theorem frontResult_flags (state : State) (input : Inputs state) (output : BitVec 32) :
    (frontResult state input output).regs.get? .rflags =
      some (X86LogicalFlags.merged input.flags output (0#1)) :=
  ((pointer_frame _ _).registers .rflags (by decide)).trans (tested_flags state input output)

theorem frontResult_budget (state : State) (input : Inputs state) (output : BitVec 32) :
    lookup (frontResult state input output) 14 = some input.budget := by
  simp only [frontResult, budgetTested, budgetLoaded, loadResult, X86Move.lookup_putPointer,
    X86Flags.putFlags_gpr, lookup_put_same]

theorem increment_at (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (before current : State) (input : Inputs before) (frame : DataFrame before current) (flags : BitVec 32)
    (currentRip : current.regs.get? .rip = some ((address input.address.toInt 32).signExtend 64))
    (frameKnown : lookup current 7 = some input.frame)
    (flagsKnown : current.regs.get? .rflags = some flags) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ output, Step current (X86Move.putPointer
      (X86Flags.putFlags (X86WriteWords.storeBytes 8 current input.usedAddress (input.used + (1#64)))
        (X86Flags.mergeFlags flags output)) (address input.address.toInt 40)) := by
  let site := rebase before current input.toBasis frame (extent := 40) input.upper 32 (by decide) currentRip
  have result := X86FrameIncrement.fetched_increment (linkedHandlers other extra) vector current site
    (address input.address.toInt 39) (address input.address.toInt 40) input.usedAddress
    input.visible input.controls input.frame input.used flags (0xa8#32)
    (by dsimp only [site, rebase]; rw [offset_int input 35 (by decide), offset_int input 39 (by decide)]; omega)
    (by rw [offset_int input 39 (by decide), offset_int input 40 (by decide)]; omega)
    input.usedUpper frameKnown ((frame.registers .ctrs (by decide)).trans input.controlsKnown)
    flagsKnown ((frame.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((frame.registers .log_register_writes (by decide)).trans input.quiet) input.usedEffective input.usedAligned
    (by exact frame.code_preserved _ _ input.loaded 32 72 rfl)
    (by exact frame.code_preserved _ _ input.loaded 33 131 rfl)
    (by exact frame.code_preserved _ _ input.loaded 34 135 rfl)
    (by
      intro index less
      dsimp only [site, rebase]
      rw [nested_address input 35 index (by decide)]
      interval_cases index <;> exact frame.code_preserved _ _ input.loaded _ _ rfl)
    (by intro index less; rw [frame.memory]; exact input.usedPresent index less)
    (by exact frame.code_preserved _ _ input.loaded 39 1 rfl)
  simpa only [increment_installed, Step] using result

def usedLoaded (state : State) (input : Inputs state) (testOutput : BitVec 32) : State :=
  loadResult (frontResult state input testOutput) 15 input.used (address input.address.toInt 23)

def usedCompared (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) : State :=
  X86Move.putPointer (X86Flags.putFlags (usedLoaded state input testOutput)
    (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput))
    (address input.address.toInt 26)

def boundedResult (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) : State :=
  X86Move.putPointer (usedCompared state input testOutput compareOutput)
    (if decide (input.budget.toNat ≤ input.used.toNat) then input.exhausted else address input.address.toInt 32)

theorem usedLoaded_data (state : State) (input : Inputs state) (output : BitVec 32) :
    DataFrame state (usedLoaded state input output) :=
  data_trans (frontResult_data state input output) (loadResult_data _ _ _ _)

theorem usedCompared_data (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) :
    DataFrame state (usedCompared state input testOutput compareOutput) :=
  data_trans (usedLoaded_data state input testOutput) (data_status _ _ _)

theorem boundedResult_data (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) :
    DataFrame state (boundedResult state input testOutput compareOutput) :=
  data_trans (usedCompared_data state input testOutput compareOutput) (data_pointer _ _)

theorem boundedResult_frame (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) :
    RegisterFrame {.r14, .r15, .rflags, .rip} state (boundedResult state input testOutput compareOutput) := by
  have first := frontResult_frame state input testOutput
  have second := loadResult_frame (frontResult state input testOutput) 15 input.used (address input.address.toInt 23)
  have third := X86Comparison.status_frame (usedLoaded state input testOutput)
    (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput)
    (address input.address.toInt 26)
  have fourth := pointer_frame (usedCompared state input testOutput compareOutput)
    (if decide (input.budget.toNat ≤ input.used.toNat) then input.exhausted else address input.address.toInt 32)
  apply (first.trans (second.trans (third.trans fourth))).mono
  intro register member
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, key] at member ⊢
  tauto

theorem boundedResult_rip (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) :
    (boundedResult state input testOutput compareOutput).regs.get? .rip = some
      ((if decide (input.budget.toNat ≤ input.used.toNat) then input.exhausted else
        address input.address.toInt 32).signExtend 64) := pointer_rip _ _

theorem boundedResult_flags (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32) :
    (boundedResult state input testOutput compareOutput).regs.get? .rflags =
      some (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput) := by
  simp [boundedResult, usedCompared, X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]

theorem bounded_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (testOutput : BitVec 32) (positive : input.budget ≠ (0#64)) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ compareOutput,
      Step (frontResult state input testOutput) (usedLoaded state input testOutput) ∧
      Step (usedLoaded state input testOutput) (usedCompared state input testOutput compareOutput) ∧
      Step (usedCompared state input testOutput compareOutput) (boundedResult state input testOutput compareOutput) := by
  let : OtherOpcodeHandlers := linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  have first : Step (frontResult state input testOutput) (usedLoaded state input testOutput) :=
    load_at other extra vector state (frontResult state input testOutput) input
      (frontResult_data state input testOutput) 16 (by decide) 15 input.used input.usedAddress
      (X86LogicalFlags.merged input.flags testOutput (0#1)) (0xa8#32)
      (by simpa only [beq_eq_false_iff_ne.mpr positive, Bool.false_eq_true, ite_false] using
        frontResult_rip state input testOutput)
      (((frontResult_frame state input testOutput).lookup 7 (by decide)).trans input.frameKnown)
      (frontResult_flags state input testOutput) input.usedUpper input.usedEffective input.usedAligned input.usedPresent
      (by change some 76 = some (X86FrameLoad.frameRex 15).toNat; decide)
      rfl (by change some 191 = some (X86FrameLoad.frameModRM 15).toNat; decide)
      (by intro index less; interval_cases index <;> rfl)
  have loadedFlags : (usedLoaded state input testOutput).regs.get? .rflags =
      some (X86LogicalFlags.merged input.flags testOutput (0#1)) :=
    ((loadResult_frame _ 15 input.used _).registers .rflags (by decide)).trans
      (frontResult_flags state input testOutput)
  have budgetKnown : lookup (usedLoaded state input testOutput) 14 = some input.budget := by
    dsimp only [usedLoaded, loadResult]
    rw [X86Move.lookup_putPointer, lookup_put_other _ 15 14 _ (by decide)]
    exact frontResult_budget state input testOutput
  have usedKnown : lookup (usedLoaded state input testOutput) 15 = some input.used := by
    simp only [usedLoaded, loadResult, X86Move.lookup_putPointer, lookup_put_same]
  let window := windowAt state (usedLoaded state input testOutput) input.toBasis
    (usedLoaded_data state input testOutput) (extent := 40) input.upper 23 (by decide) (loadResult_rip _ _ _ _)
    (expected input.displacement) ((usedLoaded_data state input testOutput).code_preserved _ _ input.loaded)
    14 15 (0x39#8)
    (by change some 77 = some (X86RegisterEncoding.rex true 14 15).toNat; decide)
    rfl (by change some 247 = some (X86RegisterEncoding.modRM 14 15).toNat; decide)
  have compare := X86Comparison.fetched_compare64 (linkedHandlers other extra) vector
    (usedLoaded state input testOutput) 14 15 window input.used input.budget
    (X86LogicalFlags.merged input.flags testOutput (0#1)) budgetKnown usedKnown loadedFlags
    (((usedLoaded_data state input testOutput).registers .log_register_writes (by decide)).trans input.quiet)
  rw [arithmetic_installed] at compare
  obtain ⟨compareOutput, compared, carry, _⟩ := compare
  have second : Step (usedLoaded state input testOutput) (usedCompared state input testOutput compareOutput) := compared
  have sense : X86BranchCondition.value .aboveEqual
      (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput) =
      decide (input.budget.toNat ≤ input.used.toNat) := by
    simp only [X86BranchCondition.value, X86Comparison.merged_carry, carry, X86BranchCondition.unsigned_sense]
  have third := branch_at other extra vector state (usedCompared state input testOutput compareOutput) input
    (usedCompared_data state input testOutput compareOutput) 26 (by decide) .aboveEqual
    (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput)
    input.displacement input.exhausted (pointer_rip _ _)
    (by simp [usedCompared, X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert])
    (by rw [offset_int input 32 (by decide)]; exact input.jump)
    rfl rfl (by intro index less; interval_cases index <;> rfl)
  rw [sense] at third
  exact ⟨compareOutput, first, second, third⟩

noncomputable def fetches [OtherOpcodeHandlers] [VectorOpcodeHandlers] : Nat → SailM Unit
  | 0 => pure ()
  | count + 1 => do Functions.x86_fetch_decode_execute (); fetches count

theorem fetches_zero [OtherOpcodeHandlers] [VectorOpcodeHandlers] (state : State) :
    (fetches 0).run state = .ok () state := rfl

theorem fetches_cons [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (count : Nat) (before middle after : State) (first : Step before middle)
    (rest : (fetches count).run middle = .ok () after) :
    (fetches (count + 1)).run before = .ok () after := by
  change (do Functions.x86_fetch_decode_execute (); fetches count).run before = _
  rw [run_bind, first]
  exact rest

theorem fetches_one [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (before after : State) (step : Step before after) : (fetches 1).run before = .ok () after :=
  fetches_cons 0 before after after step (fetches_zero after)

theorem fetches_deterministic [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (count : Nat) (before left right : State)
    (one : (fetches count).run before = .ok () left)
    (two : (fetches count).run before = .ok () right) : left = right :=
  (EStateM.Result.ok.inj (one.symm.trans two)).2

theorem fetches_add [OtherOpcodeHandlers] [VectorOpcodeHandlers] (first second : Nat) :
    fetches (first + second) = (do fetches first; fetches second) := by
  induction first with
  | zero => simp only [Nat.zero_add, fetches, pure_bind]
  | succ first ih =>
    rw [Nat.succ_add, fetches, ih]
    simp only [fetches, bind_assoc]

theorem fetches_then [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (first second : Nat) (before middle after : State)
    (one : (fetches first).run before = .ok () middle)
    (two : (fetches second).run middle = .ok () after) :
    (fetches (first + second)).run before = .ok () after := by
  rw [fetches_add, run_bind, one]
  exact two

def instructionCount {state : State} (input : Inputs state) : Nat :=
  if input.budget == (0#64) then 4
  else if decide (input.budget.toNat ≤ input.used.toNat) then 6 else 7

def writes {state : State} (input : Inputs state) : Finset Nat :=
  if fuelAvailable input.budget input.used then X86WriteWords.written input.usedAddress (List.range 8) else ∅

structure Result (state : State) (input : Inputs state) (after : State) : Prop where
  pointer : after.regs.get? .rip = some ((if fuelAvailable input.budget input.used then
    address input.address.toInt 40 else input.exhausted).signExtend 64)
  frame : X86StateFrame.Frame {.r14, .r15, .rflags, .rip} (writes input) state after
  flags : ∃ value, after.regs.get? .rflags = some value
  counter : fuelAvailable input.budget input.used = true → ∀ index < 8,
    after.mem.get? (X86WriteWords.physicalAddress input.usedAddress index) =
      some ((input.used + (1#64)).extractLsb' (8 * index) 8)
  exhausted : fuelAvailable input.budget input.used = false → after.mem = state.mem

theorem finish_result (state current : State) (input : Inputs state)
    (frame : RegisterFrame {.r14, .r15, .rflags, .rip} state current)
    (flags : BitVec 32) (available : fuelAvailable input.budget input.used = true) :
    Result state input (X86Move.putPointer
      (X86Flags.putFlags (X86WriteWords.storeBytes 8 current input.usedAddress (input.used + (1#64))) flags)
      (address input.address.toInt 40)) where
  pointer := by simp only [available, ite_true]; exact pointer_rip _ _
  frame := by
    have bytes := (X86StateFrame.registerOnly frame).trans
      (X86FrameIncrement.result_frame current input.usedAddress (input.used + (1#64)) flags
        (address input.address.toInt 40))
    apply bytes.mono
    · intro register member
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
    · simp only [writes, available, ite_true, Finset.empty_union, Finset.Subset.refl]
  counter _ index within := by
    exact X86WriteWords.store_word_byte current input.usedAddress (input.used + (1#64)) input.usedUpper index within
  flags := ⟨flags, by simp [X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]⟩
  exhausted failure := by rw [available] at failure; cases failure

theorem exhaustion_result (state : State) (input : Inputs state) (testOutput compareOutput : BitVec 32)
    (unavailable : fuelAvailable input.budget input.used = false)
    (ordered : decide (input.budget.toNat ≤ input.used.toNat) = true) :
    Result state input (boundedResult state input testOutput compareOutput) where
  pointer := by
    rw [boundedResult_rip]
    simp only [unavailable, ordered, Bool.false_eq_true, ite_false, ite_true]
  frame := by
    simpa only [writes, unavailable, Bool.false_eq_true, ite_false] using
      X86StateFrame.registerOnly (boundedResult_frame state input testOutput compareOutput)
  counter available := by rw [unavailable] at available; cases available
  flags := ⟨_, boundedResult_flags state input testOutput compareOutput⟩
  exhausted _ := (boundedResult_frame state input testOutput compareOutput).memory

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (fetches (instructionCount input)).run state = .ok () after ∧ Result state input after := by
  let : OtherOpcodeHandlers := linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨testOutput, first, second, third⟩ := front_executes other extra vector state input
  by_cases zero : input.budget = (0#64)
  · have available : fuelAvailable input.budget input.used = true := by simp [fuelAvailable, zero]
    obtain ⟨output, last⟩ := increment_at other extra vector state (frontResult state input testOutput) input
      (frontResult_data state input testOutput) (X86LogicalFlags.merged input.flags testOutput (0#1))
      (by simpa only [zero, beq_self_eq_true, ite_true] using frontResult_rip state input testOutput)
      (((frontResult_frame state input testOutput).lookup 7 (by decide)).trans input.frameKnown)
      (frontResult_flags state input testOutput)
    refine ⟨_, ?_, finish_result state (frontResult state input testOutput) input ?_
      (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) output) available⟩
    · have run := fetches_cons 3 state _ _ first (fetches_cons 2 _ _ _ second
        (fetches_cons 1 _ _ _ third (fetches_one _ _ last)))
      simpa only [instructionCount, zero, beq_self_eq_true, ite_true] using run
    · apply (frontResult_frame state input testOutput).mono
      intro register member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
  · obtain ⟨compareOutput, fourth, fifth, sixth⟩ := bounded_executes other extra vector state input testOutput zero
    by_cases ordered : input.budget.toNat ≤ input.used.toNat
    · have unavailable : fuelAvailable input.budget input.used = false := by
        cases found : fuelAvailable input.budget input.used with
        | false => rfl
        | true =>
          have less := (fuelAvailable_positive input.budget input.used zero).mp found
          omega
      refine ⟨boundedResult state input testOutput compareOutput, ?_,
        exhaustion_result state input testOutput compareOutput unavailable (by simp [ordered])⟩
      have run := fetches_cons 5 state _ _ first (fetches_cons 4 _ _ _ second
        (fetches_cons 3 _ _ _ third (fetches_cons 2 _ _ _ fourth
          (fetches_cons 1 _ _ _ fifth (fetches_one _ _ sixth)))))
      simpa only [instructionCount, beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false,
        show decide (input.budget.toNat ≤ input.used.toNat) = true from by simp [ordered], ite_true] using run
    · have available : fuelAvailable input.budget input.used = true :=
        (fuelAvailable_positive input.budget input.used zero).mpr (by omega)
      obtain ⟨output, last⟩ := increment_at other extra vector state
        (boundedResult state input testOutput compareOutput) input
        (boundedResult_data state input testOutput compareOutput)
        (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput)
        (by simpa only [show decide (input.budget.toNat ≤ input.used.toNat) = false from by simp [ordered],
          Bool.false_eq_true, ite_false] using boundedResult_rip state input testOutput compareOutput)
        (((boundedResult_frame state input testOutput compareOutput).lookup 7 (by decide)).trans input.frameKnown)
        (boundedResult_flags state input testOutput compareOutput)
      refine ⟨_, ?_, finish_result state (boundedResult state input testOutput compareOutput) input
        (boundedResult_frame state input testOutput compareOutput)
        (X86Flags.mergeFlags (X86Flags.mergeFlags (X86LogicalFlags.merged input.flags testOutput (0#1)) compareOutput)
          output) available⟩
      have run := fetches_cons 6 state _ _ first (fetches_cons 5 _ _ _ second
        (fetches_cons 4 _ _ _ third (fetches_cons 3 _ _ _ fourth
          (fetches_cons 2 _ _ _ fifth (fetches_cons 1 _ _ _ sixth (fetches_one _ _ last))))))
      simpa only [instructionCount, beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false,
        show decide (input.budget.toNat ≤ input.used.toNat) = false from by simp [ordered]] using run

theorem any_run_refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    (fetches (instructionCount input)).run state = .ok () after → Result state input after := by
  intro observed
  obtain ⟨proved, executed, correct⟩ := executes other extra vector state input
  have same := (EStateM.Result.ok.inj (executed.symm.trans observed)).2
  simpa only [same] using correct

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)

private def cells (budget used : Word) : List (Nat × BitVec 8) :=
  (List.range 40).map (fun index => (4096 + index, BitVec.ofNat 8 (((expected (0x1e0#32))[index]?).getD 0))) ++
  (List.range 8).map (fun index => (8352 + index, budget.extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (8360 + index, used.extractLsb' (8 * index) 8)) ++ [(8368, 42#8)]

private theorem cells_distinct (budget used : Word) :
    (cells budget used).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells budget used).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private def mapped (budget used : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rdi (0x2000#64)
  let registers := registers.insert .rbx (0xdead#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells budget used), (), 0, #[]⟩

private theorem mapped_known (budget used : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells budget used) : (mapped budget used).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (cells_distinct budget used) present

private theorem mapped_code (budget used : Word) (index : Nat) (within : index < 40) :
    (mapped budget used).mem.get? (4096 + index) =
      some (BitVec.ofNat 8 (((expected (0x1e0#32))[index]?).getD 0)) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl ⟨index, List.mem_range.mpr within, rfl⟩))

private theorem mapped_budget (budget used : Word) (index : Nat) (within : index < 8) :
    (mapped budget used).mem.get? (8352 + index) = some (budget.extractLsb' (8 * index) 8) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨index, List.mem_range.mpr within, rfl⟩))

private theorem mapped_used (budget used : Word) (index : Nat) (within : index < 8) :
    (mapped budget used).mem.get? (8360 + index) = some (used.extractLsb' (8 * index) 8) := by
  apply mapped_known
  simp only [cells, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨index, List.mem_range.mpr within, rfl⟩)

private def input (budget used : Word) : Inputs (mapped budget used) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [mapped, Std.ExtDHashMap.get?_insert]
  fault := by simp [mapped, Std.ExtDHashMap.get?_insert]
  msrs := by simp [mapped, Std.ExtDHashMap.get?_insert]
  segments := by simp [mapped, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [mapped, Std.ExtDHashMap.get?_insert]
  rip := by simp [mapped, Std.ExtDHashMap.get?_insert]
  displacement := 0x1e0#32
  exhausted := 0x1200#48
  upper := by decide
  jump := by decide
  loaded := by
    intro index byte present
    have within : index < 40 := by
      have bound := (List.getElem?_eq_some_iff.mp present).choose
      simpa only [expected_length] using bound
    have place : ((address (0x1000#48).toInt index).signExtend 52).toNat = 4096 + index := by
      interval_cases index <;> rfl
    rw [place, mapped_code budget used index within, present]
    rfl
  frame := 0x2000#64
  budget := budget
  used := used
  budgetAddress := 0x20a0#48
  usedAddress := 0x20a8#48
  budgetUpper := by decide
  usedUpper := by decide
  budgetEffective := by decide
  usedEffective := by decide
  budgetAligned := by decide
  usedAligned := by decide
  visible := visible
  controls := controls
  flags := 0#32
  frameKnown := by
    change ((mapped budget used).regs.get? .rdi).map (fun value : Word => value) = _
    simp [mapped, Std.ExtDHashMap.get?_insert]
  controlsKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [mapped, Std.ExtDHashMap.get?_insert]
  quiet := by simp [mapped]
  budgetPresent := by
    intro index within
    have place : ((address (0x20a0#48).toInt index).signExtend 52).toNat = 8352 + index := by
      interval_cases index <;> rfl
    rw [place]
    exact mapped_budget budget used index within
  usedPresent := by
    intro index within
    have place : ((address (0x20a8#48).toInt index).signExtend 52).toNat = 8360 + index := by
      interval_cases index <;> rfl
    rw [place]
    exact mapped_used budget used index within

theorem available (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (fetches 7).run (mapped (3#64) (2#64)) = .ok () after ∧
      after.regs.get? .rip = some (0x1028#64) ∧ after.mem.get? 8360 = some (3#8) := by
  obtain ⟨after, executed, result⟩ := executes other extra vector (mapped (3#64) (2#64)) (input (3#64) (2#64))
  refine ⟨after, executed, ?_, ?_⟩
  · exact result.pointer
  · exact result.counter (by decide) 0 (by decide)

theorem exhausted_equal (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (fetches 6).run (mapped (3#64) (3#64)) = .ok () after ∧
      after.regs.get? .rip = some (0x1200#64) ∧ after.mem = (mapped (3#64) (3#64)).mem := by
  obtain ⟨after, executed, result⟩ := executes other extra vector (mapped (3#64) (3#64)) (input (3#64) (3#64))
  exact ⟨after, executed, result.pointer, result.exhausted (by decide)⟩

theorem unlimited_wraps (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (fetches 4).run (mapped (0#64) (0xffffffffffffffff#64)) = .ok () after ∧
      after.regs.get? .rip = some (0x1028#64) ∧ after.mem.get? 8360 = some (0#8) := by
  obtain ⟨after, executed, result⟩ := executes other extra vector
    (mapped (0#64) (0xffffffffffffffff#64)) (input (0#64) (0xffffffffffffffff#64))
  refine ⟨after, executed, result.pointer, ?_⟩
  exact result.counter (by decide) 0 (by decide)

theorem wrong_counter_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (fetches 7).run (mapped (3#64) (2#64)) = .ok () after ∧ after.mem.get? 8360 = some (4#8) := by
  intro wrong
  obtain ⟨after, executed, _, counter⟩ := available other extra vector
  obtain ⟨claimed, run, value⟩ := wrong
  have same := (EStateM.Result.ok.inj (executed.symm.trans run)).2
  rw [← same, counter] at value
  exact (by decide : some (3#8) ≠ some (4#8)) value

theorem exhaustion_increment_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (fetches 6).run (mapped (3#64) (3#64)) = .ok () after ∧ after.mem.get? 8360 = some (4#8) := by
  obtain ⟨after, executed, _, unchanged⟩ := exhausted_equal other extra vector
  rintro ⟨claimed, run, value⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans run)).2
  rw [← same, unchanged] at value
  have old : (mapped (3#64) (3#64)).mem.get? 8360 = some (3#8) := by
    exact mapped_used (3#64) (3#64) 0 (by decide)
  rw [old] at value
  exact (by decide : some (3#8) ≠ some (4#8)) value

end Controls
end Mettapedia.Machines.TIsa.X86FuelPrefix

#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.front_executes
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.bounded_executes
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.executes
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.any_run_refines
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.available
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.exhausted_equal
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.unlimited_wraps
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.wrong_counter_refused
#print axioms Mettapedia.Machines.TIsa.X86FuelPrefix.Controls.exhaustion_increment_refused
