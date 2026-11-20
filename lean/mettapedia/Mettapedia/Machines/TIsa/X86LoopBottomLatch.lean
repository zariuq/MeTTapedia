import Mettapedia.Machines.TIsa.X86LoopLatch
import Mettapedia.Machines.TIsa.X86BranchGate

/-!
# Native bottom-tested counter latch as two existing source firings

The thirteen actual bytes encode REX.W ADD index,1, CMP index,bound and near
JB. Original Sail fetch/decode/execute increments the counter, compares the
new counter with the retained bound and reaches the backedge target exactly
when it is below the bound, otherwise the fallthrough exit, in three
instructions. Only the counter, flags and RIP change; every fetched prefix
preserves memory and the remaining registers.

The source join is the existing latch firing followed by the existing header
firing. The first fetched instruction alone realizes the latch firing and
reaches the header token at the test; the remaining two realize the header.
The strict index/bound premise excludes native wraparound and proves the rank
decrease. Continuing, final and wrapped-counter runs, an altered condition and
an altered backedge byte have executable controls. Body, whole-loop iteration,
fuel, early exits and public ABI remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LoopBottomLatch
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86BranchGate.handlers (X86FrameIncrement.linkedHandlers other) extra

/-- CMP index,bound followed by near JB with its raw little-endian displacement. -/
def testCode (index bound : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(rex true bound index).toNat,0x39,(modRM bound index).toNat,0x0f,0x82] ++
    (List.range 4).map (fun position => (displacement.extractLsb' (8 * position) 8).toNat)

def code (index bound : Fin 16) (displacement : BitVec 32) : List Nat :=
  X86RegisterIncrement.code index ++ testCode index bound displacement

theorem code_length (index bound : Fin 16) (displacement : BitVec 32) :
    (code index bound displacement).length = 13 := by
  simp [code, testCode, X86RegisterIncrement.code]

theorem increment_byte (index bound : Fin 16) (displacement : BitVec 32) (offset byte : Nat)
    (present : (X86RegisterIncrement.code index)[offset]? = some byte) :
    (code index bound displacement)[offset]? = some byte := by
  rw [code, List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  exact present

theorem test_byte (index bound : Fin 16) (displacement : BitVec 32) (offset : Nat) :
    (code index bound displacement)[4 + offset]? = (testCode index bound displacement)[offset]? := by
  rw [code, List.getElem?_append_right (by simp [X86RegisterIncrement.code]),
    show (X86RegisterIncrement.code index).length = 4 by rfl, Nat.add_sub_cancel_left]

theorem displacement_byte (index bound : Fin 16) (displacement : BitVec 32) (slot : Nat) (within : slot < 4) :
    (code index bound displacement)[9 + slot]? = some (displacement.extractLsb' (8 * slot) 8).toNat := by
  rw [show 9 + slot = 4 + (5 + slot) by omega, test_byte, testCode, List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  simp [within]

theorem frame_subset (index : Fin 16) :
    X86RegisterIncrement.writes index ∪ X86BranchGate.writes ⊆ X86RegisterIncrement.writes index := by
  intro register member
  simp only [X86RegisterIncrement.writes, X86BranchGate.writes, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at member ⊢
  tauto

theorem pointer_subset (index : Fin 16) :
    X86RegisterIncrement.writes index ∪ {.rip} ⊆ X86RegisterIncrement.writes index := by
  intro register member
  simp only [X86RegisterIncrement.writes, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
  tauto

theorem below_sense (left right : Word) :
    ((1#1) == Functions.bool_to_bits (left.toNat < right.toNat)) = decide (left.toNat < right.toNat) := by
  by_cases below : left.toNat < right.toNat <;> simp [Functions.bool_to_bits, below]

structure Inputs (native : State) (index bound : Fin 16) extends X86LegacyFetch.Basis native where
  indexValue : Word
  boundValue : Word
  flags : BitVec 32
  indexKnown : lookup native index = some indexValue
  boundKnown : lookup native bound = some boundValue
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  distinct : index ≠ bound
  upper : address.toInt + 13 < (2 ^ 47 : Int)
  displacement : BitVec 32
  target : BitVec 48
  jump : target.toInt = address.toInt + 13 + displacement.toInt
  loaded : codeLoaded native address.toInt (code index bound displacement)

def position {native : State} {index bound : Fin 16} (input : Inputs native index bound) (offset : Nat) : BitVec 48 :=
  address input.address.toInt offset

theorem position_exact {native : State} {index bound : Fin 16} (input : Inputs native index bound)
    (offset : Nat) (within : offset ≤ 13) :
    (position input offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem shifted {native : State} {index bound : Fin 16} (input : Inputs native index bound)
    (offset slot : Nat) (within : offset ≤ 13) :
    address (position input offset).toInt slot = position input (offset + slot) := by
  rw [position_exact input offset within]
  simp only [position, address, Int.natCast_add, Int.add_assoc]

def incrementInput {native : State} {index bound : Fin 16} (input : Inputs native index bound) :
    X86RegisterIncrement.Inputs native index := {
  input.toBasis with
  value := input.indexValue
  flags := input.flags
  valueKnown := input.indexKnown
  flagsKnown := input.flagsKnown
  quiet := input.quiet
  upper := by have := input.upper; omega
  loaded := fun offset byte present =>
    input.loaded offset byte (increment_byte index bound input.displacement offset byte present) }

theorem increment_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (input.indexValue + 1) ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some ((position input 4).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, run, framed, valueRead, flagsRead, rip, control⟩ :=
    X86RegisterIncrement.executes_control (handlers other extra) vector native index (incrementInput input)
  exact ⟨after, flags, run, framed, valueRead,
    (framed.lookup bound (X86LoopLatch.bound_outside index bound (Ne.symm input.distinct))).trans input.boundKnown,
    flagsRead, rip, control⟩

theorem executes_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (input.indexValue + 1) ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if (input.indexValue + 1).toNat < input.boundValue.toNat then input.target else position input 13).signExtend 64) ∧
      X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, middleFlags, first, firstFrame, indexRead, boundRead, flagsRead, middleRip, middleControl⟩ :=
    increment_step other extra vector native index bound input
  have middleLoaded := firstFrame.code_preserved input.address.toInt _ input.loaded
  have middleData := firstFrame.mono (X86RegisterIncrement.writes_data index)
  have middleQuiet := (middleData.registers .log_register_writes (by decide)).trans input.quiet
  let site := windowAt native middle input.toBasis middleData input.upper 4 (by decide) middleRip
    (code index bound input.displacement) middleLoaded bound index (0x39#8)
    ((test_byte index bound input.displacement 0).trans (by simp [testCode]))
    ((test_byte index bound input.displacement 1).trans (by simp [testCode]))
    ((test_byte index bound input.displacement 2).trans (by simp [testCode]))
  obtain ⟨output, executed, carry, _⟩ := X86Comparison.fetched_compare64 (handlers other extra) vector middle
    bound index site (input.indexValue + 1) input.boundValue middleFlags boundRead indexRead flagsRead middleQuiet
  let flags := X86Flags.mergeFlags middleFlags output
  let tested := X86Move.putPointer (X86Flags.putFlags middle flags) site.next
  have testFrame : RegisterFrame X86BranchGate.writes middle tested := X86Comparison.status_frame _ _ _
  have testedFrame : RegisterFrame (X86RegisterIncrement.writes index) native tested :=
    (firstFrame.trans testFrame).mono (frame_subset index)
  have testedLoaded := testedFrame.code_preserved input.address.toInt _ input.loaded
  have testedFlags : tested.regs.get? .rflags = some flags := by
    rw [(pointer_frame (X86Flags.putFlags middle flags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  have testedRip : tested.regs.get? .rip = some ((address input.address.toInt 7).signExtend 64) := by
    simp only [tested, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl
  let branch := rebase native tested input.toBasis (testedFrame.mono (X86RegisterIncrement.writes_data index))
    input.upper 7 (by decide) testedRip
  have advance : branch.modrmAddress.toInt + 4 = (position input 13).toInt := by
    change (position input 9).toInt + 4 = (position input 13).toInt
    rw [position_exact input 9 (by decide), position_exact input 13 (by decide)]
    omega
  have jump : input.target.toInt = (position input 13).toInt + input.displacement.toInt := by
    rw [position_exact input 13 (by decide)]
    exact input.jump
  have displacement : ∀ slot < 4,
      tested.mem.get? ((address branch.modrmAddress.toInt slot).signExtend 52).toNat =
        some (input.displacement.extractLsb' (8 * slot) 8) := by
    intro slot within
    change tested.mem.get? ((address (position input 9).toInt slot).signExtend 52).toNat = _
    rw [shifted input 9 slot (by decide)]
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      testedLoaded _ _ (displacement_byte index bound input.displacement slot within)
  have last := X86EscapeFetch.fetched_branch (X86Arithmetic.linkedHandlers (X86FrameIncrement.linkedHandlers other))
    extra vector .below tested branch.address branch.opcodeAddress branch.modrmAddress (position input 13) input.target
    branch.control branch.attributes flags input.displacement branch.step1
    (by have := branch.step1; have := branch.step2; omega) advance jump
    branch.status branch.fault branch.msrs branch.segments branch.longMode branch.codeMode branch.application
    branch.rip testedFlags (((testedFrame.mono (X86RegisterIncrement.writes_data index)).registers
      .log_register_writes (by decide)).trans input.quiet)
    (testedLoaded 7 0x0f ((test_byte index bound input.displacement 3).trans (by simp [testCode])))
    (testedLoaded 8 0x82 ((test_byte index bound input.displacement 4).trans (by simp [testCode])))
    displacement
  have sense : X86BranchCondition.value .below flags =
      decide ((input.indexValue + 1).toNat < input.boundValue.toNat) := by
    rw [X86BranchCondition.value, X86Comparison.merged_carry, carry, below_sense]
  rw [sense] at last
  let target := if decide ((input.indexValue + 1).toNat < input.boundValue.toNat) then input.target
    else position input 13
  let after := X86Move.putPointer tested target
  have lastFrame := pointer_frame tested target
  have two : (X86FuelPrefix.fetches 2).run native = .ok () tested :=
    X86FuelPrefix.fetches_then 1 1 native middle tested first (X86FuelPrefix.fetches_one middle tested executed)
  have three : (X86FuelPrefix.fetches 3).run native = .ok () after :=
    X86FuelPrefix.fetches_then 2 1 native tested after two (X86FuelPrefix.fetches_one tested after last)
  have finalFrame : RegisterFrame (X86RegisterIncrement.writes index) native after :=
    (testedFrame.trans lastFrame).mono (pointer_subset index)
  have testedIndex : lookup tested index = some (input.indexValue + 1) :=
    (testFrame.lookup index (by fin_cases index <;> decide)).trans indexRead
  have testedBound : lookup tested bound = some input.boundValue :=
    (testFrame.lookup bound (by fin_cases bound <;> decide)).trans boundRead
  refine ⟨after, flags, three, finalFrame, (lastFrame.lookup index (by fin_cases index <;> decide)).trans testedIndex,
    (lastFrame.lookup bound (by fin_cases bound <;> decide)).trans testedBound,
    (lastFrame.registers .rflags (by decide)).trans testedFlags, ?_, ?_, ?_⟩
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self, target, decide_eq_true_eq]
  · have testControl : X86ControlFlags.Preserved middle tested := by
      unfold X86ControlFlags.Preserved
      rw [testedFlags, flagsRead]
      simp only [Option.map_some, flags, X86ControlFlags.arithmetic_mask]
    exact (middleControl.trans testControl).trans (X86ControlFlags.of_register_frame lastFrame (by decide))
  · intro count within reached run
    have known : ∃ proved, (X86FuelPrefix.fetches count).run native = .ok () proved ∧
        RegisterFrame (X86RegisterIncrement.writes index) native proved := by
      interval_cases count
      · exact ⟨native, X86FuelPrefix.fetches_zero native, RegisterFrame.refl _ _⟩
      · exact ⟨middle, first, firstFrame⟩
      · exact ⟨tested, two, testedFrame⟩
      · exact ⟨after, three, finalFrame⟩
    obtain ⟨proved, provedRun, framed⟩ := known
    have same := X86FuelPrefix.fetches_deterministic count native proved reached provedRun run
    subst reached
    exact framed


theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (input.indexValue + 1) ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if (input.indexValue + 1).toNat < input.boundValue.toNat then input.target else position input 13).signExtend 64) ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, run, frame, indexRead, boundRead, flagsRead, rip, _control, prefixes⟩ :=
    executes_control other extra vector native index bound input
  exact ⟨after, flags, run, frame, indexRead, boundRead, flagsRead, rip, prefixes⟩

/-- The first fetched instruction realizes the source latch and stops at the header token;
the next two realize the header firing from the incremented counter. -/
theorem realizes {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound)
    (loop : Control.Loop Key) (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (latchScope : loop.latch.support ⊆ keys) (headerScope : loop.header.support ⊆ keys)
    (checked : loop.check = true)
    (current : before (.inl loop.activation) = loop.latchPoint)
    (indexRead : before (.inr loop.index) = input.indexValue)
    (boundRead : before (.inr loop.bound) = input.boundValue)
    (less : input.indexValue.toNat < input.boundValue.toNat)
    (bounded : input.boundValue.toNat ≤ loop.maximum)
    (header : loop.headerPoint = (position input 4).signExtend 64)
    (body : loop.bodyPoint = input.target.signExtend 64)
    (exit : loop.exitPoint = (position input 13).signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ middle after, ∃ latch : CellEffects.Invocation loop.latch, ∃ test : CellEffects.Invocation loop.header,
      CellEffects.system.Enables (Cells.encode keys before) latch ∧
      CellEffects.system.fire (Cells.encode keys before) latch = Cells.encode keys (loop.latchValues before) ∧
      CellEffects.system.Enables (Cells.encode keys (loop.latchValues before)) test ∧
      CellEffects.system.fire (Cells.encode keys (loop.latchValues before)) test =
        Cells.encode keys (loop.headerValues (loop.latchValues before)) ∧
      (X86FuelPrefix.fetches 1).run native = .ok () middle ∧
      lookup middle index = some (loop.latchValues before (.inr loop.index)) ∧
      lookup middle bound = some (loop.latchValues before (.inr loop.bound)) ∧
      middle.regs.get? .rip = some (loop.latchValues before (.inl loop.activation)) ∧
      (X86FuelPrefix.fetches 3).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (loop.latchValues before (.inr loop.index)) ∧
      lookup after bound = some (loop.latchValues before (.inr loop.bound)) ∧
      after.regs.get? .rip = some (loop.headerValues (loop.latchValues before) (.inl loop.activation)) ∧
      loop.rank (loop.latchValues before) < loop.rank before ∧
      ∀ count ≤ 3, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have distinct : loop.index ≠ loop.bound := (of_decide_eq_true checked).1
  obtain ⟨latch, latchEnabled, latchFired, decreases⟩ := loop.latch_realized keys before latchScope checked current
    (by rw [indexRead, boundRead]; exact less) (by rw [boundRead]; exact bounded)
  have nextIndex : loop.latchValues before (.inr loop.index) = input.indexValue + 1 := by
    simp [Control.Loop.latchValues, indexRead]
  have nextBound : loop.latchValues before (.inr loop.bound) = input.boundValue := by
    simp [Control.Loop.latchValues, Ne.symm distinct, boundRead]
  have nextPoint : loop.latchValues before (.inl loop.activation) = loop.headerPoint := by
    simp [Control.Loop.latchValues]
  have noWrap := Control.counter_increment_no_wrap input.indexValue input.boundValue less
  obtain ⟨test, testEnabled, testFired⟩ := loop.header_realized keys (loop.latchValues before) headerScope checked
    nextPoint (by rw [nextIndex, nextBound, noWrap]; omega) (by rw [nextBound]; exact bounded)
  obtain ⟨middle, _, first, _, middleIndex, middleBound, _, middleRip, _⟩ :=
    increment_step other extra vector native index bound input
  obtain ⟨after, _, run, framed, indexAfter, boundAfter, _, rip, prefixes⟩ :=
    executes other extra vector native index bound input
  refine ⟨middle, after, latch, test, latchEnabled, latchFired, testEnabled, testFired, first,
    by rw [nextIndex]; exact middleIndex, by rw [nextBound]; exact middleBound,
    by rw [nextPoint, header]; exact middleRip, run, framed,
    by rw [nextIndex]; exact indexAfter, by rw [nextBound]; exact boundAfter, ?_, decreases, prefixes⟩
  by_cases continues : (input.indexValue + 1).toNat < input.boundValue.toNat
  · simpa only [Control.Loop.headerValues, Function.update_self, Control.Loop.headerTarget, nextIndex, nextBound,
      if_pos continues, body] using rip
  · simpa only [Control.Loop.headerValues, Function.update_self, Control.Loop.headerTarget, nextIndex, nextBound,
      if_neg continues, exit] using rip


namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 13).map fun offset => (4096 + offset, BitVec.ofNat 8 (((code 10 9 (-105#32))[offset]?).getD 0))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def before (index bound : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 index
  let registers := registers.insert .r9 bound
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem image (index bound : Word) : codeLoaded (before index bound) 4096 (code 10 9 (-105#32)) := by
  intro offset byte present
  have within : offset < 13 := by simpa only [code_length] using (List.getElem?_eq_some_iff.mp present).1
  have point : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide
  have member : (4096 + offset, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨offset, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def input (index bound : Word) : Inputs (before index bound) 10 9 where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]
  indexValue := index
  boundValue := bound
  flags := 0x246#32
  indexKnown := by simp [lookup, before, key, Std.ExtDHashMap.get?_insert]; rfl
  boundKnown := by simp [lookup, before, key, Std.ExtDHashMap.get?_insert]; rfl
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  distinct := by decide
  upper := by decide
  displacement := -105#32
  target := 4004#48
  jump := by decide
  loaded := image index bound

theorem outcome (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index bound : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before index bound) = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes 10) (before index bound) after ∧
      lookup after 10 = some (index + 1) ∧ lookup after 9 = some bound ∧
      after.regs.get? .rip = some (if (index + 1).toNat < bound.toNat then (4004#64) else (4109#64)) := by
  obtain ⟨after, _, run, framed, indexRead, boundRead, _, rip, _⟩ := executes other extra vector _ 10 9 (input index bound)
  refine ⟨after, run, framed, indexRead, boundRead, ?_⟩
  have condition : ((input index bound).indexValue + 1).toNat < (input index bound).boundValue.toNat ↔
      (index + 1).toNat < bound.toNat := Iff.rfl
  by_cases continues : (index + 1).toNat < bound.toNat
  · rw [if_pos (condition.mpr continues)] at rip
    rw [if_pos continues]
    simpa [input] using rip
  · rw [if_neg (fun held => continues (condition.mp held))] at rip
    rw [if_neg continues]
    simpa [input, position, address] using rip

theorem continuing_iteration_branches_back (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before 0 2) = .ok () after ∧
      lookup after 10 = some 1 ∧ after.regs.get? .rip = some (4004#64) := by
  obtain ⟨after, run, _, indexRead, _, rip⟩ := outcome other extra vector 0 2
  exact ⟨after, run, indexRead, rip⟩

theorem last_iteration_exits (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before (0xfffffffe#64) (0xffffffff#64)) = .ok () after ∧
      lookup after 10 = some (0xffffffff#64) ∧ after.regs.get? .rip = some (4109#64) := by
  obtain ⟨after, run, _, indexRead, _, rip⟩ := outcome other extra vector (0xfffffffe#64) (0xffffffff#64)
  exact ⟨after, run, indexRead, rip⟩

private def loop : Control.Loop Nat := ⟨0, 3999, 4100, 4096, 4004, 4109, 0, 1, 4294967295⟩
private def keys : Finset (Control.Location Nat) := {.inl 0, .inr 0, .inr 1}
private def values (index bound : Word) : Control.Location Nat → Word
  | .inl _ => 4096
  | .inr 0 => index
  | .inr _ => bound

/-- The full source pair at the maximum admitted bound: latch to the header token, header to exit. -/
theorem last_iteration_realizes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ middle after, ∃ latch : CellEffects.Invocation loop.latch, ∃ test : CellEffects.Invocation loop.header,
      CellEffects.system.Enables (Cells.encode keys (values (0xfffffffe#64) (0xffffffff#64))) latch ∧
      CellEffects.system.Enables (Cells.encode keys (loop.latchValues (values (0xfffffffe#64) (0xffffffff#64)))) test ∧
      (X86FuelPrefix.fetches 1).run (before (0xfffffffe#64) (0xffffffff#64)) = .ok () middle ∧
      middle.regs.get? .rip = some (4100#64) ∧
      (X86FuelPrefix.fetches 3).run (before (0xfffffffe#64) (0xffffffff#64)) = .ok () after ∧
      after.regs.get? .rip = some (4109#64) ∧
      loop.rank (loop.latchValues (values (0xfffffffe#64) (0xffffffff#64))) = 0 := by
  obtain ⟨middle, after, latch, test, latchEnabled, _, testEnabled, _, first, _, _, middleRip, run, _, _, _, rip, _⟩ :=
    realizes other extra vector _ 10 9 (input (0xfffffffe#64) (0xffffffff#64)) loop keys
      (values (0xfffffffe#64) (0xffffffff#64)) (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  exact ⟨middle, after, latch, test, latchEnabled, testEnabled, first, middleRip, run, rip, by decide⟩

/-- Without the strict source premise the native counter wraps and re-enters the body;
the source latch refuses that state. -/
theorem wrapped_counter_reenters (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (∃ after, (X86FuelPrefix.fetches 3).run (before (BitVec.allOnes 64) 5) = .ok () after ∧
      lookup after 10 = some 0 ∧ after.regs.get? .rip = some (4004#64)) ∧
    loop.latch.guard [4096, BitVec.allOnes 64, 5] [4100, 0] = false := by
  obtain ⟨after, run, _, indexRead, _, rip⟩ := outcome other extra vector (BitVec.allOnes 64) 5
  exact ⟨⟨after, run, by simpa using indexRead, by simpa using rip⟩, by decide⟩

private noncomputable def changedCondition : State :=
  { before 0 2 with mem := (before 0 2).mem.insert 4104 (0x83#8) }

theorem changed_condition_rejected : ¬codeLoaded changedCondition 4096 (code 10 9 (-105#32)) := by
  intro loaded
  have wrong := loaded 8 0x82 (by decide)
  simp [changedCondition, address] at wrong

private noncomputable def changedBackedge : State :=
  { before 0 2 with mem := (before 0 2).mem.insert 4105 (0x98#8) }

theorem changed_backedge_rejected : ¬codeLoaded changedBackedge 4096 (code 10 9 (-105#32)) := by
  intro loaded
  have wrong := loaded 9 0x97 (by decide)
  simp [changedBackedge, address] at wrong

example : code 10 9 (-224#32) = [0x49,0x83,0xc2,0x01,0x4d,0x39,0xca,0x0f,0x82,0x20,0xff,0xff,0xff] := by decide
example : code 10 9 (-224#32) ≠ code 10 9 (-223#32) := by decide
example : (testCode 10 9 (-224#32))[4]? = some 0x82 := by decide

end Controls
end Mettapedia.Machines.TIsa.X86LoopBottomLatch
