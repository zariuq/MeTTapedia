import Mettapedia.Machines.TIsa.X86ControlFlags
import Mettapedia.Machines.TIsa.X86BranchGate
import Mettapedia.Machines.TIsa.Loop

/-!
# Native unsigned loop header as an existing resource guard

The nine actual bytes encode CMP index,bound and near JAE. Original Sail
fetch/decode/execute reaches the exit target when bound <= index and the body
fallthrough otherwise, in exactly two instructions. Both operands and all
memory are retained; every fetched prefix changes only flags and RIP.

Under the source loop's admitted index/bound invariant, the result realizes
its actual guarded control-token firing. No Boolean data cell is introduced.
Zero bound, final admitted iteration, reached bound and an altered condition
have executable proof controls. Entry/cap validation, body/latch composition,
fuel, early exits and public ABI remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LoopHeader
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers := X86BranchGate.handlers
abbrev writes : Finset Register := X86BranchGate.writes

def code (index bound : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(rex true bound index).toNat,0x39,(modRM bound index).toNat,0x0f,0x83] ++
    (List.range 4).map (fun position => (displacement.extractLsb' (8 * position) 8).toNat)

theorem code_length (index bound : Fin 16) (displacement : BitVec 32) :
    (code index bound displacement).length = 9 := by simp [code]

structure Inputs (native : State) (index bound : Fin 16) extends X86LegacyFetch.Basis native where
  indexValue : Word
  boundValue : Word
  flags : BitVec 32
  indexKnown : lookup native index = some indexValue
  boundKnown : lookup native bound = some boundValue
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  upper : address.toInt + 9 < (2 ^ 47 : Int)
  displacement : BitVec 32
  target : BitVec 48
  jump : target.toInt = address.toInt + 9 + displacement.toInt
  loaded : codeLoaded native address.toInt (code index bound displacement)

def position {native : State} {index bound : Fin 16} (input : Inputs native index bound) (offset : Nat) : BitVec 48 :=
  address input.address.toInt offset

theorem position_exact {native : State} {index bound : Fin 16} (input : Inputs native index bound)
    (offset : Nat) (within : offset ≤ 9) :
    (position input offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem shifted {native : State} {index bound : Fin 16} (input : Inputs native index bound)
    (offset slot : Nat) (within : offset ≤ 9) :
    address (position input offset).toInt slot = position input (offset + slot) := by
  rw [position_exact input offset within]
  simp only [position, address, Int.natCast_add, Int.add_assoc]

theorem compare_step_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step native after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .aboveEqual flags = decide (input.boundValue.toNat ≤ input.indexValue.toNat) ∧
      after.regs.get? .rip = some ((position input 3).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := windowAt native native input.toBasis (RegisterFrame.refl dataRegisters native) input.upper 0 (by decide)
    (by simpa [position, address] using input.rip) (code index bound input.displacement) input.loaded
    bound index (0x39#8) (by simp [code]) (by simp [code]) (by simp [code])
  obtain ⟨output, executed, carry, _⟩ := X86Comparison.fetched_compare64 (handlers other extra) vector native bound index site
    input.indexValue input.boundValue input.flags input.boundKnown input.indexKnown input.flagsKnown input.quiet
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags native flags) site.next
  refine ⟨after, flags, executed, X86Comparison.status_frame _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags native flags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · rw [X86BranchCondition.value, X86Comparison.merged_carry, carry, X86BranchCondition.unsigned_sense]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl
  · unfold X86ControlFlags.Preserved
    have seen : after.regs.get? .rflags = some flags := by
      rw [(pointer_frame (X86Flags.putFlags native flags) site.next).registers .rflags (by decide)]
      simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
    rw [seen,input.flagsKnown]
    simp only [Option.map_some,flags,X86ControlFlags.arithmetic_mask]


theorem compare_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step native after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .aboveEqual flags = decide (input.boundValue.toNat ≤ input.indexValue.toNat) ∧
      after.regs.get? .rip = some ((position input 3).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,read,sense,rip,_control⟩ := compare_step_control other extra vector native index bound input
  exact ⟨after,flags,run,frame,read,sense,rip⟩


theorem executes_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      lookup after index = some input.indexValue ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if input.boundValue.toNat ≤ input.indexValue.toNat then input.target else position input 9).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, flagsRead, sense, middleRip,middleControl⟩ := compare_step_control other extra vector native index bound input
  have loaded := framed.code_preserved input.address.toInt _ input.loaded
  have step1 : (position input 3).toInt + 1 = (position input 4).toInt := by
    rw [position_exact input 3 (by decide), position_exact input 4 (by decide)]; omega
  have step2 : (position input 4).toInt + 1 = (position input 5).toInt := by
    rw [position_exact input 4 (by decide), position_exact input 5 (by decide)]; omega
  have advance : (position input 5).toInt + 4 = (position input 9).toInt := by
    rw [position_exact input 5 (by decide), position_exact input 9 (by decide)]; omega
  have jump : input.target.toInt = (position input 9).toInt + input.displacement.toInt := by
    rw [position_exact input 9 (by decide)]; exact input.jump
  have displacement : ∀ slot < 4,
      middle.mem.get? ((address (position input 5).toInt slot).signExtend 52).toNat =
        some (input.displacement.extractLsb' (8 * slot) 8) := by
    intro slot within
    rw [shifted input 5 slot (by decide)]
    have byte : (code index bound input.displacement)[5 + slot]? =
        some (input.displacement.extractLsb' (8 * slot) 8).toNat := by
      unfold code
      rw [List.getElem?_append_right (by simp)]
      simp only [List.length_cons, List.length_nil]
      simp [within]
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ byte
  have last := X86EscapeFetch.fetched_branch (X86Arithmetic.linkedHandlers other) extra vector .aboveEqual middle
    (position input 3) (position input 4) (position input 5) (position input 9) input.target
    input.control input.attributes flags input.displacement step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans input.status)
    ((framed.registers .fault_reg (by decide)).trans input.fault)
    ((framed.registers .msrs (by decide)).trans input.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans input.segments)
    input.longMode input.codeMode ((framed.registers .app_view (by decide)).trans input.application)
    middleRip flagsRead ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 3 0x0f (by simp [code])) (loaded 4 0x83 (by simp [code])) displacement
  rw [sense] at last
  let target := if decide (input.boundValue.toNat ≤ input.indexValue.toNat) then input.target else position input 9
  let after := X86Move.putPointer middle target
  have lastFrame := pointer_frame middle target
  refine ⟨after, flags, X86FuelPrefix.fetches_cons 1 native middle after first
    (X86FuelPrefix.fetches_one middle after last), (framed.trans lastFrame).mono (by decide),
    (lastFrame.lookup index (by fin_cases index <;> decide)).trans
      ((framed.lookup index (by fin_cases index <;> decide)).trans input.indexKnown),
    (lastFrame.lookup bound (by fin_cases bound <;> decide)).trans
      ((framed.lookup bound (by fin_cases bound <;> decide)).trans input.boundKnown),
    (lastFrame.registers .rflags (by decide)).trans flagsRead, ?_, ?_⟩
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self, target, decide_eq_true_eq]
  · exact middleControl.trans (X86ControlFlags.of_register_frame lastFrame (by decide))


theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      lookup after index = some input.indexValue ∧ lookup after bound = some input.boundValue ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if input.boundValue.toNat ≤ input.indexValue.toNat then input.target else position input 9).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip,_control⟩ := executes_control other extra vector native index bound input
  exact ⟨after,flags,run,frame,indexRead,boundRead,flagsRead,rip⟩


theorem prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound) (count : Nat) (within : count ≤ 2) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches count).run native = .ok () after ∧ RegisterFrame writes native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  interval_cases count
  · exact ⟨native, X86FuelPrefix.fetches_zero native, RegisterFrame.refl _ _⟩
  · obtain ⟨after, _, run, framed, _⟩ := compare_step other extra vector native index bound input
    exact ⟨after, X86FuelPrefix.fetches_one native after run, framed⟩
  · obtain ⟨after, _, run, framed, _⟩ := executes other extra vector native index bound input
    exact ⟨after, run, framed⟩

theorem realizes {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (input : Inputs native index bound)
    (loop : Control.Loop Key) (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : loop.header.support ⊆ keys) (checked : loop.check = true)
    (current : before (.inl loop.activation) = loop.headerPoint)
    (indexRead : before (.inr loop.index) = input.indexValue)
    (boundRead : before (.inr loop.bound) = input.boundValue)
    (ordered : input.indexValue.toNat ≤ input.boundValue.toNat)
    (bounded : input.boundValue.toNat ≤ loop.maximum)
    (body : loop.bodyPoint = (position input 9).signExtend 64)
    (exit : loop.exitPoint = input.target.signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ invocation : CellEffects.Invocation loop.header,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation = Cells.encode keys (loop.headerValues before) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rip = some (loop.headerValues before (.inl loop.activation)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨invocation, enabled, fired⟩ := loop.header_realized keys before included checked current
    (by simpa only [indexRead, boundRead] using ordered) (by simpa only [boundRead] using bounded)
  obtain ⟨after, _, run, framed, _, _, _, rip⟩ := executes other extra vector native index bound input
  refine ⟨after, invocation, enabled, fired, run, framed, ?_⟩
  by_cases less : input.indexValue.toNat < input.boundValue.toNat
  · have notAbove : ¬input.boundValue.toNat ≤ input.indexValue.toNat := by omega
    simpa only [Control.Loop.headerValues, Function.update_self, Control.Loop.headerTarget,
      indexRead, boundRead, if_pos less, if_neg notAbove, body] using rip
  · have above : input.boundValue.toNat ≤ input.indexValue.toNat := by omega
    simpa only [Control.Loop.headerValues, Function.update_self, Control.Loop.headerTarget,
      indexRead, boundRead, if_neg less, if_pos above, exit] using rip

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map fun offset => (4096 + offset, BitVec.ofNat 8 (((code 12 13 (55#32))[offset]?).getD 0))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def before (index bound : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r12 index
  let registers := registers.insert .r13 bound
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem image (index bound : Word) : codeLoaded (before index bound) 4096 (code 12 13 (55#32)) := by
  intro offset byte present
  have within : offset < 9 := by
    have := (List.getElem?_eq_some_iff.mp present).1
    rw [code_length] at this
    exact this
  have point : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide
  have member : (4096 + offset, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨offset, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def input (index bound : Word) : Inputs (before index bound) 12 13 where
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
  upper := by decide
  displacement := 55#32
  target := 4160#48
  jump := by decide
  loaded := image index bound

theorem outcome (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (index bound : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before index bound) = .ok () after ∧ RegisterFrame writes (before index bound) after ∧
      after.regs.get? .rip = some (if bound.toNat ≤ index.toNat then (4160#64) else (4105#64)) := by
  obtain ⟨after, _, run, framed, _, _, _, rip⟩ := executes other extra vector _ 12 13 (input index bound)
  refine ⟨after, run, framed, ?_⟩
  by_cases above : bound.toNat ≤ index.toNat <;> simpa [above, input, position, address] using rip

theorem zero_bound_exits (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before 0 0) = .ok () after ∧
      after.regs.get? .rip = some (4160#64) := by
  obtain ⟨after, run, _, rip⟩ := outcome other extra vector 0 0
  exact ⟨after, run, rip⟩

theorem last_iteration_continues (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before (0xfffffffe#64) (0xffffffff#64)) = .ok () after ∧
      after.regs.get? .rip = some (4105#64) := by
  obtain ⟨after, run, _, rip⟩ := outcome other extra vector (0xfffffffe#64) (0xffffffff#64)
  exact ⟨after, run, rip⟩

theorem reached_bound_exits (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before (0xffffffff#64) (0xffffffff#64)) = .ok () after ∧
      after.regs.get? .rip = some (4160#64) := by
  obtain ⟨after, run, _, rip⟩ := outcome other extra vector (0xffffffff#64) (0xffffffff#64)
  exact ⟨after, run, rip⟩

private noncomputable def changed : State := { before 0 0 with mem := (before 0 0).mem.insert 4100 (0x82#8) }

theorem changed_condition_rejected : ¬codeLoaded changed 4096 (code 12 13 (55#32)) := by
  intro loaded
  have wrong := loaded 4 0x83 (by simp [code])
  simp [changed, address] at wrong

end Controls
end Mettapedia.Machines.TIsa.X86LoopHeader
