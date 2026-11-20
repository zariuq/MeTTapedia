import Mettapedia.Machines.TIsa.X86RegisterIncrement
import Mettapedia.Machines.TIsa.X86UnconditionalJump
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Native counter latch and source resource firing

The nine actual bytes execute register ADD one and a signed near JMP. The
original fetched instructions update only the counter, flags and RIP; every
prefix preserves all memory and the remaining registers. The jump target is
checked against the raw signed displacement and canonical address geometry.

For an admitted source latch, the result realizes the existing TAKE/KEEP/MAKE
firing, retains the bound and reaches its header token. The strict index/bound
premise proves that the native counter does not wrap and that the source rank
strictly decreases. This does not replace whole-loop or body-invariant proofs.

A last-iteration control at the maximum admitted bound exercises both native
instructions and the actual resource firing. Prefix frames, a refused source
latch at the bound and a changed backedge byte have separate controls. Entry,
body/iteration composition, fuel, early exits and public ABI remain open.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LoopLatch
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameIncrement.linkedHandlers (X86UnconditionalJump.linked other)

def code (index : Fin 16) (displacement : BitVec 32) : List Nat :=
  X86RegisterIncrement.code index ++ X86UnconditionalJump.Block.code displacement

theorem code_length (index : Fin 16) (displacement : BitVec 32) : (code index displacement).length = 9 := by
  simp [code, X86RegisterIncrement.code, X86UnconditionalJump.Block.code_length]

structure Inputs (native : State) (index : Fin 16) extends X86LegacyFetch.Basis native where
  value : Word
  flags : BitVec 32
  valueKnown : lookup native index = some value
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  upper : address.toInt + 9 < (2 ^ 47 : Int)
  displacement : BitVec 32
  target : BitVec 48
  jump : target.toInt = address.toInt + 9 + displacement.toInt
  loaded : codeLoaded native address.toInt (code index displacement)

def incrementInput {native : State} {index : Fin 16} (input : Inputs native index) : X86RegisterIncrement.Inputs native index := {
  input.toBasis with
  value := input.value
  flags := input.flags
  valueKnown := input.valueKnown
  flagsKnown := input.flagsKnown
  quiet := input.quiet
  upper := by have := input.upper; omega
  loaded := by
    intro offset byte present
    apply input.loaded offset byte
    rw [code, List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
    exact present }

theorem executes_control (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index : Fin 16) (input : Inputs native index) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (input.value + 1) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (input.target.signExtend 64) ∧
      X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 2, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, valueRead, flagsRead, rip, middleControl⟩ :=
    X86RegisterIncrement.executes_control (X86UnconditionalJump.linked other) vector native index (incrementInput input)
  let origin := X86StateFrame.rebase native middle input.toBasis (X86StateFrame.registerOnly framed)
    (X86RegisterIncrement.writes_data index) (extent := 9) input.upper 4 (by decide) rip
  have placed : origin.address.toInt = input.address.toInt + 4 :=
    address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 4 (by decide)
  let jumpInput : X86UnconditionalJump.Block.Inputs middle := {
    origin with
    quiet := (framed.registers .log_register_writes (by fin_cases index <;> decide)).trans input.quiet
    upper := by rw [placed]; have := input.upper; omega
    displacement := input.displacement
    target := input.target
    jump := by rw [placed]; have := input.jump; omega
    loaded := by
      intro offset byte present
      have inWhole : (code index input.displacement)[4 + offset]? = some byte := by
        rw [code, List.getElem?_append_right (by simp [X86RegisterIncrement.code]),
          show (X86RegisterIncrement.code index).length = 4 by rfl, Nat.add_sub_cancel_left]
        exact present
      have byte := framed.code_preserved input.address.toInt _ input.loaded (4 + offset) byte inWhole
      rw [placed]
      simpa only [address, Int.natCast_add, Int.add_assoc, Nat.cast_ofNat] using byte }
  obtain ⟨last, lastFrame⟩ := X86UnconditionalJump.Block.executes (X86FrameIncrement.linkedHandlers other) vector middle jumpInput
  let after := X86Move.putPointer middle input.target
  have combined := X86FuelPrefix.fetches_then 1 1 native middle after first (X86FuelPrefix.fetches_one middle after last)
  have combinedFrame : RegisterFrame (X86RegisterIncrement.writes index) native after :=
    (framed.trans lastFrame).mono (by simp [X86RegisterIncrement.writes])
  refine ⟨after, flags, combined, combinedFrame, ?_, ?_, ?_, ?_, ?_⟩
  · exact (lastFrame.lookup index (by fin_cases index <;> decide)).trans valueRead
  · exact (lastFrame.registers .rflags (by decide)).trans flagsRead
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
  · exact middleControl.trans (X86ControlFlags.of_register_frame lastFrame (by decide))
  · intro count within reached executed
    have known : ∃ proved, (X86FuelPrefix.fetches count).run native = .ok () proved ∧
        RegisterFrame (X86RegisterIncrement.writes index) native proved := by
      interval_cases count
      · exact ⟨native, X86FuelPrefix.fetches_zero native, RegisterFrame.refl _ _⟩
      · exact ⟨middle, first, framed⟩
      · exact ⟨after, combined, combinedFrame⟩
    obtain ⟨proved, run, preserved⟩ := known
    have same := X86FuelPrefix.fetches_deterministic count native proved reached run executed
    subst reached
    exact preserved

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index : Fin 16) (input : Inputs native index) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (input.value + 1) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (input.target.signExtend 64) ∧
      ∀ count ≤ 2, ∀ reached, (X86FuelPrefix.fetches count).run native = .ok () reached →
        RegisterFrame (X86RegisterIncrement.writes index) native reached := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,read,rip,_control,prefixes⟩ := executes_control other vector native index input
  exact ⟨after,flags,run,frame,value,read,rip,prefixes⟩


theorem bound_outside (index bound : Fin 16) (distinct : bound ≠ index) :
    key bound ∉ X86RegisterIncrement.writes index := by
  simp only [X86RegisterIncrement.writes, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun same => distinct (key_injective same), by fin_cases bound <;> decide, by fin_cases bound <;> decide⟩

theorem realizes {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (index bound : Fin 16) (distinct : bound ≠ index) (input : Inputs native index)
    (loop : Control.Loop Key) (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : loop.latch.support ⊆ keys) (checked : loop.check = true)
    (current : before (.inl loop.activation) = loop.latchPoint)
    (indexRead : before (.inr loop.index) = input.value)
    (boundRead : lookup native bound = some (before (.inr loop.bound)))
    (less : input.value.toNat < (before (.inr loop.bound)).toNat)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum)
    (target : loop.headerPoint = input.target.signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ invocation : CellEffects.Invocation loop.latch,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation = Cells.encode keys (loop.latchValues before) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame (X86RegisterIncrement.writes index) native after ∧
      lookup after index = some (loop.latchValues before (.inr loop.index)) ∧
      lookup after bound = some (loop.latchValues before (.inr loop.bound)) ∧
      after.regs.get? .rip = some (loop.latchValues before (.inl loop.activation)) ∧
      (loop.latchValues before (.inr loop.index)).toNat = input.value.toNat + 1 ∧
      loop.rank (loop.latchValues before) < loop.rank before := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨invocation, enabled, fired, decreases⟩ := loop.latch_realized keys before included checked current
    (by simpa only [indexRead] using less) bounded
  obtain ⟨after, _, run, framed, result, _, rip, _⟩ := executes other vector native index input
  have sourceDistinct : loop.index ≠ loop.bound := (of_decide_eq_true checked).1
  refine ⟨after, invocation, enabled, fired, run, framed, ?_, ?_, ?_, ?_, decreases⟩
  · simpa only [Control.Loop.latchValues, Function.update_self, indexRead] using result
  · have retained := (framed.lookup bound (bound_outside index bound distinct)).trans boundRead
    simpa [Control.Loop.latchValues, Ne.symm sourceDistinct] using retained
  · simpa [Control.Loop.latchValues, target] using rip
  · simpa only [Control.Loop.latchValues, Function.update_self, indexRead] using
      Control.counter_increment_no_wrap input.value (before (.inr loop.bound)) less

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map fun offset => (4096 + offset, BitVec.ofNat 8 (((code 10 (-105#32))[offset]?).getD 0))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide
private def loop : Control.Loop Nat := ⟨0,3999,4000,4096,4009,4105,0,1,4294967295⟩
private def keys : Finset (Control.Location Nat) := {.inl 0,.inr 0,.inr 1}
private def values : Control.Location Nat → Word
  | .inl _ => 4096
  | .inr 0 => 0xfffffffe#64
  | .inr _ => 0xffffffff#64

private noncomputable def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 (0xfffffffe#64)
  let registers := registers.insert .r9 (0xffffffff#64)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem image : codeLoaded before 4096 (code 10 (-105#32)) := by
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

private def input : Inputs before 10 where
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
  value := 0xfffffffe#64
  flags := 0x246#32
  valueKnown := by simp [lookup, before, key, Std.ExtDHashMap.get?_insert]; rfl
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  displacement := -105#32
  target := 4000#48
  jump := by decide
  loaded := image

theorem last_iteration (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ invocation : CellEffects.Invocation loop.latch,
      CellEffects.system.Enables (Cells.encode keys values) invocation ∧
      CellEffects.system.fire (Cells.encode keys values) invocation = Cells.encode keys (loop.latchValues values) ∧
      (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      lookup after 10 = some (0xffffffff#64) ∧ lookup after 9 = some (0xffffffff#64) ∧
      after.regs.get? .rip = some (4000#64) ∧ loop.rank (loop.latchValues values) = 0 := by
  obtain ⟨after, invocation, enabled, fired, run, _, indexRead, boundRead, rip, _, _⟩ :=
    realizes other vector before 10 9 (by decide) input loop keys values (by decide) (by decide) (by rfl)
      (by rfl) (by simp [lookup, before, key, Std.ExtDHashMap.get?_insert, values, loop]; rfl)
      (by decide) (by decide) (by rfl)
  exact ⟨after, invocation, enabled, fired, run, indexRead, boundRead, rip, by decide⟩

theorem prefixes_preserve_frame (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (count : Nat) (within : count ≤ 2) (after : State) :
    letI : OtherOpcodeHandlers := handlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches count).run before = .ok () after →
      lookup after 4 = lookup before 4 ∧ lookup after 7 = lookup before 7 ∧
        ∀ address, after.mem.get? address = before.mem.get? address := by
  let : OtherOpcodeHandlers := handlers other
  let : VectorOpcodeHandlers := vector
  intro run
  obtain ⟨_, _, _, _, _, _, _, prefixes⟩ := executes other vector before 10 input
  have preserved := prefixes count within after run
  exact ⟨preserved.lookup 4 (by decide), preserved.lookup 7 (by decide),
    fun address => by rw [preserved.memory]⟩

theorem reached_bound_source_refused : loop.latch.guard
    [4096,0xffffffff#64,0xffffffff#64] [4000,0x100000000#64] = false := by decide

private noncomputable def changed : State := { before with mem := before.mem.insert 4101 (0x98#8) }

theorem changed_backedge_rejected : ¬codeLoaded changed 4096 (code 10 (-105#32)) := by
  intro loaded
  have wrong := loaded 5 0x97 (by rfl)
  simp [changed, address] at wrong

end Controls
end Mettapedia.Machines.TIsa.X86LoopLatch
