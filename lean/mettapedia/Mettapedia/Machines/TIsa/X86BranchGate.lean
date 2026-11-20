import Mettapedia.Machines.TIsa.X86Comparison
import Mettapedia.Machines.TIsa.X86EscapeFetch
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.Branch
import Mettapedia.Machines.TIsa.X86ControlFlags

/-!
# Generic fetched TEST/JZ gate and resource-branch realization

The nine actual bytes use any physical condition register and signed disp32.
The original Sail fetch/decode/execute function takes exactly two steps,
changes only flags and RIP, and retains every data register and memory byte.
Every fetched prefix satisfies the same frame.
The full gate also preserves every nonarithmetic RFLAGS bit.

For canonical Boolean inputs the destination agrees with the existing guarded
resource branch: the control token is consumed and produced while its condition
is kept. Non-Boolean words have no source branch even though hardware TEST would
accept them. Target geometry is checked with canonical signed addresses.

Backward/forward choice, all physical registers and altered register/displacement
controls are included. Branch-arm composition, loop lowering, full admission and
public ABI composition remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchGate
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (X86Arithmetic.linkedHandlers other) extra

def code (condition : Fin 16) (displacement : BitVec 32) : List Nat :=
  [(rex true condition condition).toNat,0x85,(modRM condition condition).toNat,0x0f,0x84] ++
    (List.range 4).map (fun index => (displacement.extractLsb' (8 * index) 8).toNat)

theorem code_length (condition : Fin 16) (displacement : BitVec 32) :
    (code condition displacement).length = 9 := by simp [code]

abbrev writes : Finset Register := {.rflags,.rip}
theorem writes_data : writes ⊆ dataRegisters := by decide

structure Inputs (native : State) (condition : Fin 16) extends X86LegacyFetch.Basis native where
  value : Word
  flags : BitVec 32
  valueKnown : lookup native condition = some value
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  upper : address.toInt + 9 < (2 ^ 47 : Int)
  displacement : BitVec 32
  target : BitVec 48
  jump : target.toInt = address.toInt + 9 + displacement.toInt
  loaded : codeLoaded native address.toInt (code condition displacement)

def position {native : State} {condition : Fin 16} (input : Inputs native condition) (offset : Nat) : BitVec 48 :=
  address input.address.toInt offset

theorem position_exact {native : State} {condition : Fin 16} (input : Inputs native condition)
    (offset : Nat) (within : offset ≤ 9) :
    (position input offset).toInt = input.address.toInt + offset :=
  address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper offset within

theorem shifted {native : State} {condition : Fin 16} (input : Inputs native condition)
    (offset index : Nat) (within : offset ≤ 9) :
    address (position input offset).toInt index = position input (offset + index) := by
  rw [position_exact input offset within]
  simp only [position, address, Int.natCast_add, Int.add_assoc]

theorem test_step_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (input : Inputs native condition) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step native after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (input.value = (0#64)) ∧
      after.regs.get? .rip = some ((position input 3).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := windowAt native native input.toBasis (RegisterFrame.refl dataRegisters native) input.upper 0 (by decide)
    (by simpa [position, address] using input.rip) (code condition input.displacement) input.loaded
    condition condition (0x85#8) (by simp [code]) (by simp [code]) (by simp [code])
  obtain ⟨output, executed, _, zero⟩ := X86Comparison.fetched_test64 (handlers other extra) vector native condition condition site
    input.value input.value input.flags input.valueKnown input.valueKnown input.flagsKnown input.quiet
  let flags := X86LogicalFlags.merged input.flags output (0#1)
  let after := X86Move.putPointer (X86Flags.putFlags native flags) site.next
  refine ⟨after, flags, executed, X86Comparison.status_frame _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags native flags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · have zeroFinal := (X86LogicalFlags.merged_zero input.flags output (0#1)).trans zero
    simp only [BitVec.and_self] at zeroFinal
    have zeroEq : input.value.toNat = 0 ↔ input.value = (0#64) := by
      change input.value.toNat = (0#64).toNat ↔ _
      exact BitVec.toNat_inj
    simp only [flags, X86BranchCondition.value, zeroFinal, X86BranchCondition.zero_sense, zeroEq]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl
  · unfold X86ControlFlags.Preserved
    have seen : after.regs.get? .rflags = some flags := by
      rw [(pointer_frame (X86Flags.putFlags native flags) site.next).registers .rflags (by decide)]
      simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
    rw [seen,input.flagsKnown]
    simp only [Option.map_some,flags,X86ControlFlags.logical_mask]


theorem test_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (input : Inputs native condition) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step native after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (input.value = (0#64)) ∧
      after.regs.get? .rip = some ((position input 3).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,read,sense,rip,_control⟩ := test_step_control other extra vector native condition input
  exact ⟨after,flags,run,frame,read,sense,rip⟩


theorem executes_control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (input : Inputs native condition) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      lookup after condition = some input.value ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if input.value = (0#64) then input.target else position input 9).signExtend 64) ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, flagsRead, sense, middleRip,middleControl⟩ := test_step_control other extra vector native condition input
  have loaded := framed.code_preserved input.address.toInt _ input.loaded
  have step1 : (position input 3).toInt + 1 = (position input 4).toInt := by
    rw [position_exact input 3 (by decide), position_exact input 4 (by decide)]
    omega
  have step2 : (position input 4).toInt + 1 = (position input 5).toInt := by
    rw [position_exact input 4 (by decide), position_exact input 5 (by decide)]
    omega
  have advance : (position input 5).toInt + 4 = (position input 9).toInt := by
    rw [position_exact input 5 (by decide), position_exact input 9 (by decide)]
    omega
  have jump : input.target.toInt = (position input 9).toInt + input.displacement.toInt := by
    rw [position_exact input 9 (by decide)]
    exact input.jump
  have displacement : ∀ index < 4,
      middle.mem.get? ((address (position input 5).toInt index).signExtend 52).toNat =
        some (input.displacement.extractLsb' (8 * index) 8) := by
    intro index within
    rw [shifted input 5 index (by decide)]
    have byte : (code condition input.displacement)[5 + index]? =
        some (input.displacement.extractLsb' (8 * index) 8).toNat := by
      unfold code
      rw [List.getElem?_append_right (by simp)]
      simp only [List.length_cons, List.length_nil]
      simp [within]
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ byte
  have last := X86EscapeFetch.fetched_branch (X86Arithmetic.linkedHandlers other) extra vector .zero middle
    (position input 3) (position input 4) (position input 5) (position input 9) input.target
    input.control input.attributes flags input.displacement step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans input.status)
    ((framed.registers .fault_reg (by decide)).trans input.fault)
    ((framed.registers .msrs (by decide)).trans input.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans input.segments)
    input.longMode input.codeMode ((framed.registers .app_view (by decide)).trans input.application)
    middleRip flagsRead ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 3 0x0f (by simp [code])) (loaded 4 0x84 (by simp [code])) displacement
  rw [sense] at last
  let target := if decide (input.value = (0#64)) then input.target else position input 9
  let after := X86Move.putPointer middle target
  have lastFrame := pointer_frame middle target
  refine ⟨after, flags, X86FuelPrefix.fetches_cons 1 native middle after first
    (X86FuelPrefix.fetches_one middle after last), (framed.trans lastFrame).mono (by decide),
    (lastFrame.lookup condition (by fin_cases condition <;> decide)).trans
      ((framed.lookup condition (by fin_cases condition <;> decide)).trans input.valueKnown),
    (lastFrame.registers .rflags (by decide)).trans flagsRead, ?_, ?_⟩
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self, target, decide_eq_true_eq]
  · exact middleControl.trans (X86ControlFlags.of_register_frame lastFrame (by decide))


theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (input : Inputs native condition) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      lookup after condition = some input.value ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some
        ((if input.value = (0#64) then input.target else position input 9).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,value,read,rip,_control⟩ := executes_control other extra vector native condition input
  exact ⟨after,flags,run,frame,value,read,rip⟩


theorem prefix_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (native : State) (condition : Fin 16)
    (input : Inputs native condition) (count : Nat) (within : count ≤ 2) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches count).run native = .ok () after ∧ RegisterFrame writes native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  interval_cases count
  · exact ⟨native, X86FuelPrefix.fetches_zero native, RegisterFrame.refl _ _⟩
  · obtain ⟨after, _, run, framed, _⟩ := test_step other extra vector native condition input
    exact ⟨after, X86FuelPrefix.fetches_one native after run, framed⟩
  · obtain ⟨after, _, run, framed, _⟩ := executes other extra vector native condition input
    exact ⟨after, run, framed⟩

/-- A source branch really fires its resource rule, and reaches the same PC as the fetched gate. -/
theorem realizes {Key : Type} [DecidableEq Key]
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (condition : Fin 16) (input : Inputs native condition)
    (branch : Control.Branch Key) (keys : Finset (Control.Location Key))
    (before : Control.Location Key → Word)
    (included : branch.recipe.support ⊆ keys)
    (current : before (.inl branch.activation) = branch.point)
    (reads : before (.inr branch.condition) = input.value)
    (canonical : input.value = 0 ∨ input.value = 1)
    (yes : branch.yes = (position input 9).signExtend 64)
    (no : branch.no = input.target.signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after next, ∃ invocation : CellEffects.Invocation branch.recipe,
      CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation =
        Cells.encode keys (Function.update before (.inl branch.activation) next) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧ RegisterFrame writes native after ∧
      after.regs.get? .rip = some next ∧ lookup after condition = some input.value := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let next := (if input.value = (0#64) then input.target else position input 9).signExtend 64
  have chosen : branch.target? (before (.inr branch.condition)) = some next := by
    rw [reads, branch.target?_iff]
    rcases canonical with zero | one
    · exact Or.inl ⟨zero, by simp [next, zero, no]⟩
    · exact Or.inr ⟨one, by simp [next, one, yes]⟩
  obtain ⟨invocation, enabled, fired⟩ := branch.realized keys before next included current chosen
  obtain ⟨after, flags, executed, framed, retained, _, rip⟩ := executes other extra vector native condition input
  exact ⟨after, next, invocation, enabled, fired, executed, framed, rip, retained⟩

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells (condition : Fin 16) : List (Nat × BitVec 8) :=
  (List.range 9).map fun index =>
    (4096 + index, BitVec.ofNat 8 (((code condition (-14#32))[index]?).getD 0))

private theorem distinct (condition : Fin 16) :
    (cells condition).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells condition).map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (condition : Fin 16) (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert (key condition) (cast (key_word condition).symm value)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells condition), (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 9) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide

private theorem image (condition : Fin 16) (value : Word) :
    codeLoaded (before condition value) 4096 (code condition (-14#32)) := by
  intro index byte present
  have within : index < 9 := by
    have := (List.getElem?_eq_some_iff.mp present).1
    rw [code_length] at this
    exact this
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells condition :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct condition) member

private def input (condition : Fin 16) (value : Word) : Inputs (before condition value) condition where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  fault := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  msrs := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  segments := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  rip := by fin_cases condition <;> simp [before, key, Std.ExtDHashMap.get?_insert]
  value := value
  flags := 0x246#32
  valueKnown := by
    fin_cases condition <;> simp [lookup, before, key, Std.ExtDHashMap.get?_insert] <;> rfl
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  upper := by decide
  displacement := -14#32
  target := 4091#48
  jump := by decide
  loaded := image condition value

noncomputable def entryFixture (condition : Fin 16) (value : Word) :
    Σ native : State, Inputs native condition :=
  ⟨before condition value, input condition value⟩

theorem backward_zero (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (condition : Fin 16) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before condition 0) = .ok () after ∧
      after.regs.get? .rip = some (4091#64) ∧ RegisterFrame writes (before condition 0) after := by
  obtain ⟨after, _, run, framed, _, _, rip⟩ := executes other extra vector _ condition (input condition 0)
  exact ⟨after, run, by simpa [input] using rip, framed⟩

theorem true_fallthrough (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (condition : Fin 16) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before condition 1) = .ok () after ∧
      after.regs.get? .rip = some (4105#64) ∧ RegisterFrame writes (before condition 1) after := by
  obtain ⟨after, _, run, framed, _, _, rip⟩ := executes other extra vector _ condition (input condition 1)
  exact ⟨after, run, by simpa [position, address, input] using rip, framed⟩

theorem nonboolean_source_refused (branch : Control.Branch Nat) : branch.target? 2 = none := by
  simp [Control.Branch.target?, RegisterProfile.truth]

theorem changed_displacement : code 11 (-14#32) ≠ code 11 (-13#32) := by decide
theorem changed_register : code 11 (-14#32) ≠ code 12 (-14#32) := by decide

end Controls

end Mettapedia.Machines.TIsa.X86BranchGate
