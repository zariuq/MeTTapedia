import Mettapedia.Machines.TIsa.X86P1TagCompare
import Mettapedia.Machines.TIsa.X86ConditionByte
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Actual p1 tag comparison composed through original fetched execution

The seven-byte CMP-FLAGS span in R_DERIVE_IS_PROP is CMP R10D,6661. One
original fetched instruction sets the zero flag exactly when the loaded U32
value equals the source immediate, for every value. Memory, R10 and all other
registers outside RFLAGS/RIP are preserved.

The source comparison writes its canonical Boolean to register 7. The emitted
code leaves that Boolean in ZF only: the following IF-FLAGS jump is the
register's sole reader, so it is never materialized in R11. The complete span
is checked against the named p1 image and its source instruction; its scalar
resource firing uses the existing recipe library. The following IF, complete
consumer, admission and ABI remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1CompareCapture

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def code : List Nat := [0x41,0x81,0xfa,5,0x1a,0,0]
abbrev writes : Finset Register := {.rip,.rflags}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86ConditionByte.handlers

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 7 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 7) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by simp [position, address]

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 7 < (2 ^ 47 : Int)
  value : BitVec 32
  flags : BitVec 32
  valueKnown : lookup state 10 = some (value.zeroExtend 64)
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends Facts state origin where
  loaded : codeLoaded state origin.address.toInt code

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, Step state after ∧ RegisterFrame writes state after ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (input.value = (6661#32)) ∧
      after.regs.get? .rip = some ((position origin.address 7).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have rip : state.regs.get? .rip = some ((position origin.address 0).signExtend 64) := by
    simpa only [position_zero] using origin.rip
  let site := rebase state state origin (RegisterFrame.refl dataRegisters state) input.upper 0 (by decide) rip
  have advance : (position origin.address 3).toInt + 4 = (position origin.address 7).toInt := by
    rw [position_exact _ input.upper 3 (by decide), position_exact _ input.upper 7 (by decide)]
    omega
  have immediate : ∀ index < 4,
      state.mem.get? ((address site.next.toInt index).signExtend 52).toNat =
        some ((6661#32).extractLsb' (8 * index) 8) := by
    intro index within
    change state.mem.get? ((address (position origin.address 3).toInt index).signExtend 52).toNat = _
    rw [position_exact origin.address input.upper 3 (by decide)]
    have byte : code[3 + index]? = some ((6661#32).extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    have shifted : address (origin.address.toInt + (3 : Nat)) index = address origin.address.toInt (3 + index) := by
      simp only [address, Nat.cast_add, Int.add_assoc]
    rw [shifted]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded _ _ byte
  obtain ⟨output, executed, zero⟩ := X86P1TagCompare.fetched_cmp32 (handlers other extra) vector state site
    (position origin.address 7) input.value input.flags advance input.valueKnown input.flagsKnown input.quiet
    (by simpa only [site, rebase, position_zero] using input.loaded 0 0x41 (by rfl))
    (input.loaded 1 0x81 (by rfl)) (input.loaded 2 0xfa (by rfl)) immediate
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags state flags) (position origin.address 7)
  refine ⟨after, flags, executed, (X86P1TagCompare.result_frame _ _ _ _).mono (by decide), ?_,
    X86P1TagCompare.equal_sense _ _ zero, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags state flags) (position origin.address 7)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

def sourceInstruction : P1Source.Instr := .compare .equal .u32z 7 6 (.immediate 6661)

theorem source_instruction : X86P1LoadCapture.propImage.source.body.atPath [0, 1] =
    some (.instruction sourceInstruction) := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 67 && span.length == 7 && span.kind == "CMP-FLAGS" && span.path == some [0, 1]) = true := by
  kernel_reflexivity

theorem captured_bytes (index : Fin 7) :
    X86P1LoadCapture.propImage.view.read (67 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 67)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 7 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 7 at bounded
    exact bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (67 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (67 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 67) (offset : Nat) :
    position start offset = address base (67 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 67)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 10 = some (facts.value.zeroExtend 64) ∧ after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (facts.value = (6661#32)) ∧
      after.regs.get? .rip = some ((address base 74).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : Inputs state origin := ⟨facts, captured_loaded state base origin placed loaded⟩
  obtain ⟨after, flags, step, framed, flagsRead, sense, rip⟩ := executes other extra vector state origin input
  refine ⟨after, flags, X86FuelPrefix.fetches_one state after step, framed,
    (framed.lookup 10 (by decide)).trans facts.valueKnown, flagsRead, sense, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 7] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem source_value (value : BitVec 32) :
    P1Scalar.evaluate sourceInstruction [value.zeroExtend 64] =
      some (booleanWord (decide (value = (6661#32)))) := by
  have low : low32 (value.zeroExtend 64) = value := low32_extend32 false value
  change some (booleanWord (low32 (value.zeroExtend 64) == low32 (6661#64))) = _
  rw [low]
  change some (booleanWord (value == (6661#32))) = _
  by_cases same : value = (6661#32)
  · simp [same]
  · rw [show (value == (6661#32)) = false from beq_eq_false_iff_ne.mpr same]
    simp [same]

theorem resource_step (keys : Finset P1Source.Reg) (before : P1Source.Reg → Word) (value : BitVec 32)
    (included : (P1Scalar.recipe sourceInstruction 7).support ⊆ keys)
    (valueRead : before 6 = value.zeroExtend 64) :
    (CellEffects.profile [P1Scalar.recipe sourceInstruction 7]).theory.rewrites (Cells.encode keys before)
      (Cells.encode keys (Function.update before 7 (booleanWord (decide (value = (6661#32)))))) := by
  apply (P1Scalar.rewrite_iff sourceInstruction 7 keys before _).mpr
  refine ⟨_, included, ?_, rfl⟩
  change P1Scalar.evaluate sourceInstruction [before 6] = _
  rw [valueRead, source_value]

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 7).map (fun index => (4096 + index, BitVec.ofNat 8 ((code[index]?).getD 0)))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (value : BitVec 32) (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 (value.zeroExtend 64)
  let registers := registers.insert .r11 old
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 7) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
  interval_cases offset <;> decide

private theorem image (value : BitVec 32) (old : Word) : codeLoaded (before value old) 4096 code := by
  intro index byte present
  have within : index < 7 := by
    have within := (List.getElem?_eq_some_iff.mp present).1
    change index < 7 at within
    exact within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def origin (value : BitVec 32) (old : Word) : X86LegacyFetch.Basis (before value old) where
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

private def input (value : BitVec 32) (old : Word) : Inputs (before value old) (origin value old) where
  upper := by change (4096#48).toInt + 7 < (2 ^ 47 : Int); decide
  value := value
  flags := 0x200#32
  valueKnown := by
    change ((before value old).regs.get? .r10).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  loaded := image value old

private theorem origin_address (value : BitVec 32) (old : Word) : (origin value old).address = (4096#48) := rfl

private theorem r11_before (value : BitVec 32) (old : Word) : lookup (before value old) 11 = some old := by
  change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
  simp [before, Std.ExtDHashMap.get?_insert]

/-- One fetch decides the tag in ZF, keeps R10 and leaves an arbitrary old R11 untouched. -/
theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : BitVec 32) (old : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before value old) = .ok () after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧ lookup after 11 = some old ∧
      X86BranchCondition.value .zero flags = decide (value = (6661#32)) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (4103#64) ∧ after.mem = (before value old).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, step, framed, flagsRead, sense, rip⟩ := executes other extra vector _ _ (input value old)
  have next : ((position (origin value old).address 7).signExtend 64) = (4103#64) := by
    rw [origin_address]
    rfl
  rw [next] at rip
  refine ⟨after, flags, X86FuelPrefix.fetches_one _ _ step, ?_, (framed.lookup 11 (by decide)).trans (r11_before value old),
    sense, flagsRead, rip, framed.memory⟩
  change lookup after 10 = some ((input value old).value.zeroExtend 64)
  exact (framed.lookup 10 (by decide)).trans (input value old).valueKnown

theorem matching_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before (6661#32) (0xfedcba9876543210#64)) = .ok () after ∧
      X86BranchCondition.value .zero flags = true ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (4103#64) := by
  obtain ⟨after, flags, run, -, -, sense, flagsRead, rip, -⟩ :=
    control other extra vector (6661#32) (0xfedcba9876543210#64)
  exact ⟨after, flags, run, by simpa using sense, flagsRead, rip⟩

theorem different_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before (6660#32) (0xffffffffffffffff#64)) = .ok () after ∧
      X86BranchCondition.value .zero flags = false ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (4103#64) := by
  obtain ⟨after, flags, run, -, -, sense, flagsRead, rip, -⟩ :=
    control other extra vector (6660#32) (0xffffffffffffffff#64)
  exact ⟨after, flags, run, by simpa using sense, flagsRead, rip⟩

/-- The previously emitted SETE R11B no longer follows the comparison: the image holds the
IF-FLAGS escape byte `0x0f` and JNE opcode `0x85` at 74 and 75, not `0x41 0x0f 0x94`. -/
theorem no_materialized_boolean :
    X86P1LoadCapture.propImage.view.read 74 = some (0x0f#8) ∧
    X86P1LoadCapture.propImage.view.read 75 = some (0x85#8) := by
  constructor <;> kernel_reflexivity

end Controls

end Mettapedia.Machines.TIsa.X86P1CompareCapture
