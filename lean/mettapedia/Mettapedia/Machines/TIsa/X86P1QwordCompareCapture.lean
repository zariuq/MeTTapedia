import Mettapedia.Machines.TIsa.X86QwordZero
import Mettapedia.Machines.TIsa.X86ConditionByte
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Captured full-word zero comparison

One original fetched instruction executes CMP R10,0 in the seven-byte CMP-FLAGS
span at 136..142 of R_DERIVE_IS_PROP, source node [1,1,0,1]. For every 64-bit
input the zero flag holds exactly when the source comparison's Boolean is one,
including inputs whose low dword is zero. The Boolean is not materialized: the
following IF-FLAGS jump is its only reader. Memory and all registers outside
RFLAGS/RIP are preserved. The following branch and consumer remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1QwordCompareCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary


def code : List Nat := [0x49,0x81,0xfa,0,0,0,0]
abbrev writes : Finset Register := {.rip,.rflags}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86ConditionByte.handlers

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 7 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 7) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by simp [position, address]

theorem position_shift (start : BitVec 48) (upper : start.toInt + 7 < (2 ^ 47 : Int))
    (offset index : Nat) (within : offset ≤ 7) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact start upper offset within]
  simp only [position, address, Nat.cast_add, Int.add_assoc]

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 7 < (2 ^ 47 : Int)
  value : Word
  flags : BitVec 32
  valueKnown : lookup state 10 = some value
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
      X86BranchCondition.value .zero flags = decide (input.value = (0#64)) ∧
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
        some ((0#32).extractLsb' (8 * index) 8) := by
    intro index within
    change state.mem.get? ((address (position origin.address 3).toInt index).signExtend 52).toNat = _
    rw [position_shift origin.address input.upper 3 index (by decide)]
    have byte : code[3 + index]? = some ((0#32).extractLsb' (8 * index) 8).toNat := by
      interval_cases index <;> rfl
    simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.loaded _ _ byte
  obtain ⟨output, executed, zero⟩ := X86QwordZero.fetched (handlers other extra) vector state site
    (position origin.address 7) input.value input.flags advance input.valueKnown input.flagsKnown input.quiet
    (by simpa only [site, rebase, position_zero] using input.loaded 0 0x49 (by rfl))
    (input.loaded 1 0x81 (by rfl)) (input.loaded 2 0xfa (by rfl)) immediate
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags state flags) (position origin.address 7)
  refine ⟨after, flags, executed, (X86Comparison.status_frame state flags (position origin.address 7)).mono (by decide), ?_,
    X86QwordZero.equal_sense _ _ zero, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags state flags) (position origin.address 7)).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem captured_bytes (index : Fin 7) :
    X86P1LoadCapture.propImage.view.read (136 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem source_instruction : X86P1LoadCapture.propImage.source.body.atPath [1,1,0,1] =
    some (.instruction (.compare .equal .u64 7 6 (.immediate 0))) := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 136 && span.length == 7 && span.kind == "CMP-FLAGS" && span.path == some [1,1,0,1]) = true := by
  kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 136)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have within : index < 7 := (List.getElem?_eq_some_iff.mp present).1
  have captured := captured_bytes ⟨index,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (136 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (136 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 136) (offset : Nat) :
    position start offset = address base (136 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

theorem captured_observes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : Facts state origin) (placed : origin.address.toInt = base + 136)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 10 = some facts.value ∧ after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (facts.value = (0#64)) ∧
      after.regs.get? .rip = some ((address base 143).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : Inputs state origin := ⟨facts,captured_loaded state base origin placed loaded⟩
  obtain ⟨after,flags,step,frame,flagsRead,sense,rip⟩ := executes other extra vector state origin input
  refine ⟨after,flags,X86FuelPrefix.fetches_one state after step,frame,
    (frame.lookup 10 (by decide)).trans facts.valueKnown,flagsRead,sense,?_,?_⟩
  · simpa only [position_in_image origin.address base placed] using rip
  · intro offset within
    rw [frame.memory]
    exact loaded offset within

#print axioms executes
#print axioms captured_bytes

def sourceInstruction : P1Source.Instr := .compare .equal .u64 7 6 (.immediate 0)

theorem source_value (value : Word) :
    P1Scalar.evaluate sourceInstruction [value] = some (booleanWord (decide (value = 0))) := by
  change some (booleanWord (value == (0#64))) = some (booleanWord (decide (value = (0#64))))
  have equal : (value == (0#64)) = decide (value = (0#64)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
  rw [equal]

theorem resource_step (keys : Finset P1Source.Reg) (before : P1Source.Reg → Word) (value : Word)
    (included : (P1Scalar.recipe sourceInstruction 7).support ⊆ keys) (valueRead : before 6 = value) :
    (CellEffects.profile [P1Scalar.recipe sourceInstruction 7]).theory.rewrites (Cells.encode keys before)
      (Cells.encode keys (Function.update before 7 (booleanWord (decide (value = 0))))) := by
  apply (P1Scalar.rewrite_iff sourceInstruction 7 keys before _).mpr
  refine ⟨_,included,?_,rfl⟩
  change P1Scalar.evaluate sourceInstruction [before 6] = _
  rw [valueRead,source_value]


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

private noncomputable def before (value : Word) (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .r10 value
  let registers := registers.insert .r11 old
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 7) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
  interval_cases offset <;> decide

private theorem image (value : Word) (old : Word) : codeLoaded (before value old) 4096 code := by
  intro index byte present
  have within : index < 7 := by
    have within := (List.getElem?_eq_some_iff.mp present).1
    change index < 7 at within
    exact within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def origin (value : Word) (old : Word) : X86LegacyFetch.Basis (before value old) where
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

private def input (value : Word) (old : Word) : Inputs (before value old) (origin value old) where
  upper := by change (4096#48).toInt + 7 < (2 ^ 47 : Int); decide
  value := value
  flags := 0x200#32
  valueKnown := by
    change ((before value old).regs.get? .r10).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  loaded := image value old

private theorem origin_address (value : Word) (old : Word) : (origin value old).address = (4096#48) := rfl

private theorem r11_before (value : Word) (old : Word) : lookup (before value old) 11 = some old := by
  change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
  simp [before, Std.ExtDHashMap.get?_insert]

/-- One fetch decides the full word in ZF, keeps R10 and leaves an arbitrary old R11 untouched. -/
theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : Word) (old : Word) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before value old) = .ok () after ∧
      lookup after 10 = some value ∧ lookup after 11 = some old ∧
      X86BranchCondition.value .zero flags = decide (value = (0#64)) ∧ after.regs.get? .rflags = some flags ∧
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
  change lookup after 10 = some (input value old).value
  exact (framed.lookup 10 (by decide)).trans (input value old).valueKnown

theorem zero_matches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before (0#64) (0xfedcba9876543210#64)) = .ok () after ∧
      X86BranchCondition.value .zero flags = true ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (4103#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, run, -, -, sense, flagsRead, rip, -⟩ := control other extra vector (0#64) (0xfedcba9876543210#64)
  exact ⟨after, flags, run, by simpa using sense, flagsRead, rip⟩

/-- A zero low dword does not satisfy the full-width comparison. -/
theorem high_word_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run (before (0x100000000#64) (0xffffffffffffffff#64)) = .ok () after ∧
      X86BranchCondition.value .zero flags = false ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some (4103#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, flags, run, -, -, sense, flagsRead, rip, -⟩ :=
    control other extra vector (0x100000000#64) (0xffffffffffffffff#64)
  exact ⟨after, flags, run, by simpa using sense, flagsRead, rip⟩

/-- The previously emitted SETE R11B no longer follows the comparison: the image holds the
IF-FLAGS JNE bytes `0x0f 0x85` at 143 and 144. -/
theorem no_materialized_boolean :
    X86P1LoadCapture.propImage.view.read 143 = some (0x0f#8) ∧
    X86P1LoadCapture.propImage.view.read 144 = some (0x85#8) := by
  constructor <;> kernel_reflexivity

private noncomputable def changedRex : State :=
  { before (0x100000000#64) (0xffffffffffffffff#64) with
    mem := (before (0x100000000#64) (0xffffffffffffffff#64)).mem.insert 4096 (0x41#8) }

theorem changed_width_rejected : ¬ codeLoaded changedRex 4096 code := by
  intro loaded
  have wrong := loaded 0 0x49 (by rfl)
  simp [changedRex,address] at wrong

end Controls

#print axioms resource_step
#print axioms Controls.zero_matches
#print axioms Controls.high_word_refuses


end Mettapedia.Machines.TIsa.X86P1QwordCompareCapture
