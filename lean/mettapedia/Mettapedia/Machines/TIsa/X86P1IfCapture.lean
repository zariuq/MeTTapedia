import Mettapedia.Machines.TIsa.X86P1CompareCapture
import Mettapedia.Machines.TIsa.X86NativeJcc

/-!
# Actual p1 IF-FLAGS and the joined LOAD/comparison/control prefix

One original fetched instruction executes the near JNE in the six-byte IF-FLAGS
span at image offset 74. It reads ZF as left by the preceding CMP-FLAGS span:
a clear ZF reaches the else arm at 552, a set ZF falls through to the then arm
at 80. The source IF tests register 7, the comparison's canonical Boolean; the
emitted pair decides the same arm without materializing that register.

The actual-image two-instruction comparison/IF join retains its source
condition and frame. The ten-instruction prefix also joins the complete first
LOAD, exposing its flags rather than assuming a clobbered field exists. Memory,
R11 and the full image are preserved. This ends before either branch body; the
complete consumer, admission and ABI are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1IfCapture

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def condition : X86NativeJcc.Condition := .ordinary .nonzero
def displacement : BitVec 32 := 472#32
def code : List Nat := X86NativeJcc.code condition displacement
abbrev writes : Finset Register := {.rip}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86ConditionByte.handlers (X86Arithmetic.linkedHandlers other) extra

theorem code_bytes : code = [0x0f,0x85,0xd8,1,0,0] := by decide

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 478 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 478) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem nonzero_sense (flags : BitVec 32) :
    X86BranchCondition.value .nonzero flags = !X86BranchCondition.value .zero flags := by
  simp only [X86BranchCondition.value]
  generalize Functions._get_rflagsbits_zf flags = bit
  revert bit
  decide

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 478 < (2 ^ 47 : Int)
  flags : BitVec 32
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state) extends Facts state origin where
  loaded : codeLoaded state origin.address.toInt code

theorem generic_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86EscapeFetch.linked (X86FrameIncrement.linkedHandlers (X86Arithmetic.linkedHandlers other))
      (X86ConditionByte.byteHandlers extra) = handlers other extra := by rfl

/-- A near JNE whose taken target lies `target` bytes after its start, at any placement. -/
theorem jne_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (delta : BitVec 32) (target : Nat)
    (upper : origin.address.toInt + target < (2 ^ 47 : Int)) (beyond : 6 ≤ target)
    (relative : (target : Int) = 6 + delta.toInt) (flags : BitVec 32)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (loaded : codeLoaded state origin.address.toInt (X86NativeJcc.code condition delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step state after ∧ RegisterFrame writes state after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((if X86BranchCondition.value .nonzero flags then address origin.address.toInt target
        else address origin.address.toInt 6).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let jcc : X86NativeJcc.Inputs state condition := {
    X86PlainFetch.Facts.ofBasis origin with
    start := origin.address
    target := address origin.address.toInt target
    flags := flags
    displacement := delta
    upper := by omega
    jump := by
      rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) upper target le_rfl]
      omega
    rip := origin.rip
    flagsKnown := flagsKnown
    quiet := quiet
    bytes := loaded }
  have run := X86NativeJcc.fetched (X86FrameIncrement.linkedHandlers (X86Arithmetic.linkedHandlers other))
    (X86ConditionByte.byteHandlers extra) vector state condition jcc
  refine ⟨_, run, pointer_frame state _, ?_, X86FuelPrefix.pointer_rip _ _⟩
  rw [(pointer_frame state _).registers .rflags (by decide)]
  exact flagsKnown

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (input : Inputs state origin) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Step state after ∧ RegisterFrame writes state after ∧
      after.regs.get? .rflags = some input.flags ∧
      after.regs.get? .rip = some ((if X86BranchCondition.value .nonzero input.flags then position origin.address 478
        else position origin.address 6).signExtend 64) :=
  jne_executes other extra vector state origin displacement 478 input.upper (by decide) (by decide) input.flags
    input.flagsKnown input.quiet input.loaded

theorem source_condition :
    (X86P1LoadCapture.propImage.source.body.atPath [1]).bind (fun statement => match statement with
      | .branch condition _ _ => some condition
      | _ => none) = some 7 := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 74 && span.length == 6 && span.kind == "IF-FLAGS" && span.path == some [1]) = true := by
  kernel_reflexivity

/-- The then arm begins at the first span under source path `[1,1]`; the else arm at the first
span under `[1,2]` is the refusal immediate at 552. -/
theorem arm_starts : X86P1LoadCapture.propImage.view.read 80 = some (0x49#8) ∧
    X86P1LoadCapture.propImage.view.read 552 = some (0xb8#8) ∧
    X86P1LoadCapture.propImage.view.read 553 = some (0#8) := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem captured_bytes (index : Fin 6) :
    X86P1LoadCapture.propImage.view.read (74 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 74)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 6 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    rwa [code, X86NativeJcc.code_length] at bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (74 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (74 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

theorem position_in_image (start : BitVec 48) (base : Int) (placed : start.toInt = base + 74) (offset : Nat) :
    position start offset = address base (74 + offset) := by
  unfold position address
  rw [placed]
  congr 1
  omega

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (facts : Facts state origin)
    (placed : origin.address.toInt = base + 74)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after ∧
      after.regs.get? .rflags = some facts.flags ∧
      after.regs.get? .rip = some
        ((if X86BranchCondition.value .nonzero facts.flags then address base 552 else address base 80).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : Inputs state origin := ⟨facts, captured_loaded state base origin placed loaded⟩
  obtain ⟨after, step, framed, flagsRead, rip⟩ := executes other extra vector state origin input
  refine ⟨after, X86FuelPrefix.fetches_one state after step, framed, flagsRead, ?_, ?_⟩
  · rw [position_in_image origin.address base placed 478, position_in_image origin.address base placed 6] at rip
    exact rip
  · intro offset within
    rw [framed.memory]
    exact loaded offset within

theorem compare_then_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1CompareCapture.Facts state origin) (placed : origin.address.toInt = base + 67)
    (imageUpper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame X86P1CompareCapture.writes state after ∧
      lookup after 10 = some (facts.value.zeroExtend 64) ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (facts.value = (6661#32)) ∧
      after.regs.get? .rip = some
        ((if facts.value = (6661#32) then address base 80 else address base 552).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input : X86P1CompareCapture.Inputs state origin :=
    ⟨facts, X86P1CompareCapture.captured_loaded state base origin placed loaded⟩
  obtain ⟨middle, flags, first, firstFrame, flagsRead, sense, firstRip⟩ :=
    X86P1CompareCapture.executes (X86Arithmetic.linkedHandlers other) extra vector state origin input
  have extent : origin.address.toInt + 485 < (2 ^ 47 : Int) := by omega
  let nextOrigin := rebase state middle origin (firstFrame.mono X86P1CompareCapture.writes_data)
    extent 7 (by decide) firstRip
  have nextPlaced : nextOrigin.address.toInt = base + 74 := by
    change (address origin.address.toInt 7).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) extent 7 (by decide)]
    omega
  have middleImage : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage middle base := by
    intro offset within
    rw [firstFrame.memory]
    exact loaded offset within
  let nextFacts : Facts middle nextOrigin := {
    upper := by rw [nextPlaced]; omega
    flags := flags
    flagsKnown := flagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, last, lastFrame, finalFlags, rip, image⟩ :=
    captured_executes other extra vector middle base nextOrigin nextFacts nextPlaced middleImage
  have finalFrame : RegisterFrame X86P1CompareCapture.writes state after :=
    (firstFrame.trans lastFrame).mono (by decide)
  refine ⟨after, flags, X86FuelPrefix.fetches_then 1 1 state middle after (X86FuelPrefix.fetches_one _ _ first) last,
    finalFrame, (finalFrame.lookup 10 (by decide)).trans facts.valueKnown, finalFlags, sense, ?_, image⟩
  change after.regs.get? .rip = some
    ((if X86BranchCondition.value .nonzero flags then address base 552 else address base 80).signExtend 64) at rip
  rw [nonzero_sense, sense, show input.value = facts.value from rfl] at rip
  by_cases same : facts.value = (6661#32)
  · simpa only [same, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true] using rip
  · simpa only [same, decide_false, Bool.not_false, if_true, if_false] using rip

theorem common_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1LoadBounds.handlers other (X86ConditionByte.byteHandlers extra) =
      handlers (X86Funding.Placed.baseHandlers other) extra := by rfl

theorem load_compare_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 10).run state = .ok () after ∧
      RegisterFrame {.rip,.rflags,.r14,.r15,.r10} state after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧
      after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (value = (6661#32)) ∧
      after.regs.get? .rip = some
        ((if value = (6661#32) then address base 80 else address base 552).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, loadFlags, first, firstFrame, valueRead, loadFlagsRead, firstRip, middleImage⟩ :=
    X86P1LoadCapture.load_observes other (X86ConditionByte.byteHandlers extra) vector state base origin facts placed
      loaded value readable fits
  rw [common_handlers] at first
  have firstData : DataFrame state middle := firstFrame.mono (by decide)
  have firstRipLocal : middle.regs.get? .rip = some ((address origin.address.toInt 43).signExtend 64) := by
    rw [firstRip]
    congr 2
    unfold address
    rw [placed]
    congr 1
    omega
  let cmpOrigin := rebase state middle origin firstData facts.upper 43 (by decide) firstRipLocal
  have cmpPlaced : cmpOrigin.address.toInt = base + 67 := by
    change (address origin.address.toInt 43).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) facts.upper 43 (by decide)]
    omega
  let cmpFacts : X86P1CompareCapture.Facts middle cmpOrigin := {
    upper := by rw [cmpPlaced]; have := facts.upper; omega
    value := value
    flags := loadFlags
    valueKnown := valueRead
    flagsKnown := loadFlagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, flags, last, lastFrame, finalValue, finalFlags, sense, rip, image⟩ :=
    compare_then_if (X86Funding.Placed.baseHandlers other) extra vector middle base cmpOrigin cmpFacts cmpPlaced
      (by have := facts.upper; omega) middleImage
  exact ⟨after, flags, X86FuelPrefix.fetches_then 8 2 state middle after first last,
    (firstFrame.trans lastFrame).mono (by decide), finalValue, finalFlags, sense, rip, image⟩

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 6).map (fun index => (4096 + index, BitVec.ofNat 8 ((code[index]?).getD 0)))

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : (cells.map Prod.fst).Nodup := by
    simp only [cells, List.map_map, Function.comp_def]
    decide
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (flags : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rflags flags
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem point (offset : Nat) (within : offset < 6) :
    ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide

private theorem image (flags : BitVec 32) : codeLoaded (before flags) 4096 code := by
  intro index byte present
  have within : index < 6 := by
    have within := (List.getElem?_eq_some_iff.mp present).1
    rwa [code, X86NativeJcc.code_length] at within
  have member : (4096 + index, BitVec.ofNat 8 byte) ∈ cells :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr within, by simp only [present, Option.getD_some]⟩
  rw [point index within]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private def origin (flags : BitVec 32) : X86LegacyFetch.Basis (before flags) where
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

private def input (flags : BitVec 32) : Inputs (before flags) (origin flags) where
  upper := by change (4096#48).toInt + 478 < (2 ^ 47 : Int); decide
  flags := flags
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  loaded := image flags

private theorem origin_address (flags : BitVec 32) : (origin flags).address = (4096#48) := rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (flags : BitVec 32) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before flags) = .ok () after ∧
      after.regs.get? .rip = some (if X86BranchCondition.value .nonzero flags then (4574#64) else (4102#64)) ∧
      after.mem = (before flags).mem := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, step, framed, _, rip⟩ := executes other extra vector _ _ (input flags)
  have thenTarget : (position (origin flags).address 6).signExtend 64 = (4102#64) := by
    rw [origin_address]
    rfl
  have elseTarget : (position (origin flags).address 478).signExtend 64 = (4574#64) := by
    rw [origin_address]
    rfl
  refine ⟨after, X86FuelPrefix.fetches_one _ _ step, ?_, framed.memory⟩
  change after.regs.get? .rip = some ((if X86BranchCondition.value .nonzero flags then
    position (origin flags).address 478 else position (origin flags).address 6).signExtend 64) at rip
  by_cases jumps : X86BranchCondition.value .nonzero flags = true
  · simpa only [jumps, if_true, elseTarget] using rip
  · simpa only [jumps, Bool.false_eq_true, if_false, thenTarget] using rip

/-- ZF set (RFLAGS `0x246`): the comparison matched, so control falls through to the then arm. -/
theorem equal_falls_through (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before (0x246#32)) = .ok () after ∧
      after.regs.get? .rip = some (4102#64) ∧ after.mem = (before (0x246#32)).mem := by
  have zeroSet : X86BranchCondition.value .nonzero (0x246#32) = false := by decide
  simpa only [zeroSet, Bool.false_eq_true, if_false] using control other extra vector (0x246#32)

/-- ZF clear (RFLAGS `0x206`): the comparison failed, so control jumps to the else arm. -/
theorem different_jumps (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run (before (0x206#32)) = .ok () after ∧
      after.regs.get? .rip = some (4574#64) ∧ after.mem = (before (0x206#32)).mem := by
  have zeroClear : X86BranchCondition.value .nonzero (0x206#32) = true := by decide
  simpa only [zeroClear, if_true] using control other extra vector (0x206#32)

/-- The previous TEST R11,R11 / JZ form is not the captured span: the image opens the span with
the escape byte `0x0f`, not the REX prefix `0x4d`. -/
theorem test_form_not_loaded : X86P1LoadCapture.propImage.view.read 74 = some (0x0f#8) := by
  kernel_reflexivity

end Controls

namespace PrefixControls

private theorem byte_bounds : (List.range 647).all
    (fun index => decide (Lean.RArray.get X86P1LoadCapture.propImage.data index ≤ 255)) = true := by
  kernel_reflexivity

private theorem byte_bound (index : Nat) (within : index < 647) :
    Lean.RArray.get X86P1LoadCapture.propImage.data index ≤ 255 := by
  exact of_decide_eq_true (List.all_eq_true.mp byte_bounds index (List.mem_range.mpr within))

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)

private noncomputable def cells (value : BitVec 32) : List (Nat × BitVec 8) :=
  (List.range 647).map (fun index =>
    (4096 + index, BitVec.ofNat 8 (Lean.RArray.get X86P1LoadCapture.propImage.data index))) ++
  (List.range 8).map (fun index => (8192 + index, (12288#64).extractLsb' (8 * index) 8)) ++
  (List.range 8).map (fun index => (8200 + index, (32#64).extractLsb' (8 * index) 8)) ++
  (List.range 4).map (fun index => (12288 + index, value.extractLsb' (8 * index) 8))

private def rangeKeys (base count : Nat) : List Nat := (List.range count).map (fun index => base + index)

private theorem range_nodup (base count : Nat) : (rangeKeys base count).Nodup := by
  change ((List.range count).map (fun index => base + index)).Nodup
  apply List.Nodup.map (f := fun index => base + index)
  · intro left right same
    dsimp only at same
    omega
  · exact List.nodup_range

private theorem range_apart (left size right count : Nat) (apart : left + size ≤ right) :
    ∀ x ∈ rangeKeys left size, ∀ y ∈ rangeKeys right count, x ≠ y := by
  intro x hx y hy same
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  have := List.mem_range.mp hi
  have := List.mem_range.mp hj
  omega

private theorem distinct (value : BitVec 32) :
    (cells value).Pairwise (fun left right => (left.1 == right.1) = false) := by
  have keys : ((cells value).map Prod.fst).Nodup := by
    simp only [cells, List.map_append, List.map_map, Function.comp_def]
    change (rangeKeys 4096 647 ++ rangeKeys 8192 8 ++ rangeKeys 8200 8 ++ rangeKeys 12288 4).Nodup
    simp only [List.nodup_append, range_nodup, true_and, List.mem_append, or_imp, forall_and]
    repeat' constructor
    all_goals exact range_apart _ _ _ _ (by decide)
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using keys

private noncomputable def before (value : BitVec 32) (old : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4120#64)
  let registers := registers.insert .rdi (8192#64)
  let registers := registers.insert .rsi (12288#64)
  let registers := registers.insert .r10 (0xffffffffffffffff#64)
  let registers := registers.insert .r11 old
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList (cells value), (), 0, #[]⟩

private theorem cell (value : BitVec 32) (old : Word) (key : Nat) (byte : BitVec 8)
    (present : (key, byte) ∈ cells value) : (before value old).mem.get? key = some byte :=
  Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct value) present

private theorem positive_address (base offset : Nat) (within : base + offset < 2 ^ 47) :
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

private theorem image (value : BitVec 32) (old : Word) :
    X86P1LoadCapture.Loaded X86P1LoadCapture.propImage (before value old) 4096 := by
  intro index within
  have bounded : index < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
  have member : (4096 + index, BitVec.ofNat 8 (Lean.RArray.get X86P1LoadCapture.propImage.data index)) ∈ cells value := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr bounded, rfl⟩
  have place := positive_address 4096 index (by omega)
  change ((address 4096 index).signExtend 52).toNat = 4096 + index at place
  rw [place, cell value old _ _ member]
  simp only [P1Capture.Program.view, if_pos within]
  rw [show Nat.ble (Lean.RArray.get X86P1LoadCapture.propImage.data index) 255 = true from
    Nat.ble_eq.mpr (byte_bound index bounded)]
  rfl

private def origin (value : BitVec 32) (old : Word) : X86LegacyFetch.Basis (before value old) where
  address := 4120#48
  opcodeAddress := 4121#48
  modrmAddress := 4122#48
  next := 4123#48
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

private def facts (value : BitVec 32) (old : Word) :
    X86P1LoadBounds.Facts (before value old) (origin value old) 623 where
  upper := by change (4120#48).toInt + 623 < (2 ^ 47 : Int); decide
  frame := 8192#64
  base := 12288#64
  pointer := 12288#64
  length := 32#64
  baseAddress := 8192#48
  lengthAddress := 8200#48
  controls := controls
  visible := visible
  flags := 0x200#32
  frameKnown := by
    change ((before value old).regs.get? .rdi).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  pointerKnown := by
    change ((before value old).regs.get? .rsi).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  baseEffective := by decide
  lengthEffective := by decide
  baseUpper := by decide
  lengthUpper := by decide
  baseAligned := by decide
  lengthAligned := by decide
  controlKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  baseBytes := by
    intro index within
    change (before value old).mem.get? ((address 8192 index).signExtend 52).toNat = _
    have place := positive_address 8192 index (by omega)
    change ((address 8192 index).signExtend 52).toNat = 8192 + index at place
    rw [place]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩
  lengthBytes := by
    intro index within
    change (before value old).mem.get? ((address 8200 index).signExtend 52).toNat = _
    have place := positive_address 8200 index (by omega)
    change ((address 8200 index).signExtend 52).toNat = 8200 + index at place
    rw [place]
    apply cell
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

private def readable (value : BitVec 32) (old : Word) :
    X86P1LoadBounds.Readable (before value old) (12288#64) value where
  dataAddress := 12288#48
  effective := by decide
  upper := by decide
  aligned := by decide
  bytes := by
    intro index within
    change (before value old).mem.get? ((address 12288 index).signExtend 52).toNat = _
    have place := positive_address 12288 index (by omega)
    change ((address 12288 index).signExtend 52).toNat = 12288 + index at place
    rw [place]
    apply cell
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

structure Fixture (value : BitVec 32) (old : Word) where
  state : State
  origin : X86LegacyFetch.Basis state
  facts : X86P1LoadBounds.Facts state origin 623
  readable : X86P1LoadBounds.Readable state facts.pointer value
  placed : origin.address.toInt = 4096 + 24
  image : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state 4096
  fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat
  oldKnown : lookup state 11 = some old
  frameValue : facts.frame = (8192#64)

noncomputable def fixture (value : BitVec 32) (old : Word) : Fixture value old where
  state := before value old
  origin := origin value old
  facts := facts value old
  readable := readable value old
  placed := by change (4120#48).toInt = 4096 + 24; decide
  image := image value old
  fits := by change (12288#64 - (12288#64)).toNat + 4 ≤ (32#64).toNat; decide
  oldKnown := by
    change ((before value old).regs.get? .r11).map (fun word : Word => word) = _
    simp [before, Std.ExtDHashMap.get?_insert]
  frameValue := rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (value : BitVec 32) (old : Word) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (before value old) = .ok () after ∧
      lookup after 10 = some (value.zeroExtend 64) ∧ lookup after 11 = some old ∧
      after.regs.get? .rip = some
        ((if value = (6661#32) then address 4096 80 else address 4096 552).signExtend 64) ∧
      after.mem = (before value old).mem := by
  let : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, executed, framed, valueRead, _, _, rip, _⟩ :=
    X86P1IfCapture.load_compare_if other extra vector _ 4096 _ (facts value old)
      (by change (4120#48).toInt = 4096 + 24; decide) (image value old) value (readable value old)
      (by change (12288#64 - (12288#64)).toNat + 4 ≤ (32#64).toNat; decide)
  exact ⟨after, executed, valueRead, (framed.lookup 11 (by decide)).trans (fixture value old).oldKnown, rip,
    framed.memory⟩

theorem matching_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (before (6661#32) (0xfedcba9876543210#64)) = .ok () after ∧
      lookup after 10 = some (6661#64) ∧ lookup after 11 = some (0xfedcba9876543210#64) ∧
      after.regs.get? .rip = some (4176#64) ∧ after.mem = (before (6661#32) (0xfedcba9876543210#64)).mem := by
  obtain ⟨after, executed, valueRead, oldRead, rip, memory⟩ :=
    control other extra vector (6661#32) (0xfedcba9876543210#64)
  rw [show (6661#32).zeroExtend 64 = (6661#64) from rfl] at valueRead
  rw [if_pos rfl] at rip
  change after.regs.get? .rip = some (4176#64) at rip
  exact ⟨after, executed, valueRead, oldRead, rip, memory⟩

theorem different_tag (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (before (6660#32) (0xffffffffffffffff#64)) = .ok () after ∧
      lookup after 10 = some (6660#64) ∧ lookup after 11 = some (0xffffffffffffffff#64) ∧
      after.regs.get? .rip = some (4648#64) ∧ after.mem = (before (6660#32) (0xffffffffffffffff#64)).mem := by
  obtain ⟨after, executed, valueRead, oldRead, rip, memory⟩ :=
    control other extra vector (6660#32) (0xffffffffffffffff#64)
  rw [show (6660#32).zeroExtend 64 = (6660#64) from rfl] at valueRead
  rw [if_neg (show (6660#32) ≠ (6661#32) from by decide)] at rip
  change after.regs.get? .rip = some (4648#64) at rip
  exact ⟨after, executed, valueRead, oldRead, rip, memory⟩

end PrefixControls

end Mettapedia.Machines.TIsa.X86P1IfCapture
