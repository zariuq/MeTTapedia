import Mettapedia.Machines.TIsa.X86P1QwordCompareCapture
import Mettapedia.Machines.TIsa.X86P1QwordLoadCapture
import Mettapedia.Machines.TIsa.X86P1IfCapture

/-!
# Actual full-word field guard in the consumer image

The full-width CMP-FLAGS span at 136..142 feeds the near JNE in the IF-FLAGS
span at 143..148. A zero field falls through to output construction at 149;
any nonzero field, including one with a zero low dword, jumps to the refusal
block at 524.

The twelve-instruction load/comparison/IF join preserves the full image and
memory and relates the branch to the source comparison through ZF. Joining
the first tag guard takes ten instructions on mismatch and twenty-two on match;
the mismatch path needs no second-field bytes. Neither guard writes R11.
Concrete full-image controls preserve an explicit stack pointer and distinguish
zero from 2^32. Output stores, completion handlers, public ABI and actual
admission remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1QwordGuardCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def displacement : BitVec 32 := 375#32
def code : List Nat := X86NativeJcc.code X86P1IfCapture.condition displacement
abbrev writes : Finset Register := {.rip}
theorem writes_data : writes ⊆ dataRegisters := by decide
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86P1IfCapture.handlers other extra

theorem code_bytes : code = [0x0f,0x85,0x77,1,0,0] := by decide

structure Facts (state : State) (origin : X86LegacyFetch.Basis state) where
  upper : origin.address.toInt + 381 < (2 ^ 47 : Int)
  flags : BitVec 32
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false

theorem source_condition :
    (X86P1LoadCapture.propImage.source.body.atPath [1,1,1]).bind (fun statement => match statement with
      | .branch condition _ _ => some condition
      | _ => none) = some 7 := by kernel_reflexivity

theorem containing_span : X86P1LoadCapture.propImage.spans.any (fun span =>
    span.offset == 143 && span.length == 6 && span.kind == "IF-FLAGS" && span.path == some [1,1,1]) = true := by
  kernel_reflexivity

theorem captured_bytes (index : Fin 6) :
    X86P1LoadCapture.propImage.view.read (143 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

/-- The fall-through arm begins with the first output immediate and the jump target is the
refusal immediate `mov eax, 0`. -/
theorem arm_starts : X86P1LoadCapture.propImage.view.read 149 = some (0x41#8) ∧
    X86P1LoadCapture.propImage.view.read 524 = some (0xb8#8) ∧
    X86P1LoadCapture.propImage.view.read 525 = some (0#8) := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 143)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have within : index < 6 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    rwa [code, X86NativeJcc.code_length] at bounded
  have captured := captured_bytes ⟨index,within⟩
  rw [present,Option.map_some] at captured
  have shifted : address base (143 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (143 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans captured

theorem shifted_address (start : BitVec 48) (base : Int) (placed : start.toInt = base + 143) (offset : Nat) :
    address start.toInt offset = address base (143 + offset) := by
  unfold address
  rw [placed]
  congr 1
  omega

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state) (facts : Facts state origin)
    (placed : origin.address.toInt = base + 143)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after ∧
      after.regs.get? .rflags = some facts.flags ∧
      after.regs.get? .rip = some
        ((if X86BranchCondition.value .nonzero facts.flags then address base 524 else address base 149).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, step, framed, flagsRead, rip⟩ := X86P1IfCapture.jne_executes other extra vector state origin
    displacement 381 facts.upper (by decide) (by decide) facts.flags facts.flagsKnown facts.quiet
    (captured_loaded state base origin placed loaded)
  rw [shifted_address origin.address base placed 381, shifted_address origin.address base placed 6] at rip
  refine ⟨after, X86FuelPrefix.fetches_one state after step, framed, flagsRead, rip, ?_⟩
  intro offset within
  rw [framed.memory]
  exact loaded offset within

theorem compare_then_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1QwordCompareCapture.Facts state origin) (placed : origin.address.toInt = base + 136)
    (imageUpper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      RegisterFrame X86P1QwordCompareCapture.writes state after ∧
      lookup after 10 = some facts.value ∧ after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (facts.value = (0#64)) ∧
      after.regs.get? .rip = some
        ((if facts.value = (0#64) then address base 149 else address base 524).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, firstFrame, valueRead, flagsRead, sense, firstRip, middleImage⟩ :=
    X86P1QwordCompareCapture.captured_observes (X86Arithmetic.linkedHandlers other) extra vector state base origin
      facts placed loaded
  have extent : origin.address.toInt + 388 < (2 ^ 47 : Int) := by omega
  have relativeRip : middle.regs.get? .rip = some ((address origin.address.toInt 7).signExtend 64) := by
    rw [firstRip]
    congr 2
    unfold address
    rw [placed]
    congr 1
    omega
  let nextOrigin := rebase state middle origin (firstFrame.mono X86P1QwordCompareCapture.writes_data)
    extent 7 (by decide) relativeRip
  have nextPlaced : nextOrigin.address.toInt = base + 143 := by
    change (address origin.address.toInt 7).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) extent 7 (by decide)]
    omega
  let nextFacts : Facts middle nextOrigin := {
    upper := by rw [nextPlaced]; omega
    flags := flags
    flagsKnown := flagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, last, lastFrame, finalFlags, rip, image⟩ :=
    captured_executes other extra vector middle base nextOrigin nextFacts nextPlaced middleImage
  have finalFrame : RegisterFrame X86P1QwordCompareCapture.writes state after :=
    (firstFrame.trans lastFrame).mono (by decide)
  refine ⟨after, flags, X86FuelPrefix.fetches_then 1 1 state middle after first last, finalFrame,
    (lastFrame.lookup 10 (by decide)).trans valueRead, finalFlags, sense, ?_, image⟩
  change after.regs.get? .rip = some
    ((if X86BranchCondition.value .nonzero flags then address base 524 else address base 149).signExtend 64) at rip
  rw [X86P1IfCapture.nonzero_sense, sense] at rip
  by_cases zero : facts.value = (0#64)
  · simpa only [zero, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true] using rip
  · simpa only [zero, decide_false, Bool.not_false, if_true, if_false] using rip

theorem common_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Bounds.handlers other (X86ConditionByte.byteHandlers extra) =
      handlers (X86Funding.Placed.baseHandlers other) extra := by rfl

theorem load_compare_if (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 567) (placed : origin.address.toInt = base + 80)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (value : Word) (readable : X86P1QwordBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 24 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 12).run state = .ok () after ∧
      RegisterFrame {.rip,.rflags,.r14,.r15,.r10} state after ∧
      lookup after 10 = some value ∧ after.regs.get? .rflags = some flags ∧
      X86BranchCondition.value .zero flags = decide (value = (0#64)) ∧
      after.regs.get? .rip = some
        ((if value = (0#64) then address base 149 else address base 524).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, loadFlags, first, firstFrame, valueRead, loadFlagsRead, firstRip, middleImage⟩ :=
    X86P1QwordLoadCapture.load_observes other (X86ConditionByte.byteHandlers extra) vector state base origin facts
      placed loaded value readable fits
  rw [common_handlers] at first
  have firstData : DataFrame state middle := firstFrame.mono (by decide)
  have relativeRip : middle.regs.get? .rip = some ((address origin.address.toInt 56).signExtend 64) := by
    rw [firstRip]
    congr 2
    unfold address
    rw [placed]
    congr 1
    omega
  let cmpOrigin := rebase state middle origin firstData facts.upper 56 (by decide) relativeRip
  have cmpPlaced : cmpOrigin.address.toInt = base + 136 := by
    change (address origin.address.toInt 56).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) facts.upper 56 (by decide)]
    omega
  let cmpFacts : X86P1QwordCompareCapture.Facts middle cmpOrigin := {
    upper := by rw [cmpPlaced]; have := facts.upper; omega
    value := value
    flags := loadFlags
    valueKnown := valueRead
    flagsKnown := loadFlagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet }
  obtain ⟨after, flags, last, lastFrame, finalValue, finalFlags, sense, rip, image⟩ :=
    compare_then_if (X86Funding.Placed.baseHandlers other) extra vector middle base cmpOrigin cmpFacts cmpPlaced
      (by have := facts.upper; omega) middleImage
  exact ⟨after, flags, X86FuelPrefix.fetches_then 10 2 state middle after first last,
    (firstFrame.trans lastFrame).mono (by decide), finalValue, finalFlags, sense, rip, image⟩

theorem two_guard_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 623) (placed : origin.address.toInt = base + 24)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (tag : BitVec 32) (tagReadable : X86P1LoadBounds.Readable state facts.pointer tag)
    (tagFits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (value : Word) (fieldReadable : tag = (6661#32) → X86P1QwordBounds.Readable state facts.pointer value)
    (fieldFits : tag = (6661#32) → (facts.pointer - facts.base).toNat + 24 ≤ facts.length.toNat) :
    letI : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (if tag = (6661#32) then 22 else 10)).run state = .ok () after ∧
      RegisterFrame {.rip,.rflags,.r14,.r15,.r10} state after ∧
      lookup after 10 = some (if tag = (6661#32) then value else tag.zeroExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ after.regs.get? .rip = some
        ((if tag = (6661#32) then (if value = (0#64) then address base 149 else address base 524)
          else address base 552).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers (X86Funding.Placed.baseHandlers other) extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,firstFlags,first,firstFrame,tagRead,firstFlagsRead,_,firstRip,middleImage⟩ :=
    X86P1IfCapture.load_compare_if other extra vector state base origin facts placed loaded tag tagReadable tagFits
  by_cases matching : tag = (6661#32)
  · have fallthrough : middle.regs.get? .rip = some ((address base 80).signExtend 64) := by
      simpa only [if_pos matching] using firstRip
    have relativeRip : middle.regs.get? .rip = some ((address origin.address.toInt 56).signExtend 64) := by
      have point : address origin.address.toInt 56 = address base 80 := by
        unfold address
        rw [placed]
        congr 1
        omega
      rw [point]
      exact fallthrough
    let nextOrigin := rebase state middle origin (firstFrame.mono (by decide)) facts.upper 56 (by decide) relativeRip
    have nextPlaced : nextOrigin.address.toInt = base + 80 := by
      change (address origin.address.toInt 56).toInt = _
      rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address) facts.upper 56 (by decide)]
      omega
    let nextFacts : X86P1LoadBounds.Facts middle nextOrigin 567 := {
      upper := by rw [nextPlaced]; have := facts.upper; omega
      frame := facts.frame
      base := facts.base
      pointer := facts.pointer
      length := facts.length
      baseAddress := facts.baseAddress
      lengthAddress := facts.lengthAddress
      controls := facts.controls
      visible := facts.visible
      flags := firstFlags
      frameKnown := (firstFrame.lookup 7 (by decide)).trans facts.frameKnown
      pointerKnown := (firstFrame.lookup 6 (by decide)).trans facts.pointerKnown
      baseEffective := facts.baseEffective
      lengthEffective := facts.lengthEffective
      baseUpper := facts.baseUpper
      lengthUpper := facts.lengthUpper
      baseAligned := facts.baseAligned
      lengthAligned := facts.lengthAligned
      controlKnown := (firstFrame.registers .ctrs (by decide)).trans facts.controlKnown
      visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans facts.visibleKnown
      flagsKnown := firstFlagsRead
      quiet := (firstFrame.registers .log_register_writes (by decide)).trans facts.quiet
      baseBytes := by intro index within; rw [firstFrame.memory]; exact facts.baseBytes index within
      lengthBytes := by intro index within; rw [firstFrame.memory]; exact facts.lengthBytes index within }
    let readable := fieldReadable matching
    let nextReadable : X86P1QwordBounds.Readable middle nextFacts.pointer value := {
      dataAddress := readable.dataAddress
      effective := readable.effective
      upper := readable.upper
      aligned := readable.aligned
      bytes := by intro index within; rw [firstFrame.memory]; exact readable.bytes index within }
    obtain ⟨after,flags,last,lastFrame,valueRead,flagsRead,_,rip,image⟩ :=
      load_compare_if other extra vector middle base nextOrigin nextFacts nextPlaced middleImage value nextReadable
        (fieldFits matching)
    refine ⟨after,flags,?_,(firstFrame.trans lastFrame).mono (by decide),?_,flagsRead,?_,image⟩
    · simpa only [if_pos matching] using X86FuelPrefix.fetches_then 10 12 state middle after first last
    · simpa only [if_pos matching] using valueRead
    · simpa only [if_pos matching] using rip
  · exact ⟨middle,firstFlags,by simpa only [if_neg matching] using first,firstFrame,
      by simpa only [if_neg matching] using tagRead,firstFlagsRead,
      by simpa only [if_neg matching] using firstRip,middleImage⟩

namespace Controls

/-- The previous TEST R11,R11 / JZ guard is not the captured span: it opens with the escape
byte `0x0f`, not the REX prefix `0x4d`, and its displacement byte is `0x77`. -/
theorem test_form_not_loaded : X86P1LoadCapture.propImage.view.read 143 = some (0x0f#8) ∧
    X86P1LoadCapture.propImage.view.read 145 = some (0x77#8) := by
  constructor <;> kernel_reflexivity

end Controls

namespace PrefixControls

private noncomputable def initial (tag : BitVec 32) (old : Word) :=
  X86P1IfCapture.PrefixControls.fixture tag old

private noncomputable def before (tag : BitVec 32) (value old : Word) : State :=
  X86WriteWords.storeBytes 8 (put (initial tag old).state 4 (16384#64)) (12304#48) value

private abbrev written := X86WriteWords.written (12304#48) (List.range 8)

private theorem before_frame (tag : BitVec 32) (value old : Word) :
    X86StateFrame.Frame {.rsp} written (initial tag old).state (before tag value old) := by
  have stack : X86StateFrame.Frame {.rsp} ∅ (initial tag old).state (put (initial tag old).state 4 (16384#64)) := by
    simpa only [show key (4 : Fin 16) = .rsp from rfl] using
      X86StateFrame.registerOnly (put_frame (initial tag old).state 4 (16384#64))
  exact (stack.trans (X86WriteWords.storeBytes_frame 8 _ (12304#48) value)).mono (by simp) (by simp)

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

private theorem written_lower (key : Nat) (member : key ∈ written) : 12304 ≤ key := by
  obtain ⟨index,within,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have bounded : index < 8 := List.mem_range.mp within
  have point : X86WriteWords.physicalAddress (12304#48) index = 12304 + index := by
    exact positive_address 12304 index (by omega)
  rw [← same,point]
  omega

private theorem outside (base offset : Nat) (below : base + offset < 12304) :
    ((address (base : Int) offset).signExtend 52).toNat ∉ written := by
  rw [positive_address base offset (by omega)]
  intro member
  have := written_lower _ member
  omega

private noncomputable def origin (tag : BitVec 32) (value old : Word) : X86LegacyFetch.Basis (before tag value old) :=
  X86StateFrame.basisAt (initial tag old).state (before tag value old) (initial tag old).origin
    (before_frame tag value old) (by decide) (4120#48) (by decide)
    (by rw [(before_frame tag value old).registers .rip (by decide)]; exact (initial tag old).origin.rip)

private noncomputable def facts (tag : BitVec 32) (value old : Word) :
    X86P1LoadBounds.Facts (before tag value old) (origin tag value old) 623 where
  upper := by change (4120#48).toInt + 623 < (2 ^ 47 : Int); decide
  frame := (initial tag old).facts.frame
  base := (initial tag old).facts.base
  pointer := (initial tag old).facts.pointer
  length := (initial tag old).facts.length
  baseAddress := (initial tag old).facts.baseAddress
  lengthAddress := (initial tag old).facts.lengthAddress
  controls := (initial tag old).facts.controls
  visible := (initial tag old).facts.visible
  flags := (initial tag old).facts.flags
  frameKnown := ((before_frame tag value old).lookup 7 (by decide)).trans (initial tag old).facts.frameKnown
  pointerKnown := ((before_frame tag value old).lookup 6 (by decide)).trans (initial tag old).facts.pointerKnown
  baseEffective := (initial tag old).facts.baseEffective
  lengthEffective := (initial tag old).facts.lengthEffective
  baseUpper := (initial tag old).facts.baseUpper
  lengthUpper := (initial tag old).facts.lengthUpper
  baseAligned := (initial tag old).facts.baseAligned
  lengthAligned := (initial tag old).facts.lengthAligned
  controlKnown := ((before_frame tag value old).registers .ctrs (by decide)).trans (initial tag old).facts.controlKnown
  visibleKnown := ((before_frame tag value old).registers .seg_visibles (by decide)).trans (initial tag old).facts.visibleKnown
  flagsKnown := ((before_frame tag value old).registers .rflags (by decide)).trans (initial tag old).facts.flagsKnown
  quiet := ((before_frame tag value old).registers .log_register_writes (by decide)).trans (initial tag old).facts.quiet
  baseBytes := by
    intro index within
    rw [(before_frame tag value old).memory _ (by exact outside 8192 index (by omega))]
    exact (initial tag old).facts.baseBytes index within
  lengthBytes := by
    intro index within
    rw [(before_frame tag value old).memory _ (by exact outside 8200 index (by omega))]
    exact (initial tag old).facts.lengthBytes index within

private theorem image (tag : BitVec 32) (value old : Word) :
    X86P1LoadCapture.Loaded X86P1LoadCapture.propImage (before tag value old) 4096 := by
  intro index within
  have bound : index < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
  have excluded := outside 4096 index (by omega)
  change ((address (4096 : Int) index).signExtend 52).toNat ∉ written at excluded
  exact ((before_frame tag value old).memory _ excluded).trans ((initial tag old).image index within)

private theorem pointer_value (tag : BitVec 32) (value old : Word) : (facts tag value old).pointer = (12288#64) := rfl
private theorem base_value (tag : BitVec 32) (value old : Word) : (facts tag value old).base = (12288#64) := rfl
private theorem length_value (tag : BitVec 32) (value old : Word) : (facts tag value old).length = (32#64) := rfl

private noncomputable def tagReadable (tag : BitVec 32) (value old : Word) :
    X86P1LoadBounds.Readable (before tag value old) (12288#64) tag where
  dataAddress := 12288#48
  effective := by decide
  upper := by decide
  aligned := by decide
  bytes := by
    intro index within
    rw [(before_frame tag value old).memory _ (by exact outside 12288 index (by omega))]
    exact (initial tag old).readable.bytes index within

private noncomputable def fieldReadable (tag : BitVec 32) (value old : Word) :
    X86P1QwordBounds.Readable (before tag value old) (12288#64) value where
  dataAddress := 12304#48
  effective := by change (12288#64) + 16 = (12304#48).signExtend 64; decide
  upper := by decide
  aligned := by decide
  bytes := by
    intro index within
    exact X86WriteWords.store_word_byte (put (initial tag old).state 4 (16384#64)) (12304#48) value (by decide) index within

private theorem before_stack (tag : BitVec 32) (value old : Word) :
    (before tag value old).regs.get? .rsp = some (16384#64) := by
  change (X86WriteWords.storeBytes 8 (put (initial tag old).state 4 (16384#64)) (12304#48) value).regs.get? .rsp = _
  rw [(X86WriteWords.storeBytes_frame 8 (put (initial tag old).state 4 (16384#64)) (12304#48) value).registers_equal]
  simp [put,key,Std.ExtDHashMap.get?_insert]
  rfl

theorem control (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (tag : BitVec 32) (value old : Word) :
    letI : OtherOpcodeHandlers := X86P1QwordGuardCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (if tag = (6661#32) then 22 else 10)).run (before tag value old) = .ok () after ∧
      lookup after 10 = some (if tag = (6661#32) then value else tag.zeroExtend 64) ∧
      lookup after 11 = some old ∧
      after.regs.get? .rip = some
        ((if tag = (6661#32) then (if value = (0#64) then address 4096 149 else address 4096 524)
          else address 4096 552).signExtend 64) ∧
      after.regs.get? .rsp = some (16384#64) ∧ after.mem = (before tag value old).mem := by
  obtain ⟨after,_,run,frame,valueRead,_,rip,_⟩ :=
    X86P1QwordGuardCapture.two_guard_prefix other extra vector (before tag value old) 4096 (origin tag value old)
      (facts tag value old) (by change (4120#48).toInt = 4096 + 24; decide) (image tag value old)
      tag (by rw [pointer_value]; exact tagReadable tag value old)
      (by rw [pointer_value,base_value,length_value]; decide)
      value (fun _ => by rw [pointer_value]; exact fieldReadable tag value old)
      (by intro _; rw [pointer_value,base_value,length_value]; decide)
  exact ⟨after,run,valueRead,
    (frame.lookup 11 (by decide)).trans (((before_frame tag value old).lookup 11 (by decide)).trans (initial tag old).oldKnown),
    rip,(frame.registers .rsp (by decide)).trans (before_stack tag value old),frame.memory⟩

theorem zero_field_matches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (old : Word) :
    letI : OtherOpcodeHandlers := X86P1QwordGuardCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 22).run (before (6661#32) (0#64) old) = .ok () after ∧
      lookup after 10 = some (0#64) ∧ lookup after 11 = some old ∧
      after.regs.get? .rip = some (4245#64) ∧ after.regs.get? .rsp = some (16384#64) ∧
      after.mem = (before (6661#32) (0#64) old).mem := by
  simpa [show (address 4096 149).signExtend 64 = (4245#64) from by decide] using
    control other extra vector (6661#32) (0#64) old

theorem high_word_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (old : Word) :
    letI : OtherOpcodeHandlers := X86P1QwordGuardCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 22).run (before (6661#32) (0x100000000#64) old) = .ok () after ∧
      lookup after 10 = some (0x100000000#64) ∧ lookup after 11 = some old ∧
      after.regs.get? .rip = some (4620#64) ∧ after.regs.get? .rsp = some (16384#64) ∧
      after.mem = (before (6661#32) (0x100000000#64) old).mem := by
  simpa [show (address 4096 524).signExtend 64 = (4620#64) from by decide] using
    control other extra vector (6661#32) (0x100000000#64) old

theorem wrong_tag_refuses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (old : Word) :
    letI : OtherOpcodeHandlers := X86P1QwordGuardCapture.handlers (X86Funding.Placed.baseHandlers other) extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run (before (6660#32) (0x100000000#64) old) = .ok () after ∧
      lookup after 10 = some (6660#64) ∧ lookup after 11 = some old ∧
      after.regs.get? .rip = some (4648#64) ∧ after.regs.get? .rsp = some (16384#64) ∧
      after.mem = (before (6660#32) (0x100000000#64) old).mem := by
  simpa [show (address 4096 552).signExtend 64 = (4648#64) from by decide] using
    control other extra vector (6660#32) (0x100000000#64) old

#print axioms control
#print axioms zero_field_matches
#print axioms high_word_refuses
#print axioms wrong_tag_refuses

end PrefixControls

#print axioms compare_then_if
#print axioms load_compare_if
#print axioms two_guard_prefix

end Mettapedia.Machines.TIsa.X86P1QwordGuardCapture
