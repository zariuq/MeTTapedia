import Mettapedia.Machines.TIsa.X86P1IfCapture
import Mettapedia.Machines.TIsa.X86FailureHandler
import Mettapedia.Machines.TIsa.X86AllowanceCall

/-!
# The actual p1 refusal branch through its public ABI

The twenty-eight bytes at offset 552 in R_DERIVE_IS_PROP are the existing
four-instruction failure-handler template with zero outcome and displacement
39. Its return reaches the receipt block at 619. Captured source paths and byte
checks bind the instance to the actual image rather than its span metadata;
the exported path labels of these two spans are wrong and are not relied on.

Composition with the first LOAD, comparison and IF proves fourteen fetched
body instructions for every nonmatching readable tag. The public allowance
call then proves thirty-two instructions through the caller return: eight for
the saves and allowance setup, fourteen in the body and ten for the receipt and
restores. It preserves the full image, restores all six saved registers,
republishes the unchanged receipt and restricts memory changes. Result-field,
receipt and stack exclusions are explicit preconditions. Constructive controls
use the complete image and reject a false completion result.

Matching-tag and invalid-input paths, complete source admission/hosting and
the generic emitter theorem remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1RefusedCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86P1IfCapture.handlers (X86Funding.Placed.baseHandlers (X86UnconditionalJump.linked other)) extra

theorem failure_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FailureHandler.linkedHandlers (handlers other extra) = handlers other extra := rfl

def code : List Nat := X86FailureHandler.expected (0#32) (39#32)

theorem source_block : X86P1LoadCapture.propImage.source.body.atPath [1, 2] =
    some (.seq (.instruction (.immediate .u64 8 (0#64))) (.ret .refused 8)) := by
  kernel_reflexivity

/-- The refusal arm is the target of the first IF-FLAGS jump. Its two spans exist at 552 and 557,
but the export labels them with the inner arm's paths `[1,1,1,2,0]` and `[1,1,1,2,1]`. -/
theorem containing_spans :
    X86P1LoadCapture.propImage.spans.any (fun span =>
      span.offset == 552 && span.length == 5 && span.kind == "IMM") = true ∧
    X86P1LoadCapture.propImage.spans.any (fun span =>
      span.offset == 557 && span.length == 23 && span.kind == "RETURN") = true := by
  constructor <;> kernel_reflexivity

theorem captured_bytes (index : Fin 28) :
    X86P1LoadCapture.propImage.view.read (552 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 552)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 28 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 28 at bounded
    exact bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (552 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (552 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

def writes {state : State} (facts : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written facts.statusAddress (List.range 8) ∪
    X86WriteWords.written facts.resultAddress (List.range 8)

def ImageApart {state : State} (facts : X86FailureHandler.FrameFacts state) (base : Int) : Prop :=
  ∀ index < X86P1LoadCapture.propImage.size,
    ((address base index).signExtend 52).toNat ∉ writes facts

def handlerInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 552)
    (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (apart : ImageApart facts base) : X86FailureHandler.Inputs state (0#32) := by
  have extent : origin.address.toInt + 77 < (2 ^ 47 : Int) := by omega
  refine {
    toBasis := origin
    toFrameFacts := facts
    displacement := 39#32
    epilogue := address origin.address.toInt 67
    upper := by omega
    jump := ?_
    loaded := captured_loaded state base origin placed loaded
    codeOutside := ?_ }
  · rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address)
      extent 67 (by decide)]
    change origin.address.toInt + 67 = origin.address.toInt + 28 + 39
    omega
  · intro index byte present
    have bounded : index < 28 := by
      have bounded := (List.getElem?_eq_some_iff.mp present).1
      change index < 28 at bounded
      exact bounded
    have shifted : address origin.address.toInt index = address base (552 + index) := by
      unfold address
      rw [placed]
      congr 1
      omega
    rw [shifted]
    exact apart (552 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 552)
    (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (apart : ImageApart facts base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 619).signExtend 64) ∧
      lookup after 0 = some (0#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress index) = some (0#8)) ∧
      X86StateFrame.Frame {.rax,.rip} (writes facts) state after ∧
      after.regs.get? .rflags = some facts.flags ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := handlerInput state base origin facts placed upper loaded apart
  let after := X86FailureHandler.finished state input
  have executed := X86FailureHandler.executes (handlers other extra) vector state (0#32) input
  rw [failure_installed] at executed
  have correct := X86FailureHandler.finished_result state (0#32) input
  have finalPlace : input.epilogue = address base 619 := by
    change address origin.address.toInt 67 = address base 619
    unfold address
    rw [placed]
    congr 1
    omega
  refine ⟨after, executed, ?_, correct.rax, ?_, ?_, correct.frame, correct.flags, ?_⟩
  · simpa only [finalPlace] using correct.pointer
  · intro index within
    have same : input.statusAddress = facts.statusAddress := rfl
    have observed := correct.status index within
    rw [same] at observed
    simpa using observed
  · intro index within
    have same : input.resultAddress = facts.resultAddress := rfl
    have observed := correct.result index within
    rw [same] at observed
    simpa using observed
  · intro index within
    rw [correct.frame.memory _ (apart index within)]
    exact loaded index within

theorem load_compare_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86P1LoadBounds.Facts state origin 623) (resultFacts : X86FailureHandler.FrameFacts state)
    (placed : origin.address.toInt = base + 24)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (apart : ImageApart resultFacts base)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (different : value ≠ (6661#32)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 14).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 619).signExtend 64) ∧
      lookup after 0 = some (0#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress index) = some (0#8)) ∧
      X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15,.r10} (writes resultFacts) state after ∧
      after.regs.get? .rflags = some flags ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, firstFrame, _, flagsRead, _, middleRip, middleImage⟩ :=
    X86P1IfCapture.load_compare_if (X86UnconditionalJump.linked other) extra vector
      state base origin facts placed loaded value readable fits
  rw [if_neg different] at middleRip
  have shifted : address base 552 = address origin.address.toInt 528 := by
    unfold address
    rw [placed]
    congr 1
    omega
  rw [shifted] at middleRip
  let nextOrigin := rebase state middle origin (firstFrame.mono (by decide))
    facts.upper 528 (by decide) middleRip
  have nextPlaced : nextOrigin.address.toInt = base + 552 := by
    change (address origin.address.toInt 528).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address)
      facts.upper 528 (by decide)]
    omega
  let nextFacts : X86FailureHandler.FrameFacts middle := {
    resultFacts with
    frameKnown := (firstFrame.lookup 7 (by decide)).trans resultFacts.frameKnown
    controlsKnown := (firstFrame.registers .ctrs (by decide)).trans resultFacts.controlsKnown
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans resultFacts.visibleKnown
    flags := flags
    flagsKnown := flagsRead
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans resultFacts.quiet }
  obtain ⟨after, last, rip, rax, status, result, lastFrame, finalFlags, image⟩ :=
    captured_executes other extra vector middle base nextOrigin nextFacts nextPlaced
      (by have := facts.upper; omega) middleImage apart
  refine ⟨after, flags, X86FuelPrefix.fetches_then 10 4 state middle after first last,
    rip, rax, status, result, ?_, finalFlags, image⟩
  apply ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono
  · decide
  · simp only [Finset.empty_union]
    exact Finset.Subset.refl _

/-- One handler table for the whole call: the allowance blocks, the guard and the refusal arm. -/
noncomputable abbrev callHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  handlers (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra

theorem enter_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Stack.linkedHandlers (X86P1Sub1Fuel.handlers (callHandlers other extra)) = callHandlers other extra := rfl

theorem exit_dispatch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86AllowanceCall.Inputs.exitDispatch (callHandlers other extra) = callHandlers other extra := rfl

/-- The image opens with the allowance prologue. -/
theorem captured_entry (index : Fin 24) :
    X86P1LoadCapture.propImage.view.read index.val =
      ((X86Prologue.expected ++ X86AllowanceCall.entryCode)[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

/-- The image closes with the receipt block and the six restores. -/
theorem captured_exit (index : Fin 28) :
    X86P1LoadCapture.propImage.view.read (619 + index.val) =
      (X86AllowanceCall.exitCode[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem restored_receipt (budget receipt : Word) : budget - (budget - receipt) = receipt :=
  BitVec.sub_eq_iff_eq_add.mpr (by rw [BitVec.add_comm, BitVec.sub_add_cancel])

/-- Image bytes at `exit + index` are image bytes at `619 + index`. -/
theorem exit_address (base : Int) (exit : BitVec 48) (exitAt : exit = address base 619)
    (upper : base + 647 < (2 ^ 47 : Int)) (lower : -(2 ^ 47 : Int) ≤ base) (index : Nat) :
    address exit.toInt index = address base (619 + index) := by
  rw [exitAt, address_toInt base lower (show base + (647 : Nat) < (2 ^ 47 : Int) by exact_mod_cast upper) 619 (by decide)]
  unfold address
  congr 1
  push_cast
  omega

theorem public_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (base : Int)
    (entryAt : call.prologue.code.toInt = base) (exitAt : call.exit = address base 619)
    (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    {layout : X86Bounds.Layout} (pointerIs : layout.pointer = 6) (regionIs : layout.region = 0)
    (facts : X86Bounds.Facts layout state) (resultFacts : X86FailureHandler.FrameFacts state)
    (imageSpillApart : ∀ index < X86P1LoadCapture.propImage.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (imageBodyApart : ImageApart resultFacts base)
    (imageReceiptApart : ∀ index < X86P1LoadCapture.propImage.size,
      ((address base index).signExtend 52).toNat ∉ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (baseSpillApart : ∀ byte < 8, ((address facts.baseAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (lengthSpillApart : ∀ byte < 8, ((address facts.lengthAddress.toInt byte).signExtend 52).toNat ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress resultFacts.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress resultFacts.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (budgetBodyApart : ∀ byte < 8, X86WriteWords.physicalAddress call.fuel.budgetAddress byte ∉ writes resultFacts)
    (bottomApart : ∀ byte < 8, X86WriteWords.physicalAddress call.bottom byte ∉
      writes resultFacts ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (savedApart : ∀ slot : Fin 6, ∀ byte < 8,
      X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) byte ∉
        writes resultFacts ∪ X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable state facts.pointer value)
    (readableSpillApart : ∀ byte < 4, X86WriteWords.physicalAddress readable.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (different : value ≠ (6661#32)) :
    letI : OtherOpcodeHandlers := callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches 32).run state = .ok () after ∧
      X86AllowanceCall.Result call (writes resultFacts) (call.fuel.budget - call.fuel.receipt) body after ∧
      lookup after 0 = some (0#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress index) =
        some (call.fuel.receipt.extractLsb' (8 * index) 8)) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := callHandlers other extra
  let : VectorOpcodeHandlers := vector
  have lower : -(2 ^ 47 : Int) ≤ base := by rw [← entryAt]; simpa using BitVec.le_toInt call.prologue.code
  have codeUpper : call.prologue.code.toInt + 647 < (2 ^ 47 : Int) := by rw [entryAt]; exact upper
  have entry := call.enters (callHandlers other extra) vector
  rw [enter_dispatch] at entry
  obtain ⟨output, entered⟩ := entry
  let middle := call.entered output
  have frame := call.entered_frame output
  let origin := X86AllowanceCall.basisAt call.prologue.code 24 codeUpper (by decide) (call.enteredMode output)
    (call.entered_rip output)
  have placed : origin.address.toInt = base + 24 := by
    change (address call.prologue.code.toInt 24).toInt = _
    rw [X86AllowanceCall.offset_int call.prologue.code codeUpper 24 (by decide), entryAt]
    rfl
  let moved := X86Bounds.Facts.transport facts frame (by decide) (by decide) (by rw [pointerIs]; decide)
    (X86Flags.mergeFlags call.fuel.flags output) (call.entered_flags output) baseSpillApart lengthSpillApart
  let located := X86P1LoadCapture.located pointerIs regionIs moved origin (by rw [placed]; omega)
  let resultAt : X86FailureHandler.FrameFacts middle := {
    resultFacts with
    frameKnown := (frame.lookup 7 (by decide)).trans resultFacts.frameKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans resultFacts.controlsKnown
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans resultFacts.visibleKnown
    flags := X86Flags.mergeFlags call.fuel.flags output
    flagsKnown := call.entered_flags output
    quiet := (frame.registers .log_register_writes (by decide)).trans resultFacts.quiet }
  have imageAt : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage middle base :=
    fun index within => (frame.memory _ (imageSpillApart index within)).trans (loaded index within)
  let readableAt : X86P1LoadBounds.Readable middle located.pointer value := {
    readable with bytes := fun byte within =>
      (frame.memory _ (readableSpillApart byte within)).trans (readable.bytes byte within) }
  obtain ⟨body, flags, bodyRun, bodyRip, rax, status, result, bodyFrame, flagsRead, bodyImage⟩ :=
    load_compare_refused (X86AllowanceCall.Inputs.exitDispatch (X86P1Sub1Fuel.handlers other)) extra vector
      middle base origin located resultAt placed imageAt imageBodyApart value readableAt fits different
  let exit : X86AllowanceCall.Exit call output (writes resultFacts) body := {
    frame := bodyFrame.mono (by decide) (Finset.Subset.refl _)
    remaining := call.fuel.budget - call.fuel.receipt
    remainingKnown := (bodyFrame.lookup 5 (by decide)).trans (call.entered_allowance output)
    flags := flags
    flagsKnown := flagsRead
    budgetSafe := budgetBodyApart
    bottomSafe := bottomApart
    savedSafe := savedApart
    exitSafe := by
      intro index byte present
      have bounded : index < 28 := (List.getElem?_eq_some_iff.mp present).1
      rw [exit_address base call.exit exitAt upper lower index]
      intro member
      rcases Finset.mem_union.mp member with body | receipt
      · exact imageBodyApart (619 + index) (by rw [X86P1LoadCapture.byte_extent]; omega) body
      · exact imageReceiptApart (619 + index) (by rw [X86P1LoadCapture.byte_extent]; omega) receipt
    pointer := by rw [exitAt]; exact bodyRip }
  obtain ⟨after, run, correct⟩ :=
    call.executes (callHandlers other extra) vector output (writes resultFacts) body 14 entered bodyRun exit
      (exit_dispatch other extra)
  refine ⟨body, after, run, correct, correct.value.trans rax, ?_, ?_, ?_, ?_⟩
  · intro index within
    rw [correct.tail.memory _ (statusReceiptApart index within)]
    exact status index within
  · intro index within
    rw [correct.tail.memory _ (resultReceiptApart index within)]
    exact result index within
  · intro index within
    have published := correct.receipt index within
    change after.mem.get? _ = some (BitVec.extractLsb' (8 * index) 8
      (call.fuel.budget - (call.fuel.budget - call.fuel.receipt))) at published
    rwa [restored_receipt] at published
  · intro index within
    rw [correct.tail.memory _ (imageReceiptApart index within)]
    exact bodyImage index within

namespace Controls

private noncomputable def fixtureResult (value : BitVec 32) (old : Word) :
    X86FailureHandler.FrameFacts (X86P1IfCapture.PrefixControls.fixture value old).state :=
  let input := X86P1IfCapture.PrefixControls.fixture value old
  { frame := input.facts.frame
    statusAddress := 8336#48
    resultAddress := 8344#48
    statusUpper := by decide
    resultUpper := by decide
    statusEffective := by rw [input.frameValue]; decide
    resultEffective := by rw [input.frameValue]; decide
    statusAligned := by decide
    resultAligned := by decide
    visible := input.facts.visible
    controls := input.facts.controls
    flags := input.facts.flags
    frameKnown := input.facts.frameKnown
    controlsKnown := input.facts.controlKnown
    visibleKnown := input.facts.visibleKnown
    flagsKnown := input.facts.flagsKnown
    quiet := input.facts.quiet
    statusOutside := by intro index within; interval_cases index <;> decide }

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

private theorem fixtureApart (value : BitVec 32) (old : Word) : ImageApart (fixtureResult value old) 4096 := by
  intro index within
  have bounded : index < 647 := by simpa only [X86P1LoadCapture.byte_extent] using within
  have place := positive_address 4096 index (by omega)
  change ((address 4096 index).signExtend 52).toNat = 4096 + index at place
  rw [place]
  have footprint : writes (fixtureResult value old) =
      {8336,8337,8338,8339,8340,8341,8342,8343,8344,8345,8346,8347,8348,8349,8350,8351} := by
    change X86WriteWords.written (8336#48) (List.range 8) ∪
      X86WriteWords.written (8344#48) (List.range 8) = _
    decide
  rw [footprint]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem different_tag_returns_zero (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 14).run state = .ok () after ∧
      lookup after 0 = some (0#64) ∧ after.regs.get? .rip = some (4715#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress (8336#48) index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress (8344#48) index) = some (0#8)) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after 4096 := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := X86P1IfCapture.PrefixControls.fixture (6660#32) (0xffffffffffffffff#64)
  obtain ⟨after, _, run, rip, rax, status, result, _, _, image⟩ :=
    load_compare_refused other extra vector input.state 4096 input.origin input.facts
      (fixtureResult (6660#32) (0xffffffffffffffff#64)) input.placed input.image
      (fixtureApart (6660#32) (0xffffffffffffffff#64)) (6660#32) input.readable input.fits
      (by decide)
  exact ⟨input.state, after, run, rax, rip, status, result, image⟩

theorem wrong_completion_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after 0 = some (1#64) →
      (X86FuelPrefix.fetches 14).run state ≠ .ok () after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨state, proved, run, value, _⟩ := different_tag_returns_zero other extra vector
  refine ⟨state, ?_⟩
  intro after wrong observed
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at value
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86P1RefusedCapture
