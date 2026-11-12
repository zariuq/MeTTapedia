import Mettapedia.Machines.TIsa.X86P1IfCapture
import Mettapedia.Machines.TIsa.X86FailureHandler
import Mettapedia.Machines.TIsa.X86CallWrapper

/-!
# The actual p1 refusal branch through its public ABI

The twenty-eight bytes at offset 569 in R_DERIVE_IS_PROP are the existing
four-instruction failure-handler template with zero outcome and displacement
39. Its return reaches the epilogue at 636. Captured source paths and byte
checks bind the instance to the actual image rather than its span metadata.

Composition with the first LOAD, comparison and IF proves seventeen fetched
body instructions for every nonmatching readable tag. The public wrapper
then proves twenty-eight instructions through the caller return, preserving
the full image, restoring saved registers and restricting memory changes.
Result-field and stack exclusions are explicit preconditions. Constructive
controls use the complete image and reject a false completion result.

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

theorem containing_spans :
    X86P1LoadCapture.propImage.spans.any (fun span =>
      span.offset == 569 && span.length == 5 && span.kind == "IMM" && span.path == some [1, 2, 0]) = true ∧
    X86P1LoadCapture.propImage.spans.any (fun span =>
      span.offset == 574 && span.length == 23 && span.kind == "RETURN" && span.path == some [1, 2, 1]) = true := by
  constructor <;> kernel_reflexivity

theorem captured_bytes (index : Fin 28) :
    X86P1LoadCapture.propImage.view.read (569 + index.val) = (code[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_loaded (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + 569)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base) :
    codeLoaded state origin.address.toInt code := by
  intro index byte present
  have bounded : index < 28 := by
    have bounded := (List.getElem?_eq_some_iff.mp present).1
    change index < 28 at bounded
    exact bounded
  have capture := captured_bytes ⟨index, bounded⟩
  rw [present, Option.map_some] at capture
  have shifted : address base (569 + index) = address origin.address.toInt index := by
    unfold address
    rw [placed]
    congr 1
    omega
  simpa only [shifted] using
    (loaded (569 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)).trans capture

def writes {state : State} (facts : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written facts.statusAddress (List.range 8) ∪
    X86WriteWords.written facts.resultAddress (List.range 8)

def ImageApart {state : State} (facts : X86FailureHandler.FrameFacts state) (base : Int) : Prop :=
  ∀ index < X86P1LoadCapture.propImage.size,
    ((address base index).signExtend 52).toNat ∉ writes facts

def handlerInput (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 569)
    (upper : base + 646 < (2 ^ 47 : Int))
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
    have shifted : address origin.address.toInt index = address base (569 + index) := by
      unfold address
      rw [placed]
      congr 1
      omega
    rw [shifted]
    exact apart (569 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)

theorem captured_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (facts : X86FailureHandler.FrameFacts state) (placed : origin.address.toInt = base + 569)
    (upper : base + 646 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (apart : ImageApart facts base) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 636).signExtend 64) ∧
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
  have finalPlace : input.epilogue = address base 636 := by
    change address origin.address.toInt 67 = address base 636
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
    (facts : X86P1LoadBounds.Facts state origin) (resultFacts : X86FailureHandler.FrameFacts state)
    (placed : origin.address.toInt = base + 9)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (apart : ImageApart resultFacts base)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable state facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (different : value ≠ (6661#32)) (old : Word) (oldKnown : lookup state 11 = some old) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 17).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base 636).signExtend 64) ∧
      lookup after 0 = some (0#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress index) = some (0#8)) ∧
      X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15,.r10,.r11} (writes resultFacts) state after ∧
      after.regs.get? .rflags = some flags ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, firstFrame, _, _, flagsRead, middleRip, middleImage⟩ :=
    X86P1IfCapture.load_compare_if (X86UnconditionalJump.linked other) extra vector
      state base origin facts placed loaded value readable fits old oldKnown
  rw [if_neg different] at middleRip
  have shifted : address base 569 = address origin.address.toInt 560 := by
    unfold address
    rw [placed]
    congr 1
    omega
  rw [shifted] at middleRip
  let nextOrigin := rebase state middle origin (firstFrame.mono (by decide))
    facts.upper 560 (by decide) middleRip
  have nextPlaced : nextOrigin.address.toInt = base + 569 := by
    change (address origin.address.toInt 560).toInt = _
    rw [address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address)
      facts.upper 560 (by decide)]
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
  refine ⟨after, flags, X86FuelPrefix.fetches_then 13 4 state middle after first last,
    rip, rax, status, result, ?_, finalFlags, image⟩
  apply ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono
  · decide
  · simp only [Finset.empty_union]
    exact Finset.Subset.refl _

noncomputable abbrev callHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  handlers (X86Stack.linkedHandlers other) extra

theorem stack_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Stack.linkedHandlers (callHandlers other extra) = callHandlers other extra := rfl

theorem captured_prologue (index : Fin 9) :
    X86P1LoadCapture.propImage.view.read index.val =
      (X86Prologue.expected[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem captured_epilogue (index : Fin 10) :
    X86P1LoadCapture.propImage.view.read (636 + index.val) =
      (X86Epilogue.expected[index.val]?).map (BitVec.ofNat 8) := by
  fin_cases index <;> kernel_reflexivity

theorem public_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (caller : X86CallWrapper.Inputs state) (base : Int)
    (origin : X86LegacyFetch.Basis (X86Prologue.finished state caller.prologue))
    (facts : X86P1LoadBounds.Facts (X86Prologue.finished state caller.prologue) origin)
    (resultFacts : X86FailureHandler.FrameFacts (X86Prologue.finished state caller.prologue))
    (placed : origin.address.toInt = base + 9)
    (epilogue : caller.epilogue = address base 636)
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage state base)
    (imageStackApart : ∀ index < X86P1LoadCapture.propImage.size,
      ((address base index).signExtend 52).toNat ∉ X86Prologue.writes caller.prologue.bottom)
    (imageBodyApart : ImageApart resultFacts base)
    (stackBodyApart : ∀ slot : Fin 6, ∀ byte < 8,
      X86WriteWords.physicalAddress (X86Prologue.stackAt caller.prologue slot.val) byte ∉ writes resultFacts)
    (value : BitVec 32) (readable : X86P1LoadBounds.Readable (X86Prologue.finished state caller.prologue) facts.pointer value)
    (fits : (facts.pointer - facts.base).toNat + 4 ≤ facts.length.toNat)
    (different : value ≠ (6661#32)) (old : Word)
    (oldKnown : lookup (X86Prologue.finished state caller.prologue) 11 = some old) :
    letI : OtherOpcodeHandlers := callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches 28).run state = .ok () after ∧
      X86CallWrapper.Result state caller (writes resultFacts) body after ∧
      lookup after 0 = some (0#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.statusAddress index) = some (0#8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress resultFacts.resultAddress index) = some (0#8)) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := callHandlers other extra
  let : VectorOpcodeHandlers := vector
  let middle := X86Prologue.finished state caller.prologue
  have bodyImage : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage middle base := by
    intro index within
    rw [(X86Prologue.finished_frame state caller.prologue).memory _ (imageStackApart index within)]
    exact loaded index within
  obtain ⟨body, flags, bodyRun, pointer, rax, status, result, bodyFrame, flagsRead, bodyImage⟩ :=
    load_compare_refused (X86Stack.linkedHandlers other) extra vector middle base origin facts resultFacts
      placed bodyImage imageBodyApart value readable fits different old oldKnown
  let exit : X86CallWrapper.BodyExit state caller (writes resultFacts) body := {
    frame := bodyFrame.mono (by decide) (Finset.Subset.refl _)
    flags := flags
    flagsKnown := flagsRead
    stackApart := stackBodyApart
    epilogueApart := by
      intro index byte present
      have bounded : index < 10 := by
        have bounded := (List.getElem?_eq_some_iff.mp present).1
        change index < 10 at bounded
        exact bounded
      have addressEq : address caller.epilogue.toInt index = address base (636 + index) := by
        rw [epilogue]
        have shifted : address base 636 = address origin.address.toInt 627 := by
          unfold address
          rw [placed]
          congr 1
          omega
        rw [shifted, address_toInt origin.address.toInt (by simpa using BitVec.le_toInt origin.address)
          facts.upper 627 (by decide)]
        unfold address
        congr 1
        omega
      rw [addressEq]
      exact imageBodyApart (636 + index) (by rw [X86P1LoadCapture.byte_extent]; omega)
    pointer := by simpa only [epilogue] using pointer }
  have call := X86CallWrapper.executes (callHandlers other extra) vector state caller
    (writes resultFacts) body 17 exit
  rw [stack_installed] at call
  obtain ⟨after, run, correct⟩ := call bodyRun
  refine ⟨body, after, run, correct, correct.value.trans rax, ?_, ?_, ?_⟩
  · intro index within
    rw [correct.memory]
    exact status index within
  · intro index within
    rw [correct.memory]
    exact result index within
  · intro index within
    rw [correct.memory]
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
  have bounded : index < 646 := by simpa only [X86P1LoadCapture.byte_extent] using within
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
    ∃ state after, (X86FuelPrefix.fetches 17).run state = .ok () after ∧
      lookup after 0 = some (0#64) ∧ after.regs.get? .rip = some (4732#64) ∧
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
      (by decide) (0xffffffffffffffff#64) input.oldKnown
  exact ⟨input.state, after, run, rax, rip, status, result, image⟩

theorem wrong_completion_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after 0 = some (1#64) →
      (X86FuelPrefix.fetches 17).run state ≠ .ok () after := by
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
