import Mettapedia.Machines.TIsa.NativeFailureRefinement

/-!
# Fuel exhaustion reaches the checked native outcome handler

The actual image's fuel branch and handler exit patches supply both control
transfers. The complete prefix theorem constructs the intermediate state;
its flags, architectural frame and unchanged memory provide handler inputs.
Ten original fetched instructions then establish outcome four in RAX and
both frame result words, preserve budget/used bytes, and preserve the complete
caller image under the stated write separation.

Metadata checks derive the fuel/handler pairing for every current imported
image. A concrete fourth fuel span of R_DERIVE_IS_TYPE executes against its
complete exported image; the incremented-counter control is refused.

This theorem ends at the public epilogue. Stack restoration, complete program
source/ABI refinement, OS placement and actual hosting admission remain separate
obligations. It introduces no new instruction semantics or runtime layer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.NativeExhaustion
open _root_.X86Registers X86RegisterRefinement X86Execution NativeImage
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev linkedHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    OtherOpcodeHandlers := X86FuelPrefix.linkedHandlers (X86FailureHandler.linkedHandlers other) extra

theorem handler_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86FailureHandler.linkedHandlers (linkedHandlers other extra) = linkedHandlers other extra := by rfl

structure Inputs (state : State) where
  image : Image
  layout : image.layoutCheck = true
  fuelChecked : NativeFuelProfile.fullImageCheck image = true
  fuelSpan : Span
  fuelPresent : fuelSpan ∈ image.spans
  fuelKind : fuelSpan.kind = "FUEL_STEP"
  fuelPatch : Patch
  fuelFound : NativeFuelProfile.exhaustionPatch? image fuelSpan = some fuelPatch
  handlerSpan : Span
  handlerChecked : NativeFailureProfile.spanCheck image handlerSpan (4#32) = true
  handlerPatch : Patch
  handlerFound : NativeFailureProfile.exitPatch? image handlerSpan = some handlerPatch
  reaches : fuelPatch.target = handlerSpan.offset
  origin : X86LegacyFetch.Basis state
  fuelFacts : X86FuelPrefix.FrameFacts state
  handlerFacts : X86FailureHandler.FrameFacts state
  base : Int
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + image.size < (2 ^ 47 : Int)
  location : origin.address.toInt = base + fuelSpan.offset
  placed : X86CodePlacement.Placed state base image.view
  codeOutside : ∀ index byte, image.view.read index = some byte →
    ((address base index).signExtend 52).toNat ∉
      X86WriteWords.written handlerFacts.statusAddress (List.range 8) ∪
        X86WriteWords.written handlerFacts.resultAddress (List.range 8)
  usedOutside : ∀ index < 8, X86WriteWords.physicalAddress fuelFacts.usedAddress index ∉
    X86WriteWords.written handlerFacts.statusAddress (List.range 8) ∪
      X86WriteWords.written handlerFacts.resultAddress (List.range 8)
  budgetOutside : ∀ index < 8, X86WriteWords.physicalAddress fuelFacts.budgetAddress index ∉
    X86WriteWords.written handlerFacts.statusAddress (List.range 8) ∪
      X86WriteWords.written handlerFacts.resultAddress (List.range 8)

theorem exhaustion_span (image : Image) (checked : NativeFuelProfile.fullImageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    ∃ handler ∈ image.spans, handler.kind = "EXHAUSTED_HANDLER" ∧ patch.target = handler.offset := by
  have offset := (NativeFuelProfile.exhaustion_patch_fields_of image checked span present kind patch found).2.2
  unfold NativeFuelProfile.exhaustedOffset? at offset
  cases selected : image.spans.find? (fun candidate => candidate.kind == "EXHAUSTED_HANDLER") with
  | none => simp only [selected, Option.map_none] at offset; cases offset
  | some handler =>
    have belongs := List.mem_of_find?_eq_some selected
    have named : handler.kind = "EXHAUSTED_HANDLER" := beq_iff_eq.mp
      (List.find?_some (p := fun candidate : Span => candidate.kind == "EXHAUSTED_HANDLER") selected)
    have target : handler.offset = patch.target := by
      simpa only [selected, Option.map_some, Option.some.injEq] using offset
    exact ⟨handler, belongs, named, target.symm⟩

theorem paired_handler (image : Image) (fuelChecked : NativeFuelProfile.fullImageCheck image = true)
    (handlersChecked : NativeFailureProfile.imageCheck image = true)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    ∃ handler handlerPatch, patch.target = handler.offset ∧ NativeFailureProfile.spanCheck image handler (4#32) = true ∧
      NativeFailureProfile.exitPatch? image handler = some handlerPatch := by
  obtain ⟨handler, belongs, named, target⟩ := exhaustion_span image fuelChecked span present kind patch found
  have one := List.all_eq_true.mp handlersChecked handler belongs
  have shape : NativeFailureProfile.outcome? handler = some (4#32) := by
    simp [NativeFailureProfile.outcome?, named]
  have checked : NativeFailureProfile.spanCheck image handler (4#32) = true := by
    simpa only [shape] using one
  obtain ⟨handlerPatch, selected, _⟩ := NativeFailureProfile.bytes_of image handler (4#32) checked
  exact ⟨handler, handlerPatch, target, checked, selected⟩

theorem imported_pair (image : Image) (member : image ∈ ImportedImages.images)
    (span : Span) (present : span ∈ image.spans) (kind : span.kind = "FUEL_STEP")
    (patch : Patch) (found : NativeFuelProfile.exhaustionPatch? image span = some patch) :
    ∃ handler handlerPatch, patch.target = handler.offset ∧ NativeFailureProfile.spanCheck image handler (4#32) = true ∧
      NativeFailureProfile.exitPatch? image handler = some handlerPatch :=
  paired_handler image (List.all_eq_true.mp NativeFuelProfile.all_full_spans_checked image member)
    (List.all_eq_true.mp NativeFailureProfile.all_checked image member) span present kind patch found

def prefixInput {state : State} (input : Inputs state) : X86FuelPrefix.Inputs state :=
  NativeFuelRefinement.inputsOfImage input.image input.layout input.fuelChecked input.fuelSpan input.fuelPresent
    input.fuelKind input.fuelPatch input.fuelFound state input.origin input.fuelFacts input.base input.lower input.upper
    input.location input.placed

def handlerAddress {state : State} (input : Inputs state) : BitVec 48 := address input.base input.handlerSpan.offset

def writes {state : State} (input : Inputs state) : Finset Nat :=
  X86WriteWords.written input.handlerFacts.statusAddress (List.range 8) ∪
    X86WriteWords.written input.handlerFacts.resultAddress (List.range 8)

theorem handler_bound {state : State} (input : Inputs state) : input.handlerSpan.offset + 28 ≤ input.image.size :=
  NativeFailureRefinement.span_bound input.image input.handlerSpan (4#32) input.handlerChecked input.handlerPatch input.handlerFound

theorem handler_location {state : State} (input : Inputs state) :
    (handlerAddress input).toInt = input.base + input.handlerSpan.offset :=
  address_toInt input.base input.lower input.upper input.handlerSpan.offset (by have := handler_bound input; omega)

theorem prefix_target {state middle : State} (input : Inputs state)
    (correct : X86FuelPrefix.Result state (prefixInput input) middle)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) :
    middle.regs.get? .rip = some ((handlerAddress input).signExtend 64) := by
  have pointer := correct.pointer
  change middle.regs.get? .rip = some ((if fuelAvailable input.fuelFacts.budget input.fuelFacts.used then
    address input.origin.address.toInt 40 else address input.base input.fuelPatch.target).signExtend 64) at pointer
  simpa only [unavailable, Bool.false_eq_true, ite_false, input.reaches, handlerAddress] using pointer

def afterFacts {state middle : State} (input : Inputs state)
    (correct : X86FuelPrefix.Result state (prefixInput input) middle) (flags : BitVec 32)
    (flagsKnown : middle.regs.get? .rflags = some flags) : X86FailureHandler.FrameFacts middle :=
  { input.handlerFacts with
    flags := flags
    frameKnown := (correct.frame.lookup 7 (by decide)).trans input.handlerFacts.frameKnown
    controlsKnown := (correct.frame.registers .ctrs (by decide)).trans input.handlerFacts.controlsKnown
    visibleKnown := (correct.frame.registers .seg_visibles (by decide)).trans input.handlerFacts.visibleKnown
    flagsKnown := flagsKnown
    quiet := (correct.frame.registers .log_register_writes (by decide)).trans input.handlerFacts.quiet }

def afterOrigin {state middle : State} (input : Inputs state)
    (correct : X86FuelPrefix.Result state (prefixInput input) middle)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) : X86LegacyFetch.Basis middle :=
  X86StateFrame.basisAt state middle input.origin correct.frame (by decide) (handlerAddress input)
    (by rw [handler_location]; have := handler_bound input; have := input.upper; omega)
    (prefix_target input correct unavailable)

theorem afterPlaced {state middle : State} (input : Inputs state)
    (correct : X86FuelPrefix.Result state (prefixInput input) middle)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) :
    X86CodePlacement.Placed middle input.base input.image.view := by
  intro index byte present
  rw [correct.exhausted unavailable]
  exact input.placed index byte present

def handlerInput {state middle : State} (input : Inputs state)
    (correct : X86FuelPrefix.Result state (prefixInput input) middle)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false)
    (flags : BitVec 32) (flagsKnown : middle.regs.get? .rflags = some flags) :
    X86FailureHandler.Inputs middle (4#32) :=
  NativeFailureRefinement.inputsOfImage input.image input.layout input.handlerSpan (4#32) input.handlerChecked
    input.handlerPatch input.handlerFound middle (afterOrigin input correct unavailable)
    (afterFacts input correct flags flagsKnown) input.base input.lower input.upper
    (handler_location input) (afterPlaced input correct unavailable) input.codeOutside

theorem count_when_exhausted {state : State} (input : Inputs state)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) :
    X86FuelPrefix.instructionCount (prefixInput input) = 6 := by
  have nonzero : input.fuelFacts.budget ≠ (0#64) := by
    intro zero
    simp [fuelAvailable, zero] at unavailable
  have ordered : decide (input.fuelFacts.budget.toNat ≤ input.fuelFacts.used.toNat) = true := by
    have notLess : ¬input.fuelFacts.used.toNat < input.fuelFacts.budget.toNat := by
      intro less
      have available := (fuelAvailable_positive input.fuelFacts.budget input.fuelFacts.used nonzero).2 less
      rw [unavailable] at available
      cases available
    simp only [decide_eq_true_eq]
    omega
  simp only [X86FuelPrefix.instructionCount]
  change (if input.fuelFacts.budget == (0#64) then 4
    else if decide (input.fuelFacts.budget.toNat ≤ input.fuelFacts.used.toNat) then 6 else 7) = 6
  simp [nonzero, ordered]

theorem no_prefix_writes {state : State} (input : Inputs state)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) :
    X86FuelPrefix.writes (prefixInput input) = ∅ := by
  change (if fuelAvailable input.fuelFacts.budget input.fuelFacts.used then
    X86WriteWords.written input.fuelFacts.usedAddress (List.range 8) else ∅) = ∅
  simp only [unavailable, Bool.false_eq_true, ite_false]

def clobbers : Finset Register := {.rax, .r14, .r15, .rflags, .rip}

structure Result (state : State) (input : Inputs state) (after : State) : Prop where
  pointer : after.regs.get? .rip = some ((address input.base input.image.epilogueOffset).signExtend 64)
  rax : lookup after 0 = some (4#64)
  status : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.handlerFacts.statusAddress index) =
    some ((4#64).extractLsb' (8 * index) 8)
  value : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.handlerFacts.resultAddress index) =
    some ((4#64).extractLsb' (8 * index) 8)
  frame : X86StateFrame.Frame clobbers (writes input) state after
  used : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.fuelFacts.usedAddress index) =
    some (input.fuelFacts.used.extractLsb' (8 * index) 8)
  budget : ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.fuelFacts.budgetAddress index) =
    some (input.fuelFacts.budget.extractLsb' (8 * index) 8)
  image : X86CodePlacement.Placed after input.base input.image.view
  flags : ∃ flags, after.regs.get? .rflags = some flags

theorem result_after_handler {state middle after : State} (input : Inputs state)
    (prefixCorrect : X86FuelPrefix.Result state (prefixInput input) middle)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false)
    (flags : BitVec 32) (flagsKnown : middle.regs.get? .rflags = some flags)
    (correct : X86FailureHandler.Result middle (handlerInput input prefixCorrect unavailable flags flagsKnown) after) :
    Result state input after := by
  have fullFrame : X86StateFrame.Frame clobbers (writes input) state after := by
    apply (prefixCorrect.frame.trans correct.frame).mono
    · intro register present
      simp only [clobbers, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at present ⊢
      tauto
    · change (X86FuelPrefix.writes (prefixInput input) ∪ writes input) ⊆ writes input
      rw [no_prefix_writes input unavailable, Finset.empty_union]
  refine ⟨correct.pointer, correct.rax, correct.status, correct.result, fullFrame, ?_, ?_,
    input.placed.preserved input.base input.image.view fullFrame input.codeOutside, ⟨flags, correct.flags⟩⟩
  · intro index within
    rw [correct.frame.memory _ (input.usedOutside index within), prefixCorrect.exhausted unavailable]
    exact input.fuelFacts.usedPresent index within
  · intro index within
    rw [correct.frame.memory _ (input.budgetOutside index within), prefixCorrect.exhausted unavailable]
    exact input.fuelFacts.budgetPresent index within

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run state = .ok () after ∧ Result state input after := by
  let : OtherOpcodeHandlers := linkedHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, prefixRun, prefixCorrect⟩ := X86FuelPrefix.executes (X86FailureHandler.linkedHandlers other)
    extra vector state (prefixInput input)
  obtain ⟨flags, flagsKnown⟩ := prefixCorrect.flags
  let tail := handlerInput input prefixCorrect unavailable flags flagsKnown
  have handlerRun : (X86FuelPrefix.fetches 4).run middle = .ok () (X86FailureHandler.finished middle tail) := by
    simpa only [handler_installed] using X86FailureHandler.executes (linkedHandlers other extra) vector middle (4#32) tail
  refine ⟨_, X86FuelPrefix.fetches_then 6 4 state middle _ ?_ handlerRun, ?_⟩
  · simpa only [count_when_exhausted input unavailable] using prefixRun
  · exact result_after_handler input prefixCorrect unavailable flags flagsKnown (X86FailureHandler.finished_result middle (4#32) tail)

theorem any_run_refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state)
    (unavailable : fuelAvailable input.fuelFacts.budget input.fuelFacts.used = false) (after : State) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 10).run state = .ok () after → Result state input after := by
  intro observed
  obtain ⟨proved, run, correct⟩ := executes other extra vector state input unavailable
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  simpa only [same] using correct

namespace Controls
private noncomputable def image : Image := ImportedImages.images[0]'(by rw [ImportedImages.image_count]; decide)
private noncomputable def fuelSpan : Span :=
  (image.spans.filter (fun span => span.kind == "FUEL_STEP"))[3]'(by decide)
private def emptyPatch : Patch := ⟨0, 0, 0, 0, 0#8, false, 0, false⟩
private noncomputable def fuelPatch : Patch := (NativeFuelProfile.exhaustionPatch? image fuelSpan).getD emptyPatch
private noncomputable def handlerSpan : Span :=
  (image.spans.find? (fun span => span.kind == "EXHAUSTED_HANDLER")).getD ⟨0, 0, ""⟩
private noncomputable def handlerPatch : Patch := (NativeFailureProfile.exitPatch? image handlerSpan).getD emptyPatch

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private noncomputable def codeCells : List (Nat × Byte) :=
  (List.range image.size).map (fun index => (4096 + index, (image.view.read index).getD 0))
private def wordCells (offset : Nat) (value : Word) : List (Nat × Byte) :=
  (List.range 8).map (fun index => (1048576 + offset + index, value.extractLsb' (8 * index) 8))
private def frameCells : List (Nat × Byte) :=
  wordCells 144 (99#64) ++ wordCells 152 (77#64) ++ wordCells 160 (3#64) ++ wordCells 168 (3#64) ++ [(1048752, 42#8)]
private noncomputable def cells : List (Nat × Byte) := codeCells ++ frameCells

private theorem frame_cell_bound (key : Nat) (present : key ∈ frameCells.map Prod.fst) : 1048576 ≤ key := by
  simp only [frameCells, wordCells, List.map_append, List.map_map, Function.comp_def, List.mem_append,
    List.mem_map, List.mem_range, List.map_cons, List.map_nil, List.mem_singleton] at present
  rcases present with (((one | two) | three) | four) | five
  · obtain ⟨index, _, rfl⟩ := one; omega
  · obtain ⟨index, _, rfl⟩ := two; omega
  · obtain ⟨index, _, rfl⟩ := three; omega
  · obtain ⟨index, _, rfl⟩ := four; omega
  · omega

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  have codeUnique : (codeCells.map Prod.fst).Nodup := by
    simp only [codeCells, List.map_map, Function.comp_def]
    exact List.Nodup.map (fun _ _ equal => Nat.add_left_cancel equal) List.nodup_range
  have frameUnique : (frameCells.map Prod.fst).Nodup := by
    simp only [frameCells, wordCells, List.map_append, List.map_map, Function.comp_def]
    decide
  have separated : ∀ left ∈ codeCells.map Prod.fst, ∀ right ∈ frameCells.map Prod.fst, left ≠ right := by
    intro left codePresent right framePresent same
    simp only [codeCells, List.map_map, Function.comp_def, List.mem_map, List.mem_range] at codePresent
    obtain ⟨index, within, rfl⟩ := codePresent
    have bound := frame_cell_bound right framePresent
    have size : image.size = 1960 := by kernel_reflexivity
    rw [size] at within
    omega
  have unique : (cells.map Prod.fst).Nodup := by
    rw [cells, List.map_append, List.nodup_append]
    exact ⟨codeUnique, frameUnique, separated⟩
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using unique

private noncomputable def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1131#64)
  let registers := registers.insert .rdi (0x100000#64)
  let registers := registers.insert .rax (999#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private theorem cell (key : Nat) (byte : Byte) (present : (key, byte) ∈ cells) :
    before.mem.get? key = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private theorem code_physical (index : Nat) (within : index < image.size) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by
    have size : image.size = 1960 := by kernel_reflexivity
    rw [size] at within
    have canonical := address_toInt (extent := 1960) 4096 (by decide)
      (by decide : (4096 : Int) + 1960 < 2 ^ 47) index (by omega)
    have signed : ((address 4096 index).signExtend 52).toInt = 4096 + index := by
      rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 52), canonical]
    have positive : ((address 4096 index).signExtend 52).msb = false := by
      cases sign : ((address 4096 index).signExtend 52).msb with
      | false => rfl
      | true => have negative := BitVec.toInt_neg_of_msb_true sign; omega
    have natural := BitVec.toInt_eq_toNat_of_msb positive
    omega
private theorem placed : X86CodePlacement.Placed before 4096 image.view := by
  intro index byte read
  have within := NativeFuelRefinement.read_bound image index byte read
  have present : (4096 + index, byte) ∈ cells := by
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨index, List.mem_range.mpr within, ?_⟩
    simp only [read, Option.getD_some]
  rw [code_physical index within]
  exact cell (4096 + index) byte present

private theorem word_byte (offset : Nat) (value : Word) (index : Nat) (within : index < 8)
    (part : wordCells offset value ⊆ frameCells) :
    before.mem.get? (1048576 + offset + index) = some (value.extractLsb' (8 * index) 8) := by
  apply cell
  apply List.mem_append_right
  apply part
  exact List.mem_map.mpr ⟨index, List.mem_range.mpr within, rfl⟩

private theorem budgetPart : wordCells 160 (3#64) ⊆ frameCells := by
  intro item present
  simp only [frameCells, List.mem_append]
  exact Or.inl (Or.inl (Or.inr present))
private theorem usedPart : wordCells 168 (3#64) ⊆ frameCells := by
  intro item present
  simp only [frameCells, List.mem_append]
  exact Or.inl (Or.inr present)

private noncomputable def origin : X86LegacyFetch.Basis before where
  address := 0x1131#48
  opcodeAddress := 0x1132#48
  modrmAddress := 0x1133#48
  next := 0x1134#48
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

private noncomputable def fuelFacts : X86FuelPrefix.FrameFacts before where
  frame := 0x100000#64
  budget := 3#64
  used := 3#64
  budgetAddress := 0x1000a0#48
  usedAddress := 0x1000a8#48
  budgetUpper := by decide
  usedUpper := by decide
  budgetEffective := by decide
  usedEffective := by decide
  budgetAligned := by decide
  usedAligned := by decide
  visible := visible
  controls := controls
  flags := 0#32
  frameKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  budgetPresent := by
    intro index within
    have got := word_byte 160 (3#64) index within budgetPart
    interval_cases index <;> exact got
  usedPresent := by
    intro index within
    have got := word_byte 168 (3#64) index within usedPart
    interval_cases index <;> exact got

private noncomputable def handlerFacts : X86FailureHandler.FrameFacts before where
  frame := 0x100000#64
  statusAddress := 0x100090#48
  resultAddress := 0x100098#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := visible
  controls := controls
  flags := 0#32
  frameKnown := by simp [before, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl
  controlsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  visibleKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  flagsKnown := by simp [before, Std.ExtDHashMap.get?_insert]
  quiet := by simp [before]
  statusOutside := by intro index within; interval_cases index <;> decide

private theorem handler_write_set :
    X86WriteWords.written (0x100090#48) (List.range 8) ∪ X86WriteWords.written (0x100098#48) (List.range 8) =
      Finset.Ico 1048720 1048736 := by decide

private noncomputable def input : Inputs before where
  image := image
  layout := by kernel_reflexivity
  fuelChecked := by kernel_reflexivity
  fuelSpan := fuelSpan
  fuelPresent := by decide
  fuelKind := by kernel_reflexivity
  fuelPatch := fuelPatch
  fuelFound := by kernel_reflexivity
  handlerSpan := handlerSpan
  handlerChecked := by kernel_reflexivity
  handlerPatch := handlerPatch
  handlerFound := by kernel_reflexivity
  reaches := by kernel_reflexivity
  origin := origin
  fuelFacts := fuelFacts
  handlerFacts := handlerFacts
  base := 4096
  lower := by decide
  upper := by decide
  location := by kernel_reflexivity
  placed := placed
  codeOutside := by
    intro index byte read
    have within := NativeFuelRefinement.read_bound image index byte read
    rw [code_physical index within]
    have size : image.size = 1960 := by kernel_reflexivity
    rw [size] at within
    change 4096 + index ∉ X86WriteWords.written (0x100090#48) (List.range 8) ∪
      X86WriteWords.written (0x100098#48) (List.range 8)
    rw [handler_write_set]
    simp only [Finset.mem_Ico]
    omega
  usedOutside := by intro index within; interval_cases index <;> decide
  budgetOutside := by intro index within; interval_cases index <;> decide

theorem exported_program_name : image.name = "R_DERIVE_IS_TYPE" := by kernel_reflexivity

theorem actual_fuel_span_exhausted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run before = .ok () after ∧ lookup after 0 = some (4#64) ∧
      after.mem.get? 1048720 = some (4#8) ∧ after.mem.get? 1048728 = some (4#8) ∧
      after.mem.get? 1048744 = some (3#8) ∧ after.mem.get? 1048736 = some (3#8) ∧
      X86CodePlacement.Placed after 4096 image.view := by
  obtain ⟨after, run, correct⟩ := executes other extra vector before input (by decide)
  exact ⟨after, run, correct.rax, correct.status 0 (by decide), correct.value 0 (by decide),
    correct.used 0 (by decide), correct.budget 0 (by decide), correct.image⟩

theorem incremented_counter_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (after : State) (wrong : after.mem.get? 1048744 = some (4#8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 10).run before ≠ .ok () after := by
  intro observed
  obtain ⟨proved, run, _, _, _, used, _, _⟩ := actual_fuel_span_exhausted other extra vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at used
  contradiction

end Controls
end Mettapedia.Machines.TIsa.NativeExhaustion

#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.imported_pair
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.handlerInput
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.result_after_handler
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.executes
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.any_run_refines
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.Controls.actual_fuel_span_exhausted
#print axioms Mettapedia.Machines.TIsa.NativeExhaustion.Controls.incremented_counter_refused
