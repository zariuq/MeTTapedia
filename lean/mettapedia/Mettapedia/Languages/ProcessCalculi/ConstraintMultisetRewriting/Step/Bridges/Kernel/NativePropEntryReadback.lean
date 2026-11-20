import Mettapedia.Machines.TIsa.X86MemoryBounds
import Mettapedia.Machines.TIsa.X86P1PropRefinement

/-!
# Finite observations at the public proposition-rule caller

The premise observation contains twenty-four bytes. Capability capacity does
not require backing for its unread suffix or for the old output. Source region
declarations fix the observed modes; they do not certify an issuer or hosting
authority. The complete call retains its register, stack and receipt effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePropEntryReadback

open Mettapedia.Machines.TIsa
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView

/-- A partial observation, without requiring every logical register or byte. -/
def KnownOn (keys : Finset Key) (modes : Fin 9 → Word) (values : Key → Word)
    (state : State) : Prop :=
  ∀ key ∈ keys, readback modes state key = some (values key)

noncomputable def declaredModes (region : Fin 9) : Word :=
  BitVec.ofNat 64 (((X86P1LoadCapture.propImage.source.regions[region.val]?).map
    fun declaration => declaration.mode.number).getD 0)

theorem captured_declarations :
    X86P1LoadCapture.propImage.source.regions = X86P1LoadCapture.propImage.regions := by
  apply P1Capture.Program.regions_exact
  kernel_reflexivity

theorem declared_modes : declaredModes 0 = (1#64) ∧ declaredModes 1 = (2#64) := by
  constructor <;> kernel_reflexivity

theorem captured_regions : X86P1LoadCapture.propImage.source.regions =
    [⟨.readOnly,32#32,8#32⟩,⟨.readWrite,32#32,8#32⟩] := by
  kernel_reflexivity

theorem logical_zero_readback (modes : Fin 9 → Word) (state : State) :
    readback modes state (.register 0) = lookup state 7 := rfl

theorem observed_frame (keys : Finset Key) (modes : Fin 9 → Word) (values : Key → Word)
    (state : State) (known : KnownOn keys modes values state)
    (present : Memory.Key.register 0 ∈ keys) (receipt : X86FailureHandler.FrameFacts state) :
    values (.register 0) = receipt.frame :=
  Option.some.inj ((known (.register 0) present).symm.trans receipt.frameKnown)

def premiseKeys (pointer : Word) : Finset Key :=
  (Finset.range 24).image fun byte => .byte (pointer.toNat + byte)

def entryKeys (pointer : Word) : Finset Key :=
  { .register 0, .register 1, .register 2, .register 7,
    .capabilityBase 0, .capabilityLength 0, .capabilityMode 0,
    .capabilityBase 1, .capabilityLength 1, .capabilityMode 1 } ∪ premiseKeys pointer

def observedBytes (values : Key → Word) (pointer : Word) (byte : Fin 24) : BitVec 8 :=
  (values (.byte (pointer.toNat + byte.val))).extractLsb' 0 8

def decodeWord (bytes : Fin 24 → BitVec 8) (offset : Nat) (within : offset + 8 ≤ 24) : Word :=
  packBytes (List.ofFn fun byte : Fin 8 => bytes ⟨offset + byte.val, by have := byte.isLt; omega⟩)

def decodeTag (bytes : Fin 24 → BitVec 8) : BitVec 32 :=
  (decodeWord bytes 0 (by decide)).extractLsb' 0 32

def decodeField (bytes : Fin 24 → BitVec 8) : Word := decodeWord bytes 8 (by decide)
def decodeLevel (bytes : Fin 24 → BitVec 8) : Word := decodeWord bytes 16 (by decide)

theorem decodeWord_byte (bytes : Fin 24 → BitVec 8) (offset : Nat) (within : offset + 8 ≤ 24)
    (byte : Fin 8) :
    (decodeWord bytes offset within).extractLsb' (8 * byte.val) 8 =
      bytes ⟨offset + byte.val, by have := byte.isLt; omega⟩ := by
  simpa only [decodeWord,List.getElem_ofFn] using
    X86MemoryReadback.packed_extract
      (List.ofFn fun index : Fin 8 => bytes ⟨offset + index.val, by have := index.isLt; omega⟩)
      (by simp only [List.length_ofFn]) byte

theorem decodeTag_byte (bytes : Fin 24 → BitVec 8) (byte : Fin 4) :
    (decodeTag bytes).extractLsb' (8 * byte.val) 8 = bytes ⟨byte.val, by have := byte.isLt; omega⟩ := by
  rw [decodeTag,BitVec.extractLsb'_extractLsb'_of_le (by have := byte.isLt; omega)]
  simpa only [Nat.zero_add] using decodeWord_byte bytes 0 (by decide) ⟨byte.val,by have := byte.isLt; omega⟩

theorem observed_byte (keys : Finset Key) (modes : Fin 9 → Word) (values : Key → Word)
    (state : State) (known : KnownOn keys modes values state) (address : Nat)
    (present : Memory.Key.byte address ∈ keys) :
    memory state (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) =
      some ((values (.byte address)).extractLsb' 0 8) := by
  obtain ⟨_,_,byte,read,same⟩ := X86MemoryReadback.byte_observed modes state address _
    (known (.byte address) present)
  rw [same,X86MemoryReadback.byte_extract]
  exact read

/-- Actual descriptor observations, with only the needed pointer registers. -/
def boundsFacts (keys : Finset Key) (modes : Fin 9 → Word) (values : Key → Word)
    (state : State) (layout : X86Bounds.Layout) (pointer : Fin 12)
    (known : KnownOn keys modes values state)
    (framePresent : Memory.Key.register 0 ∈ keys)
    (pointerPresent : Memory.Key.register pointer ∈ keys)
    (basePresent : Memory.Key.capabilityBase layout.region.val ∈ keys)
    (lengthPresent : Memory.Key.capabilityLength layout.region.val ∈ keys)
    (mapped : layout.pointer = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (receipt : X86FailureHandler.FrameFacts state) : X86Bounds.Facts layout state := by
  have frameKnown : lookup state 7 = some (values (.register 0)) := known (.register 0) framePresent
  have baseRead : wordAt? (memory state) (values (.register 0) + BitVec.ofNat 64 (16 * layout.region.val)) =
      some (values (.capabilityBase layout.region.val)) := by
    have fieldRead : field? state (16 * layout.region.val) = some (values (.capabilityBase layout.region.val)) := by
      simpa only [readback,if_neg (by have := layout.region.isLt; omega : layout.region.val ≠ 255),
        if_pos layout.region.isLt] using known (.capabilityBase layout.region.val) basePresent
    unfold field? at fieldRead
    rw [frameKnown] at fieldRead
    exact fieldRead
  have lengthRead : wordAt? (memory state) (values (.register 0) + BitVec.ofNat 64 (16 * layout.region.val + 8)) =
      some (values (.capabilityLength layout.region.val)) := by
    have fieldRead : field? state (16 * layout.region.val + 8) = some (values (.capabilityLength layout.region.val)) := by
      simpa only [readback,if_neg (by have := layout.region.isLt; omega : layout.region.val ≠ 255),
        if_pos layout.region.isLt] using known (.capabilityLength layout.region.val) lengthPresent
    unfold field? at fieldRead
    rw [frameKnown] at fieldRead
    exact fieldRead
  have baseFacts := X86MemoryReadback.wordAt?_narrow_bytes state _ _ baseRead
  have lengthFacts := X86MemoryReadback.wordAt?_narrow_bytes state _ _ lengthRead
  have baseInside : 16 * layout.region.val < frameLayout.size := by have := layout.region.isLt; change _ < 192; omega
  have lengthInside : 16 * layout.region.val + 8 < frameLayout.size := by have := layout.region.isLt; change _ < 192; omega
  refine {
    frame := values (.register 0), base := values (.capabilityBase layout.region.val)
    pointer := values (.register pointer), length := values (.capabilityLength layout.region.val)
    baseAddress := X86CanonicalSpan.narrow (values (.register 0) + BitVec.ofNat 64 (16 * layout.region.val))
    lengthAddress := X86CanonicalSpan.narrow (values (.register 0) + BitVec.ofNat 64 (16 * layout.region.val + 8))
    controls := receipt.controls, visible := receipt.visible, flags := receipt.flags
    frameKnown := frameKnown, pointerKnown := ?_
    baseEffective := ?_, lengthEffective := ?_
    baseUpper := baseFacts.2.1, lengthUpper := lengthFacts.2.1
    baseAligned := ?_, lengthAligned := ?_
    controlKnown := receipt.controlsKnown, visibleKnown := receipt.visibleKnown
    flagsKnown := receipt.flagsKnown, quiet := receipt.quiet
    baseBytes := baseFacts.2.2, lengthBytes := lengthFacts.2.2 }
  · rw [mapped]
    exact known (.register pointer) pointerPresent
  · simpa only [X86Bounds.baseDisplacement,X86MemoryBounds.base_displacement] using baseFacts.1
  · simpa only [X86Bounds.lengthDisplacement,X86MemoryBounds.length_displacement] using lengthFacts.1
  · rw [X86CanonicalSpan.narrow_offset _ frameLayout.size _ (by decide) frameArea baseInside]
    exact X86CanonicalSpan.offset_aligned _ frameLayout.size _ (by decide) frameArea baseInside frameAligned (by omega)
  · rw [X86CanonicalSpan.narrow_offset _ frameLayout.size _ (by decide) frameArea lengthInside]
    exact X86CanonicalSpan.offset_aligned _ frameLayout.size _ (by decide) frameArea lengthInside frameAligned (by omega)

noncomputable def codeReads (base : Int) : Finset Nat :=
  (Finset.range X86P1SuccessCapture.image.size).image fun byte => ((address base byte).signExtend 52).toNat

def spanReads (pointer : Word) (size : Nat) : Finset Nat :=
  (Finset.range size).image fun byte => X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 byte)

/-- The six saved words above the call's stack pointer and the RBP save below it. -/
def stackReads {state : State} (caller : X86AllowanceCall.Inputs state) : Finset Nat :=
  (Finset.univ.biUnion fun slot : Fin 6 =>
    (Finset.range 8).image fun byte => X86WriteWords.physicalAddress (X86Prologue.stackAt caller.prologue slot.val) byte) ∪
  (Finset.range 8).image fun byte => X86WriteWords.physicalAddress caller.bottom byte

def budgetReads {state : State} (caller : X86AllowanceCall.Inputs state) : Finset Nat :=
  (Finset.range 8).image fun byte => X86WriteWords.physicalAddress caller.fuel.budgetAddress byte

noncomputable def protectedReads (base : Int) (values : Key → Word) : Finset Nat :=
  codeReads base ∪ spanReads (values (.register 0)) 32 ∪ spanReads (values (.register 1)) 24

/-- Raw entry observations and spatial resources, without a desired row or run. -/
structure EntryReadback (state : State) where
  caller : X86AllowanceCall.Inputs state
  receipt : X86FailureHandler.FrameFacts state
  values : Key → Word
  known : KnownOn (entryKeys (values (.register 1))) declaredModes values state
  base : Int
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + 647 < (2 ^ 47 : Int)
  loaded : X86P1LoadCapture.Loaded X86P1SuccessCapture.image state base
  entryAt : caller.prologue.code.toInt = base
  exitAt : caller.exit = address base 619
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  premiseArea : X86CanonicalSpan.Area (values (.register 1)) 24
  premiseAligned : (values (.register 1)).toNat % 8 = 0
  outputArea : X86CanonicalSpan.Area (values (.register 2)) 32
  outputAligned : (values (.register 2)).toNat % 8 = 0
  premiseFits : (values (.register 1) - values (.capabilityBase 0)).toNat + 24 ≤ (values (.capabilityLength 0)).toNat
  outputFits : (values (.register 2) - values (.capabilityBase 1)).toNat + 32 ≤ (values (.capabilityLength 1)).toNat
  prologueApart : Disjoint (protectedReads base values) (X86AllowanceCall.spillBytes caller.prologue.bottom caller.bottom)
  outputApart : Disjoint (protectedReads base values) (X86P1OutputCapture.outputWrites (X86CanonicalSpan.narrow (values (.register 2))))
  receiptApart : Disjoint (codeReads base ∪ X86P1OutputCapture.outputWrites (X86CanonicalSpan.narrow (values (.register 2))))
    (X86P1OutputCapture.receiptWrites receipt)
  stackApart : Disjoint (stackReads caller)
    (X86P1OutputCapture.outputWrites (X86CanonicalSpan.narrow (values (.register 2))) ∪ X86P1OutputCapture.receiptWrites receipt ∪
      X86AllowanceCall.receiptBytes caller.fuel.receiptAddress)
  receiptWordApart : Disjoint (codeReads base ∪ X86P1OutputCapture.outputWrites (X86CanonicalSpan.narrow (values (.register 2))) ∪
      X86P1OutputCapture.receiptWrites receipt) (X86AllowanceCall.receiptBytes caller.fuel.receiptAddress)
  budgetApart : Disjoint (budgetReads caller)
    (X86P1OutputCapture.outputWrites (X86CanonicalSpan.narrow (values (.register 2))) ∪ X86P1OutputCapture.receiptWrites receipt)

def EntryReadback.bytes {state : State} (input : EntryReadback state) : Fin 24 → BitVec 8 :=
  observedBytes input.values (input.values (.register 1))

theorem EntryReadback.byte_known {state : State} (input : EntryReadback state) (byte : Fin 24) :
    memory state (X86CanonicalSpan.physicalKey (input.values (.register 1) + BitVec.ofNat 64 byte.val)) =
      some (input.bytes byte) := by
  have found := observed_byte _ declaredModes input.values state input.known
    ((input.values (.register 1)).toNat + byte.val) (by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨byte.val,Finset.mem_range.mpr byte.isLt,rfl⟩)
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat] at found
  exact found

theorem offset_upper (pointer : Word) (size offset count : Nat) (positive : 0 < size)
    (area : X86CanonicalSpan.Area pointer size) (inside : offset < size) (fits : offset + count ≤ size) :
    (address (X86CanonicalSpan.narrow pointer).toInt offset).toInt + count ≤ (2 ^ 47 : Int) := by
  rw [← X86CanonicalSpan.narrow_offset pointer size offset positive area inside,
    X86CanonicalSpan.narrow_toInt _ (area.2 offset inside),
    X86CanonicalSpan.offset_signed pointer size offset positive area inside]
  have upper := X86CanonicalSpan.area_signed_upper pointer size positive area
  omega

theorem span_member (pointer : Word) (size first byte : Nat) (positive : 0 < size)
    (area : X86CanonicalSpan.Area pointer size) (inside : first + byte < size) :
    X86WriteWords.physicalAddress (address (X86CanonicalSpan.narrow pointer).toInt first) byte ∈ spanReads pointer size := by
  rw [X86CanonicalSpan.physicalAddress_nested pointer size first byte positive area inside]
  exact Finset.mem_image.mpr ⟨first + byte,Finset.mem_range.mpr inside,rfl⟩

theorem descriptor_member (pointer : Word) (area : X86CanonicalSpan.Area pointer frameLayout.size)
    (first byte : Nat) (inside : first + byte < 32) :
    X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (pointer + BitVec.ofNat 64 first)) byte ∈ spanReads pointer 32 := by
  have firstIn : first < frameLayout.size := by change first < 192; omega
  have within : first + byte < frameLayout.size := by change first + byte < 192; omega
  rw [X86CanonicalSpan.narrow_offset pointer frameLayout.size first (by decide) area firstIn,
    X86CanonicalSpan.physicalAddress_nested pointer frameLayout.size first byte (by decide) area within]
  exact Finset.mem_image.mpr ⟨first + byte,Finset.mem_range.mpr inside,rfl⟩

noncomputable def EntryReadback.outputFacts {state : State} (input : EntryReadback state) :
    X86Bounds.Facts (X86P1StoreCapture.boundsLayout 0) state :=
  boundsFacts _ declaredModes input.values state _ 2 input.known (by simp [entryKeys])
    (by simp [entryKeys]) (by simp [entryKeys,X86P1StoreCapture.boundsLayout,X86P1StoreCapture.site])
    (by simp [entryKeys,X86P1StoreCapture.boundsLayout,X86P1StoreCapture.site]) rfl
    input.frameArea input.frameAligned input.receipt

noncomputable def EntryReadback.premiseFacts {state : State} (input : EntryReadback state) :
    X86Bounds.Facts X86P1FieldLoadCapture.layout state :=
  boundsFacts _ declaredModes input.values state _ 1 input.known (by simp [entryKeys])
    (by simp [entryKeys]) (by simp [entryKeys,X86P1FieldLoadCapture.layout])
    (by simp [entryKeys,X86P1FieldLoadCapture.layout]) rfl
    input.frameArea input.frameAligned input.receipt

theorem EntryReadback.field_bytes {state : State} (input : EntryReadback state) (byte : Fin 8) :
    state.mem.get? (X86WriteWords.physicalAddress (address (X86CanonicalSpan.narrow (input.values (.register 1))).toInt 8) byte.val) =
      some ((decodeField input.bytes).extractLsb' (8 * byte.val) 8) := by
  rw [X86CanonicalSpan.physicalAddress_nested _ 24 8 byte.val (by decide) input.premiseArea (by have := byte.isLt; omega)]
  rw [decodeField,decodeWord_byte]
  exact input.byte_known ⟨8 + byte.val,by have := byte.isLt; omega⟩

/-- Bounds, decoded field and output protections earned from the finite observations. -/
noncomputable def EntryReadback.data {state : State} (input : EntryReadback state) : X86P1OutputCapture.DataFacts state := by
  let avoidsOutput := Finset.disjoint_left.mp input.outputApart
  refine {
    base := input.base, lower := input.lower, upper := input.upper, loaded := input.loaded
    outputFacts := input.outputFacts, premiseFacts := input.premiseFacts
    output := X86CanonicalSpan.narrow (input.values (.register 2))
    outputUpper := X86CanonicalSpan.area_narrow_upper _ 32 (by decide) input.outputArea
    outputEffective := (X86CanonicalSpan.narrow_representation _ (X86CanonicalSpan.area_base _ 32 (by decide) input.outputArea)).symm
    outputAligned := X86CanonicalSpan.narrow_aligned _ (X86CanonicalSpan.area_base _ 32 (by decide) input.outputArea) input.outputAligned
    outputFits := input.outputFits
    field := decodeField input.bytes
    fieldAddress := address (X86CanonicalSpan.narrow (input.values (.register 1))).toInt 8
    fieldUpper := offset_upper _ 24 8 8 (by decide) input.premiseArea (by decide) (by decide)
    fieldEffective := (X86CanonicalSpan.offset_representation _ 24 8 (by decide) input.premiseArea (by decide)).symm
    fieldAligned := X86CanonicalSpan.offset_aligned _ 24 8 (by decide) input.premiseArea (by decide) input.premiseAligned (by decide)
    fieldBytes := fun byte within => input.field_bytes ⟨byte,within⟩
    premiseFits := by
      change (input.values (.register 1) - input.values (.capabilityBase 0)).toNat + 16 ≤ (input.values (.capabilityLength 0)).toNat
      have := input.premiseFits
      omega
    codeApart := ?_, outputBaseApart := ?_, outputLengthApart := ?_
    premiseBaseApart := ?_, premiseLengthApart := ?_, fieldApart := ?_ }
  · intro byte within
    apply avoidsOutput
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩))
  · intro byte within
    apply avoidsOutput
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact descriptor_member _ input.frameArea 16 byte (by omega)
  · intro byte within
    apply avoidsOutput
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact descriptor_member _ input.frameArea 24 byte (by omega)
  · intro byte within
    apply avoidsOutput
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact descriptor_member _ input.frameArea 0 byte (by omega)
  · intro byte within
    apply avoidsOutput
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact descriptor_member _ input.frameArea 8 byte (by omega)
  · intro byte within
    apply avoidsOutput
    exact Finset.mem_union_right _ (span_member _ 24 8 byte (by decide) input.premiseArea (by omega))

noncomputable def EntryReadback.tagReadable {state : State} (input : EntryReadback state) :
    X86P1LoadBounds.Readable state input.premiseFacts.pointer (decodeTag input.bytes) := by
  refine {
    dataAddress := X86CanonicalSpan.narrow (input.values (.register 1))
    effective := (X86CanonicalSpan.narrow_representation _ (X86CanonicalSpan.area_base _ 24 (by decide) input.premiseArea)).symm
    upper := by have := X86CanonicalSpan.area_narrow_upper _ 24 (by decide) input.premiseArea; omega
    aligned := ?_, bytes := ?_ }
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (3#48).toNat = 2 ^ 2 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
    have aligned := (X86CanonicalSpan.narrow_mod8 _ (X86CanonicalSpan.area_base _ 24 (by decide) input.premiseArea)).trans input.premiseAligned
    change _ = 0
    omega
  · intro byte within
    change state.mem.get? (X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (input.values (.register 1))) byte) = _
    rw [← X86CanonicalSpan.physicalKey_offset _ 24 byte (by decide) input.premiseArea (by omega),decodeTag_byte input.bytes ⟨byte,within⟩]
    exact input.byte_known ⟨byte,by omega⟩

noncomputable def EntryReadback.levelReadable {state : State} (input : EntryReadback state) :
    X86P1QwordBounds.Readable state input.premiseFacts.pointer (decodeLevel input.bytes) := by
  refine {
    dataAddress := address (X86CanonicalSpan.narrow (input.values (.register 1))).toInt 16
    effective := (X86CanonicalSpan.offset_representation _ 24 16 (by decide) input.premiseArea (by decide)).symm
    upper := offset_upper _ 24 16 8 (by decide) input.premiseArea (by decide) (by decide)
    aligned := X86CanonicalSpan.offset_aligned _ 24 16 (by decide) input.premiseArea (by decide) input.premiseAligned (by decide)
    bytes := ?_ }
  intro byte within
  change state.mem.get? (X86WriteWords.physicalAddress (address (X86CanonicalSpan.narrow (input.values (.register 1))).toInt 16) byte) = _
  rw [X86CanonicalSpan.physicalAddress_nested _ 24 16 byte (by decide) input.premiseArea (by omega),decodeLevel,decodeWord_byte input.bytes 16 (by decide) ⟨byte,within⟩]
  exact input.byte_known ⟨16 + byte,by omega⟩

theorem EntryReadback.frame_eq {state : State} (input : EntryReadback state) :
    input.values (.register 0) = input.receipt.frame :=
  observed_frame _ declaredModes input.values state input.known (by simp [entryKeys]) input.receipt

theorem EntryReadback.mode_values {state : State} (input : EntryReadback state) :
    input.values (.capabilityMode 0) = (1#64) ∧ input.values (.capabilityMode 1) = (2#64) := by
  have first := input.known (.capabilityMode 0) (by simp [entryKeys])
  have second := input.known (.capabilityMode 1) (by simp [entryKeys])
  change some (declaredModes 0) = some (input.values (.capabilityMode 0)) at first
  change some (declaredModes 1) = some (input.values (.capabilityMode 1)) at second
  exact ⟨(Option.some.inj first).symm.trans declared_modes.1,(Option.some.inj second).symm.trans declared_modes.2⟩

theorem EntryReadback.premise_capacity {state : State} (input : EntryReadback state) :
    24 ≤ (input.values (.capabilityLength 0)).toNat := by
  have := input.premiseFits
  omega

theorem EntryReadback.output_capacity {state : State} (input : EntryReadback state) :
    32 ≤ (input.values (.capabilityLength 1)).toNat := by
  have := input.outputFits
  omega

theorem EntryReadback.field_output_apart {state : State} (input : EntryReadback state) :
    input.data.fieldAddress ≠ input.data.output := by
  intro equal
  have apart := input.data.fieldApart 0 (by decide)
  rw [equal] at apart
  exact apart (List.mem_toFinset.mpr (List.mem_map.mpr ⟨0,List.mem_range.mpr (by decide),rfl⟩))

theorem EntryReadback.readProtection {state : State} (input : EntryReadback state) :
    X86P1SuccessCapture.ReadProtection input.data
      (X86AllowanceCall.spillBytes input.caller.prologue.bottom input.caller.bottom) := by
  let avoids := Finset.disjoint_left.mp input.prologueApart
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro byte within
    apply avoids
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩))
  · intro byte within
    apply avoids
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (descriptor_member _ input.frameArea 16 byte (by omega)))
  · intro byte within
    apply avoids
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (descriptor_member _ input.frameArea 24 byte (by omega)))
  · intro byte within
    apply avoids
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (descriptor_member _ input.frameArea 0 byte (by omega)))
  · intro byte within
    apply avoids
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (descriptor_member _ input.frameArea 8 byte (by omega)))
  · intro byte within
    apply avoids
    exact Finset.mem_union_right _ (span_member _ 24 8 byte (by decide) input.premiseArea (by omega))

theorem EntryReadback.tag_apart {state : State} (input : EntryReadback state) :
    ∀ byte < 4, X86WriteWords.physicalAddress input.tagReadable.dataAddress byte ∉
      X86AllowanceCall.spillBytes input.caller.prologue.bottom input.caller.bottom := by
  intro byte within
  apply Finset.disjoint_left.mp input.prologueApart
  apply Finset.mem_union_right
  change X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (input.values (.register 1))) byte ∈ _
  simpa only [address,Int.natCast_zero,Int.add_zero,BitVec.ofInt_toInt] using
    span_member _ 24 0 byte (by decide) input.premiseArea (by omega)

theorem EntryReadback.level_apart {state : State} (input : EntryReadback state) :
    ∀ byte < 8, X86WriteWords.physicalAddress input.levelReadable.dataAddress byte ∉
      X86AllowanceCall.spillBytes input.caller.prologue.bottom input.caller.bottom := by
  intro byte within
  apply Finset.disjoint_left.mp input.prologueApart
  exact Finset.mem_union_right _ (span_member _ 24 16 byte (by decide) input.premiseArea (by omega))

theorem EntryReadback.code_receipt_apart {state : State} (input : EntryReadback state) :
    ∀ byte < X86P1SuccessCapture.image.size, ((address input.data.base byte).signExtend 52).toNat ∉
      X86P1OutputCapture.receiptWrites input.receipt := by
  intro byte within
  apply Finset.disjoint_left.mp input.receiptApart
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩)

theorem EntryReadback.output_receipt_apart {state : State} (input : EntryReadback state) :
    ∀ byte < 32, X86WriteWords.physicalAddress input.data.output byte ∉
      X86P1OutputCapture.receiptWrites input.receipt := by
  intro byte within
  apply Finset.disjoint_left.mp input.receiptApart
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩))

theorem EntryReadback.fuel {state : State} (input : EntryReadback state) :
    X86P1SuccessCapture.FuelProtection input.caller input.data (X86P1SuccessCapture.writes input.data input.receipt) where
  budget byte within := by
    apply Finset.disjoint_left.mp input.budgetApart
    exact Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩
  code byte within member :=
    Finset.disjoint_left.mp input.receiptWordApart
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩)))
      member
  output byte within member :=
    Finset.disjoint_left.mp input.receiptWordApart
      (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩)))) member
  bottom byte within := by
    apply Finset.disjoint_left.mp input.stackApart
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩)
  saved slot byte within := by
    apply Finset.disjoint_left.mp input.stackApart
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨slot,Finset.mem_univ _,Finset.mem_image.mpr ⟨byte,Finset.mem_range.mpr within,rfl⟩⟩)

theorem EntryReadback.status_receipt_apart {state : State} (input : EntryReadback state) :
    ∀ byte < 8, X86WriteWords.physicalAddress input.receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes input.caller.fuel.receiptAddress := by
  intro byte within
  apply Finset.disjoint_left.mp input.receiptWordApart
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩)

theorem EntryReadback.result_receipt_apart {state : State} (input : EntryReadback state) :
    ∀ byte < 8, X86WriteWords.physicalAddress input.receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes input.caller.fuel.receiptAddress := by
  intro byte within
  apply Finset.disjoint_left.mp input.receiptWordApart
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩)

theorem EntryReadback.old_known {state : State} (input : EntryReadback state) :
    lookup state 11 = some (input.values (.register 7)) :=
  input.known (.register 7) (by simp [entryKeys])

theorem prefix_readback (state : State) (pointer field : Word) (area : X86CanonicalSpan.Area pointer 32)
    (written : X86P1OutputCapture.Prefix state (X86CanonicalSpan.narrow pointer) field 32) (byte : Fin 32) :
    readback declaredModes state (.byte (pointer.toNat + byte.val)) =
      some ((X86P1OutputCapture.encoded field byte.val).zeroExtend 64) := by
  apply readback_byte_known
  · have := area.1
    have := byte.isLt
    omega
  · rw [BitVec.ofNat_add,BitVec.ofNat_toNat]
    exact area.2 byte.val byte.isLt
  · rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      X86CanonicalSpan.physicalKey_offset pointer 32 byte.val (by decide) area byte.isLt]
    exact written byte.val byte.isLt

/-- The whole caller execution, source conclusion and auxiliary effects at one entry. -/
theorem public_rule_from_entry (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (input : EntryReadback state) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches (X86P1PropRefinement.callSteps (decodeTag input.bytes) (decodeLevel input.bytes))).run state = .ok () after ∧
      X86AllowanceCall.Result input.caller
        (X86P1PropRefinement.effects input.data input.receipt (decodeTag input.bytes) (decodeLevel input.bytes))
        (input.caller.fuel.budget - input.caller.fuel.receipt) body after ∧
      (∀ conclusion : RuleTable.Tuple,
        RuleTable.Derives X86P1PropRefinement.entry.source
          [⟨(decodeTag input.bytes).toNat,[decodeField input.bytes,decodeLevel input.bytes]⟩] conclusion ↔
          lookup after 0 = some (1#64) ∧ conclusion = ⟨7173,[decodeField input.bytes]⟩) ∧
      lookup after 0 = some (X86P1PropRefinement.answer (decodeTag input.bytes) (decodeLevel input.bytes)) ∧
      (lookup after 0 = some (1#64) → ∀ byte : Fin 32,
        readback declaredModes after (.byte ((input.values (.register 2)).toNat + byte.val)) =
          some ((X86P1OutputCapture.encoded (decodeField input.bytes) byte.val).zeroExtend 64)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress input.receipt.statusAddress byte) =
        some ((X86P1PropRefinement.answer (decodeTag input.bytes) (decodeLevel input.bytes)).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress input.receipt.resultAddress byte) =
        some ((X86P1PropRefinement.answer (decodeTag input.bytes) (decodeLevel input.bytes)).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress input.caller.fuel.receiptAddress byte) =
        some (input.caller.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded X86P1SuccessCapture.image after input.base := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  have fits : (input.data.premiseFacts.pointer - input.data.premiseFacts.base).toNat + 24 ≤ input.data.premiseFacts.length.toNat := input.premiseFits
  obtain ⟨body,after,run,correct,rule,output,image⟩ := X86P1PropRefinement.public_refines_rule other extra vector state input.caller input.data
    input.entryAt input.exitAt input.receipt (decodeTag input.bytes) input.tagReadable
    (decodeLevel input.bytes) (fun _ => input.levelReadable) (fun _ => fits)
    input.readProtection input.tag_apart (fun _ => input.level_apart) input.code_receipt_apart input.output_receipt_apart
    input.status_receipt_apart input.result_receipt_apart input.fuel
  obtain ⟨_,after',run',_,value,_,status,result,published,_⟩ := X86P1PropRefinement.public_classifies other extra vector state input.caller input.data
    input.entryAt input.exitAt input.receipt (decodeTag input.bytes) input.tagReadable
    (decodeLevel input.bytes) (fun _ => input.levelReadable) (fun _ => fits)
    input.readProtection input.tag_apart (fun _ => input.level_apart) input.code_receipt_apart input.output_receipt_apart
    input.status_receipt_apart input.result_receipt_apart input.fuel
  have same : after' = after := by
    have equal := run'.symm.trans run
    cases equal
    rfl
  subst after'
  refine ⟨body,after,run,correct,rule,value,?_,status,result,published,image⟩
  intro accepted byte
  exact prefix_readback after _ (decodeField input.bytes) input.outputArea (output accepted) byte

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePropEntryReadback
