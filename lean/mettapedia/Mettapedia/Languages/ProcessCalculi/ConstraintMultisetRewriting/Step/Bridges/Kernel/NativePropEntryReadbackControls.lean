import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativePropEntryReadback

/-!
# Public-caller byte observations and complete proposition-rule controls

The positive uses the existing public entry, whose premise has only twenty-four
backed bytes and whose old output is not present. No memory map is copied or changed.
Mode provenance remains a source declaration, without an issuer certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePropEntryReadback.Controls

open Mettapedia.Machines.TIsa
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView

noncomputable abbrev entry (field : Word) := X86P1SuccessCapture.Controls.entryFixture field
noncomputable abbrev observations (field : Word) := X86P1SuccessCapture.Controls.entryObservations field

/-- Values are used only on the explicitly observed finite keys. -/
def values (field : Word) : Key → Word
  | .register register => if register = 0 then 8192 else if register = 1 then 12288 else if register = 2 then 16384 else 0
  | .capabilityBase region => if region = 0 then 12288 else if region = 1 then 16384 else 0
  | .capabilityLength region => if region < 2 then 32 else 0
  | .capabilityMode region => if region = 0 then 1 else if region = 1 then 2 else 0
  | .byte location => if inside : location - 12288 < 24 then
      (X86P1OutputCapture.Controls.fixturePremiseByte field ⟨location - 12288,inside⟩).zeroExtend 64 else 0

theorem physical_low (base byte : Nat) (small : base + byte < 2 ^ 47) :
    X86CanonicalSpan.physicalKey (BitVec.ofNat 64 base + BitVec.ofNat 64 byte) = base + byte := by
  rw [← BitVec.ofNat_add]
  have bounded : base + byte < 2 ^ 64 := by omega
  have natValue : (BitVec.ofNat 64 (base + byte)).toNat = base + byte := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded]
  have signed : (BitVec.ofNat 64 (base + byte)).toInt = ((base + byte : Nat) : Int) := by
    rw [X86CanonicalSpan.low_toInt _ (by rw [natValue]; exact small),natValue]
  unfold X86CanonicalSpan.physicalKey X86CanonicalSpan.narrow
  rw [signed]
  simpa only [address,Nat.cast_add] using X86P1OutputCapture.Controls.positive_address base byte small

theorem field_known (state : State) (frame value : Word) (offset : Nat)
    (frameKnown : lookup state 7 = some frame)
    (wordKnown : wordAt? (memory state) (frame + BitVec.ofNat 64 offset) = some value) :
    field? state offset = some value := by
  unfold field?
  rw [frameKnown]
  exact wordKnown

theorem descriptor_zero (field : Word) :
    wordAt? (memory (entry field).state) (8192#64) = some (12288#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro byte within
  rw [physical_low 8192 byte (by omega)]
  have got := (entry field).data.premiseFacts.baseBytes byte within
  change (entry field).state.mem.get? (X86WriteWords.physicalAddress (8192#48) byte) = _ at got
  rw [show X86WriteWords.physicalAddress (8192#48) byte = 8192 + byte from
    X86P1OutputCapture.Controls.positive_address 8192 byte (by omega)] at got
  exact got

theorem descriptor_eight (field : Word) :
    wordAt? (memory (entry field).state) (8200#64) = some (32#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro byte within
  rw [physical_low 8200 byte (by omega)]
  have got := (entry field).data.premiseFacts.lengthBytes byte within
  change (entry field).state.mem.get? (X86WriteWords.physicalAddress (8200#48) byte) = _ at got
  rw [show X86WriteWords.physicalAddress (8200#48) byte = 8200 + byte from
    X86P1OutputCapture.Controls.positive_address 8200 byte (by omega)] at got
  exact got

theorem descriptor_sixteen (field : Word) :
    wordAt? (memory (entry field).state) (8208#64) = some (16384#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro byte within
  rw [physical_low 8208 byte (by omega)]
  have got := (entry field).data.outputFacts.baseBytes byte within
  change (entry field).state.mem.get? (X86WriteWords.physicalAddress (8208#48) byte) = _ at got
  rw [show X86WriteWords.physicalAddress (8208#48) byte = 8208 + byte from
    X86P1OutputCapture.Controls.positive_address 8208 byte (by omega)] at got
  exact got

theorem descriptor_twentyfour (field : Word) :
    wordAt? (memory (entry field).state) (8216#64) = some (32#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro byte within
  rw [physical_low 8216 byte (by omega)]
  have got := (entry field).data.outputFacts.lengthBytes byte within
  change (entry field).state.mem.get? (X86WriteWords.physicalAddress (8216#48) byte) = _ at got
  rw [show X86WriteWords.physicalAddress (8216#48) byte = 8216 + byte from
    X86P1OutputCapture.Controls.positive_address 8216 byte (by omega)] at got
  exact got

theorem known (field : Word) :
    KnownOn (entryKeys (12288#64)) declaredModes (values field) (entry field).state := by
  intro item member
  rcases Finset.mem_union.mp member with fixed | byte
  · simp only [Finset.mem_insert,Finset.mem_singleton] at fixed
    rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (entry field).receipt.frameKnown
    · exact (entry field).data.premiseFacts.pointerKnown
    · exact (entry field).data.outputFacts.pointerKnown
    · exact (observations field).oldKnown
    · change field? (entry field).state 0 = some (12288#64)
      exact field_known _ (8192#64) _ 0 (entry field).receipt.frameKnown (descriptor_zero field)
    · change field? (entry field).state 8 = some (32#64)
      exact field_known _ (8192#64) _ 8 (entry field).receipt.frameKnown (descriptor_eight field)
    · exact congrArg some declared_modes.1
    · change field? (entry field).state 16 = some (16384#64)
      exact field_known _ (8192#64) _ 16 (entry field).receipt.frameKnown (descriptor_sixteen field)
    · change field? (entry field).state 24 = some (32#64)
      exact field_known _ (8192#64) _ 24 (entry field).receipt.frameKnown (descriptor_twentyfour field)
    · exact congrArg some declared_modes.2
  · obtain ⟨offset,inside,rfl⟩ := Finset.mem_image.mp byte
    have within : offset < 24 := Finset.mem_range.mp inside
    have bounded : 12288 + offset < 2 ^ 64 := by omega
    have canonical : X86CanonicalSpan.Canonical (BitVec.ofNat 64 (12288 + offset)) := by
      apply Or.inl
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded]
      omega
    have backing := (observations field).premiseBytes ⟨offset,within⟩
    have present : memory (entry field).state (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (12288 + offset))) =
        some (X86P1OutputCapture.Controls.fixturePremiseByte field ⟨offset,within⟩) := by
      rw [BitVec.ofNat_add,physical_low 12288 offset (by omega)]
      exact backing
    have actual := readback_byte_known declaredModes (entry field).state (12288 + offset) _ bounded canonical present
    simpa only [values,show (12288#64).toNat = 12288 from rfl,Nat.add_sub_cancel_left,
      dif_pos within] using actual

theorem span_bounds (base size location : Nat) (small : base + size < 2 ^ 47)
    (member : location ∈ spanReads (BitVec.ofNat 64 base) size) : base ≤ location ∧ location < base + size := by
  obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp member
  have within := Finset.mem_range.mp within
  rw [physical_low base byte (by omega)]
  omega

theorem written_bounds (pointer : BitVec 48) (base size location : Nat) (same : pointer.toInt = base)
    (small : base + size < 2 ^ 47) (member : location ∈ X86WriteWords.written pointer (List.range size)) :
    base ≤ location ∧ location < base + size := by
  obtain ⟨byte,within,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  have within := List.mem_range.mp within
  unfold X86WriteWords.physicalAddress
  rw [same,X86P1OutputCapture.Controls.positive_address base byte (by omega)]
  omega

theorem protected_bounds (field : Word) (location : Nat) (member : location ∈ protectedReads 4096 (values field)) :
    location < 12312 := by
  rcases Finset.mem_union.mp member with first | premise
  · rcases Finset.mem_union.mp first with code | descriptor
    · obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp code
      have within : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using Finset.mem_range.mp within
      rw [show ((address (4096 : Int) byte).signExtend 52).toNat = 4096 + byte from
        X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)]
      omega
    · have := span_bounds 8192 32 location (by decide) descriptor
      omega
  · have := span_bounds 12288 24 location (by decide) premise
    omega

theorem receipt_bounds (field : Word) (location : Nat) (member : location ∈ X86P1OutputCapture.receiptWrites (entry field).receipt) :
    8336 ≤ location ∧ location < 8352 := by
  rcases Finset.mem_union.mp member with status | result
  · have := written_bounds (8336#48) 8336 8 location rfl (by decide) status
    omega
  · have := written_bounds (8344#48) 8344 8 location rfl (by decide) result
    omega

theorem stack_bounds (field : Word) (location : Nat) (member : location ∈ stackReads (entry field).caller) :
    32720 ≤ location := by
  rcases Finset.mem_union.mp member with saved | sixth
  · obtain ⟨slot,_,byteMember⟩ := Finset.mem_biUnion.mp saved
    obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp byteMember
    have within := Finset.mem_range.mp within
    rw [X86Prologue.stack_byte (entry field).caller.prologue slot.val byte (by have := slot.isLt; omega)]
    have point : X86WriteWords.physicalAddress (32728#48) (8 * slot.val + byte) = 32728 + (8 * slot.val + byte) :=
      X86P1OutputCapture.Controls.positive_address 32728 _ (by have := slot.isLt; omega)
    change 32720 ≤ X86WriteWords.physicalAddress (32728#48) (8 * slot.val + byte)
    rw [point]
    omega
  · obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp sixth
    have within := Finset.mem_range.mp within
    change 32720 ≤ X86WriteWords.physicalAddress (32720#48) byte
    have point : X86WriteWords.physicalAddress (32720#48) byte = 32720 + byte :=
      X86P1OutputCapture.Controls.positive_address 32720 byte (by omega)
    rw [point]
    omega

theorem receipt_word_bounds (field : Word) (location : Nat)
    (member : location ∈ X86AllowanceCall.receiptBytes (entry field).caller.fuel.receiptAddress) :
    8360 ≤ location ∧ location < 8368 :=
  written_bounds (8360#48) 8360 8 location rfl (by decide) member

theorem budget_bounds (field : Word) (location : Nat) (member : location ∈ budgetReads (entry field).caller) :
    8352 ≤ location ∧ location < 8360 := by
  obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp member
  have within := Finset.mem_range.mp within
  change 8352 ≤ X86WriteWords.physicalAddress (8352#48) byte ∧ X86WriteWords.physicalAddress (8352#48) byte < 8360
  have point : X86WriteWords.physicalAddress (8352#48) byte = 8352 + byte :=
    X86P1OutputCapture.Controls.positive_address 8352 byte (by omega)
  rw [point]
  omega

/-- This constructs raw finite observations on the existing public caller only. -/
noncomputable def input (field : Word) : EntryReadback (entry field).state where
  caller := (entry field).caller
  receipt := (entry field).receipt
  values := values field
  known := known field
  base := 4096
  lower := by decide
  upper := by decide
  loaded := by simpa only [(observations field).baseValue] using (entry field).data.loaded
  entryAt := (observations field).entryAt.trans (observations field).baseValue
  exitAt := by simpa only [(observations field).baseValue] using (observations field).exitAt
  frameArea := X86CanonicalSpan.area_low (8192#64) 192 (by decide)
  frameAligned := by change (8192#64).toNat % 8 = 0; decide
  premiseArea := X86CanonicalSpan.area_low (12288#64) 24 (by decide)
  premiseAligned := by change (12288#64).toNat % 8 = 0; decide
  outputArea := X86CanonicalSpan.area_low (16384#64) 32 (by decide)
  outputAligned := by change (16384#64).toNat % 8 = 0; decide
  premiseFits := by change ((12288#64) - (12288#64)).toNat + 24 ≤ (32#64).toNat; decide
  outputFits := by change ((16384#64) - (16384#64)).toNat + 32 ≤ (32#64).toNat; decide
  prologueApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have low := protected_bounds field location member
    rcases Finset.mem_union.mp collision with five | sixth
    · have high := written_bounds (32728#48) 32728 40 location rfl (by decide) five
      omega
    · have high := written_bounds (32720#48) 32720 8 location rfl (by decide) sixth
      omega
  outputApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have low := protected_bounds field location member
    have high := written_bounds (16384#48) 16384 32 location rfl (by decide) collision
    omega
  receiptApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have bounds := receipt_bounds field location collision
    rcases Finset.mem_union.mp member with code | output
    · obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp code
      have within : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using Finset.mem_range.mp within
      rw [show ((address (4096 : Int) byte).signExtend 52).toNat = 4096 + byte from
        X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)] at bounds
      omega
    · have output := written_bounds (16384#48) 16384 32 location rfl (by decide) output
      omega
  stackApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have high := stack_bounds field location member
    rcases Finset.mem_union.mp collision with written | receiptWord
    · rcases Finset.mem_union.mp written with output | receipt
      · have low := written_bounds (16384#48) 16384 32 location rfl (by decide) output
        omega
      · have low := receipt_bounds field location receipt
        omega
    · have low := receipt_word_bounds field location receiptWord
      omega
  receiptWordApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have bounds := receipt_word_bounds field location collision
    rcases Finset.mem_union.mp member with codeOrOutput | receipt
    · rcases Finset.mem_union.mp codeOrOutput with code | output
      · obtain ⟨byte,within,rfl⟩ := Finset.mem_image.mp code
        have within : byte < 647 := by simpa only [X86P1LoadCapture.byte_extent] using Finset.mem_range.mp within
        rw [show ((address (4096 : Int) byte).signExtend 52).toNat = 4096 + byte from
          X86P1OutputCapture.Controls.positive_address 4096 byte (by omega)] at bounds
        omega
      · have output := written_bounds (16384#48) 16384 32 location rfl (by decide) output
        omega
    · have low := receipt_bounds field location receipt
      omega
  budgetApart := by
    apply Finset.disjoint_left.mpr
    intro location member collision
    have bounds := budget_bounds field location member
    rcases Finset.mem_union.mp collision with output | receipt
    · have output := written_bounds (16384#48) 16384 32 location rfl (by decide) output
      omega
    · have low := receipt_bounds field location receipt
      omega

@[simp] theorem input_values (field : Word) : (input field).values = values field := rfl
@[simp] theorem input_caller (field : Word) : (input field).caller = (entry field).caller := rfl
@[simp] theorem input_receipt (field : Word) : (input field).receipt = (entry field).receipt := rfl

theorem input_bytes (field : Word) (byte : Fin 24) :
    (input field).bytes byte = X86P1OutputCapture.Controls.fixturePremiseByte field byte := by
  rw [EntryReadback.bytes,input_values]
  change ((values field (.byte (12288 + byte.val))).extractLsb' 0 8) = _
  simp only [values,Nat.add_sub_cancel_left,dif_pos byte.isLt,X86MemoryReadback.byte_extract]

theorem eq_of_bytes {count : Nat} (left right : BitVec (8 * count))
    (same : ∀ byte : Fin count, left.extractLsb' (8 * byte.val) 8 = right.extractLsb' (8 * byte.val) 8) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  have quotient : bit / 8 < count := by omega
  have remainder : bit % 8 < 8 := Nat.mod_lt _ (by decide)
  have coordinate : 8 * (bit / 8) + bit % 8 = bit := by omega
  have equal := congrArg (fun value : BitVec 8 => value.getLsbD (bit % 8)) (same ⟨bit / 8,quotient⟩)
  simpa only [BitVec.getLsbD_extractLsb',remainder,decide_true,Bool.true_and,coordinate] using equal

theorem decoded_tag (field : Word) : decodeTag (input field).bytes = (6661#32) := by
  apply eq_of_bytes (count := 4)
  intro byte
  rw [decodeTag_byte,input_bytes]
  change (if byte.val < 4 then (6661#32).extractLsb' (8 * byte.val) 8 else
    if byte.val < 8 then 0 else if byte.val < 16 then field.extractLsb' (8 * (byte.val - 8)) 8 else 0) = _
  rw [if_pos byte.isLt]

theorem decoded_field (field : Word) : decodeField (input field).bytes = field := by
  apply eq_of_bytes (count := 8)
  intro byte
  rw [decodeField,decodeWord_byte,input_bytes]
  change (if 8 + byte.val < 4 then (6661#32).extractLsb' (8 * (8 + byte.val)) 8 else
    if 8 + byte.val < 8 then 0 else if 8 + byte.val < 16 then field.extractLsb' (8 * ((8 + byte.val) - 8)) 8 else 0) = _
  rw [if_neg (by omega),if_neg (by omega),if_pos (by have := byte.isLt; omega),Nat.add_sub_cancel_left]

theorem decoded_level (field : Word) : decodeLevel (input field).bytes = (0#64) := by
  apply eq_of_bytes (count := 8)
  intro byte
  rw [decodeLevel,decodeWord_byte,input_bytes]
  change (if 16 + byte.val < 4 then (6661#32).extractLsb' (8 * (16 + byte.val)) 8 else
    if 16 + byte.val < 8 then 0 else if 16 + byte.val < 16 then field.extractLsb' (8 * ((16 + byte.val) - 8)) 8 else 0) = _
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),BitVec.extractLsb'_zero]
  rfl

/-- The decoded same public fixture earns the complete successful caller result. -/
theorem public_call (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (field : Word) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches 106).run (entry field).state = .ok () after ∧
      X86AllowanceCall.Result (entry field).caller
        (X86P1SuccessCapture.writes (input field).data (entry field).receipt)
        ((entry field).caller.fuel.budget - (entry field).caller.fuel.receipt) body after ∧
      (∀ conclusion : RuleTable.Tuple,
        RuleTable.Derives X86P1PropRefinement.entry.source [⟨6661,[field,0]⟩] conclusion ↔
          lookup after 0 = some (1#64) ∧ conclusion = ⟨7173,[field]⟩) ∧
      lookup after 0 = some (1#64) ∧
      (∀ byte : Fin 32, readback declaredModes after (.byte (16384 + byte.val)) =
        some ((X86P1OutputCapture.encoded field byte.val).zeroExtend 64)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (entry field).receipt.statusAddress byte) =
        some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (entry field).receipt.resultAddress byte) =
        some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (entry field).caller.fuel.receiptAddress byte) =
        some ((entry field).caller.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded X86P1SuccessCapture.image after 4096 := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨body,after,run,correct,rule,value,bytes,status,result,published,image⟩ :=
    public_rule_from_entry other extra vector (entry field).state (input field)
  rw [decoded_tag,decoded_level] at run correct value status result
  rw [decoded_tag,decoded_field,decoded_level] at rule
  rw [decoded_field] at bytes
  have accepts : X86P1PropRefinement.accepts (6661#32) (0#64) := ⟨rfl,rfl⟩
  have valueOne : lookup after 0 = some (1#64) := by simpa only [X86P1PropRefinement.answer,if_pos accepts] using value
  refine ⟨body,after,?_,?_,rule,valueOne,bytes valueOne,?_,?_,published,image⟩
  · simpa only [X86P1PropRefinement.callSteps,if_pos accepts] using run
  · simpa only [X86P1PropRefinement.effects,if_pos accepts,input_caller,input_receipt] using correct
  · simpa only [X86P1PropRefinement.answer,if_pos accepts,input_receipt] using status
  · simpa only [X86P1PropRefinement.answer,if_pos accepts,input_receipt] using result

theorem high_bit_call (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches 106).run (entry (0x80000001000000ff#64)).state = .ok () after ∧
      X86AllowanceCall.Result (entry (0x80000001000000ff#64)).caller
        (X86P1SuccessCapture.writes (input (0x80000001000000ff#64)).data (entry (0x80000001000000ff#64)).receipt)
        ((entry (0x80000001000000ff#64)).caller.fuel.budget - (entry (0x80000001000000ff#64)).caller.fuel.receipt)
        body after ∧
      lookup after 0 = some (1#64) ∧
      (∀ byte : Fin 32, readback declaredModes after (.byte (16384 + byte.val)) =
        some ((X86P1OutputCapture.encoded (0x80000001000000ff#64) byte.val).zeroExtend 64)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (entry (0x80000001000000ff#64)).receipt.statusAddress byte) =
        some ((1#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (entry (0x80000001000000ff#64)).receipt.resultAddress byte) =
        some ((1#64).extractLsb' (8 * byte) 8)) := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨body,after,run,correct,_,answer,bytes,status,result,_,_⟩ := public_call other extra vector (0x80000001000000ff#64)
  exact ⟨body,after,run,correct,answer,bytes,status,result⟩

theorem high_bit_output_cannot_truncate (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after,
      (X86FuelPrefix.fetches 106).run (entry (0x80000001000000ff#64)).state = .ok () after ∧
      X86AllowanceCall.Result (entry (0x80000001000000ff#64)).caller
        (X86P1SuccessCapture.writes (input (0x80000001000000ff#64)).data (entry (0x80000001000000ff#64)).receipt)
        ((entry (0x80000001000000ff#64)).caller.fuel.budget - (entry (0x80000001000000ff#64)).caller.fuel.receipt)
        body after ∧
      (∀ byte : Fin 32, readback declaredModes after (.byte (16384 + byte.val)) =
        some ((X86P1OutputCapture.encoded (0x80000001000000ff#64) byte.val).zeroExtend 64)) ∧
      readback declaredModes after (.byte 16396) ≠
        some ((X86P1OutputCapture.encoded (((0x80000001000000ff#64).extractLsb' 0 32).zeroExtend 64) 12).zeroExtend 64) := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨body,after,run,correct,_,_,bytes,_,_,_,_⟩ := public_call other extra vector (0x80000001000000ff#64)
  refine ⟨body,after,run,correct,bytes,?_⟩
  have observed := bytes ⟨12,by decide⟩
  change readback declaredModes after (.byte 16396) =
    some ((X86P1OutputCapture.encoded (0x80000001000000ff#64) 12).zeroExtend 64) at observed
  rw [observed]
  decide

theorem capacity_is_not_backing (field : Word) :
    ¬ ∀ byte : Fin 32, ∃ value : BitVec 8, (entry field).state.mem.get? (12288 + byte.val) = some value :=
  X86P1SuccessCapture.Controls.premise_capacity_not_full_backing field

theorem old_output_is_unwritten (field : Word) (byte : Fin 32) :
    (entry field).state.mem.get? (16384 + byte.val) = none := (observations field).outputUnobserved byte

theorem no_old_output_readback (field : Word) (byte : Fin 32) :
    ¬ ∃ value, readback declaredModes (entry field).state (.byte (16384 + byte.val)) = some value := by
  rintro ⟨value,knownByte⟩
  obtain ⟨_,_,actual,present,_⟩ := X86MemoryReadback.byte_observed declaredModes (entry field).state _ value knownByte
  rw [BitVec.ofNat_add,physical_low 16384 byte.val (by have := byte.isLt; omega)] at present
  change (entry field).state.mem.get? (16384 + byte.val) = some actual at present
  rw [old_output_is_unwritten field byte] at present
  cases present

theorem field_not_truncated :
    decodeField (input (0x80000001000000ff#64)).bytes ≠
      ((0x80000001000000ff#64).extractLsb' 0 32).zeroExtend 64 := by
  rw [decoded_field]
  decide

def levelWindow (level : Word) (byte : Fin 24) : BitVec 8 :=
  if byte.val < 16 then 0 else level.extractLsb' (8 * (byte.val - 16)) 8

theorem levelWindow_decoded (level : Word) : decodeLevel (levelWindow level) = level := by
  apply eq_of_bytes (count := 8)
  intro byte
  rw [decodeLevel,decodeWord_byte]
  simp only [levelWindow,show ¬16 + byte.val < 16 by omega,if_false,Nat.add_sub_cancel_left]

/-- A codec/source-guard control, without an invented nonzero-level native fixture. -/
theorem full_high_level_refused (field : Word) (conclusion : RuleTable.Tuple) :
    decodeLevel (levelWindow (0x100000000#64)) = (0x100000000#64) ∧
      ¬ RuleTable.Derives X86P1PropRefinement.entry.source
        [⟨6661,[field,decodeLevel (levelWindow (0x100000000#64))]⟩] conclusion := by
  rw [levelWindow_decoded]
  exact ⟨rfl,X86P1PropRefinement.Controls.high_level_refused field conclusion⟩

theorem wrong_conclusion_refused (field : Word) :
    ¬ RuleTable.Derives X86P1PropRefinement.entry.source [⟨6661,[decodeField (input field).bytes,0]⟩]
      ⟨7174,[field]⟩ := by
  rw [decoded_field]
  exact X86P1PropRefinement.Controls.wrong_conclusion_refused field

theorem wrong_tag_refused (field level : Word) (conclusion : RuleTable.Tuple) :
    ¬ RuleTable.Derives X86P1PropRefinement.entry.source [⟨0,[field,level]⟩] conclusion :=
  X86P1PropRefinement.Controls.wrong_tag_refused field level conclusion

theorem actual_flags (field : Word) : (input field).receipt.flags = (0x200#32) ∧
    ((input field).receipt.flags).getLsbD 18 = false := by
  rw [input_receipt]
  refine ⟨rfl,?_⟩
  change (0x200#32).getLsbD 18 = false
  decide

theorem modes_are_not_free (state : State) : readback declaredModes state (.capabilityMode 0) ≠ some (0#64) := by
  change some (declaredModes 0) ≠ some (0#64)
  rw [declared_modes.1]
  decide

theorem short_premise_refused (state : State) (actual : EntryReadback state) :
    actual.values (.capabilityLength 0) ≠ (23#64) := by
  intro equal
  have enough := actual.premise_capacity
  rw [equal] at enough
  norm_num at enough

theorem short_output_refused (state : State) (actual : EntryReadback state) :
    actual.values (.capabilityLength 1) ≠ (31#64) := by
  intro equal
  have enough := actual.output_capacity
  rw [equal] at enough
  norm_num at enough

theorem missing_read_membership :
    Memory.Key.byte 12288 ∉ (entryKeys (12288#64)).erase (.byte 12288) := by simp

theorem unread_suffix_not_required (byte : Fin 8) :
    Memory.Key.byte (12312 + byte.val) ∉ entryKeys (12288#64) := by
  intro member
  simp [entryKeys,premiseKeys] at member
  obtain ⟨offset,within,equal⟩ := member
  omega

theorem old_output_not_required (byte : Fin 32) :
    Memory.Key.byte (16384 + byte.val) ∉ entryKeys (12288#64) := by
  intro member
  simp [entryKeys,premiseKeys] at member
  obtain ⟨offset,within,equal⟩ := member
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePropEntryReadback.Controls
