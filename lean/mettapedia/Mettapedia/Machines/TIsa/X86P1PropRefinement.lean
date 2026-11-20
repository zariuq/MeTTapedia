import Mettapedia.Machines.TIsa.ImportedTheory
import Mettapedia.Machines.TIsa.X86P1RejectionCapture

/-!
# The actual proposition rule related to native call observations

The declarative rule retains its shared word assignment. Its exact tag/zero
guard and unique conclusion are characterized independently of native runs.
The native classifier joins the proved successful and refused calls, with
their distinct instruction counts, receipts and byte footprints.

The final theorem relates return value1 to derivability from the observed
two-field premise and supplies the canonical output bytes on success. It is
conditional on readable row/capability observations and protected call memory.
Malformed frames, actual admission/hosting and the generic emitter theorem
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1PropRefinement
open RuleTable
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def entry : TheoryData.Entry := ImportedTheory.entries[13]'(by decide)

theorem identity : entry.id = 13 ∧ entry.name = "R_DERIVE_IS_PROP" ∧ entry.role = .premise := by decide

theorem derives (field : Word) :
    RuleTable.Derives entry.source [⟨6661,[field,0]⟩] ⟨7173,[field]⟩ := by
  refine ⟨fun _ => field,?_,?_⟩ <;> rfl

theorem zero_guard_necessary (field level : Word) (nonzero : level ≠ 0) (conclusion : Tuple) :
    ¬ RuleTable.Derives entry.source [⟨6661,[field,level]⟩] conclusion := by
  rintro ⟨assignment,premises,_⟩
  have second := congrArg (fun tuples : List Tuple => (tuples[0]?).bind (fun tuple => tuple.fields[1]?)) premises
  change some level = some (0#64) at second
  exact nonzero (Option.some.inj second)

theorem derives_iff (tag : BitVec 32) (field level : Word) (conclusion : Tuple) :
    RuleTable.Derives entry.source [⟨tag.toNat,[field,level]⟩] conclusion ↔
      tag = (6661#32) ∧ level = (0#64) ∧ conclusion = ⟨7173,[field]⟩ := by
  constructor
  · rintro ⟨assignment,premises,output⟩
    have head := congrArg (fun tuples : List Tuple => (tuples[0]?).map Tuple.tag) premises
    change some tag.toNat = some 6661 at head
    have tagMatch : tag = (6661#32) := BitVec.eq_of_toNat_eq (Option.some.inj head)
    have first := congrArg (fun tuples : List Tuple => (tuples[0]?).bind (fun tuple => tuple.fields[0]?)) premises
    change some field = some (assignment 0) at first
    have second := congrArg (fun tuples : List Tuple => (tuples[0]?).bind (fun tuple => tuple.fields[1]?)) premises
    change some level = some (0#64) at second
    change conclusion = (⟨7173,[assignment 0]⟩ : Tuple) at output
    rw [← Option.some.inj first] at output
    exact ⟨tagMatch,Option.some.inj second,output⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact derives field


def accepts (tag : BitVec 32) (level : Word) : Prop := tag = (6661#32) ∧ level = (0#64)
instance (tag : BitVec 32) (level : Word) : Decidable (accepts tag level) := inferInstanceAs (Decidable (_ ∧ _))
def answer (tag : BitVec 32) (level : Word) : Word := if accepts tag level then (1#64) else (0#64)
def callSteps (tag : BitVec 32) (level : Word) : Nat :=
  if accepts tag level then 106 else X86P1RejectionCapture.guardSteps tag + 22
def effects {state : State} (input : X86P1OutputCapture.DataFacts state) (receipt : X86FailureHandler.FrameFacts state)
    (tag : BitVec 32) (level : Word) : Finset Nat :=
  if accepts tag level then X86P1SuccessCapture.writes input receipt else X86P1OutputCapture.receiptWrites receipt

theorem answer_one_iff (tag : BitVec 32) (level : Word) : answer tag level = (1#64) ↔ accepts tag level := by
  by_cases yes : accepts tag level
  · rw [answer,if_pos yes]
    exact ⟨fun _ => yes,fun _ => rfl⟩
  · rw [answer,if_neg yes]
    constructor
    · intro impossible
      have distinct : (0#64) ≠ (1#64) := by decide
      exact False.elim (distinct impossible)
    · intro impossible
      exact False.elim (yes impossible)

theorem answer_rule (tag : BitVec 32) (field level : Word) (conclusion : Tuple) :
    RuleTable.Derives entry.source [⟨tag.toNat,[field,level]⟩] conclusion ↔
      answer tag level = (1#64) ∧ conclusion = ⟨7173,[field]⟩ := by
  rw [answer_one_iff]
  simpa only [accepts,and_assoc] using derives_iff tag field level conclusion

/-- The output buffer lies outside the six saved stack words whenever the stack lies outside the
successful call's writes. -/
theorem output_outside_spill (state : State) (call : X86AllowanceCall.Inputs state)
    (input : X86P1OutputCapture.DataFacts state) (receipt : X86FailureHandler.FrameFacts state)
    (fuel : X86P1SuccessCapture.FuelProtection call input (X86P1SuccessCapture.writes input receipt)) :
    ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom := by
  intro byte within member
  have written : X86WriteWords.physicalAddress input.output byte ∈ X86P1SuccessCapture.writes input receipt := by
    apply Finset.mem_union_left
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨byte,List.mem_range.mpr within,rfl⟩)
  rcases Finset.mem_union.mp member with five | sixth
  · obtain ⟨offset,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp five)
    have bounded : offset < 40 := List.mem_range.mp present
    let slot : Fin 6 := ⟨offset / 8,by omega⟩
    have avoid := fuel.saved slot (offset % 8) (by omega)
    have coordinate : X86WriteWords.physicalAddress (address call.prologue.bottom.toInt (8 * slot.val)) (offset % 8) =
        X86WriteWords.physicalAddress input.output byte := by
      change X86WriteWords.physicalAddress (X86Prologue.stackAt call.prologue slot.val) (offset % 8) = _
      rw [X86Prologue.stack_byte call.prologue slot.val _ (by have := slot.isLt; omega)]
      have amount : 8 * slot.val + offset % 8 = offset := by dsimp only [slot]; omega
      rw [amount]
      exact same
    exact avoid (coordinate ▸ Finset.mem_union_left _ written)
  · obtain ⟨offset,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp sixth)
    have bounded : offset < 8 := List.mem_range.mp present
    exact fuel.bottom offset bounded (same ▸ Finset.mem_union_left _ written)

theorem FuelProtection.restrict {state : State} {call : X86AllowanceCall.Inputs state}
    {input : X86P1OutputCapture.DataFacts state} {larger smaller : Finset Nat} (subset : smaller ⊆ larger)
    (fuel : X86P1SuccessCapture.FuelProtection call input larger) :
    X86P1SuccessCapture.FuelProtection call input smaller where
  budget byte within member := fuel.budget byte within (subset member)
  code := fuel.code
  output := fuel.output
  bottom byte within member := fuel.bottom byte within (Finset.union_subset_union subset (Finset.Subset.refl _) member)
  saved slot byte within member :=
    fuel.saved slot byte within (Finset.union_subset_union subset (Finset.Subset.refl _) member)

theorem public_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (input : X86P1OutputCapture.DataFacts state)
    (entryAt : call.prologue.code.toInt = input.base) (exitAt : call.exit = address input.base 619)
    (receipt : X86FailureHandler.FrameFacts state)
    (tag : BitVec 32) (tagReadable : X86P1LoadBounds.Readable state input.premiseFacts.pointer tag)
    (level : Word) (levelReadable : tag = (6661#32) → X86P1QwordBounds.Readable state input.premiseFacts.pointer level)
    (fits : tag = (6661#32) → (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (preserved : X86P1SuccessCapture.ReadProtection input (X86AllowanceCall.spillBytes call.prologue.bottom call.bottom))
    (tagApart : ∀ byte < 4, X86WriteWords.physicalAddress tagReadable.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (levelApart : ∀ same : tag = (6661#32), ∀ byte < 8,
      X86WriteWords.physicalAddress (levelReadable same).dataAddress byte ∉
        X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (codeApart : ∀ byte < X86P1SuccessCapture.image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ X86P1OutputCapture.receiptWrites receipt)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (fuel : X86P1SuccessCapture.FuelProtection call input (X86P1SuccessCapture.writes input receipt)) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches (callSteps tag level)).run state = .ok () after ∧
      X86AllowanceCall.Result call (effects input receipt tag level) (call.fuel.budget - call.fuel.receipt) body after ∧
      lookup after 0 = some (answer tag level) ∧
      (if accepts tag level then X86P1OutputCapture.Prefix after input.output input.field 32 else
        ∀ byte < 32, after.mem.get? (X86WriteWords.physicalAddress input.output byte) = state.mem.get? (X86WriteWords.physicalAddress input.output byte)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) = some ((answer tag level).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) = some ((answer tag level).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress call.fuel.receiptAddress byte) =
        some (call.fuel.receipt.extractLsb' (8 * byte) 8)) ∧
      X86P1LoadCapture.Loaded X86P1SuccessCapture.image after input.base := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  by_cases yes : accepts tag level
  · have tagMatch := yes.1
    have levelZero := yes.2
    subst tag
    subst level
    obtain ⟨body,after,run,correct,value,bytes,status,result,published,image⟩ :=
      X86P1SuccessCapture.public_fires other extra vector state call input entryAt exitAt receipt tagReadable
        (levelReadable rfl) (fits rfl) preserved tagApart (levelApart rfl) codeApart outputApart statusReceiptApart
        resultReceiptApart fuel
    exact ⟨body,after,by simpa only [callSteps,if_pos yes] using run,by simpa only [effects,if_pos yes] using correct,
      by simpa only [answer,if_pos yes] using value,by simpa only [if_pos yes] using bytes,
      by simpa only [answer,if_pos yes] using status,by simpa only [answer,if_pos yes] using result,published,image⟩
  · have rejected : tag ≠ (6661#32) ∨ level ≠ (0#64) := by
      by_cases same : tag = (6661#32)
      · exact Or.inr (fun zero => yes ⟨same,zero⟩)
      · exact Or.inl same
    have tagFits : (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 4 ≤ input.premiseFacts.length.toNat := by
      have := input.premiseFits
      omega
    obtain ⟨body,after,run,correct,value,bytes,status,result,published,image⟩ :=
      X86P1RejectionCapture.public_refuses other extra vector state call input entryAt exitAt receipt tag tagReadable
        level levelReadable fits tagFits rejected preserved tagApart levelApart codeApart outputApart
        (output_outside_spill state call input receipt fuel) statusReceiptApart resultReceiptApart
        (FuelProtection.restrict Finset.subset_union_right fuel)
    refine ⟨body,after,by simpa only [callSteps,if_neg yes] using run,by simpa only [effects,if_neg yes] using correct,
      by simpa only [answer,if_neg yes] using value,by simpa only [if_neg yes] using bytes,?_,?_,published,image⟩
    · intro byte within
      simpa only [answer,if_neg yes,BitVec.extractLsb'_zero] using status byte within
    · intro byte within
      simpa only [answer,if_neg yes,BitVec.extractLsb'_zero] using result byte within

theorem public_refines_rule (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (call : X86AllowanceCall.Inputs state) (input : X86P1OutputCapture.DataFacts state)
    (entryAt : call.prologue.code.toInt = input.base) (exitAt : call.exit = address input.base 619)
    (receipt : X86FailureHandler.FrameFacts state)
    (tag : BitVec 32) (tagReadable : X86P1LoadBounds.Readable state input.premiseFacts.pointer tag)
    (level : Word) (levelReadable : tag = (6661#32) → X86P1QwordBounds.Readable state input.premiseFacts.pointer level)
    (fits : tag = (6661#32) → (input.premiseFacts.pointer - input.premiseFacts.base).toNat + 24 ≤ input.premiseFacts.length.toNat)
    (preserved : X86P1SuccessCapture.ReadProtection input (X86AllowanceCall.spillBytes call.prologue.bottom call.bottom))
    (tagApart : ∀ byte < 4, X86WriteWords.physicalAddress tagReadable.dataAddress byte ∉
      X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (levelApart : ∀ same : tag = (6661#32), ∀ byte < 8,
      X86WriteWords.physicalAddress (levelReadable same).dataAddress byte ∉
        X86AllowanceCall.spillBytes call.prologue.bottom call.bottom)
    (codeApart : ∀ byte < X86P1SuccessCapture.image.size, ((address input.base byte).signExtend 52).toNat ∉ X86P1OutputCapture.receiptWrites receipt)
    (outputApart : ∀ byte < 32, X86WriteWords.physicalAddress input.output byte ∉ X86P1OutputCapture.receiptWrites receipt)
    (statusReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.statusAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (resultReceiptApart : ∀ byte < 8, X86WriteWords.physicalAddress receipt.resultAddress byte ∉
      X86AllowanceCall.receiptBytes call.fuel.receiptAddress)
    (fuel : X86P1SuccessCapture.FuelProtection call input (X86P1SuccessCapture.writes input receipt)) :
    letI : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ body after, (X86FuelPrefix.fetches (callSteps tag level)).run state = .ok () after ∧
      X86AllowanceCall.Result call (effects input receipt tag level) (call.fuel.budget - call.fuel.receipt) body after ∧
      (∀ conclusion : Tuple, RuleTable.Derives entry.source [⟨tag.toNat,[input.field,level]⟩] conclusion ↔
        lookup after 0 = some (1#64) ∧ conclusion = ⟨7173,[input.field]⟩) ∧
      (lookup after 0 = some (1#64) → X86P1OutputCapture.Prefix after input.output input.field 32) ∧
      X86P1LoadCapture.Loaded X86P1SuccessCapture.image after input.base := by
  let : OtherOpcodeHandlers := X86P1SuccessCapture.callHandlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨body,after,run,correct,value,bytes,_,_,_,image⟩ := public_classifies other extra vector state call input
    entryAt exitAt receipt tag tagReadable level levelReadable fits preserved tagApart levelApart codeApart outputApart
    statusReceiptApart resultReceiptApart fuel
  refine ⟨body,after,run,correct,?_,?_,image⟩
  · intro conclusion
    rw [value,Option.some.injEq]
    exact answer_rule tag input.field level conclusion
  · intro fired
    have accepted : accepts tag level := (answer_one_iff tag level).mp (Option.some.inj (value.symm.trans fired))
    simpa only [if_pos accepted] using bytes

namespace Controls
theorem accepts_zero (field : Word) : RuleTable.Derives entry.source [⟨6661,[field,0]⟩] ⟨7173,[field]⟩ := derives field
theorem high_level_refused (field : Word) (conclusion : Tuple) :
    ¬ RuleTable.Derives entry.source [⟨6661,[field,0x100000000]⟩] conclusion :=
  zero_guard_necessary field (0x100000000#64) (by decide) conclusion
theorem wrong_tag_refused (field level : Word) (conclusion : Tuple) :
    ¬ RuleTable.Derives entry.source [⟨0,[field,level]⟩] conclusion := by
  intro derived
  have impossible := (derives_iff (0#32) field level conclusion).mp derived
  have different : (0#32) ≠ (6661#32) := by decide
  exact different impossible.1
theorem wrong_conclusion_refused (field : Word) :
    ¬ RuleTable.Derives entry.source [⟨6661,[field,0]⟩] ⟨7174,[field]⟩ := by
  intro derived
  have impossible := (derives_iff (6661#32) field 0 ⟨7174,[field]⟩).mp derived
  have tag := congrArg Tuple.tag impossible.2.2
  norm_num at tag
theorem exact_counts : callSteps (6661#32) (0#64) = 106 ∧
    callSteps (0#32) (0#64) = 32 ∧ callSteps (6661#32) (0x100000000#64) = 44 := by decide
theorem exact_answers : answer (6661#32) (0#64) = (1#64) ∧
    answer (0#32) (0#64) = (0#64) ∧ answer (6661#32) (0x100000000#64) = (0#64) := by decide
end Controls

#print axioms derives
#print axioms derives_iff
#print axioms public_classifies
#print axioms public_refines_rule
#print axioms Controls.high_level_refused
#print axioms Controls.wrong_tag_refused
#print axioms Controls.wrong_conclusion_refused
end Mettapedia.Machines.TIsa.X86P1PropRefinement
