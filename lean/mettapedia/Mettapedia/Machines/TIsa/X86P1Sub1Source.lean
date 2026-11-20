import Mettapedia.Machines.TIsa.P1Sub1Source
import Mettapedia.Machines.TIsa.X86P1Sub1Rule
import Mettapedia.Machines.TIsa.X86WordPrimitive

/-!
# The exported Micromath leaf from source through x86 return

The two executions see the same premise words and capacity. They return the
same status, and successful publication agrees at each returned word.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Source

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86P1Sub1Entry X86P1Sub1Rule
open X86P1Sub1Guards.PremiseGuards (prefixWrites)
open X86P1Sub1Output (outputWrites)
open X86P1Sub1Exit (handlers tailRegisters)

theorem theory_compiles_to_live_body :
    P1Sub1Source.theoryBody? P1Sub1Source.micromathTheory "mm_sub1" =
      some X86P1Sub1Allowance.sub1.source.body := by
  rw [← live_export_identity]
  exact P1Sub1Source.theory_compiles_to_export

private theorem result_agrees (source : P1WordExecution.State) {state : State} (rows : InputRows state)
    (capacity : Bool → Word) (used : source.frame 22 = capacity false) (limit : source.frame 23 = capacity true) :
    P1Sub1Source.result source rows.words = rows.ruleResult (capacity false) (capacity true) := by
  have claim (row : Fin 4) : P1Sub1Source.claim rows.words row = rows.claim row := rfl
  simp only [P1Sub1Source.result, InputRows.ruleResult, claim, used, limit]
  rfl

theorem exported_source_refines_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state) (ret : ReturnInputs caller)
    (rows : InputRows state) (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (capacity : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (if limit then 184 else 176)) = some (capacity limit))
    (apart : CallSpans input output ret)
    (source : P1WordExecution.State) (sourceRows : P1Sub1Source.ReadRows source rows.words)
    (sourceOutput : P1Sub1Source.Output source)
    (used : source.frame 22 = capacity false) (limit : source.frame 23 = capacity true) :
    let result := rows.ruleResult (capacity false) (capacity true)
    let address := fun field : Fin 4 => output.base + BitVec.ofNat 64 (8 * field.val)
    ∃ srcAfter steps after,
      P1WordExecution.execute source X86P1Sub1Allowance.sub1.source.body =
        .returned result.1 result.1.word srcAfter ∧
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret ((if result.1 = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if result.1 = .completed then output.bytes ∪ ret.writes else ret.writes) result.1 after ∧
      srcAfter.frame = source.frame ∧ srcAfter.regions = source.regions ∧
      srcAfter.budget = source.budget ∧ srcAfter.spent = source.spent ∧
      (result.2 = none → srcAfter.memory = source.memory ∧ ∀ field,
        X86MemoryView.wordAt? (X86MemoryView.memory after) (address field) =
          X86MemoryView.wordAt? (X86MemoryView.memory state) (address field)) ∧
      ∀ published, result.2 = some published →
        (∀ field, X86MemoryView.wordAt? (X86MemoryView.memory after) (address field) =
          srcAfter.memory ((source.regions 4).base.toNat + 8 * field.val)) ∧
        ∀ axioms, (∀ row, Mettapedia.Languages.Micromath.Derives axioms (rows.claim row)) →
          Mettapedia.Languages.Micromath.Derives axioms published := by
  intro result address
  obtain ⟨srcAfter, ranSource, srcMemory, srcRegions, srcFrame, srcBudget, srcSpent⟩ :=
    P1Sub1Source.source_refines_substitute1 source rows.words sourceRows sourceOutput
  have agrees := result_agrees source rows capacity used limit
  rw [agrees] at ranSource srcMemory
  obtain ⟨steps, after, ranNative, returned, untouched, publishes⟩ :=
    refines_substitute1_from_spans other extra vector state caller ret rows input output out profile
      flags holds flagsKnown quiet capacity known apart
  refine ⟨srcAfter, steps, after, ranSource, ranNative, returned, srcFrame, srcRegions, srcBudget, srcSpent, ?_, ?_⟩
  · intro unpublished
    have stopped : result.1 ≠ .completed := by
      intro complete
      change (rows.ruleResult (capacity false) (capacity true)).2 = none at unpublished
      change (rows.ruleResult (capacity false) (capacity true)).1 = .completed at complete
      cases accepted : Mettapedia.Languages.Micromath.substitute1?
        (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3) with
      | none => simp [InputRows.ruleResult, accepted] at complete
      | some proposed =>
        by_cases room : (capacity false).toNat < (capacity true).toNat
        · simp [InputRows.ruleResult, accepted, room] at unpublished
        · simp [InputRows.ruleResult, accepted, room] at complete
    rw [if_neg stopped] at srcMemory
    exact ⟨srcMemory, untouched unpublished⟩
  · intro published yes
    obtain ⟨completed, _, checked⟩ := rows.ruleResult_publishes (capacity false) (capacity true) published yes
    rw [if_pos completed] at srcMemory
    obtain ⟨targetWords, derivable⟩ := publishes published yes
    refine ⟨?_, derivable⟩
    intro field
    rw [targetWords field, srcMemory, P1Sub1Source.outputMemory_at,
      P1Sub1Source.conclusionWords_readback rows.words published checked field]
    rfl

/-- Project the five qword capabilities and the initial word memory from the admitted call. -/
def sourceAtCall {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output) :
    P1WordExecution.State where
  registers reg := (lookup state (X86WordPrimitive.physical reg)).getD 0
  regions region :=
    if premise : region.val < 4 then
      ⟨rows.base ⟨region.val, premise⟩, input.length ⟨region.val, premise⟩, .readOnly⟩
    else if region = 4 then ⟨output.base, out.length, .readWrite⟩
    else ⟨0, 0, .absent⟩
  frame slot := (X86MemoryView.wordAt? (X86MemoryView.memory state)
    (input.frame + BitVec.ofNat 64 (8 * slot.val))).getD 0
  memory address :=
    if address < 2 ^ 64 then
      X86MemoryView.wordAt? (X86MemoryView.memory state) (BitVec.ofNat 64 address)
    else none
  budget := caller.fuel.budget
  spent := caller.fuel.receipt

private theorem sourceAtCall_premises {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (fits : ∀ row, (rows.base row).toNat + (input.length row).toNat < 2 ^ 64) :
    P1Sub1Source.ReadRows (sourceAtCall caller input output out) rows.words := by
  let source := sourceAtCall caller input output out
  change P1Sub1Source.ReadRows source rows.words
  have region (row : Fin 4) : source.regions (P1Sub1Source.region row) =
      ⟨rows.base row, input.length row, .readOnly⟩ := by
    simp [source, sourceAtCall, P1Sub1Source.region, row.isLt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row
    simp [region row]
  · intro row
    rw [region row]
    have known := rows.pointers row
    change lookup state (X86WordPrimitive.physical ⟨row.val + 1, _⟩) = some (rows.base row) at known
    change (lookup state (X86WordPrimitive.physical ⟨row.val + 1, _⟩)).getD 0 = rows.base row
    rw [known]
    rfl
  · intro row
    rw [region row]
    exact input.rowAligned row
  · intro row
    rw [region row]
    exact input.room row
  · intro row
    rw [region row]
    exact fits row
  · intro row field
    rw [region row]
    have within : (rows.base row).toNat + 8 * field.val < 2 ^ 64 := by
      have := (input.rowArea row).1
      have := field.isLt
      omega
    change (if (rows.base row).toNat + 8 * field.val < 2 ^ 64 then _ else none) = _
    rw [if_pos within, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact rows.bytes row field

private theorem sourceAtCall_output {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (fits : output.base.toNat + out.length.toNat < 2 ^ 64) :
    P1Sub1Source.Output (sourceAtCall caller input output out) := by
  have region : (sourceAtCall caller input output out).regions 4 =
      ⟨output.base, out.length, .readWrite⟩ := rfl
  constructor
  · rw [region]
    exact ⟨rfl, out.aligned, out.room, fits⟩
  · rw [region]
    change (lookup state (X86BoundedStore.physical 5)).getD 0 = output.base
    rw [output.pointer]
    rfl

private theorem sourceAtCall_frame_word {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (slot : Fin 24) (location : BitVec 48) (value : Word)
    (effective : input.frame + BitVec.ofNat 64 (8 * slot.val) = location.signExtend 64)
    (readable : ∀ byte < 8, state.mem.get? (X86WriteWords.physicalAddress location byte) =
      some (value.extractLsb' (8 * byte) 8)) :
    (sourceAtCall caller input output out).frame slot = value := by
  let offset := 8 * slot.val
  let pointer := input.frame + BitVec.ofNat 64 offset
  have within : offset + 8 ≤ frameLayout.size := by
    change 8 * slot.val + 8 ≤ 192
    have := slot.isLt
    omega
  have address (byte : Nat) : pointer + BitVec.ofNat 64 byte =
      input.frame + BitVec.ofNat 64 (offset + byte) := by
    simp only [pointer, BitVec.add_assoc, BitVec.ofNat_add]
  have area : X86CanonicalSpan.Area pointer 8 := by
    have bound := input.frameArea.1
    refine ⟨?_, ?_⟩
    · change (input.frame + BitVec.ofNat 64 offset).toNat + 8 ≤ 2 ^ 64
      rw [X86CanonicalSpan.add_toNat _ _ (by omega)]
      omega
    · intro byte valid
      rw [address]
      exact input.frameArea.2 _ (by omega)
  have placed : X86Execution.address (X86CanonicalSpan.narrow input.frame).toInt offset = location := by
    rw [← X86CanonicalSpan.narrow_offset _ _ _ (by decide) input.frameArea (by omega), effective]
    simp [X86CanonicalSpan.narrow, BitVec.toInt_signExtend_of_le]
  have decoded := X86MemoryView.wordAt?_known (X86MemoryView.memory state) pointer value
    ((X86MemoryView.span_iff_area pointer).mpr area) (by
      intro byte valid
      rw [address, ← X86CanonicalSpan.physicalAddress_nested _ _ offset byte (by decide) input.frameArea
        (by omega), placed]
      exact readable byte valid)
  exact congrArg (fun word : Option Word => word.getD 0) decoded

theorem sourceAtCall_fuel_words {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output) :
    let source := sourceAtCall caller input output out
    source.frame 20 = source.budget ∧ source.frame 21 = source.spent := by
  have sameFrame := Option.some.inj (input.frameKnown.symm.trans caller.fuel.frameKnown)
  exact ⟨sourceAtCall_frame_word caller input output out 20 caller.fuel.budgetAddress caller.fuel.budget
      (by rw [sameFrame]; exact caller.fuel.budgetEffective) caller.fuel.budgetPresent,
    sourceAtCall_frame_word caller input output out 21 caller.fuel.receiptAddress caller.fuel.receipt
      (by rw [sameFrame]; exact caller.fuel.receiptEffective) caller.fuel.receiptPresent⟩

theorem callSource_matches_declarations {state : State} (caller : CallerInputs state) {rows : InputRows state}
    (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (regionsFit : ∀ row, (rows.base row).toNat + (input.length row).toNat < 2 ^ 64)
    (outputFits : output.base.toNat + out.length.toNat < 2 ^ 64) :
    let source := sourceAtCall caller input output out
    let program := X86P1Sub1Allowance.sub1.source
    source.registers 0 = input.frame ∧
    (∀ (region : P1Source.Region) (decl : P1Source.RegionDecl), program.regions[region.val]? = some decl →
      let cap := source.regions region
      cap.mode = decl.mode ∧ decl.minimum.toNat ≤ cap.length.toNat ∧
      cap.base.toNat % decl.alignment.toNat = 0 ∧ cap.base.toNat + cap.length.toNat < 2 ^ 64) ∧
    ∀ entry ∈ program.entry, entry.ty = .pointer ∧ source.registers entry.register = (source.regions entry.region).base := by
  intro source program
  let borrowed : P1Source.RegionDecl := ⟨.readOnly, 32, 8⟩
  let destination : P1Source.RegionDecl := ⟨.readWrite, 32, 8⟩
  have declarations : program.regions = List.replicate 4 borrowed ++ [destination] := by
    dsimp only [program, borrowed, destination]
    kernel_reflexivity
  let premise (row : Fin 4) : P1Source.EntryReg := ⟨P1Sub1Source.pointer row, .pointer, P1Sub1Source.region row⟩
  let result : P1Source.EntryReg := ⟨5, .pointer, 4⟩
  have arguments : program.entry = (List.finRange 4).map premise ++ [result] := by
    dsimp only [program, premise, result]
    kernel_reflexivity
  have premises := sourceAtCall_premises caller input output out regionsFit
  have writable := sourceAtCall_output caller input output out outputFits
  have framePointer : source.registers 0 = input.frame := by
    change (lookup state 7).getD 0 = input.frame
    rw [input.frameKnown]
    rfl
  refine ⟨framePointer, ?_, ?_⟩
  · intro region decl declared
    rw [declarations] at declared
    by_cases before : region.val < 4
    · have withinPremises : region.val < (List.replicate 4 borrowed).length := by simpa using before
      rw [List.getElem?_append_left withinPremises, List.getElem?_replicate_of_lt before] at declared
      cases declared
      let row : Fin 4 := ⟨region.val, before⟩
      have index : region = P1Sub1Source.region row := Fin.ext rfl
      have mode : (source.regions region).mode = .readOnly := by simp [source, sourceAtCall, before]
      rw [index]
      exact ⟨by simpa only [index] using mode, premises.extent row, premises.aligned row, premises.fits row⟩
    · have after : (List.replicate 4 borrowed).length ≤ region.val := by
        simp only [List.length_replicate]
        omega
      rw [List.getElem?_append_right after, List.length_replicate] at declared
      have atDestination : region.val - 4 = 0 := by
        have bound := (List.getElem?_eq_some_iff.mp declared).1
        change region.val - 4 < 1 at bound
        omega
      rw [atDestination] at declared
      cases declared
      have index : region = 4 := Fin.ext (by change region.val = 4; omega)
      subst region
      exact ⟨writable.usable.writable, writable.usable.enough, writable.usable.aligned, writable.usable.fits⟩
  · intro entry member
    rw [arguments] at member
    rcases List.mem_append.mp member with sourceArgument | outputArgument
    · obtain ⟨row, _, rfl⟩ := List.mem_map.mp sourceArgument
      exact ⟨rfl, premises.pointerAtBase row⟩
    · have same := List.mem_singleton.mp outputArgument
      subst entry
      exact ⟨rfl, writable.pointerAtBase⟩

theorem call_refines_exported_source (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state) (ret : ReturnInputs caller)
    (rows : InputRows state) (input : InputFrame rows) (output : OutputRow state) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (capacity : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (if limit then 184 else 176)) = some (capacity limit))
    (apart : CallSpans input output ret)
    (regionsFit : ∀ row, (rows.base row).toNat + (input.length row).toNat < 2 ^ 64)
    (outputFits : output.base.toNat + out.length.toNat < 2 ^ 64) :
    let source := sourceAtCall caller input output out
    let result := rows.ruleResult (capacity false) (capacity true)
    let address := fun field : Fin 4 => output.base + BitVec.ofNat 64 (8 * field.val)
    ∃ srcAfter steps after,
      P1WordExecution.execute source X86P1Sub1Allowance.sub1.source.body =
        .returned result.1 result.1.word srcAfter ∧
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret ((if result.1 = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if result.1 = .completed then output.bytes ∪ ret.writes else ret.writes) result.1 after ∧
      srcAfter.frame = source.frame ∧ srcAfter.regions = source.regions ∧
      srcAfter.budget = caller.fuel.budget ∧ srcAfter.spent = caller.fuel.receipt ∧
      (∀ field, X86MemoryView.wordAt? (X86MemoryView.memory after) (address field) =
        srcAfter.memory (output.base.toNat + 8 * field.val)) ∧
      (result.2 = none → srcAfter.memory = source.memory) ∧
      (∀ candidate, result.2.map P1Sub1Source.claimTuple = some candidate ↔
        (capacity false).toNat < (capacity true).toNat ∧
          RuleTable.Derives P1Sub1Source.theorySub1Rule (P1Sub1Source.premiseTuples rows.words) candidate) ∧
      ∀ published, result.2 = some published →
        ∀ axioms, (∀ row, Mettapedia.Languages.Micromath.Derives axioms (rows.claim row)) →
          Mettapedia.Languages.Micromath.Derives axioms published := by
  intro source result address
  have used : source.frame 22 = capacity false := by
    change (X86MemoryView.wordAt? (X86MemoryView.memory state) (input.frame + 176)).getD 0 = capacity false
    exact congrArg (fun value : Option Word => value.getD 0) (known false)
  have limit : source.frame 23 = capacity true := by
    change (X86MemoryView.wordAt? (X86MemoryView.memory state) (input.frame + 184)).getD 0 = capacity true
    exact congrArg (fun value : Option Word => value.getD 0) (known true)
  obtain ⟨srcAfter, steps, after, sourceRuns, nativeRuns, returned, frame, regions, budget, spent,
    stopped, publishes⟩ := exported_source_refines_native other extra vector state caller ret rows input output out
      profile flags holds flagsKnown quiet capacity known apart source
      (sourceAtCall_premises caller input output out regionsFit)
      (sourceAtCall_output caller input output out outputFits) used limit
  refine ⟨srcAfter, steps, after, sourceRuns, nativeRuns, returned, frame, regions, budget, spent, ?_,
    fun missing => (stopped missing).1, ?_, fun published yes => (publishes published yes).2⟩
  · intro field
    cases value : result.2 with
    | none =>
      have within : output.base.toNat + 8 * field.val < 2 ^ 64 := by
        have := output.extent.1
        have := field.isLt
        omega
      rw [(stopped value).2 field, (stopped value).1]
      change _ = (if output.base.toNat + 8 * field.val < 2 ^ 64 then _ else none)
      rw [if_pos within, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | some published => exact (publishes published value).1 field
  · intro candidate
    have derives := P1Sub1Source.result_theory_output source rows.words candidate
    rw [result_agrees source rows capacity used limit, used, limit] at derives
    exact derives

end Mettapedia.Machines.TIsa.X86P1Sub1Source

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Source.exported_source_refines_native
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Source.theory_compiles_to_live_body
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Source.sourceAtCall_fuel_words
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Source.callSource_matches_declarations
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Source.call_refines_exported_source
