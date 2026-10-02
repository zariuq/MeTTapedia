import Mettapedia.GSLT.LanguageDef.NativeOpsReadExpressionLowering

/-! Live borrowed reads, exact refusals, undefined storage and stored-type controls. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ReadExpressionControls

open NativeIR (Atom Instruction)
open NativeWord64 (Word Fault)

def interface : Interface := ⟨[], [], [], []⟩
def address : Address := ⟨11, 0, []⟩
def sourceFrame : SourceFrame := ⟨3, 1, [⟨"p", .ref .word, 0⟩]⟩
def targetFrame : TargetFrame := ⟨3, 1, [⟨"p", .ref .word, 0⟩], [], fun _ => none⟩

def sourceMemory (pointer : Option Address) (payload : Option SourceValue) : SourceMemory :=
  ⟨fun storage element => if storage = 3 ∧ element = 0 then some (.reference pointer)
    else if storage = 11 ∧ element = 0 then payload else none, fun _ => none⟩

def targetMemory (pointer : Option Address) (payload : Option SourceValue) : TargetMemory :=
  ⟨fun storage element => ((sourceMemory pointer payload).cells storage element).map encodeValue,
    fun _ => none⟩

def sourceState (pointer : Option Address) (payload : Option SourceValue) : SourceState Unit :=
  ⟨sourceMemory pointer payload, none, true, true, (), AllocatorStats.sourceEmpty⟩

def targetState (pointer : Option Address) (payload : Option SourceValue) : TargetState Unit :=
  ⟨targetMemory pointer payload, none, true, true, (), AllocatorStats.targetEmpty⟩

/-- Allocation and calls are outside this read-only fixture. -/
def sourceHeap : SourceHeapSemantics Unit := ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩
def targetHeap : TargetHeapSemantics Unit := ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩
def sourceCalls : SourceCalls Unit := fun _ _ _ _ _ => False
def targetCalls : TargetCalls Unit := fun _ _ _ _ _ => False

def loadExpression : Expr := .load (.variable "p")
def loadOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 (.ref .word) (.readLocal "p"),
    .helper none (.reference (.temporary 1 (.ref .word))), .checkContext,
    .temporary 2 .word (.indirectRead (.temporary 1 (.ref .word)))], .temporary 2 .word, ⟨2⟩⟩

private theorem fixture_bounded : TemporaryNamesBound targetFrame 0 := by
  intro identity live
  change false = true at live
  cases live

private theorem fixture_scoped : TemporariesScoped targetFrame := by
  intro identity _
  rfl

theorem load_actual_emission :
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) loadExpression ⟨0⟩ = some loadOutput := by
  simp only [loadExpression, NativeLowering.expression?, NativeLowering.location?, inferExpr, inferLocation]
  rfl

theorem fixture_states_related (pointer : Option Address) (payload : Option SourceValue) :
    StateRelated (fun a b : Unit => a = b) (sourceState pointer payload) (targetState pointer payload) :=
  ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩

theorem fixture_pointer_tagged (pointer : Option Address) (payload : Option SourceValue) :
    SourceLocalsTagged sourceFrame (sourceState pointer payload).memory := by
  intro binding member value read
  cases List.mem_singleton.mp member
  change some (.reference pointer) = some value at read
  cases read
  exact .reference .word pointer

theorem fixture_variable_source (pointer : Option Address) (payload : Option SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame (.variable "p") (sourceState pointer payload)
      ⟨.ok (.reference pointer), sourceState pointer payload⟩ :=
  .strict rfl (.nil _) ⟨.reference pointer, rfl, rfl⟩

private theorem fixture_child_laws (pointer : Option Address) (payload : Option SourceValue) :
    ShortCircuitChildLaws (fun a b : Unit => a = b) interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame (sourceState pointer payload) .bool (.bool false) (.variable "p") :=
  guarded_short_circuit_child_laws (fun a b : Unit => a = b) interface sourceHeap sourceCalls targetHeap targetCalls
    sourceFrame (sourceState pointer payload) rfl (fixture_pointer_tagged pointer payload)
    .bool .boolean (.leaf (.variable "p"))

theorem live_load_source (value : SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame loadExpression
      (sourceState (some address) (some value)) ⟨.ok value, sourceState (some address) (some value)⟩ := by
  apply (source_read_operand_exact (fixture_child_laws (some address) (some value)) rfl _).mpr
  refine .inl ⟨.reference (some address), fixture_variable_source _ _, ?_⟩
  apply (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame (.variable "p")
    (some address) (sourceState (some address) (some value)) _).mpr
  exact ⟨address, value, rfl, rfl, rfl⟩

theorem live_load_source_exact (value : SourceValue) (out : SourceOutcome Unit) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame loadExpression
      (sourceState (some address) (some value)) out ↔
      out = ⟨.ok value, sourceState (some address) (some value)⟩ := by
  rw [source_read_operand_exact (fixture_child_laws (some address) (some value)) rfl]
  constructor
  · rintro (⟨first, firstRan, primitive⟩ | ⟨fault, firstRan, _⟩)
    · have exactFirst := (source_operand_free_expression_exact (.variable "p") rfl _ _).mp firstRan
      obtain ⟨readValue, read, same⟩ := exactFirst
      change some (.reference (some address)) = some readValue at read
      cases read
      cases same
      obtain ⟨pointed, loaded, samePointer, selected, sameOut⟩ :=
        (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame (.variable "p")
          (some address) (sourceState (some address) (some value)) out).mp primitive
      cases Option.some.inj samePointer
      change some value = some loaded at selected
      cases selected
      exact sameOut
    · have exactFirst := (source_operand_free_expression_exact (.variable "p") rfl _ _).mp firstRan
      obtain ⟨readValue, _, same⟩ := exactFirst
      cases same
  · intro same
    subst out
    exact (source_read_operand_exact (fixture_child_laws (some address) (some value)) rfl _).mp
      (live_load_source value)

theorem live_load_executes (value : SourceValue) :
    ∃ out observed, TargetRun interface targetHeap targetCalls .bool loadOutput.code loadOutput.code
        targetFrame (targetState (some address) (some value)) out ∧
      targetExpressionObservation interface loadOutput.result out observed ∧
      OutcomeRelated (fun a b : Unit => a = b)
        ⟨.ok value, sourceState (some address) (some value)⟩ observed :=
  guarded_load_preservation sourceHeap sourceCalls targetHeap targetCalls rfl
    (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) loadOutput.code load_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped (live_load_source value)

theorem live_load_no_extra_result (value : SourceValue) {out : TargetBlockOutcome Unit}
    {observed : TargetOutcome Unit}
    (ran : TargetRun interface targetHeap targetCalls .bool loadOutput.code loadOutput.code
      targetFrame (targetState (some address) (some value)) out)
    (observation : targetExpressionObservation interface loadOutput.result out observed) :
    observed.result = .ok (encodeValue value) := by
  obtain ⟨sourceOut, sourceRan, outcome⟩ := guarded_load_reflection sourceHeap sourceCalls targetHeap targetCalls
    rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) loadOutput.code load_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped ran observation
  cases (live_load_source_exact value sourceOut).mp sourceRan
  exact outcome.result

theorem wrong_loaded_result_has_no_execution (value : SourceValue) (wrong : TargetValue)
    (different : wrong ≠ encodeValue value) {out : TargetBlockOutcome Unit} {observed : TargetOutcome Unit}
    (observation : targetExpressionObservation interface loadOutput.result out observed)
    (claimed : observed.result = .ok wrong) :
    ¬ TargetRun interface targetHeap targetCalls .bool loadOutput.code loadOutput.code
      targetFrame (targetState (some address) (some value)) out := by
  intro ran
  exact different (Except.ok.inj (claimed.symm.trans (live_load_no_extra_result value ran observation)))

theorem nominal_pointer_does_not_type_pointee :
    SourceLocalsTagged sourceFrame (sourceState (some address) (some (.bool true))).memory ∧
      SourceExprEval interface sourceHeap sourceCalls sourceFrame loadExpression
        (sourceState (some address) (some (.bool true)))
        ⟨.ok (.bool true), sourceState (some address) (some (.bool true))⟩ ∧
      ¬ SourceOuterTag .word (.bool true) := by
  exact ⟨fixture_pointer_tagged _ _, live_load_source (.bool true), fun impossible => by cases impossible⟩

theorem null_load_source (payload : Option SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame loadExpression (sourceState none payload)
      ⟨.error .nullReference, sourcePoison (sourceState none payload) .nullReference⟩ := by
  apply (source_read_operand_exact (fixture_child_laws none payload) rfl _).mpr
  refine .inl ⟨.reference none, fixture_variable_source _ _, ?_⟩
  exact (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame (.variable "p")
    none (sourceState none payload) _).mpr rfl

theorem null_load_emitted_refusal (payload : Option SourceValue) :
    ∃ out observed, TargetRun interface targetHeap targetCalls .bool loadOutput.code loadOutput.code
        targetFrame (targetState none payload) out ∧
      targetExpressionObservation interface loadOutput.result out observed ∧
      observed.result = .error .nullReference := by
  obtain ⟨out, observed, ran, observation, outcome⟩ := guarded_load_preservation sourceHeap sourceCalls
    targetHeap targetCalls rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p"))
    loadOutput.code load_actual_emission ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _)
    fixture_bounded fixture_scoped (null_load_source payload)
  exact ⟨out, observed, ran, observation, outcome.result⟩

theorem missing_pointee_source_stuck (out : SourceOutcome Unit) :
    ¬ SourceExprEval interface sourceHeap sourceCalls sourceFrame loadExpression
      (sourceState (some address) none) out := by
  intro ran
  rcases (source_read_operand_exact (fixture_child_laws (some address) none) rfl _).mp ran with
    ⟨first, firstRan, primitive⟩ | ⟨fault, firstRan, _⟩
  · obtain ⟨readValue, read, same⟩ := (source_operand_free_expression_exact (.variable "p") rfl _ _).mp firstRan
    change some (.reference (some address)) = some readValue at read
    cases read
    cases same
    obtain ⟨pointed, loaded, samePointer, selected, _⟩ :=
      (source_load_primitive_exact interface sourceHeap sourceCalls sourceFrame (.variable "p")
        (some address) (sourceState (some address) none) out).mp primitive
    cases Option.some.inj samePointer
    change none = some loaded at selected
    cases selected
  · obtain ⟨readValue, _, same⟩ := (source_operand_free_expression_exact (.variable "p") rfl _ _).mp firstRan
    cases same

theorem missing_pointee_no_observable_execution {out : TargetBlockOutcome Unit} {observed : TargetOutcome Unit}
    (observation : targetExpressionObservation interface loadOutput.result out observed) :
    ¬ TargetRun interface targetHeap targetCalls .bool loadOutput.code loadOutput.code
      targetFrame (targetState (some address) none) out := by
  intro ran
  obtain ⟨sourceOut, sourceRan, _⟩ := guarded_load_reflection sourceHeap sourceCalls targetHeap targetCalls
    rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) loadOutput.code load_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped ran observation
  exact missing_pointee_source_stuck sourceOut sourceRan

theorem failed_index_publishes_raw_before_return
    {World : Type} (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (state : TargetState World) (frame : TargetFrame) (array index : Atom)
    (view : TargetAtomEval interface frame state array (.array .word none 0))
    (position : TargetAtomEval interface frame state index (.word 0))
    (unused : frame.temporaryNames.contains 1 = false)
    (clear : state.fault = none) (allocator : state.allocatorAvailable = true)
    (release : state.releaseAvailable = true) (width : heap.width .word = 1) :
    TargetRun interface heap calls .bool []
      [.helper (some (.temporary 1 (.ref .word))) (.index array index .word), .checkContext]
      frame state ⟨.returned (.bool false), targetDeclareTemporary frame 1 (.reference none),
        targetPoison state .indexOutOfBounds⟩ := by
  apply (target_index_fragment_exact view position unused TargetZero.boolean [] _).mpr
  simp [targetIndexCall, targetRawFinish, targetCheckedValue, NativeOpsMemoryGuards.targetChecked,
    NativeOpsMemoryGuards.targetReady, clear, allocator, release, width, targetIndexValue,
    NativeOpsMemoryGuards.targetIndex, NativeOpsMemoryGuards.targetExtent, targetPoison, Except.map]

theorem wrong_nominal_field_contents_not_declared :
    SourceOuterTag (.named "R") (.record "R" [.bool true]) ∧
      ¬ SourceDeclaredFields [⟨"count", .word⟩] [.bool true] := by
  refine ⟨.record "R" [.bool true], ?_⟩
  intro tagged
  cases tagged with
  | cons head tail => cases head

theorem typed_record_write_retains_member_type :
    sourceWritePath [0] (.word 9) (.record "R" [.word 7]) = some (.record "R" [.word 9]) ∧
      SourceDeclaredFields [⟨"count", .word⟩] [.word 9] :=
  ⟨rfl, (declared_record_field_write (List.Forall₂.cons (SourceOuterTag.word 7) .nil)
    "R" 0 ⟨"count", .word⟩ (.word 9) (.record "R" [.word 9]) rfl (.word 9) rfl).2⟩

def borrowedArray : Address := ⟨17, 0, []⟩
def arraySourceFrame : SourceFrame := ⟨11, 1, [⟨"a", .array .word, 0⟩]⟩
def arrayTargetFrame : TargetFrame := ⟨11, 1, [⟨"a", .array .word, 0⟩], [], fun _ => none⟩
def lengthOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 (.array .word) (.readLocal "a"),
    .temporary 2 .word (.length (.temporary 1 (.array .word)))], .temporary 2 .word, ⟨2⟩⟩

theorem length_actual_emission :
    NativeLowering.expression? interface (sourceFrameScope arraySourceFrame)
      (.length (.variable "a")) ⟨0⟩ = some lengthOutput := by
  simp only [NativeLowering.expression?, inferExpr]
  rfl

/-- This borrowed descriptor fixture is not a reached allocation. Its absent
buffer cells make the lack of element dereferences in length observable. -/
theorem borrowed_length_avoids_elements (length : Word) :
    sourceRead (sourceState none (some (.array .word (some borrowedArray) length))).memory
      borrowedArray = none ∧
    ∃ out observed, TargetRun interface targetHeap targetCalls .bool lengthOutput.code lengthOutput.code
        arrayTargetFrame (targetState none (some (.array .word (some borrowedArray) length))) out ∧
      targetExpressionObservation interface lengthOutput.result out observed ∧
      observed.result = .ok (.word (NativeWord64.encode length)) := by
  have tagged : SourceLocalsTagged arraySourceFrame
      (sourceState none (some (.array .word (some borrowedArray) length))).memory := by
    intro binding member value read
    cases List.mem_singleton.mp member
    change some (.array .word (some borrowedArray) length) = some value at read
    cases read
    exact .array .word (some borrowedArray) length
  have variableRan : SourceExprEval interface sourceHeap sourceCalls arraySourceFrame
      (.variable "a") (sourceState none (some (.array .word (some borrowedArray) length)))
      ⟨.ok (.array .word (some borrowedArray) length),
        sourceState none (some (.array .word (some borrowedArray) length))⟩ :=
    .strict rfl (.nil _) ⟨.array .word (some borrowedArray) length, rfl, rfl⟩
  have sourceRan : SourceExprEval interface sourceHeap sourceCalls arraySourceFrame
      (.length (.variable "a")) (sourceState none (some (.array .word (some borrowedArray) length)))
      ⟨.ok (.word length), sourceState none (some (.array .word (some borrowedArray) length))⟩ :=
    .strict rfl (.cons variableRan (.nil _)) rfl
  have laws := guarded_length_child_laws (fun a b : Unit => a = b) interface sourceHeap sourceCalls
    targetHeap targetCalls arraySourceFrame _ rfl tagged .bool TargetZero.boolean (.leaf (.variable "a"))
  have bounded : TemporaryNamesBound arrayTargetFrame 0 := by
    intro identity live
    change false = true at live
    cases live
  obtain ⟨out, ran, related, _, _, _⟩ := laws.forward lengthOutput.code length_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) bounded (fun _ _ => rfl) sourceRan
  obtain ⟨observed, observation⟩ := guarded_related_has_observation related
  have correspondence := guarded_related_observation_correspondence (fixture_states_related _ _)
    rfl related observation
  exact ⟨rfl, out, observed, ran, observation, correspondence.result⟩

end Mettapedia.GSLT.LanguageDef.NativeOps.ReadExpressionControls
