import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldExpression
import Mettapedia.GSLT.LanguageDef.NativeOpsKnownSourceEvaluation
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceSwitchReturns

/-! Live borrowed reads, exact refusals, undefined storage and stored-type controls. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ReferenceFieldControls

open NativeIR (Atom Instruction)
open NativeWord64 (Word Fault)

def interface : Interface := ⟨[⟨"R", [⟨"flag", .bool⟩, ⟨"count", .word⟩]⟩], [], [], []⟩
def address : Address := ⟨11, 0, []⟩
def sourceFrame : SourceFrame := ⟨3, 1, [⟨"p", .ref (.named "R"), 0⟩]⟩
def targetFrame : TargetFrame := ⟨3, 1, [⟨"p", .ref (.named "R"), 0⟩], [], fun _ => none⟩

def sourceMemory (pointer : Option Address) (payload : Option SourceValue) : SourceMemory :=
  ⟨fun storage element => if storage = 3 ∧ element = 0 then some (.reference pointer)
    else if storage = 11 ∧ element = 0 then payload.map (fun value => .record "R" [.bool true, value]) else none, fun _ => none⟩

def targetMemory (pointer : Option Address) (payload : Option SourceValue) : TargetMemory :=
  ⟨fun storage element => ((sourceMemory pointer payload).cells storage element).map encodeValue,
    fun _ => none⟩

def sourceState (pointer : Option Address) (payload : Option SourceValue) : SourceState Unit :=
  ⟨sourceMemory pointer payload, none, true, true, (), AllocatorStats.sourceEmpty⟩

def targetState (pointer : Option Address) (payload : Option SourceValue) : TargetState Unit :=
  ⟨targetMemory pointer payload, none, true, true, (), AllocatorStats.targetEmpty⟩

variable {sourceHeap : SourceHeapSemantics Unit} {targetHeap : TargetHeapSemantics Unit}
  {sourceCalls : SourceCalls Unit} {targetCalls : TargetCalls Unit}

def fieldExpression : Expr := .field (.variable "p") "count"
def fieldOutput : NativeLowering.Expression :=
  ⟨[.temporary 1 (.ref (.named "R")) (.readLocal "p"),
    .helper none (.reference (.temporary 1 (.ref (.named "R")))), .checkContext,
    .temporary 2 (.ref .word) (.fieldAddress (.temporary 1 (.ref (.named "R"))) "R" 1),
    .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))], .temporary 3 .word, ⟨3⟩⟩

private theorem fixture_bounded : TemporaryNamesBound targetFrame 0 := by
  intro identity live
  change false = true at live
  cases live

private theorem fixture_scoped : TemporariesScoped targetFrame := by
  intro identity _
  rfl

theorem fixture_base_type : inferExpr interface (sourceFrameScope sourceFrame) (.variable "p") =
    some (.ref (.named "R")) := by
  simp only [inferExpr]
  rfl

theorem field_actual_emission :
    NativeLowering.expression? interface (sourceFrameScope sourceFrame) fieldExpression ⟨0⟩ = some fieldOutput := by
  simp only [fieldExpression, NativeLowering.expression?, NativeLowering.location?, inferExpr, inferLocation]
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
  exact .reference (.named "R") pointer

theorem fixture_variable_source (pointer : Option Address) (payload : Option SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame (.variable "p") (sourceState pointer payload)
      ⟨.ok (.reference pointer), sourceState pointer payload⟩ :=
  .strict rfl (.nil _) ⟨.reference pointer, rfl, rfl⟩

theorem field_source_exact (pointer : Option Address) (payload : Option SourceValue)
    (out : SourceOutcome Unit) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression (sourceState pointer payload) out ↔
      sourcePrimitive interface sourceHeap sourceCalls sourceFrame fieldExpression
        [.reference pointer] (sourceState pointer payload) out := by
  exact source_known_strict_expression_exact fieldExpression (sourceState pointer payload) rfl
    (.cons (source_known_variable_exact (value := .reference pointer) rfl) .nil) out

theorem live_field_source_exact (value : SourceValue) (out : SourceOutcome Unit) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression
      (sourceState (some address) (some value)) out ↔
      out = ⟨.ok value, sourceState (some address) (some value)⟩ := by
  rw [field_source_exact]
  unfold fieldExpression
  rw [source_reference_field_primitive_exact (interface := interface) sourceHeap sourceCalls sourceFrame (.variable "p")
    "R" "count" 1 (some address) fixture_base_type rfl]
  constructor
  · rintro ⟨pointed, loaded, samePointer, selected, sameOut⟩
    cases Option.some.inj samePointer
    change some value = some loaded at selected
    cases selected
    exact sameOut
  · intro same
    exact ⟨address, value, rfl, rfl, same⟩

theorem live_field_source (value : SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression
      (sourceState (some address) (some value)) ⟨.ok value, sourceState (some address) (some value)⟩ :=
  (live_field_source_exact value _).mpr rfl

include sourceHeap sourceCalls

theorem live_field_executes (value : SourceValue) :
    ∃ out observed, TargetRun interface targetHeap targetCalls .bool fieldOutput.code fieldOutput.code
        targetFrame (targetState (some address) (some value)) out ∧
      targetExpressionObservation interface fieldOutput.result out observed ∧
      OutcomeRelated (fun a b : Unit => a = b)
        ⟨.ok value, sourceState (some address) (some value)⟩ observed :=
  guarded_reference_field_preservation sourceHeap sourceCalls targetHeap targetCalls rfl
    (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) fixture_base_type fieldOutput.code field_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped (live_field_source value)

theorem live_field_no_extra_result (value : SourceValue) {out : TargetBlockOutcome Unit}
    {observed : TargetOutcome Unit}
    (ran : TargetRun interface targetHeap targetCalls .bool fieldOutput.code fieldOutput.code
      targetFrame (targetState (some address) (some value)) out)
    (observation : targetExpressionObservation interface fieldOutput.result out observed) :
    observed.result = .ok (encodeValue value) := by
  obtain ⟨sourceOut, sourceRan, outcome⟩ := guarded_reference_field_reflection sourceHeap sourceCalls targetHeap targetCalls
    rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) fixture_base_type fieldOutput.code field_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped ran observation
  cases (live_field_source_exact value sourceOut).mp sourceRan
  exact outcome.result

theorem wrong_field_result_has_no_execution (value : SourceValue) (wrong : TargetValue)
    (different : wrong ≠ encodeValue value) {out : TargetBlockOutcome Unit} {observed : TargetOutcome Unit}
    (observation : targetExpressionObservation interface fieldOutput.result out observed)
    (claimed : observed.result = .ok wrong) :
    ¬ TargetRun interface targetHeap targetCalls .bool fieldOutput.code fieldOutput.code
      targetFrame (targetState (some address) (some value)) out := by
  intro ran
  exact different (Except.ok.inj (claimed.symm.trans (live_field_no_extra_result (sourceHeap := sourceHeap) (sourceCalls := sourceCalls) value ran observation)))

theorem nominal_pointer_does_not_type_pointee :
    SourceLocalsTagged sourceFrame (sourceState (some address) (some (.bool true))).memory ∧
      SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression
        (sourceState (some address) (some (.bool true)))
        ⟨.ok (.bool true), sourceState (some address) (some (.bool true))⟩ ∧
      ¬ SourceOuterTag .word (.bool true) := by
  exact ⟨fixture_pointer_tagged _ _, live_field_source (.bool true), fun impossible => by cases impossible⟩

theorem null_field_source (payload : Option SourceValue) :
    SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression (sourceState none payload)
      ⟨.error .nullReference, sourcePoison (sourceState none payload) .nullReference⟩ := by
  rw [field_source_exact]
  exact (source_reference_field_primitive_exact (interface := interface) sourceHeap sourceCalls sourceFrame (.variable "p")
    "R" "count" 1 none fixture_base_type rfl (sourceState none payload) _).mpr rfl

theorem null_field_emitted_refusal (payload : Option SourceValue) :
    ∃ out observed, TargetRun interface targetHeap targetCalls .bool fieldOutput.code fieldOutput.code
        targetFrame (targetState none payload) out ∧
      targetExpressionObservation interface fieldOutput.result out observed ∧
      observed.result = .error .nullReference := by
  obtain ⟨out, observed, ran, observation, outcome⟩ := guarded_reference_field_preservation sourceHeap sourceCalls
    targetHeap targetCalls rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) fixture_base_type
    fieldOutput.code field_actual_emission ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _)
    fixture_bounded fixture_scoped (null_field_source payload)
  exact ⟨out, observed, ran, observation, outcome.result⟩

theorem missing_record_source_stuck (out : SourceOutcome Unit) :
    ¬ SourceExprEval interface sourceHeap sourceCalls sourceFrame fieldExpression
      (sourceState (some address) none) out := by
  intro ran
  have primitive := (field_source_exact _ _ _).mp ran
  obtain ⟨pointed, loaded, samePointer, selected, _⟩ :=
    (source_reference_field_primitive_exact (interface := interface) sourceHeap sourceCalls sourceFrame (.variable "p")
      "R" "count" 1 (some address) fixture_base_type rfl (sourceState (some address) none) out).mp primitive
  cases Option.some.inj samePointer
  change none = some loaded at selected
  cases selected

theorem missing_record_no_observable_execution {out : TargetBlockOutcome Unit} {observed : TargetOutcome Unit}
    (observation : targetExpressionObservation interface fieldOutput.result out observed) :
    ¬ TargetRun interface targetHeap targetCalls .bool fieldOutput.code fieldOutput.code
      targetFrame (targetState (some address) none) out := by
  intro ran
  obtain ⟨sourceOut, sourceRan, _⟩ := guarded_reference_field_reflection sourceHeap sourceCalls targetHeap targetCalls
    rfl (fixture_pointer_tagged _ _) .boolean (.leaf (.variable "p")) fixture_base_type fieldOutput.code field_actual_emission
    ⟨rfl, rfl, rfl⟩ (fixture_states_related _ _) fixture_bounded
    fixture_scoped ran observation
  exact missing_record_source_stuck sourceOut sourceRan

end Mettapedia.GSLT.LanguageDef.NativeOps.ReferenceFieldControls
