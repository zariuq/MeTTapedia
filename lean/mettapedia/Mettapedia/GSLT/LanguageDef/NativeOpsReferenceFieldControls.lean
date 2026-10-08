import Mettapedia.GSLT.LanguageDef.NativeOpsReferenceFieldComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal
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

omit sourceHeap sourceCalls

open NativeWord64 (bounded)

def preparingInterface : Interface :=
  { interface with externals := [⟨⟨"prepare-record", [], .ref (.named "R")⟩, "prepare-record", .effect, none⟩] }

def preparedSourcePost (state : SourceState Nat) (payload : Option SourceValue)
    (ready : Bool) (increment : Nat) : SourceState Nat :=
  { state with
      memory := sourceMemory (some address) payload,
      releaseAvailable := ready, external := state.external + increment }

def preparedTargetPost (state : TargetState Nat) (payload : Option SourceValue)
    (ready : Bool) (increment : Nat) : TargetState Nat :=
  { state with
      memory := targetMemory (some address) payload,
      releaseAvailable := ready, external := state.external + increment }

inductive SourcePreparingCall : SourceCalls Nat where
  | value (state : SourceState Nat) : SourcePreparingCall "prepare-record" [] state (.reference (some address))
      (preparedSourcePost state (some (.word (bounded 64 21))) true 4)
  | refusal (state : SourceState Nat) : SourcePreparingCall "prepare-record" [] state (.reference (some address))
      (sourcePoison (preparedSourcePost state (some (.word (bounded 64 21))) true 5) .resourceFault)
  | unavailable (state : SourceState Nat) : SourcePreparingCall "prepare-record" [] state (.reference (some address))
      (preparedSourcePost state (some (.word (bounded 64 21))) false 6)
  | missing (state : SourceState Nat) : SourcePreparingCall "prepare-record" [] state (.reference (some address))
      (preparedSourcePost state none true 7)

inductive TargetPreparingCall : TargetCalls Nat where
  | value (state : TargetState Nat) : TargetPreparingCall (.external "prepare-record") [] state (.reference (some address))
      (preparedTargetPost state (some (.word (bounded 64 21))) true 4)
  | refusal (state : TargetState Nat) : TargetPreparingCall (.external "prepare-record") [] state (.reference (some address))
      (targetPoison (preparedTargetPost state (some (.word (bounded 64 21))) true 5) .resourceFault)
  | unavailable (state : TargetState Nat) : TargetPreparingCall (.external "prepare-record") [] state (.reference (some address))
      (preparedTargetPost state (some (.word (bounded 64 21))) false 6)
  | missing (state : TargetState Nat) : TargetPreparingCall (.external "prepare-record") [] state (.reference (some address))
      (preparedTargetPost state none true 7)

theorem prepared_post_correspondence {source : SourceState Nat} {target : TargetState Nat}
    (states : StateRelated Eq source target) (payload : Option SourceValue) (ready : Bool) (increment : Nat) :
    StateRelated Eq (preparedSourcePost source payload ready increment)
      (preparedTargetPost target payload ready increment) :=
  ⟨(fixture_states_related (some address) payload).memory, states.fault, states.allocator,
    rfl, congrArg (fun n => n + increment) states.external, states.allocatorStats⟩

theorem preparing_call_contract :
    ExternalCorrespondence ⟨SourcePreparingCall⟩ ⟨fun name => TargetPreparingCall (.external name)⟩ Eq := by
  constructor
  · intro name arguments source target raw post states called
    cases called with
    | value => exact ⟨_, .value target, prepared_post_correspondence states _ true 4⟩
    | refusal => exact ⟨_, .refusal target, poison_correspondence (prepared_post_correspondence states _ true 5) _⟩
    | unavailable => exact ⟨_, .unavailable target, prepared_post_correspondence states _ false 6⟩
    | missing => exact ⟨_, .missing target, prepared_post_correspondence states none true 7⟩
  · intro name arguments source target raw post states called
    generalize encoded : encodeValues arguments = targetArguments at called
    cases called with
    | value =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .value source, rfl, prepared_post_correspondence states _ true 4⟩
    | refusal =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .refusal source, rfl, poison_correspondence (prepared_post_correspondence states _ true 5) _⟩
    | unavailable =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .unavailable source, rfl, prepared_post_correspondence states _ false 6⟩
    | missing =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .missing source, rfl, prepared_post_correspondence states none true 7⟩

theorem preparing_success_tag (heap : SourceHeapSemantics Nat) (frame : SourceFrame)
    (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval preparingInterface heap SourcePreparingCall frame (.call "prepare-record" [])
      before ⟨.ok value, post⟩) : SourceOuterTag (.ref (.named "R")) value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "prepare-record" before _).mp ran
  cases called <;> cases clear : before.fault <;>
    simp only [sourceObserve, sourcePoison, preparedSourcePost, clear] at observed
  all_goals cases observed
  all_goals constructor

theorem preparing_child_instance (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (frame : SourceFrame) (source : SourceState Nat) :
    StatefulChildLaws Eq preparingInterface sourceHeap SourcePreparingCall targetHeap TargetPreparingCall
      frame source .word (.word 0) (.call "prepare-record" []) := by
  apply nullary_external_stateful_child_laws Eq preparingInterface sourceHeap SourcePreparingCall
    targetHeap TargetPreparingCall preparing_call_contract frame source "prepare-record" (.ref (.named "R"))
    .word (.word 0) _ _ rfl .unsignedWord
  · simp only [inferExpr, inferExprList, lookupFunction, preparingInterface]; rfl
  · intro impossible; cases impossible

def preparedFieldExpression : Expr := .field (.call "prepare-record" []) "count"

def preparedFieldOutput : NativeLowering.Expression :=
  ⟨[.call (some (.temporary 1 (.ref (.named "R")))) (.external "prepare-record") [], .checkContext,
    .helper none (.reference (.temporary 1 (.ref (.named "R")))), .checkContext,
    .temporary 2 (.ref .word) (.fieldAddress (.temporary 1 (.ref (.named "R"))) "R" 1),
    .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))], .temporary 3 .word, ⟨3⟩⟩

theorem preparing_base_type (frame : SourceFrame) :
    inferExpr preparingInterface (sourceFrameScope frame) (.call "prepare-record" []) = some (.ref (.named "R")) := by
  simp only [inferExpr, inferExprList, lookupFunction, preparingInterface]; rfl

theorem preparing_field_actual_lowering :
    NativeLowering.expression? preparingInterface (sourceFrameScope sourceFrame) preparedFieldExpression ⟨0⟩ =
      some preparedFieldOutput := by
  simp only [preparedFieldExpression, NativeLowering.expression?, NativeLowering.location?, NativeLowering.arguments?,
    inferExpr, inferLocation, inferExprList, lookupFunction, preparingInterface]; rfl

theorem preparing_field_child_instance (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (frame : SourceFrame) (source : SourceState Nat) (clear : source.fault = none) :
    StatefulChildLaws Eq preparingInterface sourceHeap SourcePreparingCall targetHeap TargetPreparingCall
      frame source .word (.word 0) preparedFieldExpression :=
  stateful_reference_field_child_laws Eq preparingInterface sourceHeap SourcePreparingCall
    targetHeap TargetPreparingCall frame source clear .word (.word 0) .unsignedWord (.call "prepare-record" []) "R" "count"
    (preparing_base_type frame) (fun before _ => preparing_child_instance sourceHeap targetHeap frame before)
    (preparing_success_tag sourceHeap frame)

def preparingSource : SourceState Nat :=
  ⟨sourceMemory (some address) (some (.word (bounded 64 13))), none, true, true, 0, AllocatorStats.sourceEmpty⟩

def preparingTarget : TargetState Nat :=
  ⟨targetMemory (some address) (some (.word (bounded 64 13))), none, true, true, 0, AllocatorStats.targetEmpty⟩

theorem preparing_initial_related : StateRelated Eq preparingSource preparingTarget :=
  ⟨(fixture_states_related _ _).memory, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩

theorem preparing_field_source_success (heap : SourceHeapSemantics Nat) :
    SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame preparedFieldExpression preparingSource
      ⟨.ok (.word (bounded 64 21)), preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 4⟩ := by
  have child : SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame (.call "prepare-record" []) preparingSource
      ⟨.ok (.reference (some address)), preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 4⟩ :=
    (source_nullary_call_exact "prepare-record" preparingSource _).mpr ⟨_, _, .value preparingSource, rfl⟩
  refine .strict rfl (.cons child (.nil _)) ?_
  apply (source_reference_field_primitive_exact heap SourcePreparingCall sourceFrame (.call "prepare-record" [])
    "R" "count" 1 (some address) (preparing_base_type sourceFrame) rfl _ _).mpr
  exact ⟨address, .word (bounded 64 21), rfl, rfl, rfl⟩

theorem preparing_field_target_success (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (root : List Instruction) :
    ∃ out, TargetRun preparingInterface targetHeap TargetPreparingCall .word root preparedFieldOutput.code
        targetFrame preparingTarget out ∧ out.flow = .normal ∧ out.state.external = 4 ∧
      out.state.memory.cells 11 0 = some (.record "R" [.bool true, .word 21]) ∧
      TargetAtomEval preparingInterface out.frame out.state preparedFieldOutput.result (.word 21) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (preparing_field_child_instance sourceHeap targetHeap sourceFrame preparingSource rfl).forward
      root (targetFrame := targetFrame) preparing_field_actual_lowering ⟨rfl, rfl, rfl⟩ preparing_initial_related
      (by intro identity live; cases live) (by intro identity _; rfl) (preparing_field_source_success sourceHeap)
  rcases related with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

theorem preparing_field_actual_reflection (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (root : List Instruction) {out : TargetBlockOutcome Nat}
    (ran : TargetRun preparingInterface targetHeap TargetPreparingCall .word root preparedFieldOutput.code
      targetFrame preparingTarget out) :
    ∃ sourceOut, SourceExprEval preparingInterface sourceHeap SourcePreparingCall sourceFrame
        preparedFieldExpression preparingSource sourceOut ∧
      CheckedExpressionRelated Eq preparingInterface (.word 0) preparedFieldOutput.result sourceOut out := by
  obtain ⟨sourceOut, sourceRan, related, _, _, _⟩ :=
    (preparing_field_child_instance sourceHeap targetHeap sourceFrame preparingSource rfl).backward
      root (targetFrame := targetFrame) preparing_field_actual_lowering ⟨rfl, rfl, rfl⟩ preparing_initial_related
      (by intro identity live; cases live) (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRan, related⟩

theorem preparing_field_value_differs_from_old_cell :
    targetRead preparingTarget.memory (sourceFieldAddress address 1) = some (.word 13) ∧
      (.word 21 : TargetValue) ≠ .word 13 := by
  refine ⟨rfl, ?_⟩
  intro same
  have numbers := congrArg BitVec.toNat (TargetValue.word.inj same)
  contradiction

theorem preparing_field_source_first_fault (heap : SourceHeapSemantics Nat) :
    SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame preparedFieldExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  have child : SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame (.call "prepare-record" []) preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ :=
    (source_nullary_call_exact "prepare-record" preparingSource _).mpr ⟨_, _, .refusal preparingSource, rfl⟩
  exact .strictFault rfl (.consFault child)

theorem preparing_field_target_first_fault (targetHeap : TargetHeapSemantics Nat) (root : List Instruction) :
    ∃ out, TargetRun preparingInterface targetHeap TargetPreparingCall .word root preparedFieldOutput.code
        targetFrame preparingTarget out ∧ out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 5 ∧ out.state.memory.cells 11 0 = some (.record "R" [.bool true, .word 21]) ∧
      out.frame.temporaryNames.contains 2 = false ∧ out.frame.temporaryNames.contains 3 = false := by
  let post := targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary targetFrame 1 (.reference (some address)), post⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal preparingTarget) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem preparing_field_source_unavailable (heap : SourceHeapSemantics Nat) :
    SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame preparedFieldExpression preparingSource
      ⟨.error .invalidRequest,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6) .invalidRequest⟩ := by
  have child : SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame (.call "prepare-record" []) preparingSource
      ⟨.ok (.reference (some address)), preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6⟩ :=
    (source_nullary_call_exact "prepare-record" preparingSource _).mpr ⟨_, _, .unavailable preparingSource, rfl⟩
  refine .strict rfl (.cons child (.nil _)) ?_
  apply (source_reference_field_primitive_exact heap SourcePreparingCall sourceFrame (.call "prepare-record" [])
    "R" "count" 1 (some address) (preparing_base_type sourceFrame) rfl _ _).mpr
  rfl

theorem preparing_field_target_unavailable (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (root : List Instruction) :
    ∃ out, TargetRun preparingInterface targetHeap TargetPreparingCall .word root preparedFieldOutput.code
        targetFrame preparingTarget out ∧ out.flow = .returned (.word 0) ∧ out.state.fault = some .invalidRequest ∧
      out.state.external = 6 ∧ out.state.releaseAvailable = false ∧
      out.state.memory.cells 11 0 = some (.record "R" [.bool true, .word 21]) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (preparing_field_child_instance sourceHeap targetHeap sourceFrame preparingSource rfl).forward
      root (targetFrame := targetFrame) preparing_field_actual_lowering ⟨rfl, rfl, rfl⟩ preparing_initial_related
      (by intro identity live; cases live) (by intro identity _; rfl) (preparing_field_source_unavailable sourceHeap)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.release, states.memory.1 11 0⟩


theorem preparing_missing_field_primitive_stuck (heap : SourceHeapSemantics Nat) (out : SourceOutcome Nat) :
    ¬ sourcePrimitive preparingInterface heap SourcePreparingCall sourceFrame preparedFieldExpression
      [.reference (some address)] (preparedSourcePost preparingSource none true 7) out := by
  intro ran
  obtain ⟨pointed, value, same, read, _⟩ :=
    (source_reference_field_primitive_exact heap SourcePreparingCall sourceFrame (.call "prepare-record" [])
      "R" "count" 1 (some address) (preparing_base_type sourceFrame) rfl _ out).mp ran
  cases Option.some.inj same
  change none = some value at read
  cases read

theorem preparing_missing_field_target_stuck (heap : TargetHeapSemantics Nat)
    (root : List Instruction) (out : TargetBlockOutcome Nat) :
    ¬ TargetRun preparingInterface heap TargetPreparingCall .word root
      (NativeLowering.checkReference (.temporary 1 (.ref (.named "R"))) ++
        [.temporary 2 (.ref .word) (.fieldAddress (.temporary 1 (.ref (.named "R"))) "R" 1),
         .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))])
      (targetDeclareTemporary targetFrame 1 (.reference (some address)))
      (preparedTargetPost preparingTarget none true 7) out := by
  intro ran
  let sourceHeap : SourceHeapSemantics Nat := ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩
  have states := prepared_post_correspondence preparing_initial_related none true 7
  have read := declared_temporary_atom preparingInterface targetFrame
    (preparedTargetPost preparingTarget none true 7) 1 (.ref (.named "R")) (.reference (some address))
  obtain ⟨sourceOut, sourceRan, _, _, _, _⟩ := stateful_checked_reference_field_fragment_profile states rfl
    sourceHeap SourcePreparingCall sourceFrame (targetDeclareTemporary targetFrame 1 (.reference (some address)))
    (.call "prepare-record" []) (some address) "R" "count" 1 .word .word (preparing_base_type sourceFrame) rfl
    (.temporary 1 (.ref (.named "R"))) ⟨1⟩ read
    (declared_temporary_bound (before := 0) (after := 1) (identity := 1)
      (by intro _ live; cases live) (Nat.zero_le _) (Nat.le_refl _) _)
    (declared_temporaries_completeNames (by intro _ _; rfl) _ _) .unsignedWord root ran
  exact preparing_missing_field_primitive_stuck sourceHeap sourceOut sourceRan

theorem omitted_field_guards_allow_faulted_read (heap : TargetHeapSemantics Nat) (root : List Instruction) :
    TargetRun preparingInterface heap TargetPreparingCall .word root
      [.call (some (.temporary 1 (.ref (.named "R")))) (.external "prepare-record") [],
       .temporary 2 (.ref .word) (.fieldAddress (.temporary 1 (.ref (.named "R"))) "R" 1),
       .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))] targetFrame preparingTarget
      ⟨.normal, targetDeclareTemporary
        (targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (.reference (some address)))
          2 (.reference (some (sourceFieldAddress address 1)))) 3 (.word 21),
        targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal preparingTarget) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.fieldAddress
      (declared_temporary_atom preparingInterface targetFrame _ 1 (.ref (.named "R")) (.reference (some address)))))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.indirect
      (declared_temporary_atom preparingInterface _ _ 2 (.ref .word) (.reference (some (sourceFieldAddress address 1)))) rfl))
  exact .nil _ _ _

theorem omitted_field_reference_check_reads_unavailable_record (heap : TargetHeapSemantics Nat)
    (root : List Instruction) :
    TargetRun preparingInterface heap TargetPreparingCall .word root
      [.call (some (.temporary 1 (.ref (.named "R")))) (.external "prepare-record") [], .checkContext,
       .temporary 2 (.ref .word) (.fieldAddress (.temporary 1 (.ref (.named "R"))) "R" 1),
       .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))] targetFrame preparingTarget
      ⟨.normal, targetDeclareTemporary
        (targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (.reference (some address)))
          2 (.reference (some (sourceFieldAddress address 1)))) 3 (.word 21),
        preparedTargetPost preparingTarget (some (.word (bounded 64 21))) false 6⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.unavailable preparingTarget) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.fieldAddress
      (declared_temporary_atom preparingInterface targetFrame _ 1 (.ref (.named "R")) (.reference (some address)))))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.indirect
      (declared_temporary_atom preparingInterface _ _ 2 (.ref .word) (.reference (some (sourceFieldAddress address 1)))) rfl))
  exact .nil _ _ _

theorem field_reference_guard_omission_changes_observation :
    (targetObserve (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) false 6)
      (.word 21)).result = .ok (.word 21) ∧
    (sourceObserve
      (sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6) .invalidRequest)
      (.word (bounded 64 21))).result = .error .invalidRequest := ⟨rfl, rfl⟩

theorem preparing_field_type (frame : SourceFrame) :
    inferExpr preparingInterface (sourceFrameScope frame) preparedFieldExpression = some .word := by
  simp only [preparedFieldExpression, inferExpr, inferExprList, lookupFunction, preparingInterface]; rfl

theorem preparing_field_success_tag (heap : SourceHeapSemantics Nat)
    (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval preparingInterface heap SourcePreparingCall sourceFrame
      preparedFieldExpression before ⟨.ok value, post⟩) : SourceOuterTag .word value := by
  apply stateful_reference_field_source_tag (preparing_base_type sourceFrame) (index := 1) rfl
    (preparing_success_tag heap sourceFrame) ?_ (preparing_field_type sourceFrame) ran
  intro start middle pointed selected type typed child read
  have sameType : type = .word := (Option.some.inj ((preparing_field_type sourceFrame).symm.trans typed)).symm
  subst type
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "prepare-record" start _).mp child
  cases called <;> cases clear : start.fault <;>
    simp only [sourceObserve, sourcePoison, preparedSourcePost, clear] at observed
  all_goals cases observed
  all_goals simp only [sourceReferenceCall, source_raw_finish_memory] at read
  · change some (.word (bounded 64 21)) = some selected at read
    cases read
    exact .word _
  · change some (.word (bounded 64 21)) = some selected at read
    cases read
    exact .word _
  · change none = some selected at read
    cases read

end Mettapedia.GSLT.LanguageDef.NativeOps.ReferenceFieldControls
