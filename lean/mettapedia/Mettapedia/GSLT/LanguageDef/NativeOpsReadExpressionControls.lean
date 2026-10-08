import Mettapedia.GSLT.LanguageDef.NativeOpsReadExpressionLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal

/-! Live borrowed reads, effectful ordered slices, exact refusals, undefined storage and stored-type controls. -/

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

open NativeWord64 (bounded)

def preparedSourceValue (array : Bool) : SourceValue :=
  if array then .array .word (some address) (bounded 64 7) else .reference (some address)

def preparedTargetValue (array : Bool) : TargetValue :=
  if array then .array .word (some address) 7 else .reference (some address)

def preparedType (array : Bool) : NativeType := if array then .array .word else .ref .word

def preparingInterface (array : Bool) : Interface :=
  ⟨[], [], [], [⟨⟨"prepare", [], preparedType array⟩, "prepare", .effect, none⟩]⟩

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

inductive SourcePreparingCall (array : Bool) : SourceCalls Nat where
  | value (state : SourceState Nat) :
      SourcePreparingCall array "prepare" [] state (preparedSourceValue array)
        (preparedSourcePost state (some (.word (bounded 64 21))) true 4)
  | refusal (state : SourceState Nat) :
      SourcePreparingCall array "prepare" [] state (preparedSourceValue array)
        (sourcePoison (preparedSourcePost state (some (.word (bounded 64 21))) true 5) .resourceFault)
  | unavailable (state : SourceState Nat) :
      SourcePreparingCall array "prepare" [] state (preparedSourceValue array)
        (preparedSourcePost state (some (.word (bounded 64 21))) false 6)
  | missing (state : SourceState Nat) :
      SourcePreparingCall array "prepare" [] state (preparedSourceValue array)
        (preparedSourcePost state none true 7)

inductive TargetPreparingCall (array : Bool) : TargetCalls Nat where
  | value (state : TargetState Nat) :
      TargetPreparingCall array (.external "prepare") [] state (preparedTargetValue array)
        (preparedTargetPost state (some (.word (bounded 64 21))) true 4)
  | refusal (state : TargetState Nat) :
      TargetPreparingCall array (.external "prepare") [] state (preparedTargetValue array)
        (targetPoison (preparedTargetPost state (some (.word (bounded 64 21))) true 5) .resourceFault)
  | unavailable (state : TargetState Nat) :
      TargetPreparingCall array (.external "prepare") [] state (preparedTargetValue array)
        (preparedTargetPost state (some (.word (bounded 64 21))) false 6)
  | missing (state : TargetState Nat) :
      TargetPreparingCall array (.external "prepare") [] state (preparedTargetValue array)
        (preparedTargetPost state none true 7)

theorem prepared_value_correspondence (array : Bool) :
    preparedTargetValue array = encodeValue (preparedSourceValue array) := by
  cases array <;> rfl

theorem prepared_post_correspondence {source : SourceState Nat} {target : TargetState Nat}
    (states : StateRelated Eq source target) (payload : Option SourceValue) (ready : Bool) (increment : Nat) :
    StateRelated Eq (preparedSourcePost source payload ready increment)
      (preparedTargetPost target payload ready increment) :=
  ⟨(fixture_states_related (some address) payload).memory, states.fault, states.allocator,
    rfl, congrArg (fun n => n + increment) states.external, states.allocatorStats⟩

theorem preparing_call_contract (array : Bool) :
    ExternalCorrespondence ⟨SourcePreparingCall array⟩
      ⟨fun name => TargetPreparingCall array (.external name)⟩ Eq := by
  constructor
  · intro name arguments source target raw post states called
    cases called with
    | value =>
        refine ⟨_, ?_, prepared_post_correspondence states _ true 4⟩
        rw [← prepared_value_correspondence array]
        exact .value target
    | refusal =>
        refine ⟨_, ?_, poison_correspondence (prepared_post_correspondence states _ true 5) _⟩
        rw [← prepared_value_correspondence array]
        exact .refusal target
    | unavailable =>
        refine ⟨_, ?_, prepared_post_correspondence states _ false 6⟩
        rw [← prepared_value_correspondence array]
        exact .unavailable target
    | missing =>
        refine ⟨_, ?_, prepared_post_correspondence states none true 7⟩
        rw [← prepared_value_correspondence array]
        exact .missing target
  · intro name arguments source target raw post states called
    generalize encoded : encodeValues arguments = targetArguments at called
    cases called with
    | value =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .value source, prepared_value_correspondence array,
          prepared_post_correspondence states _ true 4⟩
    | refusal =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .refusal source, prepared_value_correspondence array,
          poison_correspondence (prepared_post_correspondence states _ true 5) _⟩
    | unavailable =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .unavailable source, prepared_value_correspondence array,
          prepared_post_correspondence states _ false 6⟩
    | missing =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        exact ⟨_, _, .missing source, prepared_value_correspondence array,
          prepared_post_correspondence states none true 7⟩

theorem preparing_success_tag (array : Bool) (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval (preparingInterface array) heap (SourcePreparingCall array)
      frame (.call "prepare" []) before ⟨.ok value, post⟩) : SourceOuterTag (preparedType array) value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "prepare" before _).mp ran
  cases called <;>
    cases clear : before.fault <;>
    simp only [sourceObserve, sourcePoison, preparedSourcePost, clear] at observed
  all_goals cases observed
  all_goals cases array <;> constructor

theorem preparing_child_instance (array : Bool)
    (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (frame : SourceFrame) (source : SourceState Nat) :
    StatefulChildLaws Eq (preparingInterface array) sourceHeap (SourcePreparingCall array)
      targetHeap (TargetPreparingCall array) frame source .word (.word 0) (.call "prepare" []) := by
  apply nullary_external_stateful_child_laws Eq (preparingInterface array) sourceHeap (SourcePreparingCall array)
    targetHeap (TargetPreparingCall array) (preparing_call_contract array) frame source
    "prepare" (preparedType array) .word (.word 0) _ _ rfl .unsignedWord
  · simp only [inferExpr, inferExprList, lookupFunction, preparingInterface]
    cases array <;> rfl
  · cases array <;> intro impossible <;> cases impossible

def preparedReadExpression (array : Bool) : Expr :=
  if array then .length (.call "prepare" []) else .load (.call "prepare" [])

def preparedReadValue (array : Bool) : SourceValue := .word (bounded 64 (if array then 7 else 21))

def preparedReadOutput (supply : NativeIR.Supply) (array : Bool) : NativeLowering.Expression :=
  let atom := NativeIR.Atom.temporary (supply.next + 1) (preparedType array)
  ⟨[.call (some (.temporary (supply.next + 1) (preparedType array))) (.external "prepare") [], .checkContext] ++
      (if array then [] else NativeLowering.checkReference atom) ++
      [.temporary (supply.next + 2) .word (if array then .length atom else .indirectRead atom)],
    .temporary (supply.next + 2) .word, ⟨supply.next + 2⟩⟩

theorem preparing_read_actual_lowering (scope : Scope) (supply : NativeIR.Supply) (array : Bool) :
    NativeLowering.expression? (preparingInterface array) scope (preparedReadExpression array) supply =
      some (preparedReadOutput supply array) := by
  cases array <;> simp only [preparedReadExpression, NativeLowering.expression?,
    NativeLowering.location?, NativeLowering.arguments?, inferExpr, inferLocation, inferExprList,
    lookupFunction, preparingInterface, preparedType, List.find?_cons, List.find?_nil, List.any_nil,
    Bool.false_eq_true, if_false, if_true]
  all_goals rfl

theorem preparing_read_child_instance (array : Bool)
    (sourceHeap : SourceHeapSemantics Nat) (targetHeap : TargetHeapSemantics Nat)
    (frame : SourceFrame) (source : SourceState Nat) (clear : source.fault = none) :
    StatefulChildLaws Eq (preparingInterface array) sourceHeap (SourcePreparingCall array)
      targetHeap (TargetPreparingCall array) frame source .word (.word 0) (preparedReadExpression array) := by
  cases array with
  | false =>
      apply stateful_load_child_laws Eq (preparingInterface false) sourceHeap (SourcePreparingCall false)
        targetHeap (TargetPreparingCall false) frame source clear .word (.word 0) .unsignedWord (.call "prepare" [])
        (fun before _ => preparing_child_instance false sourceHeap targetHeap frame before)
      intro before post value type typed ran
      have same : type = .word := by
        simp only [inferExpr, inferExprList, lookupFunction, preparingInterface, preparedType] at typed
        cases typed; rfl
      subst type
      exact preparing_success_tag false sourceHeap frame before post value ran
  | true =>
      apply stateful_length_child_laws Eq (preparingInterface true) sourceHeap (SourcePreparingCall true)
        targetHeap (TargetPreparingCall true) frame source clear .word (.word 0) (.call "prepare" [])
        (fun before _ => preparing_child_instance true sourceHeap targetHeap frame before)
      intro before post value element typed ran
      have same : element = .word := by
        simp only [inferExpr, inferExprList, lookupFunction, preparingInterface, preparedType] at typed
        cases typed; rfl
      subst element
      exact preparing_success_tag true sourceHeap frame before post value ran

def preparingSource : SourceState Nat :=
  ⟨sourceMemory (some address) (some (.word (bounded 64 13))), none, true, true, 0, AllocatorStats.sourceEmpty⟩

def preparingTarget : TargetState Nat :=
  ⟨targetMemory (some address) (some (.word (bounded 64 13))), none, true, true, 0, AllocatorStats.targetEmpty⟩

theorem preparing_initial_related : StateRelated Eq preparingSource preparingTarget :=
  ⟨(fixture_states_related _ _).memory, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩

theorem preparing_read_source_success (array : Bool) (heap : SourceHeapSemantics Nat) :
    SourceExprEval (preparingInterface array) heap (SourcePreparingCall array) sourceFrame
      (preparedReadExpression array) preparingSource
      ⟨.ok (preparedReadValue array),
        preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 4⟩ := by
  have child : SourceExprEval (preparingInterface array) heap (SourcePreparingCall array) sourceFrame
      (.call "prepare" []) preparingSource
      ⟨.ok (preparedSourceValue array),
        preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 4⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .value preparingSource, rfl⟩
  cases array with
  | false =>
      refine .strict rfl (.cons child (.nil _)) ?_
      apply (source_load_primitive_exact _ _ _ _ (.call "prepare" []) (some address) _ _).mpr
      exact ⟨address, .word (bounded 64 21), rfl, rfl, rfl⟩
  | true => exact .strict rfl (.cons child (.nil _)) rfl

theorem preparing_read_target_success (array : Bool) (sourceHeap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun (preparingInterface array) targetHeap (TargetPreparingCall array) .word root
        (preparedReadOutput ⟨0⟩ array).code targetFrame preparingTarget out ∧
      out.flow = .normal ∧ out.state.external = 4 ∧ out.state.memory.cells 11 0 = some (.word 21) ∧
      TargetAtomEval (preparingInterface array) out.frame out.state
        (preparedReadOutput ⟨0⟩ array).result (encodeValue (preparedReadValue array)) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (preparing_read_child_instance array sourceHeap targetHeap sourceFrame preparingSource rfl).forward
      root (targetFrame := targetFrame) (preparing_read_actual_lowering _ ⟨0⟩ array) ⟨rfl, rfl, rfl⟩
      preparing_initial_related (by intro identity live; cases live) (by intro identity _; rfl) (preparing_read_source_success array sourceHeap)
  rcases related with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

theorem preparing_read_actual_reflection (array : Bool) (sourceHeap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (root : List NativeIR.Instruction)
    {out : TargetBlockOutcome Nat}
    (ran : TargetRun (preparingInterface array) targetHeap (TargetPreparingCall array) .word root
      (preparedReadOutput ⟨0⟩ array).code targetFrame preparingTarget out) :
    ∃ sourceOut,
      SourceExprEval (preparingInterface array) sourceHeap (SourcePreparingCall array) sourceFrame
        (preparedReadExpression array) preparingSource sourceOut ∧
      CheckedExpressionRelated Eq (preparingInterface array) (.word 0)
        (preparedReadOutput ⟨0⟩ array).result sourceOut out := by
  obtain ⟨sourceOut, sourceRan, related, _, _, _⟩ :=
    (preparing_read_child_instance array sourceHeap targetHeap sourceFrame preparingSource rfl).backward
      root (targetFrame := targetFrame) (preparing_read_actual_lowering _ ⟨0⟩ array) ⟨rfl, rfl, rfl⟩
      preparing_initial_related (by intro identity live; cases live) (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRan, related⟩

theorem preparing_load_value_differs_from_old_cell :
    encodeValue (preparedReadValue false) ≠ .word 13 ∧
      preparingTarget.memory.cells 11 0 = some (.word 13) := by
  refine ⟨?_, rfl⟩
  intro same
  have bits := TargetValue.word.inj same
  have numbers := congrArg BitVec.toNat bits
  contradiction



theorem preparing_read_source_first_fault (array : Bool) (heap : SourceHeapSemantics Nat) :
    SourceExprEval (preparingInterface array) heap (SourcePreparingCall array) sourceFrame
      (preparedReadExpression array) preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  have child : SourceExprEval (preparingInterface array) heap (SourcePreparingCall array) sourceFrame
      (.call "prepare" []) preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .refusal preparingSource, rfl⟩
  cases array <;> exact .strictFault rfl (.consFault child)

theorem preparing_read_target_first_fault (array : Bool)
    (targetHeap : TargetHeapSemantics Nat) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun (preparingInterface array) targetHeap (TargetPreparingCall array) .word root
        (preparedReadOutput ⟨0⟩ array).code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 5 ∧ out.state.memory.cells 11 0 = some (.word 21) ∧
      out.frame.temporaryNames.contains 2 = false := by
  let post := targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary targetFrame 1 (preparedTargetValue array), post⟩,
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  cases array <;>
    apply TargetRun.next (TargetInstructionEval.call .nil (.refusal preparingTarget) (.fresh rfl))
  all_goals exact .return (.contextFault rfl .unsignedWord)


theorem preparing_load_source_unavailable (heap : SourceHeapSemantics Nat) :
    SourceExprEval (preparingInterface false) heap (SourcePreparingCall false) sourceFrame
      (preparedReadExpression false) preparingSource
      ⟨.error .invalidRequest,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6) .invalidRequest⟩ := by
  have child : SourceExprEval (preparingInterface false) heap (SourcePreparingCall false) sourceFrame
      (.call "prepare" []) preparingSource
      ⟨.ok (preparedSourceValue false),
        preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .unavailable preparingSource, rfl⟩
  refine .strict rfl (.cons child (.nil _)) ?_
  apply (source_load_primitive_exact _ _ _ _ (.call "prepare" []) (some address) _ _).mpr
  rfl

theorem preparing_load_target_unavailable (sourceHeap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun (preparingInterface false) targetHeap (TargetPreparingCall false) .word root
        (preparedReadOutput ⟨0⟩ false).code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .invalidRequest ∧
      out.state.external = 6 ∧ out.state.releaseAvailable = false ∧
      out.state.memory.cells 11 0 = some (.word 21) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (preparing_read_child_instance false sourceHeap targetHeap sourceFrame preparingSource rfl).forward
      root (targetFrame := targetFrame) (preparing_read_actual_lowering _ ⟨0⟩ false) ⟨rfl, rfl, rfl⟩
      preparing_initial_related (by intro identity live; cases live) (by intro identity _; rfl)
      (preparing_load_source_unavailable sourceHeap)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.release, states.memory.1 11 0⟩

theorem preparing_missing_load_primitive_stuck (heap : SourceHeapSemantics Nat) (out : SourceOutcome Nat) :
    ¬ sourcePrimitive (preparingInterface false) heap (SourcePreparingCall false) sourceFrame
      (.load (.call "prepare" [])) [.reference (some address)]
      (preparedSourcePost preparingSource none true 7) out := by
  intro ran
  obtain ⟨pointed, value, same, read, _⟩ :=
    (source_load_primitive_exact _ _ _ _ (.call "prepare" []) (some address) _ out).mp ran
  cases Option.some.inj same
  change none = some value at read
  cases read

theorem preparing_missing_load_target_stuck (heap : TargetHeapSemantics Nat)
    (root : List NativeIR.Instruction) (out : TargetBlockOutcome Nat) :
    ¬ TargetRun (preparingInterface false) heap (TargetPreparingCall false) .word root
      (NativeLowering.checkReference (.temporary 1 (.ref .word)) ++
        [.temporary 2 .word (.indirectRead (.temporary 1 (.ref .word)))])
      (targetDeclareTemporary targetFrame 1 (.reference (some address)))
      (preparedTargetPost preparingTarget none true 7) out := by
  intro ran
  let sourceHeap : SourceHeapSemantics Nat := ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩
  have states := prepared_post_correspondence preparing_initial_related none true 7
  have read := declared_temporary_atom (preparingInterface false) targetFrame
    (preparedTargetPost preparingTarget none true 7) 1 (.ref .word) (.reference (some address))
  obtain ⟨sourceOut, sourceRan, _, _, _, _⟩ := stateful_checked_load_fragment_profile states
    sourceHeap (SourcePreparingCall false) heap (TargetPreparingCall false) sourceFrame
    (targetDeclareTemporary targetFrame 1 (.reference (some address))) (.call "prepare" [])
    (some address) (.temporary 1 (.ref .word)) ⟨1⟩ .word .word read
    (declared_temporary_bound (before := 0) (after := 1) (identity := 1)
      (by intro _ live; cases live) (Nat.zero_le _) (Nat.le_refl _) _)
    (declared_temporaries_completeNames (by intro _ _; rfl) _ _) .unsignedWord root ran
  exact preparing_missing_load_primitive_stuck sourceHeap sourceOut sourceRan

theorem preparing_length_still_reads_descriptor (heap : SourceHeapSemantics Nat) :
    SourceExprEval (preparingInterface true) heap (SourcePreparingCall true) sourceFrame
      (preparedReadExpression true) preparingSource
      ⟨.ok (.word (bounded 64 7)), preparedSourcePost preparingSource none true 7⟩ ∧
    sourceRead (preparedSourcePost preparingSource none true 7).memory address = none := by
  have child : SourceExprEval (preparingInterface true) heap (SourcePreparingCall true) sourceFrame
      (.call "prepare" []) preparingSource
      ⟨.ok (preparedSourceValue true), preparedSourcePost preparingSource none true 7⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .missing preparingSource, rfl⟩
  exact ⟨.strict rfl (.cons child (.nil _)) rfl, rfl⟩


theorem preparing_length_target_missing_buffer (sourceHeap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun (preparingInterface true) targetHeap (TargetPreparingCall true) .word root
        (preparedReadOutput ⟨0⟩ true).code targetFrame preparingTarget out ∧
      out.flow = .normal ∧ out.state.external = 7 ∧ out.state.memory.cells 11 0 = none ∧
      TargetAtomEval (preparingInterface true) out.frame out.state
        (preparedReadOutput ⟨0⟩ true).result (.word 7) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (preparing_read_child_instance true sourceHeap targetHeap sourceFrame preparingSource rfl).forward
      root (targetFrame := targetFrame) (preparing_read_actual_lowering _ ⟨0⟩ true) ⟨rfl, rfl, rfl⟩
      preparing_initial_related (by intro identity live; cases live) (by intro identity _; rfl)
      (preparing_length_still_reads_descriptor sourceHeap).1
  rcases related with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

theorem omitted_read_guards_allow_faulted_dereference (heap : TargetHeapSemantics Nat)
    (root : List NativeIR.Instruction) :
    TargetRun (preparingInterface false) heap (TargetPreparingCall false) .word root
      [.call (some (.temporary 1 (.ref .word))) (.external "prepare") [],
       .temporary 2 .word (.indirectRead (.temporary 1 (.ref .word)))] targetFrame preparingTarget
      ⟨.normal, targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (.reference (some address))) 2 (.word 21),
        targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal preparingTarget) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.indirect
      (declared_temporary_atom (preparingInterface false) targetFrame _ 1 (.ref .word) (.reference (some address))) rfl))
  exact .nil _ _ _



theorem omitted_reference_check_reads_unavailable_storage (heap : TargetHeapSemantics Nat)
    (root : List NativeIR.Instruction) :
    TargetRun (preparingInterface false) heap (TargetPreparingCall false) .word root
      [.call (some (.temporary 1 (.ref .word))) (.external "prepare") [], .checkContext,
       .temporary 2 .word (.indirectRead (.temporary 1 (.ref .word)))] targetFrame preparingTarget
      ⟨.normal, targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (.reference (some address))) 2 (.word 21),
        preparedTargetPost preparingTarget (some (.word (bounded 64 21))) false 6⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.unavailable preparingTarget) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.indirect
      (declared_temporary_atom (preparingInterface false) targetFrame _ 1 (.ref .word) (.reference (some address))) rfl))
  exact .nil _ _ _

theorem reference_guard_omission_changes_observation :
    (targetObserve (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) false 6)
      (.word 21)).result = .ok (.word 21) ∧
    (sourceObserve
      (sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) false 6) .invalidRequest)
      (.word (bounded 64 21))).result = .error .invalidRequest := ⟨rfl, rfl⟩

def indexPreparingInterface : Interface :=
  ⟨[], [], [], [⟨⟨"prepare", [], .array .word⟩, "prepare", .effect, none⟩,
    ⟨⟨"position", [], .word⟩, "position", .effect, none⟩]⟩

def indexSourceHeap : SourceHeapSemantics Nat :=
  ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩
def indexTargetHeap : TargetHeapSemantics Nat :=
  ⟨fun _ => 1, fun _ _ _ _ => False, fun _ _ _ _ => False⟩

inductive SourceIndexPreparingCall : SourceCalls Nat where
  | array {name arguments state value post} (called : SourcePreparingCall true name arguments state value post) :
      SourceIndexPreparingCall name arguments state value post
  | position (state : SourceState Nat) :
      SourceIndexPreparingCall "position" [] state (.word (bounded 64 0))
        (preparedSourcePost state (some (.word (bounded 64 34))) true 8)
  | refusal (state : SourceState Nat) :
      SourceIndexPreparingCall "position" [] state (.word (bounded 64 0))
        (sourcePoison (preparedSourcePost state (some (.word (bounded 64 34))) true 9) .resourceFault)
  | unavailable (state : SourceState Nat) :
      SourceIndexPreparingCall "position" [] state (.word (bounded 64 0))
        (preparedSourcePost state (some (.word (bounded 64 34))) false 10)
  | missing (state : SourceState Nat) :
      SourceIndexPreparingCall "position" [] state (.word (bounded 64 0))
        (preparedSourcePost state none true 11)
  | bounds (state : SourceState Nat) :
      SourceIndexPreparingCall "position" [] state (.word (bounded 64 7))
        (preparedSourcePost state (some (.word (bounded 64 34))) true 12)

inductive TargetIndexPreparingCall : TargetCalls Nat where
  | array {target arguments state value post} (called : TargetPreparingCall true target arguments state value post) :
      TargetIndexPreparingCall target arguments state value post
  | position (state : TargetState Nat) :
      TargetIndexPreparingCall (.external "position") [] state (.word 0)
        (preparedTargetPost state (some (.word (bounded 64 34))) true 8)
  | refusal (state : TargetState Nat) :
      TargetIndexPreparingCall (.external "position") [] state (.word 0)
        (targetPoison (preparedTargetPost state (some (.word (bounded 64 34))) true 9) .resourceFault)
  | unavailable (state : TargetState Nat) :
      TargetIndexPreparingCall (.external "position") [] state (.word 0)
        (preparedTargetPost state (some (.word (bounded 64 34))) false 10)
  | missing (state : TargetState Nat) :
      TargetIndexPreparingCall (.external "position") [] state (.word 0)
        (preparedTargetPost state none true 11)
  | bounds (state : TargetState Nat) :
      TargetIndexPreparingCall (.external "position") [] state (.word 7)
        (preparedTargetPost state (some (.word (bounded 64 34))) true 12)

theorem index_preparing_call_contract :
    ExternalCorrespondence ⟨SourceIndexPreparingCall⟩
      ⟨fun name => TargetIndexPreparingCall (.external name)⟩ Eq := by
  constructor
  · intro name arguments source target raw post states called
    cases called with
    | array called =>
        obtain ⟨post, targetCalled, related⟩ := (preparing_call_contract true).forward _ _ _ _ _ _ states called
        exact ⟨post, .array targetCalled, related⟩
    | position => exact ⟨_, .position target, prepared_post_correspondence states _ true 8⟩
    | refusal => exact ⟨_, .refusal target, poison_correspondence (prepared_post_correspondence states _ true 9) _⟩
    | unavailable => exact ⟨_, .unavailable target, prepared_post_correspondence states _ false 10⟩
    | missing => exact ⟨_, .missing target, prepared_post_correspondence states none true 11⟩
    | bounds => exact ⟨_, .bounds target, prepared_post_correspondence states _ true 12⟩
  · intro name arguments source target raw post states called
    generalize encoded : encodeValues arguments = targetArguments at called
    cases called with
    | array called =>
        rw [← encoded] at called
        obtain ⟨value, post, sourceCalled, same, related⟩ :=
          (preparing_call_contract true).backward _ _ _ _ _ _ states called
        exact ⟨value, post, .array sourceCalled, same, related⟩
    | position | refusal | unavailable | missing | bounds =>
        have empty : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        first
        | exact ⟨_, _, .position source, rfl, prepared_post_correspondence states _ true 8⟩
        | exact ⟨_, _, .refusal source, rfl, poison_correspondence (prepared_post_correspondence states _ true 9) _⟩
        | exact ⟨_, _, .unavailable source, rfl, prepared_post_correspondence states _ false 10⟩
        | exact ⟨_, _, .missing source, rfl, prepared_post_correspondence states none true 11⟩
        | exact ⟨_, _, .bounds source, rfl, prepared_post_correspondence states _ true 12⟩

theorem index_preparing_array_success_tag (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval indexPreparingInterface heap SourceIndexPreparingCall frame
      (.call "prepare" []) before ⟨.ok value, post⟩) : SourceOuterTag (.array .word) value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "prepare" before _).mp ran
  generalize chosen : ("prepare" : String) = name at called
  cases called with
  | array called =>
      cases chosen
      have smaller : SourceExprEval (preparingInterface true) heap (SourcePreparingCall true) frame
          (.call "prepare" []) before ⟨.ok value, post⟩ :=
        (source_nullary_call_exact "prepare" before _).mpr ⟨raw, after, called, observed⟩
      exact preparing_success_tag true heap frame before post value smaller
  | position | refusal | unavailable | missing | bounds =>
      exact False.elim ((by decide : ("prepare" : String) ≠ "position") chosen)

theorem index_preparing_position_success_tag (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval indexPreparingInterface heap SourceIndexPreparingCall frame
      (.call "position" []) before ⟨.ok value, post⟩) : SourceOuterTag .word value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "position" before _).mp ran
  generalize chosen : ("position" : String) = name at called
  cases called with
  | array called =>
      cases called <;> exact False.elim ((by decide : ("position" : String) ≠ "prepare") chosen)
  | position | refusal | unavailable | missing | bounds =>
      cases clear : before.fault <;>
        simp only [sourceObserve, sourcePoison, preparedSourcePost, clear] at observed
      all_goals cases observed
      all_goals exact .word _

theorem index_preparing_nullary_instance (heap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (frame : SourceFrame) (source : SourceState Nat)
    (name : String) (type : NativeType)
    (typing : inferExpr indexPreparingInterface (sourceFrameScope frame) (.call name []) = some type)
    (nonunit : type ≠ .unit) :
    StatefulChildLaws Eq indexPreparingInterface heap SourceIndexPreparingCall targetHeap TargetIndexPreparingCall
      frame source .word (.word 0) (.call name []) :=
  nullary_external_stateful_child_laws Eq indexPreparingInterface heap SourceIndexPreparingCall
    targetHeap TargetIndexPreparingCall index_preparing_call_contract frame source name type .word (.word 0)
    typing nonunit rfl .unsignedWord

def indexPreparingExpression : Expr := .index (.call "prepare" []) (.call "position" [])
def indexPreparingOutput : NativeLowering.Expression :=
  ⟨[.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
    .call (some (.temporary 2 .word)) (.external "position") [], .checkContext,
    .helper (some (.temporary 3 (.ref .word))) (.index (.temporary 1 (.array .word)) (.temporary 2 .word) .word),
    .checkContext, .temporary 4 .word (.indirectRead (.temporary 3 (.ref .word)))],
    .temporary 4 .word, ⟨4⟩⟩

theorem index_preparing_actual_emission :
    NativeLowering.expression? indexPreparingInterface (sourceFrameScope sourceFrame)
      indexPreparingExpression ⟨0⟩ = some indexPreparingOutput := by
  simp only [indexPreparingExpression, NativeLowering.expression?, NativeLowering.location?,
    NativeLowering.arguments?, inferExpr, inferLocation, inferExprList, lookupFunction,
    indexPreparingInterface, List.find?_cons, List.find?_nil]
  rfl

theorem index_preparing_child_instance (source : SourceState Nat) (clear : source.fault = none) :
    StatefulChildLaws Eq indexPreparingInterface indexSourceHeap SourceIndexPreparingCall
      indexTargetHeap TargetIndexPreparingCall sourceFrame source .word (.word 0) indexPreparingExpression := by
  apply stateful_index_child_laws Eq indexPreparingInterface indexSourceHeap SourceIndexPreparingCall
    indexTargetHeap TargetIndexPreparingCall sourceFrame source clear .word (.word 0) .unsignedWord
    (.call "prepare" []) (.call "position" [])
  · intro before _
    exact index_preparing_nullary_instance indexSourceHeap indexTargetHeap sourceFrame before "prepare" (.array .word)
      (by simp only [inferExpr, inferExprList, lookupFunction, indexPreparingInterface]; rfl)
      (by intro impossible; cases impossible)
  · intro before _
    exact index_preparing_nullary_instance indexSourceHeap indexTargetHeap sourceFrame before "position" .word
      (by simp only [inferExpr, inferExprList, lookupFunction, indexPreparingInterface]; rfl)
      (by intro impossible; cases impossible)
  · intro type typed
    have same : type = .word := by
      simp only [inferExpr, inferExprList, lookupFunction, indexPreparingInterface] at typed
      cases typed; rfl
    subst type; rfl
  · intro before post value type typed ran
    have same : type = .word := by
      simp only [inferExpr, inferExprList, lookupFunction, indexPreparingInterface] at typed
      cases typed; rfl
    subst type
    exact index_preparing_array_success_tag indexSourceHeap sourceFrame before post value ran
  · exact index_preparing_position_success_tag indexSourceHeap sourceFrame

def indexPreparingMiddle : SourceState Nat :=
  preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 4

def indexPreparingFinal : SourceState Nat :=
  preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) true 8

theorem index_preparing_source_success :
    SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource ⟨.ok (.word (bounded 64 34)), indexPreparingFinal⟩ := by
  have arrayRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "prepare" []) preparingSource ⟨.ok (preparedSourceValue true), indexPreparingMiddle⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .array (.value preparingSource), rfl⟩
  have positionRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "position" []) indexPreparingMiddle ⟨.ok (.word (bounded 64 0)), indexPreparingFinal⟩ :=
    (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
      ⟨_, _, .position indexPreparingMiddle, rfl⟩
  refine .strict rfl (.cons arrayRan (.cons positionRan (.nil _))) ?_
  apply (source_index_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" [])
    .word (some address) (bounded 64 7) (bounded 64 0) indexPreparingFinal _).mpr
  exact ⟨address, .word (bounded 64 34), rfl, rfl, rfl⟩

theorem index_preparing_target_success (root : List Instruction) :
    ∃ out, TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
        indexPreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .normal ∧ out.state.external = 12 ∧
      out.state.memory.cells 11 0 = some (.word 34) ∧
      TargetAtomEval indexPreparingInterface out.frame out.state indexPreparingOutput.result (.word 34) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (index_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) index_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) index_preparing_source_success
  rcases checked with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

theorem index_preparing_actual_reflection (root : List Instruction) {out : TargetBlockOutcome Nat}
    (ran : TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
      indexPreparingOutput.code targetFrame preparingTarget out) :
    ∃ sourceOut, SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource sourceOut ∧
      CheckedExpressionRelated Eq indexPreparingInterface (.word 0) indexPreparingOutput.result sourceOut out := by
  obtain ⟨sourceOut, sourceRan, checked, _, _, _⟩ := (index_preparing_child_instance preparingSource rfl).backward
    root (targetFrame := targetFrame) index_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) ran
  exact ⟨sourceOut, sourceRan, checked⟩

theorem index_preparing_stale_reads_differ :
    (.word (bounded 64 13) : SourceValue) ≠ .word (bounded 64 34) ∧
      (.word (bounded 64 21) : SourceValue) ≠ .word (bounded 64 34) := by
  constructor <;> intro same
  all_goals have words := SourceValue.word.inj same
  all_goals have numbers := congrArg (fun word => word.val) words
  all_goals contradiction

theorem index_preparing_source_first_fault :
    SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  apply SourceExprEval.strictFault rfl
  apply SourceArgumentsEval.consFault
  exact (source_nullary_call_exact "prepare" preparingSource _).mpr
    ⟨_, _, .array (.refusal preparingSource), rfl⟩

theorem index_preparing_target_first_fault (root : List Instruction) :
    ∃ out, TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
        indexPreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 5 ∧ out.state.memory.cells 11 0 = some (.word 21) ∧
      out.frame.temporaryNames.contains 2 = false ∧ out.frame.temporaryNames.contains 3 = false ∧
      out.frame.temporaryNames.contains 4 = false := by
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary targetFrame 1 (preparedTargetValue true),
      targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.array (.refusal preparingTarget)) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem index_preparing_source_second_fault :
    SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) true 9) .resourceFault⟩ := by
  apply SourceExprEval.strictFault rfl
  refine SourceArgumentsEval.cons (middle := indexPreparingMiddle)
    (value := preparedSourceValue true) ?_ (.consFault ?_)
  · exact (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .array (.value preparingSource), rfl⟩
  · exact (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
      ⟨_, _, .refusal indexPreparingMiddle, rfl⟩

theorem index_preparing_target_second_fault (root : List Instruction) :
    ∃ out, TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
        indexPreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 13 ∧ out.state.memory.cells 11 0 = some (.word 34) ∧
      out.frame.temporaryNames.contains 1 = true ∧ out.frame.temporaryNames.contains 2 = true ∧
      out.frame.temporaryNames.contains 3 = false ∧ out.frame.temporaryNames.contains 4 = false := by
  let middle := preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4
  let first := targetDeclareTemporary targetFrame 1 (preparedTargetValue true)
  let post := targetPoison (preparedTargetPost middle (some (.word (bounded 64 34))) true 9) .resourceFault
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary first 2 (.word 0), post⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.array (.value preparingTarget)) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal middle) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem index_preparing_source_unavailable :
    SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource
      ⟨.error .invalidRequest,
        sourcePoison (preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) false 10) .invalidRequest⟩ := by
  have arrayRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "prepare" []) preparingSource ⟨.ok (preparedSourceValue true), indexPreparingMiddle⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .array (.value preparingSource), rfl⟩
  have positionRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "position" []) indexPreparingMiddle
      ⟨.ok (.word (bounded 64 0)), preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) false 10⟩ :=
    (source_nullary_call_exact "position" indexPreparingMiddle _).mpr ⟨_, _, .unavailable indexPreparingMiddle, rfl⟩
  refine .strict rfl (.cons arrayRan (.cons positionRan (.nil _))) ?_
  exact (source_index_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" [])
    .word (some address) (bounded 64 7) (bounded 64 0) _ _).mpr rfl

theorem index_preparing_target_unavailable (root : List Instruction) :
    ∃ out, TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
        indexPreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .invalidRequest ∧
      out.state.external = 14 ∧ out.state.releaseAvailable = false ∧
      out.state.memory.cells 11 0 = some (.word 34) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (index_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) index_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) index_preparing_source_unavailable
  rcases checked with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.release, states.memory.1 11 0⟩

theorem index_preparing_source_bounds_fault :
    SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression preparingSource
      ⟨.error .indexOutOfBounds,
        sourcePoison (preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) true 12) .indexOutOfBounds⟩ := by
  have arrayRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "prepare" []) preparingSource ⟨.ok (preparedSourceValue true), indexPreparingMiddle⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr ⟨_, _, .array (.value preparingSource), rfl⟩
  have positionRan : SourceExprEval indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      (.call "position" []) indexPreparingMiddle
      ⟨.ok (.word (bounded 64 7)), preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) true 12⟩ :=
    (source_nullary_call_exact "position" indexPreparingMiddle _).mpr ⟨_, _, .bounds indexPreparingMiddle, rfl⟩
  refine .strict rfl (.cons arrayRan (.cons positionRan (.nil _))) ?_
  exact (source_index_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" [])
    .word (some address) (bounded 64 7) (bounded 64 7) _ _).mpr rfl

theorem index_preparing_target_bounds_fault (root : List Instruction) :
    ∃ out, TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
        indexPreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .indexOutOfBounds ∧
      out.state.external = 16 ∧ out.state.memory.cells 11 0 = some (.word 34) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (index_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) index_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) index_preparing_source_bounds_fault
  rcases checked with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 11 0⟩

theorem index_preparing_missing_primitive_has_no_run (out : SourceOutcome Nat) :
    ¬ sourcePrimitive indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
      indexPreparingExpression [.array .word (some address) (bounded 64 7), .word (bounded 64 0)]
      (preparedSourcePost indexPreparingMiddle none true 11) out := by
  intro ran
  obtain ⟨pointed, value, same, read, _⟩ := (source_index_primitive_exact _ _ _ _
    (.call "prepare" []) (.call "position" []) .word (some address) (bounded 64 7)
    (bounded 64 0) _ out).mp ran
  have fixed : pointed = address := by
    have pointer : (.reference (some address) : SourceValue) = .reference (some pointed) := same
    exact (Option.some.inj (SourceValue.reference.inj pointer)).symm
  subst pointed
  change none = some value at read
  cases read

theorem index_preparing_missing_target_has_no_run (root : List Instruction) (out : TargetBlockOutcome Nat) :
    ¬ TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
      [.helper (some (.temporary 3 (.ref .word))) (.index (.temporary 1 (.array .word)) (.temporary 2 .word) .word),
       .checkContext, .temporary 4 .word (.indirectRead (.temporary 3 (.ref .word)))]
      (targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (preparedTargetValue true)) 2 (.word 0))
      (preparedTargetPost (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4) none true 11) out := by
  intro ran
  let frame := targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (preparedTargetValue true)) 2 (.word 0)
  let post := preparedTargetPost (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4) none true 11
  have states := prepared_post_correspondence
    (prepared_post_correspondence preparing_initial_related (some (.word (bounded 64 21))) true 4) none true 11
  have arrayRead : TargetAtomEval indexPreparingInterface frame post (.temporary 1 (.array .word))
      (preparedTargetValue true) := .temporary rfl rfl
  have positionRead : TargetAtomEval indexPreparingInterface frame post (.temporary 2 .word) (.word 0) := .temporary rfl rfl
  have frameBounded : TemporaryNamesBound frame 2 := by
    apply declared_temporary_bound (before := 1) (after := 2) (identity := 2) _ (by omega) (Nat.le_refl _)
    exact declared_temporary_bound (before := 0) (after := 1) (identity := 1)
      (by intro _ live; cases live) (by omega) (Nat.le_refl _) _
  have hscope : TemporariesScoped frame :=
    declared_temporaries_completeNames (declared_temporaries_completeNames (by intro _ _; rfl) _ _) _ _
  obtain ⟨sourceOut, sourceRead, _, _, _, _⟩ := stateful_checked_raw_reference_read_profile
    (index_call_correspondence states (bounded 64 7) 1 (bounded 64 0) (some address))
    (target_index_call_exact (heap := indexTargetHeap) arrayRead positionRead) ⟨2⟩ .word
    frameBounded hscope .unsignedWord root ran
  exact index_preparing_missing_primitive_has_no_run sourceOut sourceRead

theorem index_array_tag_does_not_type_pointee :
    SourceOuterTag (.array .word) (.array .word (some address) (bounded 64 7)) ∧
      sourcePrimitive indexPreparingInterface indexSourceHeap SourceIndexPreparingCall sourceFrame
        indexPreparingExpression [.array .word (some address) (bounded 64 7), .word (bounded 64 0)]
        (preparedSourcePost indexPreparingMiddle (some (.bool true)) true 8)
        ⟨.ok (.bool true), preparedSourcePost indexPreparingMiddle (some (.bool true)) true 8⟩ ∧
      ¬ SourceOuterTag .word (.bool true) := by
  refine ⟨.array _ _ _, ?_, fun impossible => by cases impossible⟩
  apply (source_index_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" [])
    .word (some address) (bounded 64 7) (bounded 64 0) _ _).mpr
  exact ⟨address, .bool true, rfl, rfl, rfl⟩

theorem index_omitted_checks_admit_faulted_dereference (root : List Instruction) :
    let first := targetDeclareTemporary targetFrame 1 (preparedTargetValue true)
    let second := targetDeclareTemporary first 2 (.word 0)
    let location := targetDeclareTemporary second 3 (.reference (some address))
    let post := targetPoison (preparedTargetPost
      (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4)
      (some (.word (bounded 64 34))) true 9) .resourceFault
    TargetRun indexPreparingInterface indexTargetHeap TargetIndexPreparingCall .word root
      [.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
       .call (some (.temporary 2 .word)) (.external "position") [],
       .temporary 3 (.ref .word) (.elementAddress (.temporary 1 (.array .word)) (.temporary 2 .word) .word),
       .temporary 4 .word (.indirectRead (.temporary 3 (.ref .word)))] targetFrame preparingTarget
      ⟨.normal, targetDeclareTemporary location 4 (.word 34), post⟩ := by
  dsimp only
  apply TargetRun.next (TargetInstructionEval.call .nil (.array (.value preparingTarget)) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal _) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.elementAddress (.temporary rfl rfl) (.temporary rfl rfl)))
  apply TargetRun.next (TargetInstructionEval.temporary rfl
    (TargetPureEval.indirect (.temporary rfl rfl) rfl))
  exact .nil _ _ _


def slicePreparingInterface : Interface :=
  ⟨[], [], [], [⟨⟨"prepare", [], .array .word⟩, "prepare", .effect, none⟩,
    ⟨⟨"position", [], .word⟩, "position", .effect, none⟩,
    ⟨⟨"count", [], .word⟩, "count", .effect, none⟩]⟩

inductive SourceSlicePreparingCall : SourceCalls Nat where
  | prior {name arguments state value post}
      (called : SourceIndexPreparingCall name arguments state value post) :
      SourceSlicePreparingCall name arguments state value post
  | count (state : SourceState Nat) :
      SourceSlicePreparingCall "count" [] state (.word (bounded 64 2))
        (preparedSourcePost state (some (.word (bounded 64 55))) true 16)
  | refusal (state : SourceState Nat) :
      SourceSlicePreparingCall "count" [] state (.word (bounded 64 0))
        (sourcePoison (preparedSourcePost state (some (.word (bounded 64 55))) true 17) .resourceFault)
  | bounds (state : SourceState Nat) :
      SourceSlicePreparingCall "count" [] state (.word (bounded 64 8))
        (preparedSourcePost state (some (.word (bounded 64 55))) true 18)
  | empty (state : SourceState Nat) :
      SourceSlicePreparingCall "count" [] state (.word (bounded 64 0))
        (preparedSourcePost state (some (.word (bounded 64 55))) true 19)
  | unavailable (state : SourceState Nat) :
      SourceSlicePreparingCall "count" [] state (.word (bounded 64 2))
        (preparedSourcePost state (some (.word (bounded 64 55))) false 20)

inductive TargetSlicePreparingCall : TargetCalls Nat where
  | prior {target arguments state value post}
      (called : TargetIndexPreparingCall target arguments state value post) :
      TargetSlicePreparingCall target arguments state value post
  | count (state : TargetState Nat) :
      TargetSlicePreparingCall (.external "count") [] state (.word 2)
        (preparedTargetPost state (some (.word (bounded 64 55))) true 16)
  | refusal (state : TargetState Nat) :
      TargetSlicePreparingCall (.external "count") [] state (.word 0)
        (targetPoison (preparedTargetPost state (some (.word (bounded 64 55))) true 17) .resourceFault)
  | bounds (state : TargetState Nat) :
      TargetSlicePreparingCall (.external "count") [] state (.word 8)
        (preparedTargetPost state (some (.word (bounded 64 55))) true 18)
  | empty (state : TargetState Nat) :
      TargetSlicePreparingCall (.external "count") [] state (.word 0)
        (preparedTargetPost state (some (.word (bounded 64 55))) true 19)
  | unavailable (state : TargetState Nat) :
      TargetSlicePreparingCall (.external "count") [] state (.word 2)
        (preparedTargetPost state (some (.word (bounded 64 55))) false 20)

theorem slice_preparing_call_contract :
    ExternalCorrespondence ⟨SourceSlicePreparingCall⟩
      ⟨fun name => TargetSlicePreparingCall (.external name)⟩ Eq := by
  constructor
  · intro name arguments source target raw post states called
    cases called with
    | prior called =>
        obtain ⟨post, targetCalled, related⟩ := index_preparing_call_contract.forward _ _ _ _ _ _ states called
        exact ⟨post, .prior targetCalled, related⟩
    | count => exact ⟨_, .count target, prepared_post_correspondence states _ true 16⟩
    | refusal => exact ⟨_, .refusal target, poison_correspondence (prepared_post_correspondence states _ true 17) _⟩
    | bounds => exact ⟨_, .bounds target, prepared_post_correspondence states _ true 18⟩
    | empty => exact ⟨_, .empty target, prepared_post_correspondence states _ true 19⟩
    | unavailable => exact ⟨_, .unavailable target, prepared_post_correspondence states _ false 20⟩
  · intro name arguments source target raw post states called
    generalize encoded : encodeValues arguments = targetArguments at called
    cases called with
    | prior called =>
        rw [← encoded] at called
        obtain ⟨value, post, sourceCalled, same, related⟩ :=
          index_preparing_call_contract.backward _ _ _ _ _ _ states called
        exact ⟨value, post, .prior sourceCalled, same, related⟩
    | count | refusal | bounds | empty | unavailable =>
        have emptyArguments : arguments = [] := by
          simpa only [decode_encode_values, decodeValues] using congrArg decodeValues encoded
        subst arguments
        first
        | exact ⟨_, _, .count source, rfl, prepared_post_correspondence states _ true 16⟩
        | exact ⟨_, _, .refusal source, rfl, poison_correspondence (prepared_post_correspondence states _ true 17) _⟩
        | exact ⟨_, _, .bounds source, rfl, prepared_post_correspondence states _ true 18⟩
        | exact ⟨_, _, .empty source, rfl, prepared_post_correspondence states _ true 19⟩
        | exact ⟨_, _, .unavailable source, rfl, prepared_post_correspondence states _ false 20⟩

theorem slice_preparing_array_success_tag (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval slicePreparingInterface heap SourceSlicePreparingCall frame
      (.call "prepare" []) before ⟨.ok value, post⟩) : SourceOuterTag (.array .word) value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "prepare" before _).mp ran
  generalize chosen : ("prepare" : String) = name at called
  cases called with
  | prior called =>
      cases chosen
      exact index_preparing_array_success_tag heap frame before post value
        ((source_nullary_call_exact "prepare" before _).mpr ⟨raw, after, called, observed⟩)
  | count | refusal | bounds | empty | unavailable =>
      exact False.elim ((by decide : ("prepare" : String) ≠ "count") chosen)

theorem slice_preparing_position_success_tag (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval slicePreparingInterface heap SourceSlicePreparingCall frame
      (.call "position" []) before ⟨.ok value, post⟩) : SourceOuterTag .word value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "position" before _).mp ran
  generalize chosen : ("position" : String) = name at called
  cases called with
  | prior called =>
      cases chosen
      exact index_preparing_position_success_tag heap frame before post value
        ((source_nullary_call_exact "position" before _).mpr ⟨raw, after, called, observed⟩)
  | count | refusal | bounds | empty | unavailable =>
      exact False.elim ((by decide : ("position" : String) ≠ "count") chosen)

theorem slice_preparing_count_success_tag (heap : SourceHeapSemantics Nat)
    (frame : SourceFrame) (before post : SourceState Nat) (value : SourceValue)
    (ran : SourceExprEval slicePreparingInterface heap SourceSlicePreparingCall frame
      (.call "count" []) before ⟨.ok value, post⟩) : SourceOuterTag .word value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact "count" before _).mp ran
  generalize chosen : ("count" : String) = name at called
  cases called with
  | prior called =>
      cases called with
      | array called =>
          cases called <;> exact False.elim ((by decide : ("count" : String) ≠ "prepare") chosen)
      | position | refusal | unavailable | missing | bounds =>
          exact False.elim ((by decide : ("count" : String) ≠ "position") chosen)
  | count | refusal | bounds | empty | unavailable =>
      cases clear : before.fault <;>
        simp only [sourceObserve, sourcePoison, preparedSourcePost, clear] at observed
      all_goals cases observed
      all_goals exact .word _

theorem slice_preparing_nullary_instance (heap : SourceHeapSemantics Nat)
    (targetHeap : TargetHeapSemantics Nat) (frame : SourceFrame) (source : SourceState Nat)
    (name : String) (type : NativeType)
    (typing : inferExpr slicePreparingInterface (sourceFrameScope frame) (.call name []) = some type)
    (nonunit : type ≠ .unit) :
    StatefulChildLaws Eq slicePreparingInterface heap SourceSlicePreparingCall targetHeap TargetSlicePreparingCall
      frame source .word (.word 0) (.call name []) :=
  nullary_external_stateful_child_laws Eq slicePreparingInterface heap SourceSlicePreparingCall
    targetHeap TargetSlicePreparingCall slice_preparing_call_contract frame source name type .word (.word 0)
    typing nonunit rfl .unsignedWord

def slicePreparingExpression : Expr := .slice (.call "prepare" []) (.call "position" []) (.call "count" [])
def slicePreparingOutput : NativeLowering.Expression :=
  ⟨[.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
    .call (some (.temporary 2 .word)) (.external "position") [], .checkContext,
    .call (some (.temporary 3 .word)) (.external "count") [], .checkContext,
    .temporary 4 (.array .word) (.zero (.array .word)),
    .helper (some (.arrayData (.temporary 4 (.array .word)) .word))
      (.slice (.temporary 1 (.array .word)) (.temporary 2 .word) (.temporary 3 .word) .word),
    .checkContext, .assign (.arrayLength (.temporary 4 (.array .word))) (.temporary 3 .word)],
    .temporary 4 (.array .word), ⟨4⟩⟩

theorem slice_preparing_actual_emission :
    NativeLowering.expression? slicePreparingInterface (sourceFrameScope sourceFrame)
      slicePreparingExpression ⟨0⟩ = some slicePreparingOutput := by
  simp only [slicePreparingExpression, NativeLowering.expression?,
    NativeLowering.arguments?, inferExpr, inferExprList, lookupFunction,
    slicePreparingInterface, List.find?_cons, List.find?_nil]
  rfl

theorem slice_preparing_child_instance (source : SourceState Nat) (clear : source.fault = none) :
    StatefulChildLaws Eq slicePreparingInterface indexSourceHeap SourceSlicePreparingCall
      indexTargetHeap TargetSlicePreparingCall sourceFrame source .word (.word 0) slicePreparingExpression := by
  apply stateful_slice_child_laws Eq slicePreparingInterface indexSourceHeap SourceSlicePreparingCall
    indexTargetHeap TargetSlicePreparingCall sourceFrame source clear .word (.word 0) .unsignedWord
    (.call "prepare" []) (.call "position" []) (.call "count" [])
  · intro before _
    exact slice_preparing_nullary_instance indexSourceHeap indexTargetHeap sourceFrame before "prepare" (.array .word)
      (by simp only [inferExpr, inferExprList, lookupFunction, slicePreparingInterface]; rfl)
      (by intro impossible; cases impossible)
  · intro before _
    exact slice_preparing_nullary_instance indexSourceHeap indexTargetHeap sourceFrame before "position" .word
      (by simp only [inferExpr, inferExprList, lookupFunction, slicePreparingInterface]; rfl)
      (by intro impossible; cases impossible)
  · intro before _
    exact slice_preparing_nullary_instance indexSourceHeap indexTargetHeap sourceFrame before "count" .word
      (by simp only [inferExpr, inferExprList, lookupFunction, slicePreparingInterface]; rfl)
      (by intro impossible; cases impossible)
  · intro type typed
    have same : type = .word := by
      simp only [inferExpr, inferExprList, lookupFunction, slicePreparingInterface] at typed
      cases typed; rfl
    subst type; rfl
  · intro before post value type typed ran
    have same : type = .word := by
      simp only [inferExpr, inferExprList, lookupFunction, slicePreparingInterface] at typed
      cases typed; rfl
    subst type
    exact slice_preparing_array_success_tag indexSourceHeap sourceFrame before post value ran
  · exact slice_preparing_position_success_tag indexSourceHeap sourceFrame
  · exact slice_preparing_count_success_tag indexSourceHeap sourceFrame

def slicePreparingFinal : SourceState Nat :=
  preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) true 16

theorem slice_preparing_source_success :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.ok (.array .word (some address) (bounded 64 2)), slicePreparingFinal⟩ := by
  have arrayRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "prepare" []) preparingSource ⟨.ok (preparedSourceValue true), indexPreparingMiddle⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .prior (.array (.value preparingSource)), rfl⟩
  have positionRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "position" []) indexPreparingMiddle ⟨.ok (.word (bounded 64 0)), indexPreparingFinal⟩ :=
    (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
      ⟨_, _, .prior (.position indexPreparingMiddle), rfl⟩
  have countRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "count" []) indexPreparingFinal ⟨.ok (.word (bounded 64 2)), slicePreparingFinal⟩ :=
    (source_nullary_call_exact "count" indexPreparingFinal _).mpr
      ⟨_, _, .count indexPreparingFinal, rfl⟩
  refine .strict rfl (.cons arrayRan (.cons positionRan (.cons countRan (.nil _)))) ?_
  apply (source_slice_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" []) (.call "count" [])
    .word (some address) (some address) (bounded 64 7) (bounded 64 0) (bounded 64 2) slicePreparingFinal rfl _).mpr
  rfl

theorem slice_preparing_target_success (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .normal ∧ out.state.external = 28 ∧
      out.state.memory.cells 11 0 = some (.word 55) ∧
      TargetAtomEval slicePreparingInterface out.frame out.state slicePreparingOutput.result
        (.array .word (some address) 2) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (slice_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) slice_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) slice_preparing_source_success
  rcases checked with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

theorem slice_preparing_actual_reflection (root : List Instruction) {out : TargetBlockOutcome Nat}
    (ran : TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
      slicePreparingOutput.code targetFrame preparingTarget out) :
    ∃ sourceOut, SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource sourceOut ∧
      CheckedExpressionRelated Eq slicePreparingInterface (.word 0) slicePreparingOutput.result sourceOut out := by
  obtain ⟨sourceOut, sourceRan, checked, _, _, _⟩ := (slice_preparing_child_instance preparingSource rfl).backward
    root (targetFrame := targetFrame) slice_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) ran
  exact ⟨sourceOut, sourceRan, checked⟩


/-- The third service is reached after both earlier effects, and the helper
observes its entire post-state. The fixture reuses the existing prefix services. -/
theorem slice_preparing_source_count_step (amount : NativeWord64.Word)
    (post : SourceState Nat) (pointer : Option Address)
    (called : SourceSlicePreparingCall "count" [] indexPreparingFinal (.word amount) post)
    (clear : post.fault = none)
    (reference : (sourceSliceCall post (bounded 64 7) 1 (bounded 64 0) amount (some address)).value =
      .reference pointer) :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      (sourceObserve (sourceSliceCall post (bounded 64 7) 1 (bounded 64 0) amount (some address)).state
        (.array .word pointer amount)) := by
  have arrayRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "prepare" []) preparingSource ⟨.ok (preparedSourceValue true), indexPreparingMiddle⟩ :=
    (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .prior (.array (.value preparingSource)), rfl⟩
  have positionRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "position" []) indexPreparingMiddle ⟨.ok (.word (bounded 64 0)), indexPreparingFinal⟩ :=
    (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
      ⟨_, _, .prior (.position indexPreparingMiddle), rfl⟩
  have countRan : SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      (.call "count" []) indexPreparingFinal ⟨.ok (.word amount), post⟩ :=
    (source_nullary_call_exact "count" indexPreparingFinal _).mpr
      ⟨_, _, called, by simp only [sourceObserve, clear]⟩
  refine .strict rfl (.cons arrayRan (.cons positionRan (.cons countRan (.nil _)))) ?_
  exact (source_slice_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" []) (.call "count" [])
    .word (some address) pointer (bounded 64 7) (bounded 64 0) amount post reference _).mpr rfl

theorem slice_preparing_source_first_fault :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost preparingSource (some (.word (bounded 64 21))) true 5) .resourceFault⟩ := by
  apply SourceExprEval.strictFault rfl
  apply SourceArgumentsEval.consFault
  exact (source_nullary_call_exact "prepare" preparingSource _).mpr
    ⟨_, _, .prior (.array (.refusal preparingSource)), rfl⟩

theorem slice_preparing_target_first_fault (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 5 ∧ out.state.memory.cells 11 0 = some (.word 21) ∧
      out.frame.temporaryNames.contains 2 = false ∧ out.frame.temporaryNames.contains 3 = false ∧
      out.frame.temporaryNames.contains 4 = false := by
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary targetFrame 1 (preparedTargetValue true),
      targetPoison (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 5) .resourceFault⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.refusal preparingTarget))) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem slice_preparing_source_second_fault :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost indexPreparingMiddle (some (.word (bounded 64 34))) true 9) .resourceFault⟩ := by
  apply SourceExprEval.strictFault rfl
  refine SourceArgumentsEval.cons (middle := indexPreparingMiddle)
    (value := preparedSourceValue true) ?_ (.consFault ?_)
  · exact (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .prior (.array (.value preparingSource)), rfl⟩
  · exact (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
      ⟨_, _, .prior (.refusal indexPreparingMiddle), rfl⟩

theorem slice_preparing_target_second_fault (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 13 ∧ out.state.memory.cells 11 0 = some (.word 34) ∧
      out.frame.temporaryNames.contains 1 = true ∧ out.frame.temporaryNames.contains 2 = true ∧
      out.frame.temporaryNames.contains 3 = false ∧ out.frame.temporaryNames.contains 4 = false := by
  let middle := preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4
  let first := targetDeclareTemporary targetFrame 1 (preparedTargetValue true)
  let post := targetPoison (preparedTargetPost middle (some (.word (bounded 64 34))) true 9) .resourceFault
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary first 2 (.word 0), post⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.value preparingTarget))) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.refusal middle)) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem slice_preparing_source_third_fault :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.error .resourceFault,
        sourcePoison (preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) true 17) .resourceFault⟩ := by
  apply SourceExprEval.strictFault rfl
  refine SourceArgumentsEval.cons (middle := indexPreparingMiddle)
    (value := preparedSourceValue true)
    (out := ⟨.error .resourceFault,
      sourcePoison (preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) true 17) .resourceFault⟩) ?_ ?_
  · exact (source_nullary_call_exact "prepare" preparingSource _).mpr
      ⟨_, _, .prior (.array (.value preparingSource)), rfl⟩
  · refine SourceArgumentsEval.cons (middle := indexPreparingFinal) (value := .word (bounded 64 0)) ?_
      (.consFault ?_)
    · exact (source_nullary_call_exact "position" indexPreparingMiddle _).mpr
        ⟨_, _, .prior (.position indexPreparingMiddle), rfl⟩
    · exact (source_nullary_call_exact "count" indexPreparingFinal _).mpr
        ⟨_, _, .refusal indexPreparingFinal, rfl⟩

theorem slice_preparing_target_third_fault (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = 29 ∧ out.state.memory.cells 11 0 = some (.word 55) ∧
      out.frame.temporaryNames.contains 1 = true ∧ out.frame.temporaryNames.contains 2 = true ∧
      out.frame.temporaryNames.contains 3 = true ∧ out.frame.temporaryNames.contains 4 = false := by
  let middle := preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4
  let first := targetDeclareTemporary targetFrame 1 (preparedTargetValue true)
  let secondState := preparedTargetPost middle (some (.word (bounded 64 34))) true 8
  let second := targetDeclareTemporary first 2 (.word 0)
  let post := targetPoison (preparedTargetPost secondState (some (.word (bounded 64 55))) true 17) .resourceFault
  refine ⟨⟨.returned (.word 0), targetDeclareTemporary second 3 (.word 0), post⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.value preparingTarget))) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.position middle)) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal secondState) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem slice_preparing_source_bounds_fault :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.error .indexOutOfBounds,
        sourcePoison (preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) true 18) .indexOutOfBounds⟩ :=
  slice_preparing_source_count_step (bounded 64 8) _ none (.bounds _) rfl rfl

theorem slice_preparing_target_bounds_fault (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .indexOutOfBounds ∧
      out.state.external = 30 ∧ out.state.memory.cells 11 0 = some (.word 55) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (slice_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) slice_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) slice_preparing_source_bounds_fault
  rcases checked with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 11 0⟩

theorem slice_preparing_source_unavailable :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.error .invalidRequest,
        sourcePoison (preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) false 20) .invalidRequest⟩ :=
  slice_preparing_source_count_step (bounded 64 2) _ none (.unavailable _) rfl rfl

theorem slice_preparing_target_unavailable (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .invalidRequest ∧
      out.state.external = 32 ∧ out.state.releaseAvailable = false ∧
      out.state.memory.cells 11 0 = some (.word 55) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (slice_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) slice_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) slice_preparing_source_unavailable
  rcases checked with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.release, states.memory.1 11 0⟩

theorem slice_preparing_source_empty :
    SourceExprEval slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression preparingSource
      ⟨.ok (.array .word none (bounded 64 0)),
        preparedSourcePost indexPreparingFinal (some (.word (bounded 64 55))) true 19⟩ :=
  slice_preparing_source_count_step (bounded 64 0) _ none (.empty _) rfl rfl

theorem slice_preparing_target_empty (root : List Instruction) :
    ∃ out, TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
        slicePreparingOutput.code targetFrame preparingTarget out ∧
      out.flow = .normal ∧ out.state.external = 31 ∧
      out.state.memory.cells 11 0 = some (.word 55) ∧
      TargetAtomEval slicePreparingInterface out.frame out.state slicePreparingOutput.result (.array .word none 0) := by
  obtain ⟨out, ran, checked, _, _, _⟩ := (slice_preparing_child_instance preparingSource rfl).forward
    root (targetFrame := targetFrame) slice_preparing_actual_emission ⟨rfl, rfl, rfl⟩ preparing_initial_related
    (by intro _ live; cases live) (by intro _ _; rfl) slice_preparing_source_empty
  rcases checked with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 11 0, value⟩

/-- A slice constructs a borrowed descriptor. It does not load its pointee. -/
theorem slice_does_not_require_initialized_pointee :
    sourcePrimitive slicePreparingInterface indexSourceHeap SourceSlicePreparingCall sourceFrame
      slicePreparingExpression [.array .word (some address) (bounded 64 7), .word (bounded 64 0), .word (bounded 64 2)]
      (preparedSourcePost indexPreparingFinal none true 16)
      ⟨.ok (.array .word (some address) (bounded 64 2)), preparedSourcePost indexPreparingFinal none true 16⟩ ∧
      sourceRead (preparedSourcePost indexPreparingFinal none true 16).memory address = none := by
  refine ⟨?_, rfl⟩
  exact (source_slice_primitive_exact _ _ _ _ (.call "prepare" []) (.call "position" []) (.call "count" [])
    .word (some address) (some address) (bounded 64 7) (bounded 64 0) (bounded 64 2) _ rfl _).mpr rfl


def sliceTargetBeforeCount : TargetState Nat :=
  preparedTargetPost (preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4)
    (some (.word (bounded 64 34))) true 8

def sliceTargetFinal : TargetState Nat :=
  preparedTargetPost sliceTargetBeforeCount (some (.word (bounded 64 55))) true 16

def sliceTargetOperands (amount : BitVec 64) : TargetFrame :=
  targetDeclareTemporary
    (targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (preparedTargetValue true)) 2 (.word 0))
    3 (.word amount)

/-- Omitting the emitted length assignment retains the raw data pointer with
an empty length. This is an actual target execution with a different readout. -/
theorem omitted_slice_length_returns_zero (root : List Instruction) :
    let descriptor := targetUpdateTemporary
      (targetDeclareTemporary (sliceTargetOperands 2) 4 (.array .word none 0))
      4 (.array .word (some address) 0)
    TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
      [.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
       .call (some (.temporary 2 .word)) (.external "position") [], .checkContext,
       .call (some (.temporary 3 .word)) (.external "count") [], .checkContext,
       .temporary 4 (.array .word) (.zero (.array .word)),
       .helper (some (.arrayData (.temporary 4 (.array .word)) .word))
         (.slice (.temporary 1 (.array .word)) (.temporary 2 .word) (.temporary 3 .word) .word),
       .checkContext] targetFrame preparingTarget
      ⟨.normal, descriptor, sliceTargetFinal⟩ ∧
      TargetAtomEval slicePreparingInterface descriptor sliceTargetFinal
        slicePreparingOutput.result (.array .word (some address) 0) ∧
      (.array .word (some address) 0 : TargetValue) ≠ .array .word (some address) 2 := by
  dsimp only
  refine ⟨?_, .temporary rfl rfl, ?_⟩
  · apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.value preparingTarget))) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.position _)) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.call .nil (.count _) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.temporary rfl (TargetPureEval.zero (.emptyView .word)))
    apply TargetRun.next ((target_array_data_helper_exact (targetSliceCall sliceTargetFinal 7 1 0 2 (some address))
      rfl (fun other => target_slice_call_exact (.temporary rfl rfl) (.temporary rfl rfl) (.temporary rfl rfl) other)
      (.temporary rfl rfl) _).mpr rfl)
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    exact .nil _ _ _
  · intro same
    exact (by decide : (0 : BitVec 64) ≠ 2) (TargetValue.array.inj same).2.2

/-- Without the context check, the helper's raw default is stored and the
length assignment still runs, even though the context already carries a fault. -/
theorem omitted_slice_context_assigns_faulted_length (root : List Instruction) :
    let post := targetPoison
      (preparedTargetPost sliceTargetBeforeCount (some (.word (bounded 64 55))) true 18) .indexOutOfBounds
    let descriptor := targetUpdateTemporary
      (targetUpdateTemporary (targetDeclareTemporary (sliceTargetOperands 8) 4 (.array .word none 0))
        4 (.array .word none 0)) 4 (.array .word none 8)
    TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
      [.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
       .call (some (.temporary 2 .word)) (.external "position") [], .checkContext,
       .call (some (.temporary 3 .word)) (.external "count") [], .checkContext,
       .temporary 4 (.array .word) (.zero (.array .word)),
       .helper (some (.arrayData (.temporary 4 (.array .word)) .word))
         (.slice (.temporary 1 (.array .word)) (.temporary 2 .word) (.temporary 3 .word) .word),
       .assign (.arrayLength (.temporary 4 (.array .word))) (.temporary 3 .word)] targetFrame preparingTarget
      ⟨.normal, descriptor, post⟩ ∧ post.fault = some .indexOutOfBounds ∧
      TargetAtomEval slicePreparingInterface descriptor post slicePreparingOutput.result (.array .word none 8) := by
  dsimp only
  refine ⟨?_, rfl, .temporary rfl rfl⟩
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.value preparingTarget))) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.position _)) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.call .nil (.bounds _) (.fresh rfl))
  apply TargetRun.next (TargetInstructionEval.contextClear rfl)
  apply TargetRun.next (TargetInstructionEval.temporary rfl (TargetPureEval.zero (.emptyView .word)))
  apply TargetRun.next ((target_array_data_helper_exact
    (targetSliceCall (preparedTargetPost sliceTargetBeforeCount (some (.word (bounded 64 55))) true 18)
      7 1 0 8 (some address)) rfl
    (fun other => target_slice_call_exact (.temporary rfl rfl) (.temporary rfl rfl) (.temporary rfl rfl) other)
    (.temporary rfl rfl) _).mpr rfl)
  apply TargetRun.next (TargetInstructionEval.assign (.temporary rfl rfl) (.arrayLength (.temporary rfl rfl)))
  exact .nil _ _ _

/-- Reordering the last two services preserves this returned descriptor but
changes the visible memory. Their external effects therefore do not commute. -/
theorem reordered_slice_services_change_memory (root : List Instruction) :
    let first := preparedTargetPost preparingTarget (some (.word (bounded 64 21))) true 4
    let second := preparedTargetPost first (some (.word (bounded 64 55))) true 16
    let post := preparedTargetPost second (some (.word (bounded 64 34))) true 8
    let operands := targetDeclareTemporary
      (targetDeclareTemporary (targetDeclareTemporary targetFrame 1 (preparedTargetValue true)) 3 (.word 2))
      2 (.word 0)
    let descriptor := targetUpdateTemporary
      (targetUpdateTemporary (targetDeclareTemporary operands 4 (.array .word none 0))
        4 (.array .word (some address) 0)) 4 (.array .word (some address) 2)
    TargetRun slicePreparingInterface indexTargetHeap TargetSlicePreparingCall .word root
      [.call (some (.temporary 1 (.array .word))) (.external "prepare") [], .checkContext,
       .call (some (.temporary 3 .word)) (.external "count") [], .checkContext,
       .call (some (.temporary 2 .word)) (.external "position") [], .checkContext,
       .temporary 4 (.array .word) (.zero (.array .word)),
       .helper (some (.arrayData (.temporary 4 (.array .word)) .word))
         (.slice (.temporary 1 (.array .word)) (.temporary 2 .word) (.temporary 3 .word) .word),
       .checkContext, .assign (.arrayLength (.temporary 4 (.array .word))) (.temporary 3 .word)]
      targetFrame preparingTarget ⟨.normal, descriptor, post⟩ ∧
      TargetAtomEval slicePreparingInterface descriptor post slicePreparingOutput.result (.array .word (some address) 2) ∧
      post.external = 28 ∧ post.memory.cells 11 0 = some (.word 34) ∧
      ¬ StateRelated Eq slicePreparingFinal post := by
  dsimp only
  refine ⟨?_, .temporary rfl rfl, rfl, rfl, ?_⟩
  · apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.array (.value preparingTarget))) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.call .nil (.count _) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.call .nil (.prior (.position _)) (.fresh rfl))
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.temporary rfl (TargetPureEval.zero (.emptyView .word)))
    apply TargetRun.next ((target_array_data_helper_exact (targetSliceCall _ 7 1 0 2 (some address))
      rfl (fun other => target_slice_call_exact (.temporary rfl rfl) (.temporary rfl rfl) (.temporary rfl rfl) other)
      (.temporary rfl rfl) _).mpr rfl)
    apply TargetRun.next (TargetInstructionEval.contextClear rfl)
    apply TargetRun.next (TargetInstructionEval.assign (.temporary rfl rfl) (.arrayLength (.temporary rfl rfl)))
    exact .nil _ _ _
  · intro related
    have cell := related.memory.1 11 0
    change some (.word 34 : TargetValue) = some (.word 55) at cell
    exact (by decide : (34 : BitVec 64) ≠ 55) (TargetValue.word.inj (Option.some.inj cell))


end Mettapedia.GSLT.LanguageDef.NativeOps.ReadExpressionControls
