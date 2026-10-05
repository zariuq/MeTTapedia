import Mettapedia.GSLT.LanguageDef.NativeOpsScalarExpressionLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState
import Mettapedia.GSLT.LanguageDef.NativeOpsExternal
import Mettapedia.GSLT.LanguageDef.NativeOpsShortCircuitCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsStrictBinaryComposition

/-! Controls separating sticky context faults, retained effects and view refusal. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.RuntimeControls

open NativeWord64

private def sourceMemory : SourceMemory :=
  ⟨fun _ _ => none, fun _ => none⟩

private def targetMemory : TargetMemory :=
  ⟨fun _ _ => none, fun _ => none⟩

private def sourceState : SourceState (Bool × Nat) :=
  ⟨sourceMemory, none, true, true, (false, 0), AllocatorStats.sourceEmpty⟩

private def targetState : TargetState (Bool × Nat) :=
  ⟨targetMemory, none, true, true, (false, 0), AllocatorStats.targetEmpty⟩

theorem clear_context_normal_return :
    (targetObserve targetState (.word 7)).result = .ok (.word 7) := rfl

theorem private_default_is_not_normal_return :
    (targetObserve { targetState with fault := some .resourceFault } (.word 0)).result =
      .error .resourceFault := rfl

theorem first_fault_survives_later_division_refusal :
    (targetFinish { targetState with fault := some .resourceFault }
      (.error .divisionByZero) (.word 0)).result = .error .resourceFault := rfl

theorem reader_poison_does_not_poison_context :
    (targetObserve { targetState with external := (true, 1) } (.word 17)).result =
      .ok (.word 17) := rfl

theorem reader_poison_is_retained_after_context_refusal :
    (targetFinish { targetState with external := (true, 1) }
      (.error .lengthOverflow) (.word 0)).state.external = (true, 1) := rfl

theorem source_effects_before_resource_refusal_are_retained :
    (sourceFinish { sourceState with external := (false, 9) }
      (.error .resourceFault)).state.external = (false, 9) := rfl

theorem target_effects_before_resource_refusal_are_retained :
    (targetFinish { targetState with external := (false, 9) }
      (.error .resourceFault) (.word 0)).state.external = (false, 9) := rfl

theorem allocation_table_rehash_before_resource_refusal_is_retained :
    (targetFinish { targetState with
      allocatorStats := AllocatorStats.targetRehash ⟨8, 1, 16, 1, 3⟩ 32 }
      (.error .resourceFault) (.word 0)).state.allocatorStats = ⟨8, 1, 32, 1, 0⟩ := rfl

private def liveSource : SourceMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.word (bounded 64 13)) else none,
    fun storage => if storage = 1 then some (bounded 64 8) else none⟩

private def liveTarget : TargetMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.word 13) else none,
    fun storage => if storage = 1 then some 8 else none⟩

theorem source_allocation_before_later_refusal_is_retained :
    (sourceFinish { sourceState with memory := liveSource }
      (.error .resourceFault)).state.memory.cells 1 0 = some (.word (bounded 64 13)) := rfl

theorem target_allocation_before_later_refusal_is_retained :
    (targetFinish { targetState with memory := liveTarget }
      (.error .resourceFault) (.word 0)).state.memory.cells 1 0 = some (.word 13) := rfl

theorem live_memory_related : MemoryRelated liveSource liveTarget := by
  constructor
  · intro storage index
    change (if storage = 1 ∧ index = 0 then some (TargetValue.word 13) else none) =
      (if storage = 1 ∧ index = 0 then some (SourceValue.word (bounded 64 13)) else none).map encodeValue
    split <;> rfl
  · intro storage
    change (if storage = 1 then some (8 : BitVec 64) else none) =
      (if storage = 1 then some (bounded 64 8) else none).map encode
    split <;> rfl

/-- The two service relations are defined separately over their actual
values and states. Each has a successful and a faulting storage effect. -/
inductive SourceEffectCall : SourceCalls (Bool × Nat) where
  | value (state : SourceState (Bool × Nat)) :
      SourceEffectCall "touch" [] state (.word (bounded 64 17))
        { state with memory := liveSource, external := (true, state.external.2 + 1) }
  | refusal (state : SourceState (Bool × Nat)) :
      SourceEffectCall "touch" [] state (.word (bounded 64 99))
        (sourcePoison { state with memory := liveSource, external := (true, state.external.2 + 2) }
          .resourceFault)
  | overwrite (state : SourceState (Bool × Nat)) :
      SourceEffectCall "overwrite" [] state (.word (bounded 64 21))
        { state with
          memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21)), external := (true, state.external.2 + 4) }
  | notify (state : SourceState (Bool × Nat)) :
      SourceEffectCall "notify" [] state .unit
        { state with external := (true, state.external.2 + 8) }
  | consume (state : SourceState (Bool × Nat)) (first last : NativeWord64.Word) :
      SourceEffectCall "consume" [.word first, .word last] state (.word first)
        { state with external := (true, state.external.2 + 16) }
  | sink (state : SourceState (Bool × Nat)) (first last : NativeWord64.Word) :
      SourceEffectCall "sink" [.word first, .word last] state .unit
        { state with external := (true, state.external.2 + 32) }

inductive TargetEffectCall : TargetCalls (Bool × Nat) where
  | value (state : TargetState (Bool × Nat)) :
      TargetEffectCall (.external "touch") [] state (.word 17)
        { state with memory := liveTarget, external := (true, state.external.2 + 1) }
  | refusal (state : TargetState (Bool × Nat)) :
      TargetEffectCall (.external "touch") [] state (.word 99)
        (targetPoison { state with memory := liveTarget, external := (true, state.external.2 + 2) }
          .resourceFault)
  | overwrite (state : TargetState (Bool × Nat)) :
      TargetEffectCall (.external "overwrite") [] state (.word 21)
        { state with
          memory := targetStoreCell liveTarget 1 0 (.word 21), external := (true, state.external.2 + 4) }
  | notify (state : TargetState (Bool × Nat)) :
      TargetEffectCall (.external "notify") [] state .unit
        { state with external := (true, state.external.2 + 8) }
  | consume (state : TargetState (Bool × Nat)) (first last : BitVec 64) :
      TargetEffectCall (.external "consume") [.word first, .word last] state (.word first)
        { state with external := (true, state.external.2 + 16) }
  | sink (state : TargetState (Bool × Nat)) (first last : BitVec 64) :
      TargetEffectCall (.external "sink") [.word first, .word last] state .unit
        { state with external := (true, state.external.2 + 32) }

theorem effect_call_post_related {source : SourceState (Bool × Nat)}
    {target : TargetState (Bool × Nat)} (states : StateRelated Eq source target) (increment : Nat) :
    StateRelated Eq
      { source with memory := liveSource, external := (true, source.external.2 + increment) }
      { target with memory := liveTarget, external := (true, target.external.2 + increment) } := by
  exact ⟨live_memory_related, states.fault, states.allocator, states.release,
    congrArg (fun world : Bool × Nat => (true, world.2 + increment)) states.external,
    states.allocatorStats⟩

theorem overwrite_call_post_related {source : SourceState (Bool × Nat)}
    {target : TargetState (Bool × Nat)} (states : StateRelated Eq source target) :
    StateRelated Eq
      { source with
          memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21)), external := (true, source.external.2 + 4) }
      { target with
          memory := targetStoreCell liveTarget 1 0 (.word 21), external := (true, target.external.2 + 4) } := by
  exact ⟨store_cell_correspondence liveSource liveTarget live_memory_related 1 0 _,
    states.fault, states.allocator, states.release,
    congrArg (fun world : Bool × Nat => (true, world.2 + 4)) states.external, states.allocatorStats⟩

theorem notify_call_post_related {source : SourceState (Bool × Nat)}
    {target : TargetState (Bool × Nat)} (states : StateRelated Eq source target) :
    StateRelated Eq { source with external := (true, source.external.2 + 8) }
      { target with external := (true, target.external.2 + 8) } := by
  exact ⟨states.memory, states.fault, states.allocator, states.release,
    congrArg (fun world : Bool × Nat => (true, world.2 + 8)) states.external, states.allocatorStats⟩

theorem effect_world_post_related {source : SourceState (Bool × Nat)}
    {target : TargetState (Bool × Nat)} (states : StateRelated Eq source target) (increment : Nat) :
    StateRelated Eq { source with external := (true, source.external.2 + increment) }
      { target with external := (true, target.external.2 + increment) } := by
  exact ⟨states.memory, states.fault, states.allocator, states.release,
    congrArg (fun world : Bool × Nat => (true, world.2 + increment)) states.external, states.allocatorStats⟩

theorem independent_effect_call_contract :
    ExternalCorrespondence ⟨SourceEffectCall⟩
      ⟨fun name => TargetEffectCall (.external name)⟩ Eq := by
  constructor
  · intro name arguments source target raw post states called
    cases called with
    | value => exact ⟨_, .value target, effect_call_post_related states 1⟩
    | refusal => exact ⟨_, .refusal target, poison_correspondence (effect_call_post_related states 2) _⟩
    | overwrite => exact ⟨_, .overwrite target, overwrite_call_post_related states⟩
    | notify => exact ⟨_, .notify target, notify_call_post_related states⟩
    | consume _ first last => exact ⟨_, .consume target (encode first) (encode last), effect_world_post_related states 16⟩
    | sink _ first last => exact ⟨_, .sink target (encode first) (encode last), effect_world_post_related states 32⟩
  · intro name arguments source target raw post states called
    generalize encoded : encodeValues arguments = targetArguments at called
    cases called with
    | value =>
        have empty : arguments = [] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues] using decoded
        subst arguments
        exact ⟨_, _, .value source, rfl, effect_call_post_related states 1⟩
    | refusal =>
        have empty : arguments = [] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues] using decoded
        subst arguments
        exact ⟨_, _, .refusal source, rfl, poison_correspondence (effect_call_post_related states 2) _⟩
    | overwrite =>
        have empty : arguments = [] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues] using decoded
        subst arguments
        exact ⟨_, _, .overwrite source, rfl, overwrite_call_post_related states⟩
    | notify =>
        have empty : arguments = [] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues] using decoded
        subst arguments
        exact ⟨_, _, .notify source, rfl, notify_call_post_related states⟩
    | consume _ first last =>
        have actual : arguments = [.word first.toFin, .word last.toFin] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues, decodeValue] using decoded
        subst arguments
        refine ⟨_, _, .consume source first.toFin last.toFin, ?_, effect_world_post_related states 16⟩
        simp only [encodeValue, encode, BitVec.ofFin_toFin]
    | sink _ first last =>
        have actual : arguments = [.word first.toFin, .word last.toFin] := by
          have decoded := congrArg decodeValues encoded
          simpa only [decode_encode_values, decodeValues, decodeValue] using decoded
        subst arguments
        exact ⟨_, _, .sink source first.toFin last.toFin, rfl, effect_world_post_related states 32⟩

def effectCallInterface (type : NativeType) : Interface :=
  ⟨[], [], [], [⟨⟨"touch", [], type⟩, "touch", .effect, none⟩]⟩

theorem effect_call_word_actual_lowering (scope : Scope) (supply : NativeIR.Supply) :
    NativeLowering.expression? (effectCallInterface .word) scope (.call "touch" []) supply =
      some ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external "touch") [],
        .checkContext], .temporary (NativeIR.fresh supply).1 .word, (NativeIR.fresh supply).2⟩ := by
  simp only [NativeLowering.expression?, inferExpr, inferExprList, NativeLowering.arguments?,
    lookupFunction, effectCallInterface, List.find?_cons, List.find?_nil, List.any_nil]
  rfl

theorem effect_call_source_value (interface : Interface)
    (heap : SourceHeapSemantics (Bool × Nat)) (frame : SourceFrame) :
    SourceExprEval interface heap SourceEffectCall frame (.call "touch" []) sourceState
      ⟨.ok (.word (bounded 64 17)),
        { sourceState with memory := liveSource, external := (true, 1) }⟩ := by
  exact (source_nullary_call_exact "touch" sourceState _).mpr
    ⟨_, _, .value sourceState, rfl⟩

theorem effect_call_source_refusal (interface : Interface)
    (heap : SourceHeapSemantics (Bool × Nat)) (frame : SourceFrame) :
    SourceExprEval interface heap SourceEffectCall frame (.call "touch" []) sourceState
      ⟨.error .resourceFault,
        { sourceState with memory := liveSource, external := (true, 2), fault := some .resourceFault }⟩ := by
  exact (source_nullary_call_exact "touch" sourceState _).mpr
    ⟨_, _, .refusal sourceState, rfl⟩

theorem effect_call_checked_target_exact (interface : Interface)
    (heap : TargetHeapSemantics (Bool × Nat)) (frame : TargetFrame) (identity : Nat)
    (unused : frame.temporaryNames.contains identity = false)
    (root : List NativeIR.Instruction) (out : TargetBlockOutcome (Bool × Nat)) :
    TargetRun interface heap TargetEffectCall .word root
      [.call (some (.temporary identity .word)) (.external "touch") [], .checkContext]
      frame targetState out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity (.word 17),
        { targetState with memory := liveTarget, external := (true, 1) }⟩ ∨
      out = ⟨.returned (.word 0), targetDeclareTemporary frame identity (.word 99),
        { targetState with memory := liveTarget, external := (true, 2), fault := some .resourceFault }⟩ := by
  rw [target_call_temporary_checked_fragment_exact unused TargetAtomsEval.nil TargetZero.unsignedWord]
  constructor
  · rintro ⟨raw, post, called, same⟩
    generalize named : NativeIR.CallTarget.external "touch" = targetName at called
    cases called with
    | value => exact .inl same
    | refusal => exact .inr same
    | overwrite =>
        exact False.elim ((by decide : ("touch" : String) ≠ "overwrite")
          (NativeIR.CallTarget.external.inj named))
    | notify =>
        exact False.elim ((by decide : ("touch" : String) ≠ "notify")
          (NativeIR.CallTarget.external.inj named))

  · intro same
    rcases same with good | failed
    · exact ⟨_, _, .value targetState, good⟩
    · exact ⟨_, _, .refusal targetState, failed⟩

theorem effect_call_refusal_retains_live_cell :
    (sourceObserve
      (sourcePoison { sourceState with memory := liveSource, external := (true, 2) } .resourceFault)
      (.word (bounded 64 99))).state.memory.cells 1 0 = some (.word (bounded 64 13)) := rfl

theorem effect_call_refusal_cannot_roll_back :
    ¬ StateRelated Eq
      (sourcePoison { sourceState with memory := liveSource, external := (true, 2) } .resourceFault)
      (targetPoison targetState .resourceFault) := by
  intro states
  have cell := states.memory.1 1 0
  cases cell

theorem effect_call_refusal_raw_is_not_observed :
    (targetObserve
      (targetPoison { targetState with memory := liveTarget, external := (true, 2) } .resourceFault)
      (.word 99)).result ≠ .ok (.word 99) := by
  intro same
  cases same

theorem unit_signature_does_not_establish_call_abi (scope : Scope) :
    inferExpr (effectCallInterface .unit) scope (.call "touch" []) = some .unit ∧
    SourceEffectCall "touch" [] sourceState (.word (bounded 64 17))
      { sourceState with memory := liveSource, external := (true, 1) } ∧
    SourceValue.word (bounded 64 17) ≠ .unit := by
  refine ⟨?_, .value sourceState, ?_⟩
  · simp only [inferExpr, inferExprList, lookupFunction, effectCallInterface,
      List.find?_cons, List.find?_nil]
    rfl
  · intro same; cases same

def effectCallFrame : TargetFrame := ⟨1, 1, [⟨"outer", .word, 0⟩], [], fun _ => none⟩

/-- Without the emitted context check, an actual later aliased write is
possible after the service has already faulted. The fault remains sticky. -/
theorem omitted_context_check_executes_later_write (interface : Interface)
    (heap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) :
    TargetRun interface heap TargetEffectCall .word root
      [.call (some (.temporary 1 .word)) (.external "touch") [],
       .write (.localAddress "outer" .word) (.word 21)] effectCallFrame targetState
      ⟨.normal, targetDeclareTemporary effectCallFrame 1 (.word 99),
        { targetState with
          memory := targetStoreCell liveTarget 1 0 (.word 21), external := (true, 2), fault := some .resourceFault }⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal targetState) (.fresh rfl))
  exact TargetRun.next (TargetInstructionEval.write
    (address := ⟨1, 0, []⟩)
    (memory := targetStoreCell liveTarget 1 0 (.word 21))
    (.localAddress rfl) (.word 21) rfl) (.nil _ _ _)

theorem emitted_context_check_stops_later_write (interface : Interface)
    (heap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) :
    TargetRun interface heap TargetEffectCall .word root
      [.call (some (.temporary 1 .word)) (.external "touch") [], .checkContext,
       .write (.localAddress "outer" .word) (.word 21)] effectCallFrame targetState
      ⟨.returned (.word 0), targetDeclareTemporary effectCallFrame 1 (.word 99),
        { targetState with
          memory := liveTarget,
          external := (true, 2), fault := some .resourceFault }⟩ := by
  apply TargetRun.next (TargetInstructionEval.call .nil (.refusal targetState) (.fresh rfl))
  exact .return (.contextFault rfl .unsignedWord)

theorem context_check_omission_changes_live_cell :
    (targetStoreCell liveTarget 1 0 (.word 21)).cells 1 0 ≠ liveTarget.cells 1 0 := by
  intro same
  change some (TargetValue.word 21) = some (.word 13) at same
  have values : (21 : BitVec 64) = 13 := TargetValue.word.inj (Option.some.inj same)
  have numbers := congrArg BitVec.toNat values
  contradiction

theorem unit_effect_call_actual_lowering (scope : Scope) (supply : NativeIR.Supply) :
    NativeLowering.expression? (effectCallInterface .unit) scope (.call "touch" []) supply =
      some ⟨[.call none (.external "touch") [], .checkContext], .unit, supply⟩ := by
  simp only [NativeLowering.expression?, inferExpr, inferExprList, NativeLowering.arguments?,
    lookupFunction, effectCallInterface, List.find?_cons, List.find?_nil, List.any_nil]
  rfl

theorem discarded_nonunit_service_actually_runs (interface : Interface)
    (heap : TargetHeapSemantics (Bool × Nat)) (frame : TargetFrame)
    (root : List NativeIR.Instruction) :
    TargetRun interface heap TargetEffectCall .word root
      [.call none (.external "touch") [], .checkContext] frame targetState
      ⟨.normal, frame, { targetState with memory := liveTarget, external := (true, 1) }⟩ := by
  exact (target_call_discard_checked_fragment_exact TargetAtomsEval.nil TargetZero.unsignedWord root _).mpr
    ⟨.word 17, _, .value targetState, rfl⟩

theorem discarded_nonunit_service_observation_fails :
    ¬ OutcomeRelated Eq
      (sourceObserve { sourceState with memory := liveSource, external := (true, 1) }
        (.word (bounded 64 17)))
      (targetObserve { targetState with memory := liveTarget, external := (true, 1) } .unit) := by
  intro related
  have same := related.result
  cases same

/-- The ABI is proved from the independently defined service clauses. -/
theorem notify_call_unit {name : String} {arguments : List SourceValue}
    {source post : SourceState (Bool × Nat)} {raw : SourceValue}
    (called : SourceEffectCall name arguments source raw post) (named : name = "notify") :
    raw = .unit := by
  cases called with
  | value | refusal =>
      exact False.elim ((by decide : ("touch" : String) ≠ "notify") named)
  | overwrite =>
      exact False.elim ((by decide : ("overwrite" : String) ≠ "notify") named)
  | notify => rfl
  | consume _ _ => exact False.elim ((by decide : ("consume" : String) ≠ "notify") named)
  | sink _ _ => exact False.elim ((by decide : ("sink" : String) ≠ "notify") named)

def effectArgumentsInterface : Interface :=
  ⟨[], [], [],
    [⟨⟨"touch", [], .word⟩, "touch", .effect, none⟩,
     ⟨⟨"notify", [], .unit⟩, "notify", .effect, none⟩,
     ⟨⟨"overwrite", [], .word⟩, "overwrite", .effect, none⟩]⟩

def effectArguments : List Expr :=
  [.call "touch" [], .call "notify" [], .call "overwrite" []]

def effectArgumentOutput (supply : NativeIR.Supply) : NativeLowering.Arguments :=
  ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external "touch") [],
      .checkContext, .call none (.external "notify") [], .checkContext,
      .call (some (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word))
        (.external "overwrite") [], .checkContext],
    [.temporary (NativeIR.fresh supply).1 .word, .unit,
      .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word],
    (NativeIR.fresh (NativeIR.fresh supply).2).2⟩

theorem effect_arguments_actual_lowering (scope : Scope) (supply : NativeIR.Supply) :
    NativeLowering.arguments? effectArgumentsInterface scope effectArguments supply =
      some (effectArgumentOutput supply) := by
  simp only [effectArguments, effectArgumentsInterface, effectArgumentOutput, NativeLowering.arguments?,
    NativeLowering.expression?, inferExpr, inferExprList, lookupFunction]
  rfl

theorem effect_arguments_child_instances
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) :
    ∀ expression ∈ effectArguments, ∀ source, source.fault = none →
      StatefulChildLaws Eq effectArgumentsInterface sourceHeap SourceEffectCall targetHeap
        TargetEffectCall frame source .word (.word 0) expression := by
  intro expression member source _
  simp only [effectArguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact nullary_external_stateful_child_laws Eq effectArgumentsInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source "touch" .word .word
      (.word 0) (by simp only [effectArgumentsInterface, inferExpr, inferExprList, lookupFunction]; rfl) (by intro same; cases same) rfl .unsignedWord
  · exact nullary_unit_external_stateful_child_laws Eq effectArgumentsInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source "notify" .word
      (.word 0) (by simp only [effectArgumentsInterface, inferExpr, inferExprList, lookupFunction]; rfl) rfl (fun _ _ called => notify_call_unit called rfl) .unsignedWord
  · exact nullary_external_stateful_child_laws Eq effectArgumentsInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source "overwrite" .word .word
      (.word 0) (by simp only [effectArgumentsInterface, inferExpr, inferExprList, lookupFunction]; rfl) (by intro same; cases same) rfl .unsignedWord

private def effectSourceFrame : SourceFrame := ⟨1, 1, [⟨"outer", .word, 0⟩]⟩
private def argumentSource : SourceState (Bool × Nat) := { sourceState with memory := liveSource }
private def argumentTarget : TargetState (Bool × Nat) := { targetState with memory := liveTarget }
private def argumentPost : SourceState (Bool × Nat) :=
  { argumentSource with memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21)), external := (true, 13) }

theorem effect_arguments_initial_related : StateRelated Eq argumentSource argumentTarget :=
  ⟨live_memory_related, rfl, rfl, rfl, rfl, AllocatorStats.empty_related⟩

theorem effect_arguments_source_success (heap : SourceHeapSemantics (Bool × Nat)) :
    SourceArgumentsEval effectArgumentsInterface heap SourceEffectCall effectSourceFrame
      effectArguments argumentSource ⟨.ok [.word (bounded 64 17), .unit, .word (bounded 64 21)],
        argumentPost⟩ := by
  let first : SourceState (Bool × Nat) :=
    { argumentSource with memory := liveSource, external := (true, 1) }
  let second : SourceState (Bool × Nat) := { first with external := (true, 9) }
  have firstRun : SourceExprEval effectArgumentsInterface heap SourceEffectCall effectSourceFrame
      (.call "touch" []) argumentSource ⟨.ok (.word (bounded 64 17)), first⟩ :=
    (source_nullary_call_exact "touch" argumentSource _).mpr ⟨_, _, .value argumentSource, rfl⟩
  have secondRun : SourceExprEval effectArgumentsInterface heap SourceEffectCall effectSourceFrame
      (.call "notify" []) first ⟨.ok .unit, second⟩ :=
    (source_nullary_call_exact "notify" first _).mpr ⟨_, _, .notify first, rfl⟩
  have thirdRun : SourceExprEval effectArgumentsInterface heap SourceEffectCall effectSourceFrame
      (.call "overwrite" []) second ⟨.ok (.word (bounded 64 21)), argumentPost⟩ :=
    (source_nullary_call_exact "overwrite" second _).mpr ⟨_, _, .overwrite second, rfl⟩
  exact .cons firstRun (.cons secondRun (.cons thirdRun (.nil argumentPost)))

/-- The first value is 17, the unit service consumes no result slot, the last
value is 21, and the final local cell is 21. All three external effects remain. -/
theorem effect_arguments_target_success (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun effectArgumentsInterface targetHeap TargetEffectCall .word root
        (effectArgumentOutput ⟨0⟩).code effectCallFrame argumentTarget out ∧
      out.flow = .normal ∧ out.state.external = (true, 13) ∧
      out.state.memory.cells 1 0 = some (.word 21) ∧
      TargetAtomsEval effectArgumentsInterface out.frame out.state
        (effectArgumentOutput ⟨0⟩).results [.word 17, .unit, .word 21] ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ := stateful_arguments_forward Eq
    effectArgumentsInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall effectSourceFrame
    .word (.word 0) effectArguments (effect_arguments_child_instances sourceHeap targetHeap effectSourceFrame)
    root (targetFrame := effectCallFrame) rfl (effect_arguments_actual_lowering _ ⟨0⟩) ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related
    (by intro identity live; cases live) (by intro identity _; rfl)
    (effect_arguments_source_success sourceHeap)
  rcases related with ⟨states, _, normal, values⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 1 0, values, protection⟩

theorem effect_arguments_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun effectArgumentsInterface targetHeap TargetEffectCall .word root
      (effectArgumentOutput ⟨0⟩).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceArgumentsEval effectArgumentsInterface sourceHeap SourceEffectCall effectSourceFrame
        effectArguments argumentSource sourceOut ∧
      CheckedArgumentsRelated Eq effectArgumentsInterface (.word 0)
        (effectArgumentOutput ⟨0⟩).results sourceOut out := by
  obtain ⟨sourceOut, sourceRun, related, _, _, _⟩ := stateful_arguments_reflection Eq
    effectArgumentsInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall effectSourceFrame
    .word (.word 0) effectArguments (effect_arguments_child_instances sourceHeap targetHeap effectSourceFrame)
    root (targetFrame := effectCallFrame) rfl (effect_arguments_actual_lowering _ ⟨0⟩) ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related
    (by intro identity live; cases live) (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRun, related⟩

private def argumentRefusal : SourceState (Bool × Nat) :=
  { argumentSource with external := (true, 2), fault := some .resourceFault }

theorem effect_arguments_source_first_fault (heap : SourceHeapSemantics (Bool × Nat)) :
    SourceArgumentsEval effectArgumentsInterface heap SourceEffectCall effectSourceFrame
      effectArguments argumentSource ⟨.error .resourceFault, argumentRefusal⟩ := by
  exact .consFault ((source_nullary_call_exact "touch" argumentSource _).mpr
    ⟨_, _, .refusal argumentSource, rfl⟩)

/-- The actual compiled guard stops before both later services, retaining
the first refusal's storage and external effect. -/
theorem effect_arguments_target_first_fault (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) :
    ∃ out,
      TargetRun effectArgumentsInterface targetHeap TargetEffectCall .word root
        (effectArgumentOutput ⟨0⟩).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = (true, 2) ∧ out.state.memory.cells 1 0 = some (.word 13) := by
  obtain ⟨out, ran, related, _, _, _⟩ := stateful_arguments_forward Eq
    effectArgumentsInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall effectSourceFrame
    .word (.word 0) effectArguments (effect_arguments_child_instances sourceHeap targetHeap effectSourceFrame)
    root (targetFrame := effectCallFrame) rfl (effect_arguments_actual_lowering _ ⟨0⟩) ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related
    (by intro identity live; cases live) (by intro identity _; rfl)
    (effect_arguments_source_first_fault sourceHeap)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0⟩

/-- Fixed-state scalar evidence cannot be used to hide a service effect. -/
theorem effectful_child_is_not_fixed_state
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat)) :
    ¬ ShortCircuitChildLaws Eq effectArgumentsInterface sourceHeap SourceEffectCall targetHeap
      TargetEffectCall effectSourceFrame argumentSource .word (.word 0) (.call "touch" []) := by
  intro laws
  have ran : SourceExprEval effectArgumentsInterface sourceHeap SourceEffectCall effectSourceFrame
      (.call "touch" []) argumentSource
      ⟨.ok (.word (bounded 64 17)), { argumentSource with external := (true, 1) }⟩ :=
    (source_nullary_call_exact "touch" argumentSource _).mpr ⟨_, _, .value argumentSource, rfl⟩
  have same := laws.sourceState ran
  have counted := congrArg (fun state : SourceState (Bool × Nat) => state.external.2) same
  change (1 : Nat) = 0 at counted
  cases counted

/-- A real effectful unit service consumes no result identity, so the old
strict-growth child profile cannot describe its actual emission. -/
theorem unit_child_supply_is_not_strict
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) :
    ¬ ShortCircuitChildLaws Eq effectArgumentsInterface sourceHeap SourceEffectCall targetHeap
      TargetEffectCall frame source .word (.word 0) (.call "notify" []) := by
  intro laws
  have compiled : NativeLowering.expression? effectArgumentsInterface (sourceFrameScope frame)
      (.call "notify" []) ⟨0⟩ = some ⟨[.call none (.external "notify") [], .checkContext], .unit, ⟨0⟩⟩ := by
    simp only [effectArgumentsInterface, NativeLowering.expression?, NativeLowering.arguments?,
      inferExpr, inferExprList, lookupFunction]
    rfl
  exact (Nat.lt_irrefl 0) (laws.bounds compiled).1


def collectingInterface : Interface :=
  { effectArgumentsInterface with externals :=
    effectArgumentsInterface.externals ++
      [⟨⟨"consume", [⟨"first", .word⟩, ⟨"last", .word⟩], .word⟩,
          "consume", .effect, none⟩,
       ⟨⟨"sink", [⟨"first", .word⟩, ⟨"last", .word⟩], .unit⟩,
          "sink", .effect, none⟩] }

def collectingArguments : List Expr := [.call "touch" [], .call "overwrite" []]

def collectingName (unit : Bool) : String := if unit then "sink" else "consume"

def collectingValue (unit : Bool) : SourceValue :=
  if unit then .unit else .word (bounded 64 17)

def collectingOperands (supply : NativeIR.Supply) : NativeLowering.Arguments :=
  ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external "touch") [],
      .checkContext,
      .call (some (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word))
        (.external "overwrite") [], .checkContext],
    [.temporary (NativeIR.fresh supply).1 .word,
      .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word],
    (NativeIR.fresh (NativeIR.fresh supply).2).2⟩

def collectingOutput (supply : NativeIR.Supply) (unit : Bool) : NativeLowering.Expression :=
  let operands := collectingOperands supply
  if unit then
    ⟨operands.code ++ [.call none (.external "sink") operands.results, .checkContext],
      .unit, operands.supply⟩
  else
    ⟨operands.code ++
      [.call (some (.temporary (NativeIR.fresh operands.supply).1 .word))
        (.external "consume") operands.results, .checkContext],
      .temporary (NativeIR.fresh operands.supply).1 .word, (NativeIR.fresh operands.supply).2⟩

private def collectingAfterArguments : SourceState (Bool × Nat) :=
  { argumentSource with
    memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21)), external := (true, 5) }

private def collectingPost (unit : Bool) : SourceState (Bool × Nat) :=
  { collectingAfterArguments with external := (true, if unit then 37 else 21) }

theorem collecting_call_actual_lowering (scope : Scope) (supply : NativeIR.Supply)
    (unit : Bool) :
    NativeLowering.expression? collectingInterface scope
      (.call (collectingName unit) collectingArguments) supply =
        some (collectingOutput supply unit) := by
  cases unit <;>
    simp only [collectingInterface, effectArgumentsInterface, collectingArguments, collectingName,
      collectingOutput, collectingOperands, NativeLowering.expression?, NativeLowering.arguments?,
      inferExpr, inferExprList, lookupFunction] <;> rfl

theorem collecting_arguments_source_success (heap : SourceHeapSemantics (Bool × Nat)) :
    SourceArgumentsEval collectingInterface heap SourceEffectCall effectSourceFrame
      collectingArguments argumentSource
      ⟨.ok [.word (bounded 64 17), .word (bounded 64 21)], collectingAfterArguments⟩ := by
  let first : SourceState (Bool × Nat) := { argumentSource with external := (true, 1) }
  have firstRun : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.call "touch" []) argumentSource ⟨.ok (.word (bounded 64 17)), first⟩ :=
    (source_nullary_call_exact "touch" argumentSource _).mpr ⟨_, _, .value argumentSource, rfl⟩
  have lastRun : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.call "overwrite" []) first
      ⟨.ok (.word (bounded 64 21)), collectingAfterArguments⟩ :=
    (source_nullary_call_exact "overwrite" first _).mpr ⟨_, _, .overwrite first, rfl⟩
  exact .cons firstRun (.cons lastRun (.nil collectingAfterArguments))

theorem collecting_call_source_success (heap : SourceHeapSemantics (Bool × Nat)) (unit : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.call (collectingName unit) collectingArguments) argumentSource
      ⟨.ok (collectingValue unit), collectingPost unit⟩ := by
  apply (source_call_expression_exact (collectingName unit) collectingArguments argumentSource _).mpr
  apply Or.inl
  refine ⟨_, collectingAfterArguments, collectingValue unit, collectingPost unit,
    collecting_arguments_source_success heap, ?_, ?_⟩
  · cases unit
    · exact .consume collectingAfterArguments (bounded 64 17) (bounded 64 21)
    · exact .sink collectingAfterArguments (bounded 64 17) (bounded 64 21)
  · cases unit <;> rfl

theorem collecting_arguments_child_instances
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) :
    ∀ expression ∈ collectingArguments, ∀ source, source.fault = none →
      StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap
        TargetEffectCall frame source .word (.word 0) expression := by
  intro expression member source _
  simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact nullary_external_stateful_child_laws Eq collectingInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source "touch" .word .word
      (.word 0) (by simp only [collectingInterface, effectArgumentsInterface, inferExpr,
        inferExprList, lookupFunction]; rfl) (by intro same; cases same) rfl .unsignedWord
  · exact nullary_external_stateful_child_laws Eq collectingInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source "overwrite" .word .word
      (.word 0) (by simp only [collectingInterface, effectArgumentsInterface, inferExpr,
        inferExprList, lookupFunction]; rfl) (by intro same; cases same) rfl .unsignedWord

theorem sink_call_unit {name : String} {arguments : List SourceValue}
    {source post : SourceState (Bool × Nat)} {raw : SourceValue}
    (called : SourceEffectCall name arguments source raw post) (named : name = "sink") :
    raw = .unit := by
  cases called with
  | value | refusal => exact False.elim ((by decide : ("touch" : String) ≠ "sink") named)
  | overwrite => exact False.elim ((by decide : ("overwrite" : String) ≠ "sink") named)
  | notify => exact False.elim ((by decide : ("notify" : String) ≠ "sink") named)
  | consume _ _ => exact False.elim ((by decide : ("consume" : String) ≠ "sink") named)
  | sink _ _ => rfl

theorem collecting_call_child_instance
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (unit : Bool) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap
      TargetEffectCall frame source .word (.word 0)
      (.call (collectingName unit) collectingArguments) := by
  cases unit
  · exact external_nonunit_call_stateful_child_laws Eq collectingInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source clear "consume"
      collectingArguments .word .word (.word 0)
      (by simp only [collectingInterface, effectArgumentsInterface, collectingArguments, inferExpr,
        inferExprList, lookupFunction]; rfl) (by intro same; cases same) rfl
      (collecting_arguments_child_instances sourceHeap targetHeap frame) .unsignedWord
  · exact external_unit_call_stateful_child_laws Eq collectingInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall independent_effect_call_contract frame source clear "sink"
      collectingArguments .word (.word 0)
      (by simp only [collectingInterface, effectArgumentsInterface, collectingArguments, inferExpr,
        inferExprList, lookupFunction]; rfl) rfl
      (collecting_arguments_child_instances sourceHeap targetHeap frame)
      (fun _ _ _ _ called => sink_call_unit called rfl) .unsignedWord

/-- Both return conventions preserve the saved first argument after the later
argument overwrites the aliased source cell. All three service effects remain. -/
theorem collecting_call_target_success (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (unit : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (collectingOutput ⟨0⟩ unit).code effectCallFrame argumentTarget out ∧
      out.flow = .normal ∧ out.state.external = (true, if unit then 37 else 21) ∧
      out.state.memory.cells 1 0 = some (.word 21) ∧
      TargetAtomEval collectingInterface out.frame out.state
        (collectingOutput ⟨0⟩ unit).result (encodeValue (collectingValue unit)) ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ :=
    (collecting_call_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl unit).forward
      root (targetFrame := effectCallFrame) (collecting_call_actual_lowering _ ⟨0⟩ unit) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (collecting_call_source_success sourceHeap unit)
  rcases related with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 1 0, value, protection⟩

theorem collecting_call_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (unit : Bool) {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun collectingInterface targetHeap TargetEffectCall .word root
      (collectingOutput ⟨0⟩ unit).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
        (.call (collectingName unit) collectingArguments) argumentSource sourceOut ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0)
        (collectingOutput ⟨0⟩ unit).result sourceOut out := by
  obtain ⟨sourceOut, sourceRun, related, _, _, _⟩ :=
    (collecting_call_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl unit).backward
      root (targetFrame := effectCallFrame) (collecting_call_actual_lowering _ ⟨0⟩ unit) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRun, related⟩

theorem collecting_call_source_first_fault (heap : SourceHeapSemantics (Bool × Nat)) (unit : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.call (collectingName unit) collectingArguments) argumentSource
      ⟨.error .resourceFault, argumentRefusal⟩ := by
  apply (source_call_expression_exact (collectingName unit) collectingArguments argumentSource _).mpr
  refine Or.inr ⟨.resourceFault, argumentRefusal, ?_, rfl⟩
  exact .consFault ((source_nullary_call_exact "touch" argumentSource _).mpr
    ⟨_, _, .refusal argumentSource, rfl⟩)

/-- The first argument's fault prevents both the overwrite and the enclosing
service, under either result convention. Its complete post-state is retained. -/
theorem collecting_call_target_first_fault (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (unit : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (collectingOutput ⟨0⟩ unit).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = (true, 2) ∧ out.state.memory.cells 1 0 = some (.word 13) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (collecting_call_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl unit).forward
      root (targetFrame := effectCallFrame) (collecting_call_actual_lowering _ ⟨0⟩ unit) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (collecting_call_source_first_fault sourceHeap unit)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0⟩

theorem collecting_call_saved_value_differs_from_final_cell :
    collectingValue false ≠ .word (bounded 64 21) := by
  intro same
  have numbers := congrArg Fin.val (SourceValue.word.inj same)
  change (17 : Nat) = 21 at numbers
  contradiction

theorem collecting_call_unit_has_no_result_slot :
    (collectingOutput ⟨0⟩ true).supply.next = 2 ∧
      (collectingOutput ⟨0⟩ false).supply.next = 3 := ⟨rfl, rfl⟩


/-- The scalar operation observes two saved values after their services have
changed shared storage. The outer conversion exercises unary composition. -/
def effectScalarExpr (narrow : Bool) : Expr :=
  let sum := Expr.binary (.word .add) (.call "touch" []) (.call "overwrite" [])
  if narrow then .unary .toByte sum else sum

def effectScalarValue (narrow : Bool) : SourceValue :=
  if narrow then .byte (bounded 8 38) else .word (bounded 64 38)

def effectScalarOutput (supply : NativeIR.Supply) (narrow : Bool) : NativeLowering.Expression :=
  let operands := collectingOperands supply
  let summed := NativeLowering.prependCode operands.code
    (NativeLowering.pureTemporary operands.supply .word
      (.binary (.word .add) (.temporary (NativeIR.fresh supply).1 .word)
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word)))
  if narrow then NativeLowering.prependCode summed.code
    (NativeLowering.pureTemporary summed.supply .byte (.unary .toByte summed.result))
  else summed

theorem effect_scalar_actual_lowering (scope : Scope) (supply : NativeIR.Supply) (narrow : Bool) :
    NativeLowering.expression? collectingInterface scope (effectScalarExpr narrow) supply =
      some (effectScalarOutput supply narrow) := by
  let invocation (supply : NativeIR.Supply) (name : String) : NativeLowering.Expression :=
    ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external name) [], .checkContext],
      .temporary (NativeIR.fresh supply).1 .word, (NativeIR.fresh supply).2⟩
  have callCompiled (name : String) (supply : NativeIR.Supply)
      (typed : inferExpr collectingInterface scope (.call name []) = some .word) :
      NativeLowering.expression? collectingInterface scope (.call name []) supply =
        some (invocation supply name) := by
    rw [NativeLowering.expression?]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.word, typed, ?_⟩
    refine Option.bind_eq_some_iff.mpr ⟨⟨[], [], supply⟩, (by rw [NativeLowering.arguments?]), ?_⟩
    rfl
  have firstTyped : inferExpr collectingInterface scope (.call "touch" []) = some .word := by
    simp only [inferExpr, inferExprList, lookupFunction, collectingInterface, effectArgumentsInterface]
    rfl
  have secondTyped : inferExpr collectingInterface scope (.call "overwrite" []) = some .word := by
    simp only [inferExpr, inferExprList, lookupFunction, collectingInterface, effectArgumentsInterface]
    rfl
  have sumTyped : inferExpr collectingInterface scope
      (.binary (.word .add) (.call "touch" []) (.call "overwrite" [])) = some .word := by
    rw [inferExpr, firstTyped, secondTyped]
    rfl
  have sumCompiled : NativeLowering.expression? collectingInterface scope
      (.binary (.word .add) (.call "touch" []) (.call "overwrite" [])) supply =
      some (effectScalarOutput supply false) := by
    rw [NativeLowering.expression?]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.word, sumTyped, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨invocation supply "touch", callCompiled "touch" supply firstTyped, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨invocation (NativeIR.fresh supply).2 "overwrite",
      callCompiled "overwrite" (NativeIR.fresh supply).2 secondTyped, ?_⟩
    simp only [NativeLowering.numericGuard, List.append_nil]
    rfl
  cases narrow
  · exact sumCompiled
  · change NativeLowering.expression? collectingInterface scope
        (.unary .toByte (.binary (.word .add) (.call "touch" []) (.call "overwrite" []))) supply = _
    rw [NativeLowering.expression?]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.byte, ?_, ?_⟩
    · rw [inferExpr, sumTyped]
      rfl
    · exact Option.bind_eq_some_iff.mpr ⟨effectScalarOutput supply false, sumCompiled, rfl⟩

theorem effect_scalar_child_instance
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (narrow : Bool) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (effectScalarExpr narrow) := by
  have binary := stateful_unchecked_binary_child_laws Eq collectingInterface sourceHeap SourceEffectCall
    targetHeap TargetEffectCall frame source clear .word (.word 0) UncheckedScalarBinary.add
    (.call "touch" []) (.call "overwrite" [])
    (collecting_arguments_child_instances sourceHeap targetHeap frame)
  cases narrow
  · exact binary
  · exact stateful_unary_child_laws Eq collectingInterface sourceHeap SourceEffectCall
      targetHeap TargetEffectCall frame source .word (.word 0) .toByte _ binary

theorem effect_scalar_source_success (heap : SourceHeapSemantics (Bool × Nat)) (narrow : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectScalarExpr narrow) argumentSource ⟨.ok (effectScalarValue narrow), collectingAfterArguments⟩ := by
  have binary : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.binary (.word .add) (.call "touch" []) (.call "overwrite" [])) argumentSource
      ⟨.ok (.word (bounded 64 38)), collectingAfterArguments⟩ :=
    (source_unchecked_binary_stateful_exact UncheckedScalarBinary.add _ _ argumentSource _).mpr
      (.inl ⟨.word (bounded 64 17), .word (bounded 64 21), collectingAfterArguments,
        .word (bounded 64 38), collecting_arguments_source_success heap, rfl, rfl⟩)
  cases narrow
  · exact binary
  · exact (source_unary_expression_stateful_exact .toByte _ argumentSource _).mpr
      (.inl ⟨.word (bounded 64 38), collectingAfterArguments, .byte (bounded 8 38), binary, rfl, rfl⟩)

/-- Both actual lowerings retain the shared cell's final 21 and external
count 5, while their result is the saved-value sum 38. -/
theorem effect_scalar_target_success (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (narrow : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (effectScalarOutput ⟨0⟩ narrow).code effectCallFrame argumentTarget out ∧
      out.flow = .normal ∧ out.state.external = (true, 5) ∧
      out.state.memory.cells 1 0 = some (.word 21) ∧
      TargetAtomEval collectingInterface out.frame out.state
        (effectScalarOutput ⟨0⟩ narrow).result (encodeValue (effectScalarValue narrow)) ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ :=
    (effect_scalar_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl narrow).forward
      root (targetFrame := effectCallFrame) (effect_scalar_actual_lowering _ ⟨0⟩ narrow) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (effect_scalar_source_success sourceHeap narrow)
  rcases related with ⟨states, _, normal, value⟩
  exact ⟨out, ran, normal, states.external.symm, states.memory.1 1 0, value, protection⟩

theorem effect_scalar_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (narrow : Bool) {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun collectingInterface targetHeap TargetEffectCall .word root
      (effectScalarOutput ⟨0⟩ narrow).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
        (effectScalarExpr narrow) argumentSource sourceOut ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0)
        (effectScalarOutput ⟨0⟩ narrow).result sourceOut out := by
  obtain ⟨sourceOut, sourceRun, related, _, _, _⟩ :=
    (effect_scalar_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl narrow).backward
      root (targetFrame := effectCallFrame) (effect_scalar_actual_lowering _ ⟨0⟩ narrow) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRun, related⟩

theorem effect_scalar_source_first_fault (heap : SourceHeapSemantics (Bool × Nat)) (narrow : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectScalarExpr narrow) argumentSource ⟨.error .resourceFault, argumentRefusal⟩ := by
  have binary : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.binary (.word .add) (.call "touch" []) (.call "overwrite" [])) argumentSource
      ⟨.error .resourceFault, argumentRefusal⟩ :=
    (source_unchecked_binary_stateful_exact UncheckedScalarBinary.add _ _ argumentSource _).mpr
      (.inr ⟨.resourceFault, argumentRefusal,
        .consFault ((source_nullary_call_exact "touch" argumentSource _).mpr
          ⟨_, _, .refusal argumentSource, rfl⟩), rfl⟩)
  cases narrow
  · exact binary
  · exact (source_unary_expression_stateful_exact .toByte _ argumentSource _).mpr
      (.inr ⟨.resourceFault, argumentRefusal, binary, rfl⟩)

/-- The first fault skips the overwrite, addition and optional conversion;
its earlier service effects and live cell remain observable. -/
theorem effect_scalar_target_first_fault (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (narrow : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (effectScalarOutput ⟨0⟩ narrow).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = (true, 2) ∧ out.state.memory.cells 1 0 = some (.word 13) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (effect_scalar_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl narrow).forward
      root (targetFrame := effectCallFrame) (effect_scalar_actual_lowering _ ⟨0⟩ narrow) ⟨rfl, rfl, rfl⟩
      effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (effect_scalar_source_first_fault sourceHeap narrow)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0⟩

theorem effect_scalar_sum_is_not_repeated_final_cell :
    effectScalarValue false ≠ .word (bounded 64 42) := by
  intro same
  have numbers := congrArg Fin.val (SourceValue.word.inj same)
  change (38 : Nat) = 42 at numbers
  contradiction

theorem effect_scalar_nested_result_supply :
    (effectScalarOutput ⟨0⟩ false).supply.next = 3 ∧
      (effectScalarOutput ⟨0⟩ true).supply.next = 4 := ⟨rfl, rfl⟩


/-- Each Boolean producer performs two real services. Its second service
overwrites shared storage after the first result has been saved. -/
def effectComparisonExpr (value : Bool) : Expr :=
  .binary (.compare (if value then .lt else .eq)) (.call "touch" []) (.call "overwrite" [])

def effectComparisonOutput (supply : NativeIR.Supply) (value : Bool) : NativeLowering.Expression :=
  let operands := collectingOperands supply
  NativeLowering.prependCode operands.code
    (NativeLowering.pureTemporary operands.supply .bool
      (.binary (.compare (if value then .lt else .eq))
        (.temporary (NativeIR.fresh supply).1 .word)
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word)))

def effectComparisonPost (source : SourceState (Bool × Nat)) : SourceState (Bool × Nat) :=
  let first : SourceState (Bool × Nat) :=
    { source with memory := liveSource, external := (true, source.external.2 + 1) }
  { first with
    memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21)),
    external := (true, first.external.2 + 4) }

def effectComparisonFault (source : SourceState (Bool × Nat)) : SourceState (Bool × Nat) :=
  sourcePoison { source with memory := liveSource, external := (true, source.external.2 + 2) }
    .resourceFault

theorem effect_comparison_typing (scope : Scope) (value : Bool) :
    inferExpr collectingInterface scope (effectComparisonExpr value) = some .bool := by
  cases value <;> simp only [effectComparisonExpr, inferExpr, inferExprList, lookupFunction,
    collectingInterface, effectArgumentsInterface] <;> rfl

theorem effect_comparison_actual_lowering (scope : Scope) (supply : NativeIR.Supply) (value : Bool) :
    NativeLowering.expression? collectingInterface scope (effectComparisonExpr value) supply =
      some (effectComparisonOutput supply value) := by
  let invocation (supply : NativeIR.Supply) (name : String) : NativeLowering.Expression :=
    ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external name) [], .checkContext],
      .temporary (NativeIR.fresh supply).1 .word, (NativeIR.fresh supply).2⟩
  have callCompiled (name : String) (supply : NativeIR.Supply)
      (typed : inferExpr collectingInterface scope (.call name []) = some .word) :
      NativeLowering.expression? collectingInterface scope (.call name []) supply =
        some (invocation supply name) := by
    have emitted := NativeLowering.call_lowering_exact collectingInterface scope name [] supply .word
      ⟨[], [], supply⟩ typed (by rw [NativeLowering.arguments?])
    simpa only [collectingInterface, effectArgumentsInterface, List.any_nil,
      Bool.false_eq_true, reduceCtorEq, if_false, List.nil_append, invocation] using emitted
  have firstTyped : inferExpr collectingInterface scope (.call "touch" []) = some .word := by
    simp only [inferExpr, inferExprList, lookupFunction, collectingInterface, effectArgumentsInterface]
    rfl
  have secondTyped : inferExpr collectingInterface scope (.call "overwrite" []) = some .word := by
    simp only [inferExpr, inferExprList, lookupFunction, collectingInterface, effectArgumentsInterface]
    rfl
  cases value <;> change NativeLowering.expression? collectingInterface scope (.binary _ _ _) supply = _
  all_goals
    rw [NativeLowering.expression?]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.bool, ?_, ?_⟩
    · rw [inferExpr, firstTyped, secondTyped]; rfl
    · apply Option.bind_eq_some_iff.mpr
      refine ⟨invocation supply "touch", callCompiled "touch" supply firstTyped, ?_⟩
      apply Option.bind_eq_some_iff.mpr
      refine ⟨invocation (NativeIR.fresh supply).2 "overwrite",
        callCompiled "overwrite" (NativeIR.fresh supply).2 secondTyped, ?_⟩
      simp only [NativeLowering.numericGuard, List.append_nil]
      rfl

theorem effect_comparison_child_instance
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (value : Bool) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (effectComparisonExpr value) :=
  stateful_unchecked_binary_child_laws Eq collectingInterface sourceHeap SourceEffectCall
    targetHeap TargetEffectCall frame source clear .word (.word 0)
    (UncheckedScalarBinary.compare (if value then .lt else .eq)) _ _
    (collecting_arguments_child_instances sourceHeap targetHeap frame)

theorem effect_comparison_source_success (heap : SourceHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (value : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall frame (effectComparisonExpr value)
      source ⟨.ok (.bool value), effectComparisonPost source⟩ := by
  let first : SourceState (Bool × Nat) :=
    { source with memory := liveSource, external := (true, source.external.2 + 1) }
  have firstRun : SourceExprEval collectingInterface heap SourceEffectCall frame
      (.call "touch" []) source ⟨.ok (.word (bounded 64 17)), first⟩ :=
    (source_nullary_call_exact "touch" source _).mpr
      ⟨_, _, .value source, by simp only [first, sourceObserve, clear]⟩
  have lastRun : SourceExprEval collectingInterface heap SourceEffectCall frame
      (.call "overwrite" []) first ⟨.ok (.word (bounded 64 21)), effectComparisonPost source⟩ :=
    (source_nullary_call_exact "overwrite" first _).mpr
      ⟨_, _, .overwrite first, by simp only [first, effectComparisonPost, sourceObserve, clear]⟩
  apply (source_unchecked_binary_stateful_exact (UncheckedScalarBinary.compare _) _ _ source _).mpr
  refine Or.inl ⟨.word (bounded 64 17), .word (bounded 64 21), effectComparisonPost source,
    .bool value, .cons firstRun (.cons lastRun (.nil _)), ?_, ?_⟩
  · cases value <;> rfl
  · simp only [sourceObserve, effectComparisonPost, clear]

theorem effect_comparison_source_fault (heap : SourceHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none) (value : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall frame (effectComparisonExpr value)
      source ⟨.error .resourceFault, effectComparisonFault source⟩ := by
  apply (source_unchecked_binary_stateful_exact (UncheckedScalarBinary.compare _) _ _ source _).mpr
  refine Or.inr ⟨.resourceFault, effectComparisonFault source, ?_, rfl⟩
  exact .consFault ((source_nullary_call_exact "touch" source _).mpr ⟨_, _, .refusal source, by simp only [effectComparisonFault, sourceObserve, sourcePoison, clear]⟩)

def effectShortCircuitExpr (continueValue ready : Bool) : Expr :=
  .binary (shortCircuitBinary continueValue) (effectComparisonExpr ready) (effectComparisonExpr true)

def effectShortCircuitOutput (supply : NativeIR.Supply) (continueValue ready : Bool) : NativeLowering.Expression :=
  let first := effectComparisonOutput supply ready
  shortCircuitOutput continueValue first
    (effectComparisonOutput (NativeLowering.pureTemporary first.supply .bool (.copy first.result)).supply true)

def effectShortCircuitPost (continueValue ready : Bool) : SourceState (Bool × Nat) :=
  if ready = continueValue then effectComparisonPost (effectComparisonPost argumentSource)
  else effectComparisonPost argumentSource

theorem effect_short_circuit_actual_lowering (scope : Scope) (supply : NativeIR.Supply)
    (continueValue ready : Bool) :
    NativeLowering.expression? collectingInterface scope (effectShortCircuitExpr continueValue ready) supply =
      some (effectShortCircuitOutput supply continueValue ready) := by
  have typing : inferExpr collectingInterface scope (effectShortCircuitExpr continueValue ready) = some .bool := by
    cases continueValue <;> change inferExpr collectingInterface scope (.binary _ _ _) = _ <;>
      rw [inferExpr, effect_comparison_typing, effect_comparison_typing] <;> rfl
  cases continueValue <;> change NativeLowering.expression? collectingInterface scope (.binary _ _ _) supply = _
  all_goals
    rw [NativeLowering.expression?]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨.bool, typing, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨effectComparisonOutput supply ready, effect_comparison_actual_lowering scope supply ready, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    refine ⟨effectComparisonOutput
      (NativeLowering.pureTemporary (effectComparisonOutput supply ready).supply .bool
        (.copy (effectComparisonOutput supply ready).result)).supply true,
      effect_comparison_actual_lowering _ _ true, ?_⟩
    rfl

theorem effect_short_circuit_child_instance
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (continueValue ready : Bool) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (effectShortCircuitExpr continueValue ready) :=
  stateful_short_circuit_child_laws clear continueValue
    (effect_comparison_child_instance sourceHeap targetHeap frame source clear ready)
    (fun middle clear => effect_comparison_child_instance sourceHeap targetHeap frame middle clear true)

theorem effect_short_circuit_source_success (heap : SourceHeapSemantics (Bool × Nat))
    (continueValue ready : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectShortCircuitExpr continueValue ready) argumentSource
      ⟨.ok (.bool (if ready = continueValue then true else ready)), effectShortCircuitPost continueValue ready⟩ := by
  have first := effect_comparison_source_success heap effectSourceFrame argumentSource rfl ready
  by_cases selected : ready = continueValue
  · subst ready
    simpa only [effectShortCircuitExpr, effectShortCircuitPost, if_true] using
      source_short_circuit_taken continueValue first
        (effect_comparison_source_success heap effectSourceFrame (effectComparisonPost argumentSource) rfl true)
  · have skipped : ready = !continueValue := by
      cases ready <;> cases continueValue <;> first | exact False.elim (selected rfl) | rfl
    subst ready
    simpa only [effectShortCircuitExpr, effectShortCircuitPost, selected, if_false] using source_short_circuit_skip continueValue first

/-- Taken execution retains both sets of effects (count 10); skipped execution
retains only the guard's effects (count 5). Both retain the last aliased write. -/
theorem effect_short_circuit_target_success (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (continueValue ready : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (effectShortCircuitOutput ⟨0⟩ continueValue ready).code effectCallFrame argumentTarget out ∧
      out.flow = .normal ∧ out.state.external = (true, if ready = continueValue then 10 else 5) ∧
      out.state.memory.cells 1 0 = some (.word 21) ∧
      TargetAtomEval collectingInterface out.frame out.state
        (effectShortCircuitOutput ⟨0⟩ continueValue ready).result
          (.bool (if ready = continueValue then true else ready)) ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ :=
    (effect_short_circuit_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl continueValue ready).forward
      root (targetFrame := effectCallFrame) (effect_short_circuit_actual_lowering _ ⟨0⟩ continueValue ready)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (effect_short_circuit_source_success sourceHeap continueValue ready)
  rcases related with ⟨states, _, normal, value⟩
  refine ⟨out, ran, normal, ?_, ?_, value, protection⟩
  · by_cases selected : ready = continueValue
    all_goals simpa [effectShortCircuitPost, effectComparisonPost, argumentSource, sourceState, selected] using states.external.symm
  · have encoded : encode (bounded 64 21) = (21 : BitVec 64) := rfl
    by_cases selected : ready = continueValue
    all_goals simpa [effectShortCircuitPost, effectComparisonPost, sourceStoreCell, encodeValue, encoded, selected] using states.memory.1 1 0

theorem effect_short_circuit_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (continueValue ready : Bool) {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun collectingInterface targetHeap TargetEffectCall .word root
      (effectShortCircuitOutput ⟨0⟩ continueValue ready).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
        (effectShortCircuitExpr continueValue ready) argumentSource sourceOut ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0)
        (effectShortCircuitOutput ⟨0⟩ continueValue ready).result sourceOut out := by
  obtain ⟨sourceOut, sourceRun, related, _, _, _⟩ :=
    (effect_short_circuit_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl continueValue ready).backward
      root (targetFrame := effectCallFrame) (effect_short_circuit_actual_lowering _ ⟨0⟩ continueValue ready)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) ran
  exact ⟨sourceOut, sourceRun, related⟩

theorem effect_short_circuit_source_first_fault (heap : SourceHeapSemantics (Bool × Nat))
    (continueValue ready : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectShortCircuitExpr continueValue ready) argumentSource
      ⟨.error .resourceFault, effectComparisonFault argumentSource⟩ :=
  source_short_circuit_left_fault continueValue
    (effect_comparison_source_fault heap effectSourceFrame argumentSource rfl ready)

theorem effect_short_circuit_source_right_fault (heap : SourceHeapSemantics (Bool × Nat))
    (continueValue : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectShortCircuitExpr continueValue continueValue) argumentSource
      ⟨.error .resourceFault, effectComparisonFault (effectComparisonPost argumentSource)⟩ :=
  source_short_circuit_taken continueValue
    (effect_comparison_source_success heap effectSourceFrame argumentSource rfl continueValue)
    (effect_comparison_source_fault heap effectSourceFrame (effectComparisonPost argumentSource) rfl true)

theorem effect_short_circuit_target_faults (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (continueValue : Bool) (rightFault : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (effectShortCircuitOutput ⟨0⟩ continueValue continueValue).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = (true, if rightFault then 7 else 2) ∧
      out.state.memory.cells 1 0 = some (.word 13) := by
  have sourceRun : SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
      (effectShortCircuitExpr continueValue continueValue) argumentSource
      ⟨.error .resourceFault, if rightFault then effectComparisonFault (effectComparisonPost argumentSource)
        else effectComparisonFault argumentSource⟩ := by
    cases rightFault
    · exact effect_short_circuit_source_first_fault sourceHeap continueValue continueValue
    · exact effect_short_circuit_source_right_fault sourceHeap continueValue
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (effect_short_circuit_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl continueValue continueValue).forward
      root (targetFrame := effectCallFrame) (effect_short_circuit_actual_lowering _ ⟨0⟩ continueValue continueValue)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) sourceRun
  cases rightFault <;> simp only [Bool.false_eq_true, if_false, if_true] at related ⊢
  all_goals
    rcases related with ⟨states, _, returned⟩
    exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0⟩

theorem effect_short_circuit_retained_effects_differ :
    (effectShortCircuitPost true true).external ≠ (effectShortCircuitPost true false).external := by decide

theorem effect_short_circuit_private_result_supply (continueValue ready : Bool) :
    (effectShortCircuitOutput ⟨0⟩ continueValue ready).supply.next = 7 := rfl

/-- The service contract is inspected at actual success prefixes; inferred
signatures alone do not supply the value tag. -/
theorem effect_word_nullary_success_tag (heap : SourceHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (name : String) (named : name = "touch" ∨ name = "overwrite")
    {source post : SourceState (Bool × Nat)} {value : SourceValue}
    (ran : SourceExprEval collectingInterface heap SourceEffectCall frame (.call name [])
      source ⟨.ok value, post⟩) : SourceOuterTag .word value := by
  obtain ⟨raw, after, called, observed⟩ := (source_nullary_call_exact name source _).mp ran
  have rawTag : SourceOuterTag .word raw := by
    cases called with
    | value | refusal | overwrite => constructor
    | notify =>
        rcases named with named | named
        · exact False.elim ((by decide : ("notify" : String) ≠ "touch") named)
        · exact False.elim ((by decide : ("notify" : String) ≠ "overwrite") named)
  have observedResult := congrArg SourceOutcome.result observed
  cases fault : after.fault with
  | none =>
      simp only [sourceObserve, fault, Except.ok.injEq] at observedResult
      cases observedResult
      exact rawTag
  | some fault => simp only [sourceObserve, fault, reduceCtorEq] at observedResult

theorem collecting_arguments_success_tags (heap : SourceHeapSemantics (Bool × Nat))
    (frame : SourceFrame) :
    ∀ expression ∈ collectingArguments, ∀ source post value type,
      inferExpr collectingInterface (sourceFrameScope frame) expression = some type →
      SourceExprEval collectingInterface heap SourceEffectCall frame expression source ⟨.ok value, post⟩ →
      SourceOuterTag type value := by
  intro expression member source post value type typed ran
  simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have same : NativeType.word = type := by
      simp only [inferExpr, inferExprList, lookupFunction, collectingInterface,
        effectArgumentsInterface, List.find?_nil] at typed
      exact Option.some.inj typed
    cases same
    exact effect_word_nullary_success_tag heap frame "touch" (.inl rfl) ran
  · have same : NativeType.word = type := by
      simp only [inferExpr, inferExprList, lookupFunction, collectingInterface,
        effectArgumentsInterface, List.find?_nil] at typed
      exact Option.some.inj typed
    cases same
    exact effect_word_nullary_success_tag heap frame "overwrite" (.inr rfl) ran

def effectWordExpr (operation : WordOp) : Expr :=
  .binary (.word operation) (.call "touch" []) (.call "overwrite" [])

def effectWordOutput (supply : NativeIR.Supply) (operation : WordOp) : NativeLowering.Expression :=
  let operands := collectingOperands supply
  NativeLowering.prependCode
    (operands.code ++ NativeLowering.numericGuard (.word operation) (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word))
    (NativeLowering.pureTemporary operands.supply .word
      (.binary (.word operation) (.temporary (NativeIR.fresh supply).1 .word) (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word)))

theorem effect_word_actual_lowering (scope : Scope) (supply : NativeIR.Supply) (operation : WordOp) :
    NativeLowering.expression? collectingInterface scope (effectWordExpr operation) supply =
      some (effectWordOutput supply operation) := by
  cases operation <;>
    simp only [effectWordExpr, effectWordOutput, collectingOperands, NativeLowering.expression?,
      NativeLowering.numericGuard, NativeLowering.arguments?, inferExpr, inferExprList, lookupFunction,
      List.find?_nil, collectingInterface,
      effectArgumentsInterface] <;> rfl

theorem effect_word_child_instance
    (sourceHeap : SourceHeapSemantics (Bool × Nat)) (targetHeap : TargetHeapSemantics (Bool × Nat))
    (frame : SourceFrame) (source : SourceState (Bool × Nat)) (clear : source.fault = none)
    (operation : WordOp) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (effectWordExpr operation) :=
  stateful_guarded_binary_child_laws Eq collectingInterface sourceHeap SourceEffectCall targetHeap
    TargetEffectCall frame source clear .word (.word 0) (.word operation) .unsignedWord _ _
    (collecting_arguments_child_instances sourceHeap targetHeap frame)
    (collecting_arguments_success_tags sourceHeap frame)

theorem effect_word_source_success (heap : SourceHeapSemantics (Bool × Nat)) (operation : WordOp) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (effectWordExpr operation) argumentSource
      (sourceFinish collectingAfterArguments ((sourceBinary operation (bounded 64 17) (bounded 64 21)).map SourceValue.word)) := by
  apply (source_guarded_binary_stateful_exact (.word operation) _ _ argumentSource _).mpr
  exact .inl ⟨_, _, collectingAfterArguments, _, collecting_arguments_source_success heap, rfl, rfl⟩

theorem effect_word_target_success (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (operation : WordOp) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (effectWordOutput ⟨0⟩ operation).code effectCallFrame argumentTarget out ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0) (effectWordOutput ⟨0⟩ operation).result
        (sourceFinish collectingAfterArguments ((sourceBinary operation (bounded 64 17) (bounded 64 21)).map SourceValue.word)) out ∧
      out.state.external = (true, 5) ∧ out.state.memory.cells 1 0 = some (.word 21) ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ :=
    (effect_word_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl operation).forward
      root (targetFrame := effectCallFrame) (effect_word_actual_lowering _ ⟨0⟩ operation)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (effect_word_source_success sourceHeap operation)
  have effects : (sourceFinish collectingAfterArguments
      ((sourceBinary operation (bounded 64 17) (bounded 64 21)).map SourceValue.word)).state.external = (true, 5) := by
    cases sourceBinary operation (bounded 64 17) (bounded 64 21) <;> rfl
  have stored : (sourceFinish collectingAfterArguments
      ((sourceBinary operation (bounded 64 17) (bounded 64 21)).map SourceValue.word)).state.memory.cells 1 0 =
      some (.word (bounded 64 21)) := by
    cases sourceBinary operation (bounded 64 17) (bounded 64 21) <;> rfl
  refine ⟨out, ran, related, related.1.external.symm.trans effects, ?_, protection⟩
  exact (related.1.memory.1 1 0).trans (congrArg (Option.map encodeValue) stored)

theorem effect_word_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (operation : WordOp) {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun collectingInterface targetHeap TargetEffectCall .word root
      (effectWordOutput ⟨0⟩ operation).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
        (effectWordExpr operation) argumentSource sourceOut ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0)
        (effectWordOutput ⟨0⟩ operation).result sourceOut out := by
  obtain ⟨sourceOut, executed, related, _, _, _⟩ :=
    (effect_word_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl operation).backward
      root (targetFrame := effectCallFrame) (effect_word_actual_lowering _ ⟨0⟩ operation)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) ran
  exact ⟨sourceOut, executed, related⟩

private def overwriteAfter (source : SourceState (Bool × Nat)) : SourceState (Bool × Nat) :=
  { source with
    memory := sourceStoreCell liveSource 1 0 (.word (bounded 64 21))
    external := (true, source.external.2 + 4) }

private def overwriteExpr (operation : WordOp) : Expr :=
  .binary (.word operation) (.call "overwrite" []) (.call "overwrite" [])

theorem overwrite_source_success (heap : SourceHeapSemantics (Bool × Nat)) (frame : SourceFrame)
    (source : SourceState (Bool × Nat)) (clear : source.fault = none) :
    SourceExprEval collectingInterface heap SourceEffectCall frame (.call "overwrite" []) source
      ⟨.ok (.word (bounded 64 21)), overwriteAfter source⟩ := by
  apply (source_nullary_call_exact "overwrite" source _).mpr
  refine ⟨_, _, .overwrite source, ?_⟩
  simp only [sourceObserve, clear, overwriteAfter]

theorem overwrite_children_tags (heap : SourceHeapSemantics (Bool × Nat)) (frame : SourceFrame) :
    ∀ expression ∈ [Expr.call "overwrite" [], .call "overwrite" []], ∀ source post value type,
      inferExpr collectingInterface (sourceFrameScope frame) expression = some type →
      SourceExprEval collectingInterface heap SourceEffectCall frame expression source ⟨.ok value, post⟩ →
      SourceOuterTag type value := by
  intro expression member
  have included : expression ∈ collectingArguments := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    cases member
    simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false, or_true]
  exact collecting_arguments_success_tags heap frame expression included

theorem overwrite_word_child_instance (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (frame : SourceFrame)
    (source : SourceState (Bool × Nat)) (clear : source.fault = none) (operation : WordOp) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (overwriteExpr operation) := by
  apply stateful_guarded_binary_child_laws Eq collectingInterface sourceHeap SourceEffectCall targetHeap
    TargetEffectCall frame source clear .word (.word 0) (.word operation) .unsignedWord
  · intro expression member before unpoisoned
    have included : expression ∈ collectingArguments := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      cases member
      simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false, or_true]
    exact collecting_arguments_child_instances sourceHeap targetHeap frame expression included before unpoisoned
  · exact overwrite_children_tags sourceHeap frame

theorem overwrite_word_source_success (heap : SourceHeapSemantics (Bool × Nat)) (frame : SourceFrame)
    (source : SourceState (Bool × Nat)) (clear : source.fault = none) (operation : WordOp) :
    SourceExprEval collectingInterface heap SourceEffectCall frame (overwriteExpr operation) source
      (sourceFinish (overwriteAfter (overwriteAfter source))
        ((sourceBinary operation (bounded 64 21) (bounded 64 21)).map SourceValue.word)) := by
  apply (source_guarded_binary_stateful_exact (.word operation) _ _ source _).mpr
  refine .inl ⟨.word (bounded 64 21), .word (bounded 64 21),
    overwriteAfter (overwriteAfter source), _, ?_, rfl, rfl⟩
  exact .cons (overwrite_source_success heap frame source clear)
    (.cons (overwrite_source_success heap frame (overwriteAfter source) clear)
      (.nil (overwriteAfter (overwriteAfter source))))

private def guardWordOp (shift right : Bool) : WordOp :=
  if shift then (if right then .shr else .shl) else (if right then .mod else .div)

private def guardInputOp (shift : Bool) : WordOp := if shift then .mul else .sub
private def guardInputValue (shift : Bool) : NativeWord64.Word := bounded 64 (if shift then 441 else 0)
private def guardInputFault (shift : Bool) : Fault := if shift then .shiftOutOfRange else .divisionByZero
private def guardEffectExpr (shift right : Bool) : Expr :=
  .binary (.word (guardWordOp shift right)) (.call "touch" []) (overwriteExpr (guardInputOp shift))

private def guardEffectAfter : SourceState (Bool × Nat) :=
  overwriteAfter (overwriteAfter { argumentSource with external := (true, 1) })

theorem guard_effect_source_fault (heap : SourceHeapSemantics (Bool × Nat)) (shift right : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame (guardEffectExpr shift right)
      argumentSource ⟨.error (guardInputFault shift), sourcePoison guardEffectAfter (guardInputFault shift)⟩ := by
  let first : SourceState (Bool × Nat) := { argumentSource with external := (true, 1) }
  have touch : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (.call "touch" []) argumentSource ⟨.ok (.word (bounded 64 17)), first⟩ :=
    (source_nullary_call_exact "touch" argumentSource _).mpr ⟨_, _, .value argumentSource, rfl⟩
  have rhs : SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame
      (overwriteExpr (guardInputOp shift)) first ⟨.ok (.word (guardInputValue shift)), guardEffectAfter⟩ := by
    have executed := overwrite_word_source_success heap effectSourceFrame first rfl (guardInputOp shift)
    cases shift <;> exact executed
  apply (source_guarded_binary_stateful_exact (.word (guardWordOp shift right)) _ _ argumentSource _).mpr
  refine .inl ⟨_, _, guardEffectAfter, .error (guardInputFault shift),
    .cons touch (.cons rhs (.nil guardEffectAfter)), ?_, ?_⟩
  · cases shift <;> cases right <;> rfl
  · cases shift <;> rfl

theorem guard_effect_child_instance (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (frame : SourceFrame)
    (source : SourceState (Bool × Nat)) (clear : source.fault = none) (shift right : Bool) :
    StatefulChildLaws Eq collectingInterface sourceHeap SourceEffectCall targetHeap TargetEffectCall
      frame source .word (.word 0) (guardEffectExpr shift right) := by
  apply stateful_guarded_binary_child_laws Eq collectingInterface sourceHeap SourceEffectCall targetHeap
    TargetEffectCall frame source clear .word (.word 0) (.word (guardWordOp shift right)) .unsignedWord
  · intro expression member before unpoisoned
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact collecting_arguments_child_instances sourceHeap targetHeap frame _
        (by simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false, true_or]) before unpoisoned
    · exact overwrite_word_child_instance sourceHeap targetHeap frame before unpoisoned (guardInputOp shift)
  · intro expression member before post value type typed ran
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact collecting_arguments_success_tags sourceHeap frame _
        (by simp only [collectingArguments, List.mem_cons, List.not_mem_nil, or_false, true_or])
        before post value type typed ran
    · exact source_guarded_binary_stateful_success_tag (.word (guardInputOp shift)) typed
        (overwrite_children_tags sourceHeap frame) ran

private def overwriteOperands (supply : NativeIR.Supply) : NativeLowering.Arguments :=
  ⟨[.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external "overwrite") [], .checkContext,
    .call (some (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word)) (.external "overwrite") [],
    .checkContext],
    [.temporary (NativeIR.fresh supply).1 .word,
      .temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word],
    (NativeIR.fresh (NativeIR.fresh supply).2).2⟩

private def overwriteOutput (supply : NativeIR.Supply) (shift : Bool) : NativeLowering.Expression :=
  let operands := overwriteOperands supply
  NativeLowering.prependCode operands.code
    (NativeLowering.pureTemporary operands.supply .word
      (.binary (.word (guardInputOp shift)) (.temporary (NativeIR.fresh supply).1 .word)
        (.temporary (NativeIR.fresh (NativeIR.fresh supply).2).1 .word)))

private def guardEffectOutput (supply : NativeIR.Supply) (shift right : Bool) : NativeLowering.Expression :=
  let rhs := overwriteOutput (NativeIR.fresh supply).2 shift
  NativeLowering.prependCode
    ([.call (some (.temporary (NativeIR.fresh supply).1 .word)) (.external "touch") [], .checkContext] ++
      rhs.code ++ NativeLowering.numericGuard (.word (guardWordOp shift right)) rhs.result)
    (NativeLowering.pureTemporary rhs.supply .word
      (.binary (.word (guardWordOp shift right)) (.temporary (NativeIR.fresh supply).1 .word) rhs.result))

theorem guard_effect_actual_lowering (scope : Scope) (supply : NativeIR.Supply) (shift right : Bool) :
    NativeLowering.expression? collectingInterface scope (guardEffectExpr shift right) supply =
      some (guardEffectOutput supply shift right) := by
  cases shift <;> cases right <;>
    simp only [guardEffectExpr, guardEffectOutput, guardWordOp, guardInputOp, overwriteExpr,
      overwriteOutput, overwriteOperands, NativeLowering.expression?, NativeLowering.arguments?,
      NativeLowering.numericGuard, inferExpr, inferExprList, lookupFunction, collectingInterface,
      effectArgumentsInterface] <;> rfl

/-- A numeric fault occurs after three separately authored service calls.
The saved left value and all earlier store/external effects remain observable. -/
theorem guard_effect_target_fault (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (shift right : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (guardEffectOutput ⟨0⟩ shift right).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some (guardInputFault shift) ∧
      out.state.external = (true, 9) ∧ out.state.memory.cells 1 0 = some (.word 21) ∧
      TemporaryProtection 0 effectCallFrame out.frame := by
  obtain ⟨out, ran, related, protection, _, _⟩ :=
    (guard_effect_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl shift right).forward
      root (targetFrame := effectCallFrame) (guard_effect_actual_lowering _ ⟨0⟩ shift right)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (guard_effect_source_fault sourceHeap shift right)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0, protection⟩

theorem guard_effect_source_first_fault (heap : SourceHeapSemantics (Bool × Nat)) (shift right : Bool) :
    SourceExprEval collectingInterface heap SourceEffectCall effectSourceFrame (guardEffectExpr shift right)
      argumentSource ⟨.error .resourceFault,
        sourcePoison { argumentSource with external := (true, 2) } .resourceFault⟩ := by
  apply (source_guarded_binary_stateful_exact (.word (guardWordOp shift right)) _ _ argumentSource _).mpr
  refine .inr ⟨.resourceFault, _, .consFault ?_, rfl⟩
  exact (source_nullary_call_exact "touch" argumentSource _).mpr ⟨_, _, .refusal argumentSource, rfl⟩

theorem guard_effect_target_first_fault (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction) (shift right : Bool) :
    ∃ out,
      TargetRun collectingInterface targetHeap TargetEffectCall .word root
        (guardEffectOutput ⟨0⟩ shift right).code effectCallFrame argumentTarget out ∧
      out.flow = .returned (.word 0) ∧ out.state.fault = some .resourceFault ∧
      out.state.external = (true, 2) ∧ out.state.memory.cells 1 0 = some (.word 13) := by
  obtain ⟨out, ran, related, _, _, _⟩ :=
    (guard_effect_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl shift right).forward
      root (targetFrame := effectCallFrame) (guard_effect_actual_lowering _ ⟨0⟩ shift right)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) (guard_effect_source_first_fault sourceHeap shift right)
  rcases related with ⟨states, _, returned⟩
  exact ⟨out, ran, returned, states.fault, states.external.symm, states.memory.1 1 0⟩

private def wrongNotifyInterface : Interface :=
  ⟨[], [], [], [⟨⟨"notify", [], .word⟩, "notify", .effect, none⟩]⟩
private def wrongNotifyExpr : Expr := .binary (.word .div) (.call "notify" []) (.word (bounded 64 0))
private def wrongNotifyOutput : NativeLowering.Expression :=
  ⟨[.call (some (.temporary 1 .word)) (.external "notify") [], .checkContext,
    .temporary 2 .word (.word 0), .checkedNumericGuard .div (.temporary 2 .word),
    .temporary 3 .word (.binary (.word .div) (.temporary 1 .word) (.temporary 2 .word))],
    .temporary 3 .word, ⟨3⟩⟩

theorem wrong_service_tag_actual_lowering (scope : Scope) :
    NativeLowering.expression? wrongNotifyInterface scope wrongNotifyExpr ⟨0⟩ = some wrongNotifyOutput := by
  simp only [wrongNotifyInterface, wrongNotifyExpr, wrongNotifyOutput, NativeLowering.expression?,
    NativeLowering.arguments?, inferExpr, inferExprList, lookupFunction]
  rfl

theorem wrong_service_tag_source_call_exact (heap : SourceHeapSemantics (Bool × Nat))
    (out : SourceOutcome (Bool × Nat)) :
    SourceExprEval wrongNotifyInterface heap SourceEffectCall effectSourceFrame (.call "notify" [])
      argumentSource out ↔
      out = ⟨.ok .unit, { argumentSource with external := (true, 8) }⟩ := by
  rw [source_nullary_call_exact]
  constructor
  · rintro ⟨raw, post, called, observed⟩
    generalize named : ("notify" : String) = name at called
    cases called with
    | value | refusal => exact False.elim ((by decide : ("notify" : String) ≠ "touch") named)
    | overwrite => exact False.elim ((by decide : ("notify" : String) ≠ "overwrite") named)
    | notify => exact observed
  · intro same
    subst out
    exact ⟨_, _, .notify argumentSource, rfl⟩

/-- The declared word-returning service actually returns unit. The source
arithmetic has no transition, whereas the emitted right guard can still fault. -/
theorem wrong_service_tag_source_has_no_execution (heap : SourceHeapSemantics (Bool × Nat))
    (out : SourceOutcome (Bool × Nat)) :
    ¬ SourceExprEval wrongNotifyInterface heap SourceEffectCall effectSourceFrame wrongNotifyExpr argumentSource out := by
  intro ran
  rcases (source_guarded_binary_stateful_exact (.word .div) _ _ argumentSource out).mp ran with
    ⟨first, second, middle, computed, arguments, primitive, _⟩ | ⟨fault, post, arguments, _⟩
  · obtain ⟨afterFirst, firstRun, rest⟩ :=
      (source_arguments_cons_success_exact (.call "notify" []) [.word (bounded 64 0)]
        argumentSource middle first [second]).mp arguments
    cases (wrong_service_tag_source_call_exact heap _).mp firstRun
    obtain ⟨afterLast, lastRun, ending⟩ :=
      (source_arguments_cons_success_exact (.word (bounded 64 0)) [] _ middle second []).mp rest
    cases (source_operand_free_expression_exact (.word (bounded 64 0)) rfl _ _).mp lastRun
    cases (source_arguments_nil_exact _ _).mp ending
    cases primitive
  · rcases (source_arguments_cons_fault_exact (.call "notify" []) [.word (bounded 64 0)]
      argumentSource post fault).mp arguments with firstFailed | ⟨value, middle, firstRun, rest⟩
    · cases (wrong_service_tag_source_call_exact heap _).mp firstFailed
    · cases (wrong_service_tag_source_call_exact heap _).mp firstRun
      rcases (source_arguments_cons_fault_exact (.word (bounded 64 0)) [] _ post fault).mp rest with
        lastFailed | ⟨value, middle, lastRun, ending⟩
      · cases (source_operand_free_expression_exact (.word (bounded 64 0)) rfl _ _).mp lastFailed
      · cases (source_arguments_nil_exact middle _).mp ending

theorem wrong_service_tag_target_has_extra_fault (heap : TargetHeapSemantics (Bool × Nat))
    (root : List NativeIR.Instruction) :
    ∃ after,
      TargetRun wrongNotifyInterface heap TargetEffectCall .word root wrongNotifyOutput.code
        effectCallFrame argumentTarget
        ⟨.returned (.word 0), after,
          targetPoison { argumentTarget with external := (true, 8) } .divisionByZero⟩ := by
  let middle := targetDeclareTemporary effectCallFrame 1 .unit
  let after := targetDeclareTemporary middle 2 (.word 0)
  refine ⟨after, .next (.call .nil (.notify argumentTarget) (.fresh (by rfl)))
    (.next (.contextClear rfl) (.next (.temporary (by rfl) (.word 0)) ?_))⟩
  exact .return (.numericFault
    (declared_temporary_atom wrongNotifyInterface middle _ 2 .word (.word 0)) rfl .unsignedWord)

theorem wrong_service_result_refuses_word_profile : ¬ SourceOuterTag .word SourceValue.unit := by
  intro tagged
  cases tagged

theorem guard_effect_actual_reflection (sourceHeap : SourceHeapSemantics (Bool × Nat))
    (targetHeap : TargetHeapSemantics (Bool × Nat)) (root : List NativeIR.Instruction)
    (shift right : Bool) {out : TargetBlockOutcome (Bool × Nat)}
    (ran : TargetRun collectingInterface targetHeap TargetEffectCall .word root
      (guardEffectOutput ⟨0⟩ shift right).code effectCallFrame argumentTarget out) :
    ∃ sourceOut,
      SourceExprEval collectingInterface sourceHeap SourceEffectCall effectSourceFrame
        (guardEffectExpr shift right) argumentSource sourceOut ∧
      CheckedExpressionRelated Eq collectingInterface (.word 0)
        (guardEffectOutput ⟨0⟩ shift right).result sourceOut out := by
  obtain ⟨sourceOut, executed, related, _, _, _⟩ :=
    (guard_effect_child_instance sourceHeap targetHeap effectSourceFrame argumentSource rfl shift right).backward
      root (targetFrame := effectCallFrame) (guard_effect_actual_lowering _ ⟨0⟩ shift right)
      ⟨rfl, rfl, rfl⟩ effect_arguments_initial_related (by intro identity live; cases live)
      (by intro identity _; rfl) ran
  exact ⟨sourceOut, executed, related⟩

end Mettapedia.GSLT.LanguageDef.NativeOps.RuntimeControls
