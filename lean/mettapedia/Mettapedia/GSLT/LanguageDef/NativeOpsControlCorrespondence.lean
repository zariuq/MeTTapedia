import Mettapedia.GSLT.LanguageDef.NativeOpsStatementLowering

/-!
# Statement execution through actual compiled children

The public constructor laws compose already proved expression implementations
with actual local mutations. A concrete factory instantiates the guarded and
short-circuit children. The source execution invariant covers the structured
local family, including switch selection, finite while iterations and abrupt exits. It preserves
the actual frame, cell tags, fault state and normally reached checked scope.
These laws do not supply arbitrary call/heap contracts or replace
continuation-aware reflection for label-bearing whole blocks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Supply LoopLabels)
open NativeLowering (Block)

theorem declaration_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {type : NativeType} {initializer : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default initializer)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.declare name type initializer) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.declare name type initializer)
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := declaration_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    initializer supply value valueLowered
  rcases (source_declaration_statement_exact name type initializer sourceFrame source sourceOut).mp ran with
    ⟨actual, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    obtain ⟨⟨flow, middle, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    have afterFrames := temporary_protection_preserves_source_frame frames protection
    obtain ⟨declaredFrames, declaredStates⟩ := declaration_correspondence afterFrames states name type actual
    let declared := targetDeclareLocal middle target name type (encodeValue actual)
    have tail : TargetRun interface targetHeap targetCalls result root
        [.declareLocal name type value.result] middle target ⟨.normal, declared.1, declared.2⟩ :=
      (target_declare_local_run_exact read root _).mpr rfl
    exact ⟨⟨.normal, declared.1, declared.2⟩, target_append_normal root _ _ jumpFree first tail,
      ⟨declaredStates, declaredFrames, .normal⟩, afterBounded,
      target_declare_local_scoped afterScoped target name type (encodeValue actual)⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    obtain ⟨⟨flow, afterFrame, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, afterFrame, targetPoison target fault⟩,
      target_append_returned root _ [.declareLocal name type value.result] jumpFree first,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

theorem declaration_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {type : NativeType} {initializer : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default initializer)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.declare name type initializer) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.declare name type initializer)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := declaration_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    initializer supply value valueLowered
  rcases target_split_jump_free_prefix root value.code [.declareLocal name type value.result] jumpFree ran with
    ⟨middle, post, first, tail⟩ | ⟨returned, after, post, first, same⟩
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root valueLowered frames states bounded hscope first
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    cases (target_declare_local_run_exact read root out).mp tail
    obtain ⟨declaredFrames, declaredStates⟩ := declaration_correspondence
      (temporary_protection_preserves_source_frame frames protection) states name type actual
    exact ⟨⟨.normal, (sourceDeclareLocal sourceFrame source name type actual).1,
      (sourceDeclareLocal sourceFrame source name type actual).2⟩, .declare evaluated,
      ⟨declaredStates, declaredFrames, .normal⟩, afterBounded,
      target_declare_local_scoped afterScoped target name type (encodeValue actual)⟩
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root valueLowered frames states bounded hscope first
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩, .declareFault evaluated,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

theorem short_circuit_declaration_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {result : NativeType}
    {default : TargetValue} {name : String} {type : NativeType} {initializer : Expr}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression initializer)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.declare name type initializer) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.declare name type initializer)
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  declaration_child_preservation (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero supported)
    root compiled frames states bounded hscope ran

theorem short_circuit_declaration_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {result : NativeType}
    {default : TargetValue} {name : String} {type : NativeType} {initializer : Expr}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression initializer)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.declare name type initializer) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.declare name type initializer)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  declaration_child_reflection (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero supported)
    root compiled frames states bounded hscope ran

theorem local_set_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {value : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default value)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.set (.variable name) value) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.set (.variable name) value)
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, replacement, _, _, lowered, same⟩ := local_set_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    value supply replacement lowered
  rcases (source_set_statement_exact (.variable name) value sourceFrame source sourceOut).mp ran with
    ⟨address, middle, actual, after, memory, located, evaluated, written, same⟩ |
      ⟨fault, after, located, same⟩ | ⟨address, middle, fault, after, located, evaluated, same⟩
  · obtain ⟨actualAddress, found, exactLocation⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls sourceFrame name source _).mp located
    cases exactLocation
    subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    obtain ⟨⟨flow, last, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root lowered frames states bounded hscope evaluated
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    have afterFrames := temporary_protection_preserves_source_frame frames protection
    have targetLocated : TargetAtomEval interface last target (.localAddress name type)
        (.reference (some address)) :=
      .localAddress ((local_address_correspondence afterFrames name).trans found)
    obtain ⟨native, stored, postRelated⟩ := written_state_preservation states address actual memory written
    have tail : TargetRun interface targetHeap targetCalls result root
        [.write (.localAddress name type) replacement.result] last target
        ⟨.normal, last, { target with memory := native }⟩ :=
      (target_normal_then_exact (target_write_instruction_exact targetLocated read stored) root [] _).mpr (.nil _ _ _)
    exact ⟨⟨.normal, last, { target with memory := native }⟩,
      target_append_normal root _ _ jumpFree first tail, ⟨postRelated, afterFrames, .normal⟩,
      afterBounded, afterScoped⟩
  · obtain ⟨_, _, impossible⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls sourceFrame name source _).mp located
    cases impossible
  · obtain ⟨_, _, exactLocation⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls sourceFrame name source _).mp located
    cases exactLocation
    subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    obtain ⟨⟨flow, last, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root lowered frames states bounded hscope evaluated
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, last, targetPoison target fault⟩,
      target_append_returned root _ [.write (.localAddress name type) replacement.result] jumpFree first,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

theorem local_set_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {value : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default value)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.set (.variable name) value) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.set (.variable name) value)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨type, replacement, _, _, lowered, same⟩ := local_set_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    value supply replacement lowered
  rcases target_split_jump_free_prefix root replacement.code [.write (.localAddress name type) replacement.result]
      jumpFree ran with
    ⟨last, post, first, tail⟩ | ⟨returned, last, post, first, same⟩
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root lowered frames states bounded hscope first
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    have afterFrames := temporary_protection_preserves_source_frame frames protection
    cases tail with
    | next instruction rest =>
        cases instruction with
        | write nativeLocated nativeRead stored =>
            cases target_atom_unique read nativeRead
            cases nativeLocated with
            | localAddress found =>
                cases rest
                have sourceLocated := (local_address_correspondence afterFrames name).symm.trans found
                obtain ⟨memory, written, postRelated⟩ := written_state_reflection states _ actual _ stored
                exact ⟨⟨.normal, sourceFrame, { source with memory := memory }⟩,
                  .set ((source_variable_location_exact interface sourceHeap sourceCalls sourceFrame name source _).mpr
                    ⟨_, sourceLocated, rfl⟩) evaluated written,
                  ⟨postRelated, afterFrames, .normal⟩, afterBounded, afterScoped⟩
    | «return» instruction | resume instruction _ _ | escape instruction _ => cases instruction
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root lowered frames states bounded hscope first
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    have sourceAddress : ∃ address, sourceLocalAddress sourceFrame name = some address := by
      obtain ⟨_, _, _, checked, _, _, _⟩ := set_lowering_exact compiled
      obtain ⟨_, nameTyped, _, _⟩ := set_checked_types checked
      simp only [inferLocation] at nameTyped
      exact source_typed_local_has_address nameTyped
    obtain ⟨address, found⟩ := sourceAddress
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩,
      .setValueFault ((source_variable_location_exact interface sourceHeap sourceCalls sourceFrame name source _).mpr
        ⟨address, found, rfl⟩) evaluated,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

theorem short_circuit_local_set_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {result : NativeType}
    {default : TargetValue} {name : String} {value : Expr}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression value)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.set (.variable name) value) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.set (.variable name) value)
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  local_set_child_preservation (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero supported)
    root compiled frames states bounded hscope ran

theorem short_circuit_local_set_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld} {result : NativeType}
    {default : TargetValue} {name : String} {value : Expr}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression value)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.set (.variable name) value) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.set (.variable name) value)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame :=
  local_set_child_reflection (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls sourceFrame source clear tagged result zero supported)
    root compiled frames states bounded hscope ran

/-- Discarding an implemented expression preserves its actual normal or
fault outcome; the result temporary remains part of the native frame. -/
theorem effect_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {expression : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.effect expression) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.effect expression)
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := effect_lowering_exact compiled
  subst output
  rcases (source_effect_statement_exact expression sourceFrame source sourceOut).mp ran with
    ⟨actual, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    obtain ⟨⟨flow, middle, post⟩, actualRun, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, normal, unchanged, _⟩
    cases normal
    change post = target at unchanged
    subst post
    exact ⟨⟨.normal, middle, target⟩, actualRun,
      ⟨states, temporary_protection_preserves_source_frame frames protection, .normal⟩,
      afterBounded, afterScoped⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    obtain ⟨⟨flow, middle, post⟩, actualRun, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, middle, targetPoison target fault⟩, actualRun,
      ⟨poison_correspondence states fault,
        temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

/-- Backward transport observes the expression's actual native path and
retains its complete state and temporary protection. -/
theorem effect_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {expression : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.effect expression) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.effect expression)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := effect_lowering_exact compiled
  subst output
  obtain ⟨⟨answer, after⟩, evaluated, related, protection, afterBounded, afterScoped⟩ :=
    child.backward root valueLowered frames states bounded hscope ran
  cases answer with
  | ok actual =>
      rcases related with ⟨unchanged, normal, post, _⟩
      change after = source at unchanged
      subst after
      exact ⟨⟨.normal, sourceFrame, source⟩, .effect evaluated,
        ⟨by simpa only [post] using states,
          temporary_protection_preserves_source_frame frames protection,
          by simpa only [normal] using (ControlFlowRelated.normal (loops := loops) (default := default))⟩,
        afterBounded, afterScoped⟩
  | error fault =>
      rcases related with ⟨poisoned, returned, post⟩
      change after = sourcePoison source fault at poisoned
      subst after
      exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩, .effectFault evaluated,
        ⟨by simpa only [post] using poison_correspondence states fault,
          temporary_protection_preserves_source_frame frames protection,
          by simpa only [returned] using (ControlFlowRelated.fault (loops := loops) (default := default) fault)⟩,
        afterBounded, afterScoped⟩

/-- A successful return appends exactly the native return instruction;
an expression fault stops before that instruction. -/
theorem return_value_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {expression : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.return (some expression)) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.return (some expression))
      sourceFrame source sourceOut) :
    ∃ out, TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := return_value_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    expression supply value valueLowered
  rcases (source_return_value_statement_exact expression sourceFrame source sourceOut).mp ran with
    ⟨actual, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    obtain ⟨⟨flow, middle, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    have tail : TargetRun interface targetHeap targetCalls result root
        [.return value.result] middle target ⟨.returned (encodeValue actual), middle, target⟩ :=
      (target_return_then_exact read root [] _).mpr rfl
    exact ⟨⟨.returned (encodeValue actual), middle, target⟩,
      target_append_normal root _ _ jumpFree first tail,
      ⟨states, temporary_protection_preserves_source_frame frames protection, .returned actual⟩,
      afterBounded, afterScoped⟩
  · subst sourceOut
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    obtain ⟨⟨flow, middle, post⟩, first, related, protection, afterBounded, afterScoped⟩ :=
      child.forward root valueLowered frames states bounded hscope evaluated
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, middle, targetPoison target fault⟩,
      target_append_returned root _ [.return value.result] jumpFree first,
      ⟨poison_correspondence states fault,
        temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

/-- Reflect the actual expression prefix and return suffix, including a
faulted prefix that never reaches the authored return. -/
theorem return_value_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {expression : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression)
    (root : List Instruction) {loops : List LoopLabels} {supply : Supply} {output : Block}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.return (some expression)) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.return (some expression))
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  obtain ⟨nextScope, value, _, valueLowered, same⟩ := return_value_lowering_exact compiled
  subst output
  have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
    expression supply value valueLowered
  rcases target_split_jump_free_prefix root value.code [.return value.result] jumpFree ran with
    ⟨middle, post, first, tail⟩ | ⟨returned, after, post, first, same⟩
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root valueLowered frames states bounded hscope first
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    cases (target_return_then_exact read root [] out).mp tail
    exact ⟨⟨.returned actual, sourceFrame, source⟩, .returnValue evaluated,
      ⟨states, temporary_protection_preserves_source_frame frames protection, .returned actual⟩,
      afterBounded, afterScoped⟩
  · obtain ⟨sourceOut, evaluated, related, protection, afterBounded, afterScoped⟩ :=
      child.backward root valueLowered frames states bounded hscope first
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst out
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩, .returnFault evaluated,
      ⟨poison_correspondence states fault,
        temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      afterBounded, afterScoped⟩

theorem declaration_child_profiles {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {frame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {type : NativeType} {initializer : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      frame source result default initializer)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame source.memory)
    {loops : List LoopLabels} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope frame)
      (.declare name type initializer) supply = some output)
    {out : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.declare name type initializer) frame source out) :
    SourceFrameExtends frame out.frame ∧ SourceLocalsBelow out.frame ∧
      LocalTypesCoherent out.frame.bindings ∧ SourceLocalsTagged out.frame out.state.memory ∧
      (out.flow = .normal → sourceFrameScope out.frame = output.scope) := by
  obtain ⟨nextScope, value, checked, _, same⟩ := declaration_lowering_exact compiled
  obtain ⟨typing, scopeSame⟩ := declaration_checked_type checked
  subst output
  rcases (source_declaration_statement_exact name type initializer frame source out).mp ran with
    ⟨actual, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩
  · subst out
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    exact ⟨source_declaration_extends frame source name type actual,
      source_declare_local_below (state := source) below name type actual,
      source_declare_local_coherent (state := source) coherent below name type actual,
      source_declare_local_tagged tagged below name type (child.sourceTag typing evaluated),
      fun _ => by rw [scopeSame]; rfl⟩
  · subst out
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    exact ⟨source_frame_extends_refl frame, below, coherent,
      (source_poison_preserves_effects source fault).1.symm ▸ tagged,
      fun impossible => by cases impossible⟩

theorem local_set_child_profiles {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {frame : SourceFrame} {source : SourceState SourceWorld}
    {result : NativeType} {default : TargetValue} {name : String} {value : Expr}
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      frame source result default value)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame source.memory)
    {loops : List LoopLabels} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope frame)
      (.set (.variable name) value) supply = some output)
    {out : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.set (.variable name) value) frame source out) :
    SourceFrameExtends frame out.frame ∧ SourceLocalsBelow out.frame ∧
      LocalTypesCoherent out.frame.bindings ∧ SourceLocalsTagged out.frame out.state.memory ∧
      (out.flow = .normal → sourceFrameScope out.frame = output.scope) := by
  obtain ⟨type, replacement, typed, typing, _, same⟩ := local_set_lowering_exact compiled
  subst output
  rcases (source_set_statement_exact (.variable name) value frame source out).mp ran with
    ⟨address, middle, actual, after, memory, located, evaluated, written, same⟩ |
      ⟨fault, after, located, same⟩ | ⟨address, middle, fault, after, located, evaluated, same⟩
  · obtain ⟨_, found, exactLocation⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls frame name source _).mp located
    cases exactLocation
    subst out
    have unchanged := child.sourceState evaluated
    change after = source at unchanged
    subst after
    exact ⟨source_frame_extends_refl frame, below, coherent,
      source_local_write_tagged tagged coherent typed found (child.sourceTag typing evaluated) written,
      fun _ => rfl⟩
  · obtain ⟨_, _, impossible⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls frame name source _).mp located
    cases impossible
  · obtain ⟨_, _, exactLocation⟩ :=
      (source_variable_location_exact interface sourceHeap sourceCalls frame name source _).mp located
    cases exactLocation
    subst out
    have unchanged := child.sourceState evaluated
    change after = sourcePoison source fault at unchanged
    subst after
    exact ⟨source_frame_extends_refl frame, below, coherent,
      (source_poison_preserves_effects source fault).1.symm ▸ tagged,
      fun impossible => by cases impossible⟩

theorem source_local_normal_profile {World : Type} {frame : SourceFrame} {state : SourceState World}
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none) :
    SourceLocalOutcomeProfile frame (sourceFrameScope frame) ⟨.normal, frame, state⟩ :=
  ⟨source_frame_extends_refl frame, below, coherent, tagged, clear, fun _ => rfl⟩

theorem source_local_fault_profile {World : Type} {frame : SourceFrame} {state : SourceState World}
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none)
    (nextScope : Scope) (fault : NativeWord64.Fault) :
    SourceLocalOutcomeProfile frame nextScope ⟨.fault fault, frame, sourcePoison state fault⟩ := by
  refine ⟨source_frame_extends_refl frame, below, coherent, ?_, ?_, ?_⟩
  · simpa only [sourcePoison, clear] using tagged
  · simp only [sourcePoison, clear]
  · intro impossible; cases impossible

theorem source_local_declaration_profile {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {frame : SourceFrame} {state : SourceState World} {result : NativeType} {loops : Nat}
    {name : String} {type : NativeType} {initializer : Expr} {nextScope : Scope}
    (supported : SourceShortCircuitExpression initializer)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none)
    (checked : checkStatement interface result loops (sourceFrameScope frame)
      (.declare name type initializer) = some nextScope)
    {out : SourceBlockOutcome World}
    (ran : SourceStatementEval interface heap calls (.declare name type initializer) frame state out) :
    SourceLocalOutcomeProfile frame nextScope out := by
  obtain ⟨typing, scopeSame⟩ := declaration_checked_type checked
  rcases (source_declaration_statement_exact name type initializer frame state out).mp ran with
    ⟨value, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩
  · subst out
    have unchanged := short_circuit_source_state supported state clear evaluated
    change after = state at unchanged
    subst after
    refine ⟨source_declaration_extends frame state name type value,
      source_declare_local_below (state := state) below name type value,
      source_declare_local_coherent (state := state) coherent below name type value,
      source_declare_local_tagged tagged below name type
        (short_circuit_source_success_tag supported clear tagged typing evaluated),
      clear, ?_⟩
    intro _; rw [scopeSame]; rfl
  · subst out
    have poisoned := short_circuit_source_state supported state clear evaluated
    change after = sourcePoison state fault at poisoned
    subst after
    exact source_local_fault_profile below coherent tagged clear nextScope fault

theorem source_local_set_profile {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {frame : SourceFrame} {state : SourceState World} {result : NativeType} {loops : Nat}
    {name : String} {value : Expr} {nextScope : Scope}
    (supported : SourceShortCircuitExpression value)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none)
    (checked : checkStatement interface result loops (sourceFrameScope frame)
      (.set (.variable name) value) = some nextScope)
    {out : SourceBlockOutcome World}
    (ran : SourceStatementEval interface heap calls (.set (.variable name) value) frame state out) :
    SourceLocalOutcomeProfile frame nextScope out := by
  obtain ⟨type, place, typing, scopeSame⟩ := set_checked_types checked
  have typed : lookupVariable (sourceFrameScope frame) name = some type := by
    simpa only [inferLocation] using place
  rcases (source_set_statement_exact (.variable name) value frame state out).mp ran with
    ⟨address, middle, actual, after, memory, located, evaluated, written, same⟩ |
      ⟨fault, after, located, same⟩ | ⟨address, middle, fault, after, located, evaluated, same⟩
  · obtain ⟨_, found, exactLocation⟩ :=
      (source_variable_location_exact interface heap calls frame name state _).mp located
    cases exactLocation
    subst out
    have unchanged := short_circuit_source_state supported state clear evaluated
    change after = state at unchanged
    subst after
    refine ⟨source_frame_extends_refl frame, below, coherent,
      source_local_write_tagged tagged coherent typed found
        (short_circuit_source_success_tag supported clear tagged typing evaluated) written,
      clear, ?_⟩
    intro _; exact scopeSame.symm
  · obtain ⟨_, _, impossible⟩ :=
      (source_variable_location_exact interface heap calls frame name state _).mp located
    cases impossible
  · obtain ⟨_, _, exactLocation⟩ :=
      (source_variable_location_exact interface heap calls frame name state _).mp located
    cases exactLocation
    subst out
    have poisoned := short_circuit_source_state supported state clear evaluated
    change after = sourcePoison state fault at poisoned
    subst after
    exact source_local_fault_profile below coherent tagged clear nextScope fault

theorem branch_checked_scopes {interface : Interface} {result : NativeType} {loops : Nat}
    {scope nextScope : Scope} {condition : Expr} {yes no : List Statement}
    (checked : checkStatement interface result loops scope (.branch condition yes no) = some nextScope) :
    ∃ yesScope noScope, inferExpr interface scope condition = some .bool ∧
      checkBlock interface result loops scope yes = some yesScope ∧
      checkBlock interface result loops scope no = some noScope ∧ nextScope = scope := by
  rw [checkStatement] at checked
  rcases Option.bind_eq_some_iff.mp checked with ⟨type, inferred, checked⟩
  split at checked
  · cases checked
  · rename_i same
    have equal : type = .bool := by
      by_cases equal : type = .bool
      · exact equal
      · exact False.elim (same equal)
    subst type
    rcases Option.bind_eq_some_iff.mp checked with ⟨yesScope, first, checked⟩
    rcases Option.bind_eq_some_iff.mp checked with ⟨noScope, second, checked⟩
    exact ⟨yesScope, noScope, inferred, first, second, (Option.some.inj checked).symm⟩

theorem while_checked_scope {interface : Interface} {result : NativeType} {loops : Nat}
    {scope nextScope : Scope} {condition : Expr} {body : List Statement}
    (checked : checkStatement interface result loops scope (.while condition body) = some nextScope) :
    ∃ bodyScope, inferExpr interface scope condition = some .bool ∧
      checkBlock interface result (loops + 1) scope body = some bodyScope ∧ nextScope = scope := by
  rw [checkStatement] at checked
  rcases Option.bind_eq_some_iff.mp checked with ⟨type, inferred, checked⟩
  split at checked
  · cases checked
  · rename_i same
    have equal : type = .bool := by
      by_cases equal : type = .bool
      · exact equal
      · exact False.elim (same equal)
    subst type
    rcases Option.bind_eq_some_iff.mp checked with ⟨bodyScope, bodyChecked, checked⟩
    exact ⟨bodyScope, inferred, bodyChecked, (Option.some.inj checked).symm⟩

/-- Actual finite executions of the structured local family retain the
invariants required by the next checked continuation. Induction follows the
execution derivation, including every repeated loop body. -/
theorem source_local_control_block_profiles {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {body : List Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World}
    (ran : SourceBlockEval interface heap calls body frame state out) :
    ∀ {result : NativeType} {loops : Nat} {nextScope : Scope},
      SourceLocalControlBlock body → SourceLocalsBelow frame →
      LocalTypesCoherent frame.bindings → SourceLocalsTagged frame state.memory →
      state.fault = none →
      checkBlock interface result loops (sourceFrameScope frame) body = some nextScope →
      SourceLocalOutcomeProfile frame nextScope out := by
  induction ran using SourceBlockEval.rec
    (motive_1 := fun statement frame state out _ =>
      ∀ {result : NativeType} {loops : Nat} {nextScope : Scope},
        SourceLocalControlStatement statement → SourceLocalsBelow frame →
        LocalTypesCoherent frame.bindings → SourceLocalsTagged frame state.memory →
        state.fault = none →
        checkStatement interface result loops (sourceFrameScope frame) statement = some nextScope →
        SourceLocalOutcomeProfile frame nextScope out) with
  | declare evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | declare _ _ pure =>
        exact source_local_declaration_profile pure below coherent tagged clear checked (.declare evaluated)
  | declareFault evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | declare _ _ pure =>
        exact source_local_declaration_profile pure below coherent tagged clear checked (.declareFault evaluated)
  | set located evaluated written =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | set _ pure =>
        exact source_local_set_profile pure below coherent tagged clear checked (.set located evaluated written)
  | setLocationFault located =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | set _ pure =>
        exact source_local_set_profile pure below coherent tagged clear checked (.setLocationFault located)
  | setValueFault located evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | set _ pure =>
        exact source_local_set_profile pure below coherent tagged clear checked (.setValueFault located evaluated)
  | @branch condition yes no selected frame before middle inner evaluated body bodyIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | branch pure yesSupported noSupported =>
        have unchanged := short_circuit_source_state pure before clear evaluated
        change middle = before at unchanged
        obtain ⟨yesScope, noScope, _, yesChecked, noChecked, scopeSame⟩ := branch_checked_scopes checked
        have selectedSupported : SourceLocalControlBlock (if selected then yes else no) := by
          cases selected <;> assumption
        have selectedChecked : checkBlock interface result loops (sourceFrameScope frame)
            (if selected then yes else no) = some (if selected then yesScope else noScope) := by
          cases selected <;> assumption
        have innerProfile := bodyIH selectedSupported below coherent
          (by simpa only [unchanged] using tagged) (by simpa only [unchanged] using clear) selectedChecked
        cases scopeSame
        exact source_local_profile_close below coherent innerProfile
  | @branchFault condition yes no frame before after error evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | branch pure _ _ =>
        have poisoned := short_circuit_source_state pure before clear evaluated
        change after = sourcePoison before error at poisoned
        subst after
        exact source_local_fault_profile below coherent tagged clear nextScope error
  | @whileDone condition body frame before after tested =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | «while» pure _ =>
        have unchanged := short_circuit_source_state pure before clear tested
        change after = before at unchanged
        subst after
        obtain ⟨_, _, _, scopeSame⟩ := while_checked_scope checked
        cases scopeSame
        exact source_local_normal_profile below coherent tagged clear
  | @whileFault condition body frame before after error tested =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | «while» pure _ =>
        have poisoned := short_circuit_source_state pure before clear tested
        change after = sourcePoison before error at poisoned
        subst after
        exact source_local_fault_profile below coherent tagged clear nextScope error
  | @whileRepeat condition body frame before middle iteration last tested bodyRun again rest bodyIH restIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | «while» pure bodySupported =>
        have unchanged := short_circuit_source_state pure before clear tested
        change middle = before at unchanged
        obtain ⟨_, _, bodyChecked, _⟩ := while_checked_scope checked
        have inner := bodyIH bodySupported below coherent
          (by simpa only [unchanged] using tagged) (by simpa only [unchanged] using clear) bodyChecked
        have closed := source_local_profile_close below coherent inner
        have clearAgain : (sourceCloseBlock frame iteration).state.fault = none := by
          change iteration.state.fault = none
          rcases again with normal | continued
          · simpa only [normal] using inner.fault
          · simpa only [continued] using inner.fault
        have checkedAgain : checkStatement interface result loops
            (sourceFrameScope (sourceCloseBlock frame iteration).frame)
            (.while condition body) = some nextScope := checked
        have lastProfile := restIH (.while pure bodySupported)
          closed.below closed.coherent closed.tagged clearAgain checkedAgain
        exact source_local_profile_trans closed.extended lastProfile
  | @whileBreak condition body frame before middle iteration tested bodyRun broke bodyIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | «while» pure bodySupported =>
        have unchanged := short_circuit_source_state pure before clear tested
        change middle = before at unchanged
        obtain ⟨_, _, bodyChecked, scopeSame⟩ := while_checked_scope checked
        have inner := bodyIH bodySupported below coherent
          (by simpa only [unchanged] using tagged) (by simpa only [unchanged] using clear) bodyChecked
        have closed := source_local_profile_close below coherent inner
        cases scopeSame
        refine ⟨closed.extended, closed.below, closed.coherent, closed.tagged, ?_, fun _ => rfl⟩
        change iteration.state.fault = none
        simpa only [broke] using inner.fault
  | @whileStop condition body frame before middle iteration tested bodyRun _ bodyIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | «while» pure bodySupported =>
        have unchanged := short_circuit_source_state pure before clear tested
        change middle = before at unchanged
        obtain ⟨_, _, bodyChecked, scopeSame⟩ := while_checked_scope checked
        have inner := bodyIH bodySupported below coherent
          (by simpa only [unchanged] using tagged) (by simpa only [unchanged] using clear) bodyChecked
        cases scopeSame
        exact source_local_profile_close below coherent inner
  | @switch selector arms otherwise frame before middle value inner evaluated body bodyIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | switch pure armsSupported fallbackSupported =>
        have unchanged := short_circuit_source_state pure before clear evaluated
        change middle = before at unchanged
        have selectedSupported := source_select_case_property SourceLocalControlBlock value
          armsSupported fallbackSupported
        obtain ⟨selectedScope, selectedChecked⟩ := switch_checked_selection checked value
        have profile := bodyIH selectedSupported below coherent
          (by simpa only [unchanged] using tagged) (by simpa only [unchanged] using clear) selectedChecked
        have scopeSame := (switch_checked_type checked).2.2
        cases scopeSame
        exact source_local_profile_close below coherent profile
  | @switchFault selector arms otherwise frame before after fault evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | switch pure _ _ =>
        have poisoned := short_circuit_source_state pure before clear evaluated
        change after = sourcePoison before fault at poisoned
        subst after
        exact source_local_fault_profile below coherent tagged clear nextScope fault
  | «break» frame state =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    rw [checkStatement] at checked
    split at checked
    · cases checked
    · cases Option.some.inj checked
      exact ⟨source_frame_extends_refl frame, below, coherent, tagged, clear,
        fun impossible => by cases impossible⟩
  | «continue» frame state =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    rw [checkStatement] at checked
    split at checked
    · cases checked
    · cases Option.some.inj checked
      exact ⟨source_frame_extends_refl frame, below, coherent, tagged, clear,
        fun impossible => by cases impossible⟩
  | @effect expression frame before after value evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | effect pure =>
        have unchanged := short_circuit_source_state pure before clear evaluated
        change after = before at unchanged
        subst after
        rw [checkStatement] at checked
        obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp checked
        cases Option.some.inj same
        exact source_local_normal_profile below coherent tagged clear
  | @effectFault expression frame before after error evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | effect pure =>
        have poisoned := short_circuit_source_state pure before clear evaluated
        change after = sourcePoison before error at poisoned
        subst after
        exact source_local_fault_profile below coherent tagged clear nextScope error
  | free _ _ _ =>
      rename_i result loops nextScope supported below coherent tagged clear checked
      cases supported
  | freeFault _ =>
      rename_i result loops nextScope supported below coherent tagged clear checked
      cases supported
  | returnUnit frame state =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    rw [checkStatement] at checked
    split at checked
    · cases Option.some.inj checked
      exact ⟨source_frame_extends_refl frame, below, coherent, tagged, clear,
        fun impossible => by cases impossible⟩
    · cases checked
  | @returnValue expression frame before after value evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | returnValue pure =>
        have unchanged := short_circuit_source_state pure before clear evaluated
        change after = before at unchanged
        subst after
        exact ⟨source_frame_extends_refl frame, below, coherent, tagged, clear,
          fun impossible => by cases impossible⟩
  | @returnFault expression frame before after error evaluated =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | returnValue pure =>
        have poisoned := short_circuit_source_state pure before clear evaluated
        change after = sourcePoison before error at poisoned
        subst after
        exact source_local_fault_profile below coherent tagged clear nextScope error
  | @block body frame before inner bodyRun bodyIH =>
    rename_i result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | block bodySupported =>
        rw [checkStatement] at checked
        obtain ⟨_, bodyChecked, same⟩ := Option.bind_eq_some_iff.mp checked
        have innerProfile := bodyIH bodySupported below coherent tagged clear bodyChecked
        cases Option.some.inj same
        exact source_local_profile_close below coherent innerProfile
  | nil frame state =>
    intro result loops nextScope supported below coherent tagged clear checked
    rw [checkBlock] at checked
    cases Option.some.inj checked
    exact source_local_normal_profile below coherent tagged clear
  | @cons first rest frame middleFrame before middle last firstRun restRun firstIH restIH =>
    intro result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | cons head tail =>
        rw [checkBlock] at checked
        obtain ⟨middleScope, headChecked, tailChecked⟩ := Option.bind_eq_some_iff.mp checked
        have firstProfile := firstIH head below coherent tagged clear headChecked
        have actualScope := firstProfile.scope rfl
        rw [← actualScope] at tailChecked
        have lastProfile := restIH tail firstProfile.below firstProfile.coherent
          firstProfile.tagged firstProfile.fault tailChecked
        exact source_local_profile_trans firstProfile.extended lastProfile
  | stop firstRun abrupt firstIH =>
    intro result loops nextScope supported below coherent tagged clear checked
    cases supported with
    | cons head _ =>
        rw [checkBlock] at checked
        obtain ⟨_, headChecked, _⟩ := Option.bind_eq_some_iff.mp checked
        have firstProfile := firstIH head below coherent tagged clear headChecked
        exact ⟨firstProfile.extended, firstProfile.below, firstProfile.coherent, firstProfile.tagged,
          firstProfile.fault, fun impossible => False.elim (abrupt impossible)⟩

theorem source_local_control_statement_profiles {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {statement : Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World}
    (ran : SourceStatementEval interface heap calls statement frame state out)
    {result : NativeType} {loops : Nat} {nextScope : Scope}
    (supported : SourceLocalControlStatement statement)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none)
    (checked : checkStatement interface result loops (sourceFrameScope frame) statement = some nextScope) :
    SourceLocalOutcomeProfile frame nextScope out := by
  have singleton : SourceBlockEval interface heap calls [statement] frame state out := by
    cases out with
    | mk flow current post =>
        cases flow
        · exact .cons ran (.nil current post)
        all_goals exact .stop ran (by intro impossible; cases impossible)
  apply source_local_control_block_profiles singleton (.cons supported .nil) below coherent tagged clear
  rw [checkBlock, checked]
  simp only [bind, Option.bind_some, checkBlock]

/-- The dynamic invariant uses the scope emitted by the actual compiler.
    Abrupt source outcomes retain their reached scope rather than the
    unchecked declarations of an unexecuted tail. -/
theorem compiled_local_statement_source_profile {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {statement : Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World} {result : NativeType} {loops : List LoopLabels}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope frame)
      statement supply = some output)
    (ran : SourceStatementEval interface heap calls statement frame state out)
    (supported : SourceLocalControlStatement statement)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none) :
    SourceLocalOutcomeProfile frame output.scope out :=
  source_local_control_statement_profiles ran supported below coherent tagged clear
    (statement_lowering_checked_scope compiled)

theorem compiled_local_block_source_profile {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {body : List Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World} {result : NativeType} {loops : List LoopLabels}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.block? interface result loops (sourceFrameScope frame)
      body supply = some output)
    (ran : SourceBlockEval interface heap calls body frame state out)
    (supported : SourceLocalControlBlock body)
    (below : SourceLocalsBelow frame) (coherent : LocalTypesCoherent frame.bindings)
    (tagged : SourceLocalsTagged frame state.memory) (clear : state.fault = none) :
    SourceLocalOutcomeProfile frame output.scope out :=
  source_local_control_block_profiles ran supported below coherent tagged clear
    (block_lowering_checked_scope compiled)

end Mettapedia.GSLT.LanguageDef.NativeOps
