import Mettapedia.GSLT.LanguageDef.NativeOpsStatementLowering

/-!
# Statement execution through actual compiled children

The public constructor laws compose already proved expression implementations
with actual local mutations. A concrete factory instantiates the guarded and
short-circuit children. These laws do not supply arbitrary call/heap contracts
or replace continuation-aware reflection for label-bearing whole blocks.
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

end Mettapedia.GSLT.LanguageDef.NativeOps
