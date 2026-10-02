import Mettapedia.GSLT.LanguageDef.NativeOpsReadExpressionLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceControl
import Mettapedia.GSLT.LanguageDef.NativeOpsLocationLeaves

/-!
# Statement effects and their exact source and target observations

The constructor laws use the existing finite evaluations. Stores retain their
actual memory updates; faults stop before later instructions; lexical cleanup
keeps the existing monotone local counter. No call or allocation adequacy is
postulated by this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction LoopLabels)
open NativeWord64 (Fault)

inductive ControlFlowRelated (loops : List LoopLabels) (default : TargetValue) :
    SourceFlow → TargetFlow → Prop
  | normal : ControlFlowRelated loops default .normal .normal
  | returned (value : SourceValue) :
      ControlFlowRelated loops default (.returned value) (.returned (encodeValue value))
  | fault (fault : Fault) : ControlFlowRelated loops default (.fault fault) (.returned default)
  | broke {current : LoopLabels} {outer : List LoopLabels} (active : loops = current :: outer) :
      ControlFlowRelated loops default .broke (.jumped current.exit)
  | continued {current : LoopLabels} {outer : List LoopLabels} (active : loops = current :: outer) :
      ControlFlowRelated loops default .continued (.jumped current.entry)

structure ControlOutcomeRelated {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (loops : List LoopLabels) (default : TargetValue)
    (source : SourceBlockOutcome SourceWorld) (target : TargetBlockOutcome TargetWorld) : Prop where
  state : StateRelated worldRelated source.state target.state
  frame : FrameRelated source.frame target.frame
  flow : ControlFlowRelated loops default source.flow target.flow

theorem close_control_outcomes {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {loops : List LoopLabels} {default : TargetValue}
    {sourceMarker : SourceFrame} {targetMarker : TargetFrame}
    {source : SourceBlockOutcome SourceWorld} {target : TargetBlockOutcome TargetWorld}
    (markers : FrameRelated sourceMarker targetMarker)
    (related : ControlOutcomeRelated worldRelated loops default source target) :
    ControlOutcomeRelated worldRelated loops default (sourceCloseBlock sourceMarker source)
      (targetCloseBlock targetMarker target) := by
  obtain ⟨frames, states⟩ := scope_exit_correspondence markers related.frame related.state
  exact ⟨states, frames, related.flow⟩

theorem source_declaration_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (type : NativeType) (initializer : Expr) (frame : SourceFrame)
    (before : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.declare name type initializer) frame before out ↔
      (∃ value after, SourceExprEval interface heap calls frame initializer before ⟨.ok value, after⟩ ∧
        out = ⟨.normal, (sourceDeclareLocal frame after name type value).1,
          (sourceDeclareLocal frame after name type value).2⟩) ∨
      (∃ fault after, SourceExprEval interface heap calls frame initializer before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | declare evaluated => exact .inl ⟨_, _, evaluated, rfl⟩
    | declareFault evaluated => exact .inr ⟨_, _, evaluated, rfl⟩
  · rintro (⟨value, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩)
    · subst out
      exact .declare evaluated
    · subst out
      exact .declareFault evaluated

theorem source_set_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (location value : Expr) (frame : SourceFrame) (before : SourceState World)
    (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.set location value) frame before out ↔
      (∃ address middle replacement after memory,
        SourceLocationEval interface heap calls frame location before ⟨.ok address, middle⟩ ∧
        SourceExprEval interface heap calls frame value middle ⟨.ok replacement, after⟩ ∧
        sourceWrite after.memory address replacement = some memory ∧
        out = ⟨.normal, frame, { after with memory := memory }⟩) ∨
      (∃ fault after, SourceLocationEval interface heap calls frame location before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) ∨
      (∃ address middle fault after,
        SourceLocationEval interface heap calls frame location before ⟨.ok address, middle⟩ ∧
        SourceExprEval interface heap calls frame value middle ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | set located evaluated written => exact .inl ⟨_, _, _, _, _, located, evaluated, written, rfl⟩
    | setLocationFault located => exact .inr (.inl ⟨_, _, located, rfl⟩)
    | setValueFault located evaluated => exact .inr (.inr ⟨_, _, _, _, located, evaluated, rfl⟩)
  · rintro (⟨address, middle, replacement, after, memory, located, evaluated, written, same⟩ |
      ⟨fault, after, located, same⟩ | ⟨address, middle, fault, after, located, evaluated, same⟩)
    · subst out
      exact .set located evaluated written
    · subst out
      exact .setLocationFault located
    · subst out
      exact .setValueFault located evaluated

theorem source_branch_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (condition : Expr) (whenTrue whenFalse : List Statement) (frame : SourceFrame)
    (before : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.branch condition whenTrue whenFalse) frame before out ↔
      (∃ selected middle inner,
        SourceExprEval interface heap calls frame condition before ⟨.ok (.bool selected), middle⟩ ∧
        SourceBlockEval interface heap calls (if selected then whenTrue else whenFalse) frame middle inner ∧
        out = sourceCloseBlock frame inner) ∨
      (∃ fault after, SourceExprEval interface heap calls frame condition before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | branch evaluated body => exact .inl ⟨_, _, _, evaluated, body, rfl⟩
    | branchFault evaluated => exact .inr ⟨_, _, evaluated, rfl⟩
  · rintro (⟨selected, middle, inner, evaluated, body, same⟩ | ⟨fault, after, evaluated, same⟩)
    · subst out
      exact .branch evaluated body
    · subst out
      exact .branchFault evaluated

theorem source_effect_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (expression : Expr) (frame : SourceFrame) (before : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.effect expression) frame before out ↔
      (∃ value after, SourceExprEval interface heap calls frame expression before ⟨.ok value, after⟩ ∧
        out = ⟨.normal, frame, after⟩) ∨
      (∃ fault after, SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | effect evaluated => exact .inl ⟨_, _, evaluated, rfl⟩
    | effectFault evaluated => exact .inr ⟨_, _, evaluated, rfl⟩
  · rintro (⟨value, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩)
    · subst out
      exact .effect evaluated
    · subst out
      exact .effectFault evaluated

theorem source_return_value_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (expression : Expr) (frame : SourceFrame) (before : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.return (some expression)) frame before out ↔
      (∃ value after, SourceExprEval interface heap calls frame expression before ⟨.ok value, after⟩ ∧
        out = ⟨.returned value, frame, after⟩) ∨
      (∃ fault after, SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | returnValue evaluated => exact .inl ⟨_, _, evaluated, rfl⟩
    | returnFault evaluated => exact .inr ⟨_, _, evaluated, rfl⟩
  · rintro (⟨value, after, evaluated, same⟩ | ⟨fault, after, evaluated, same⟩)
    · subst out
      exact .returnValue evaluated
    · subst out
      exact .returnFault evaluated

theorem source_statements_cons_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (first : Statement) (rest : List Statement) (frame : SourceFrame) (before : SourceState World)
    (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls (first :: rest) frame before out ↔
      (∃ middleFrame middle, SourceStatementEval interface heap calls first frame before
        ⟨.normal, middleFrame, middle⟩ ∧ SourceBlockEval interface heap calls rest middleFrame middle out) ∨
      (SourceStatementEval interface heap calls first frame before out ∧ out.flow ≠ .normal) := by
  constructor
  · intro ran
    cases ran with
    | cons firstRan restRan => exact .inl ⟨_, _, firstRan, restRan⟩
    | stop firstRan abrupt => exact .inr ⟨firstRan, abrupt⟩
  · rintro (⟨middleFrame, middle, firstRan, restRan⟩ | ⟨firstRan, abrupt⟩)
    · exact .cons firstRan restRan
    · exact .stop firstRan abrupt

theorem target_declare_local_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {name : String} {type : NativeType} {atom : Atom} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state atom value) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.declareLocal name type atom) frame state out ↔
      out = ⟨.normal, (targetDeclareLocal frame state name type value).1,
        (targetDeclareLocal frame state name type value).2⟩ := by
  constructor
  · intro ran
    cases ran with
    | declareLocal otherRead =>
        cases target_atom_unique read otherRead
        rfl
  · intro same
    subst out
    exact .declareLocal read

theorem target_write_instruction_defined_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {pointer replacement : Atom} {address : Address} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (located : TargetAtomEval interface frame state pointer (.reference (some address)))
    (read : TargetAtomEval interface frame state replacement value) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.write pointer replacement) frame state out ↔
      ∃ memory, targetWrite state.memory address value = some memory ∧
        out = ⟨.normal, frame, { state with memory := memory }⟩ := by
  constructor
  · intro ran
    cases ran with
    | write otherLocated otherRead stored =>
        cases target_atom_unique located otherLocated
        cases target_atom_unique read otherRead
        exact ⟨_, stored, rfl⟩
  · rintro ⟨memory, stored, same⟩
    subst out
    exact .write located read stored

theorem target_declare_local_run_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {name : String} {type : NativeType} {atom : Atom} {value : TargetValue}
    {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state atom value) (root : List Instruction)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.declareLocal name type atom] frame state out ↔
      out = ⟨.normal, (targetDeclareLocal frame state name type value).1,
        (targetDeclareLocal frame state name type value).2⟩ :=
  (target_normal_then_exact (target_declare_local_instruction_exact read) root [] out).trans
    (target_run_empty_exact root _ _ out)

theorem written_state_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} (states : StateRelated worldRelated source target)
    (address : Address) (value : SourceValue) (memory : SourceMemory)
    (written : sourceWrite source.memory address value = some memory) :
    ∃ native, targetWrite target.memory address (encodeValue value) = some native ∧
      StateRelated worldRelated { source with memory := memory } { target with memory := native } := by
  obtain ⟨native, stored, memories⟩ := memory_write_forward source.memory target.memory states.memory
    address value memory written
  exact ⟨native, stored, memories, states.fault, states.allocator, states.release,
    states.external, states.allocatorStats⟩

theorem written_state_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {source : SourceState SourceWorld}
    {target : TargetState TargetWorld} (states : StateRelated worldRelated source target)
    (address : Address) (value : SourceValue) (memory : TargetMemory)
    (written : targetWrite target.memory address (encodeValue value) = some memory) :
    ∃ model, sourceWrite source.memory address value = some model ∧
      StateRelated worldRelated { source with memory := model } { target with memory := memory } := by
  obtain ⟨model, stored, memories⟩ := memory_write_backward source.memory target.memory states.memory
    address value memory written
  exact ⟨model, stored, memories, states.fault, states.allocator, states.release,
    states.external, states.allocatorStats⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
