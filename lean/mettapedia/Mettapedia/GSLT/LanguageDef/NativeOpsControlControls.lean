import Mettapedia.GSLT.LanguageDef.NativeOpsStatementBoundaries
import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionControls

/-! Controls for compiled labels, actual continuations and lexical effects. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.ControlControls

open NativeIR (Instruction Label Supply)

def falseLoop : Statement := .while (.bool false) []

def falseLoopOutput (scope : Scope) (supply : Supply) : NativeLowering.Block :=
  ⟨[.label (freshLoopLabels supply).entry,
    .scope [.temporary (supply.next + 3) .bool (.bool false),
      .branch (.negated (.temporary (supply.next + 3) .bool)) [.jump (freshLoopLabels supply).exit] [],
      .jump (freshLoopLabels supply).entry],
    .label (freshLoopLabels supply).exit], scope, ⟨supply.next + 3⟩⟩

theorem false_loop_supported : SourceLocalControlStatement falseLoop :=
  .while (.guarded (.leaf (.bool false))) .nil

theorem false_loop_actual_lowering (interface : Interface) (result : NativeType)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply) :
    NativeLowering.statement? interface result loops scope falseLoop supply =
      some (falseLoopOutput scope supply) := by
  simp [falseLoop, falseLoopOutput, NativeLowering.statement?, NativeLowering.block?,
    NativeLowering.expression?, NativeLowering.pureTemporary, freshLoopLabels,
    NativeIR.fresh, checkStatement, checkBlock, inferExpr, Nat.add_assoc]

theorem false_loop_labels_derived (interface : Interface) (result : NativeType)
    (scope : Scope) (supply : Supply) :
    supply.next ≤ (falseLoopOutput scope supply).supply.next ∧
      CodeJumpsWithin (falseLoopOutput scope supply).supply.next (falseLoopOutput scope supply).code ∧
      TopLabelsAbove supply.next (falseLoopOutput scope supply).code :=
  statement_lowering_bounds (fun _ impossible => by cases impossible)
    (false_loop_actual_lowering interface result [] scope supply)

def unitCallInterface : Interface := ⟨[], [], [⟨"touch", [], .unit⟩], []⟩

/-- A statically admitted unit call with no operands needs no private
    identifier. This is a compiler boundary control, not a call-body proof. -/
theorem unit_call_actual_lowering (scope : Scope) (supply : Supply) :
    NativeLowering.expression? unitCallInterface scope (.call "touch" []) supply =
      some ⟨[.call none (.function "touch") [], .checkContext], .unit, supply⟩ := by
  simp [NativeLowering.expression?, NativeLowering.arguments?, inferExpr, inferExprList,
    lookupFunction, unitCallInterface]

theorem unit_call_boundary (scope : Scope) (supply : Supply) :
    LoweringBoundary supply supply [.call none (.function "touch") [], .checkContext] :=
  expression_lowering_boundary _ _ _ _ _ (unit_call_actual_lowering scope supply)

theorem not_every_expression_grows_supply :
    ¬ (∀ (interface : Interface) (scope : Scope) (expression : Expr) (supply : Supply)
        (output : NativeLowering.Expression),
      NativeLowering.expression? interface scope expression supply = some output →
        supply.next < output.supply.next) := by
  intro strict
  exact Nat.lt_irrefl 0 (strict unitCallInterface [] (.call "touch" []) ⟨0⟩
    ⟨[.call none (.function "touch") [], .checkContext], .unit, ⟨0⟩⟩
    (unit_call_actual_lowering [] ⟨0⟩))

theorem false_loop_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (frame : SourceFrame) (state : SourceState World) :
    SourceStatementEval interface heap calls falseLoop frame state ⟨.normal, frame, state⟩ :=
  .whileDone (.strict rfl (.nil state) rfl)

/-- A real compiled loop reaches its exit; its condition temporary is removed
    before the following fragment begins. No allocation or call leaf is used. -/
theorem false_loop_target {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) (supply : Supply) :
    TargetRun interface heap calls result (falseLoopOutput [] supply).code (falseLoopOutput [] supply).code
      (targetEmptyFrame storage) state ⟨.normal, targetEmptyFrame storage, state⟩ := by
  let frame := targetEmptyFrame storage
  let conditionFrame := targetDeclareTemporary frame (supply.next + 3) (.bool false)
  let entry := (freshLoopLabels supply).entry
  let exit := (freshLoopLabels supply).exit
  let iteration : List Instruction :=
    [.temporary (supply.next + 3) .bool (.bool false),
      .branch (.negated (.temporary (supply.next + 3) .bool)) [.jump exit] [], .jump entry]
  have conditionScoped : TemporariesScoped conditionFrame :=
    declared_temporaries_completeNames (target_empty_frame_scoped storage) _ _
  have tested : TargetConditionEval interface conditionFrame state
      (.negated (.temporary (supply.next + 3) .bool)) true :=
    .negated (declared_temporary_atom interface frame state _ _ _)
  have arm : TargetRun interface heap calls result [.jump exit] [.jump exit] conditionFrame state
      ⟨.jumped exit, conditionFrame, state⟩ := .escape (.jump exit conditionFrame state) rfl
  have branch : TargetInstructionEval interface heap calls result
      (.branch (.negated (.temporary (supply.next + 3) .bool)) [.jump exit] []) conditionFrame state
      ⟨.jumped exit, conditionFrame, state⟩ := by
    have ran := TargetInstructionEval.branch (heap := heap) (calls := calls) (result := result)
      (whenFalse := []) tested arm
    rw [target_close_self conditionFrame state conditionScoped] at ran
    exact ran
  have inner : TargetRun interface heap calls result iteration iteration frame state
      ⟨.jumped exit, conditionFrame, state⟩ :=
    .next (.temporary rfl (.bool false)) (.escape branch rfl)
  have closed : targetCloseBlock frame ⟨.jumped exit, conditionFrame, state⟩ =
      ⟨.jumped exit, frame, state⟩ := by
    simp only [targetCloseBlock, targetLeaveScope, conditionFrame, frame, targetDeclareTemporary,
      targetEmptyFrame, List.contains_nil, Bool.false_eq_true, if_false, targetDropLocals_empty]
  have scopeRan : TargetInstructionEval interface heap calls result (.scope iteration) frame state
      ⟨.jumped exit, frame, state⟩ := by
    have ran := TargetInstructionEval.scope inner
    rw [closed] at ran
    exact ran
  have found : targetAfterLabel? (falseLoopOutput [] supply).code exit = some [] := by
    simpa only [falseLoopOutput, exit, iteration, List.append_nil] using loop_root_after_exit supply iteration []
  exact .next (.label entry frame state) (.resume scopeRan found (.nil _ frame state))

def suffix : List Instruction := [.declareLocal "after" .word (.word 1)]

/-- A constructor continuation really stores a local once after the compiled
    loop. The complete stored state and monotone local counter are retained. -/
theorem false_loop_then_store {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) (supply : Supply) :
    TargetRun interface heap calls result ((falseLoopOutput [] supply).code ++ suffix)
      ((falseLoopOutput [] supply).code ++ suffix) (targetEmptyFrame storage) state
      ⟨.normal, (targetDeclareLocal (targetEmptyFrame storage) state "after" .word (.word 1)).1,
        (targetDeclareLocal (targetEmptyFrame storage) state "after" .word (.word 1)).2⟩ := by
  have bounds := false_loop_labels_derived interface result [] supply
  apply target_extend_continuation bounds.2.1 bounds.2.1
    (top_labels_above_singleton _ _ (fun _ impossible => by cases impossible))
    (false_loop_target interface heap calls result storage state supply)
  exact .normal (.next (.declareLocal (.word 1)) (.nil _ _ _))

theorem continuation_store_counter {World : Type} (storage : Nat) (state : TargetState World) :
    (targetDeclareLocal (targetEmptyFrame storage) state "after" .word (.word 1)).1.nextLocal = 1 := rfl

def captured : Label := ⟨.exit, 1⟩

def capturedPrefix : List Instruction := [.jump captured]

def capturingSuffix : List Instruction := [.label captured, .declareLocal "extra" .word (.word 9)]

theorem captured_prefix_escapes {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    TargetRun interface heap calls result capturedPrefix capturedPrefix frame state
      ⟨.jumped captured, frame, state⟩ := .escape (.jump captured frame state) rfl

theorem capturing_suffix_is_not_fresh : ¬ TopLabelsAbove 1 capturingSuffix := by
  intro fresh
  have impossible := fresh captured (List.mem_cons_self)
  exact Nat.lt_irrefl 1 impossible

/-- Omitting the proved label discipline admits a genuine changed behavior:
    the new suffix captures an outward jump and performs an extra store. -/
theorem capturing_suffix_changes_execution {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    TargetRun interface heap calls result (capturedPrefix ++ capturingSuffix)
      (capturedPrefix ++ capturingSuffix) frame state
      ⟨.normal, (targetDeclareLocal frame state "extra" .word (.word 9)).1,
        (targetDeclareLocal frame state "extra" .word (.word 9)).2⟩ :=
  .resume (.jump captured frame state) rfl (.next (.declareLocal (.word 9)) (.nil _ _ _))

theorem original_continuation_cannot_invent_store {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    ¬ TargetContinues interface heap calls result (capturedPrefix ++ capturingSuffix) capturingSuffix
      ⟨.jumped captured, frame, state⟩
      ⟨.normal, (targetDeclareLocal frame state "extra" .word (.word 9)).1,
        (targetDeclareLocal frame state "extra" .word (.word 9)).2⟩ := by
  intro following
  cases following

def localBreakLoop (name : String) (value : NativeWord64.Word) : Statement :=
  .while (.bool true) [.declare name .word (.word value), .break]

def localBreakLoopOutput (scope : Scope) (supply : Supply) (name : String)
    (value : NativeWord64.Word) : NativeLowering.Block :=
  ⟨[.label (freshLoopLabels supply).entry,
    .scope [.temporary (supply.next + 3) .bool (.bool true),
      .branch (.negated (.temporary (supply.next + 3) .bool)) [.jump (freshLoopLabels supply).exit] [],
      .temporary (supply.next + 4) .word (.word (NativeWord64.encode value)),
      .declareLocal name .word (.temporary (supply.next + 4) .word),
      .jump (freshLoopLabels supply).exit, .jump (freshLoopLabels supply).entry],
    .label (freshLoopLabels supply).exit], scope, ⟨supply.next + 4⟩⟩

theorem local_break_loop_actual_lowering (interface : Interface) (result : NativeType)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply)
    (name : String) (value : NativeWord64.Word) (fresh : lookupVariable scope name = none) :
    NativeLowering.statement? interface result loops scope (localBreakLoop name value) supply =
      some (localBreakLoopOutput scope supply name value) := by
  simp [localBreakLoop, localBreakLoopOutput, NativeLowering.statement?, NativeLowering.block?,
    NativeLowering.expression?, NativeLowering.pureTemporary, freshLoopLabels,
    NativeIR.fresh, checkStatement, checkBlock, inferExpr, fresh, validType, Nat.add_assoc]

/-- The source really declares the local before breaking. Cleanup retains
the counter and removes the inner binding and cell. -/
theorem local_break_loop_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (name : String) (value : NativeWord64.Word) (frame : SourceFrame) (state : SourceState World) :
    SourceStatementEval interface heap calls (localBreakLoop name value) frame state
      { sourceCloseBlock frame
        ⟨.broke, (sourceDeclareLocal frame state name .word (.word value)).1,
          (sourceDeclareLocal frame state name .word (.word value)).2⟩ with flow := .normal } := by
  apply SourceStatementEval.whileBreak (source_bool_evaluates interface heap calls frame true state)
  · exact .cons (.declare (.strict rfl (.nil state) rfl))
      (.stop (.break _ _) (by intro impossible; cases impossible))
  · rfl

/-- The compiled loop retains its tested condition and actual local store,
then exits through the generated label without executing the back edge. -/
theorem local_break_loop_target {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (name : String) (value : NativeWord64.Word) (frame : TargetFrame) (state : TargetState World)
    (supply : Supply) (bounded : TemporaryNamesBound frame supply.next)
    (hscope : TemporariesScoped frame) :
    let tested := targetDeclareTemporary frame (supply.next + 3) (.bool true)
    let initialized := targetDeclareTemporary tested (supply.next + 4) (.word (NativeWord64.encode value))
    let declared := targetDeclareLocal initialized state name .word (.word (NativeWord64.encode value))
    TargetRun interface heap calls result (localBreakLoopOutput [] supply name value).code
      (localBreakLoopOutput [] supply name value).code frame state
      ⟨.normal, (targetCloseBlock frame ⟨.jumped (freshLoopLabels supply).exit, declared.1, declared.2⟩).frame,
        (targetCloseBlock frame ⟨.jumped (freshLoopLabels supply).exit, declared.1, declared.2⟩).state⟩ := by
  dsimp only
  let tested := targetDeclareTemporary frame (supply.next + 3) (.bool true)
  let initialized := targetDeclareTemporary tested (supply.next + 4) (.word (NativeWord64.encode value))
  let declared := targetDeclareLocal initialized state name .word (.word (NativeWord64.encode value))
  let entry := (freshLoopLabels supply).entry
  let exit := (freshLoopLabels supply).exit
  let iteration : List Instruction :=
    [.temporary (supply.next + 3) .bool (.bool true),
      .branch (.negated (.temporary (supply.next + 3) .bool)) [.jump exit] [],
      .temporary (supply.next + 4) .word (.word (NativeWord64.encode value)),
      .declareLocal name .word (.temporary (supply.next + 4) .word), .jump exit, .jump entry]
  have testFresh : frame.temporaryNames.contains (supply.next + 3) = false :=
    temporary_bound_fresh bounded (by omega)
  have testedBound : TemporaryNamesBound tested (supply.next + 3) :=
    declared_temporary_bound bounded (by omega) (Nat.le_refl _) _
  have valueFresh : tested.temporaryNames.contains (supply.next + 4) = false :=
    temporary_bound_fresh testedBound (by omega)
  have testedScoped : TemporariesScoped tested :=
    declared_temporaries_completeNames hscope _ _
  have guard : TargetInstructionEval interface heap calls result
      (.branch (.negated (.temporary (supply.next + 3) .bool)) [.jump exit] []) tested state
      ⟨.normal, tested, state⟩ :=
    (target_loop_guard_instruction_exact
      (declared_temporary_atom interface frame state _ _ _) testedScoped exit _).mpr rfl
  have inner : TargetRun interface heap calls result iteration iteration frame state
      ⟨.jumped exit, declared.1, declared.2⟩ :=
    .next (.temporary testFresh (.bool true))
      (.next guard (.next (.temporary valueFresh (.word _))
        (.next (.declareLocal (declared_temporary_atom interface tested state _ _ _))
          (.escape (.jump exit declared.1 declared.2) rfl))))
  apply (target_scoped_loop_iteration_exact entry exit iteration frame state _).mpr
  refine ⟨⟨.jumped exit, declared.1, declared.2⟩, inner, ?_⟩
  have different : entry ≠ exit := by
    intro equal
    have kinds := congrArg NativeIR.Label.kind equal
    cases kinds
  dsimp only
  rw [if_neg different, if_pos rfl]

theorem local_break_source_counter {World : Type} (name : String) (value : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) :
    (sourceCloseBlock frame
      ⟨.broke, (sourceDeclareLocal frame state name .word (.word value)).1,
        (sourceDeclareLocal frame state name .word (.word value)).2⟩).frame.nextLocal =
      frame.nextLocal + 1 := rfl

/-- Source and actual emitted target executions retain the same complete
post-state at the declared observation, including the inner allocation. -/
theorem local_break_loop_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) (loops : List NativeIR.LoopLabels) (default : TargetValue)
    (name : String) (value : NativeWord64.Word)
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (supply : Supply) (bounded : TemporaryNamesBound targetFrame supply.next)
    (hscope : TemporariesScoped targetFrame)
    (fresh : lookupVariable (sourceFrameScope sourceFrame) name = none) :
    ∃ output sourceOut targetOut,
      NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
        (localBreakLoop name value) supply = some output ∧
      SourceStatementEval interface sourceHeap sourceCalls (localBreakLoop name value) sourceFrame source sourceOut ∧
      TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target targetOut ∧
      ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
      sourceOut.frame.nextLocal = sourceFrame.nextLocal + 1 := by
  let tested := targetDeclareTemporary targetFrame (supply.next + 3) (.bool true)
  let initialized := targetDeclareTemporary tested (supply.next + 4) (.word (NativeWord64.encode value))
  have initializedFrames : FrameRelated sourceFrame initialized := by
    exact ⟨frames.storage, frames.nextLocal, frames.bindings⟩
  obtain ⟨declaredFrames, declaredStates⟩ :=
    declaration_correspondence initializedFrames states name .word (.word value)
  obtain ⟨closedFrames, closedStates⟩ := scope_exit_correspondence frames declaredFrames declaredStates
  refine ⟨localBreakLoopOutput (sourceFrameScope sourceFrame) supply name value, _, _,
    local_break_loop_actual_lowering interface result loops _ supply name value fresh,
    local_break_loop_source interface sourceHeap sourceCalls name value sourceFrame source,
    local_break_loop_target interface targetHeap targetCalls result name value targetFrame target supply bounded hscope,
    ⟨closedStates, closedFrames, .normal⟩, rfl⟩

private theorem local_break_body_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (value : NativeWord64.Word) (frame : SourceFrame)
    (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls [.declare name .word (.word value), .break] frame state out ↔
      out = ⟨.broke, (sourceDeclareLocal frame state name .word (.word value)).1,
        (sourceDeclareLocal frame state name .word (.word value)).2⟩ := by
  constructor
  · intro ran
    cases ran with
    | cons first rest =>
        cases first with
        | declare evaluated =>
            cases (source_operand_free_expression_exact (.word value) rfl state _).mp evaluated
            cases rest with
            | cons first rest => cases first
            | stop first abrupt => cases first; rfl
    | stop first abrupt =>
        cases first with
        | declare evaluated => exact False.elim (abrupt rfl)
        | declareFault evaluated =>
            cases (source_operand_free_expression_exact (.word value) rfl state _).mp evaluated
  · intro same
    subst out
    exact .cons (.declare (.strict rfl (.nil state) rfl))
      (.stop (.break _ _) (by intro impossible; cases impossible))

theorem local_break_loop_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (value : NativeWord64.Word) (frame : SourceFrame)
    (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (localBreakLoop name value) frame state out ↔
      out = { sourceCloseBlock frame
        ⟨.broke, (sourceDeclareLocal frame state name .word (.word value)).1,
          (sourceDeclareLocal frame state name .word (.word value)).2⟩ with flow := .normal } := by
  rw [localBreakLoop, source_while_iteration_exact]
  constructor
  · rintro (⟨after, tested, same⟩ | ⟨fault, after, tested, same⟩ | ⟨middle, inner, tested, body, following⟩)
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
      cases (local_break_body_exact name value frame state inner).mp body
      exact following
  · intro same
    subst out
    exact (source_while_iteration_exact _ _ _ _ _).mp
      (local_break_loop_source interface heap calls name value frame state)

/-- Every finite target run of this actual compiled store/break fragment has
the same complete outcome. Reflection inspects the emitted instructions and
the generated exit lookup, rather than comparing a replacement loop. -/
theorem local_break_loop_target_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (name : String) (value : NativeWord64.Word) (frame : TargetFrame) (state : TargetState World)
    (supply : Supply) (bounded : TemporaryNamesBound frame supply.next)
    (hscope : TemporariesScoped frame) (out : TargetBlockOutcome World) :
    let tested := targetDeclareTemporary frame (supply.next + 3) (.bool true)
    let initialized := targetDeclareTemporary tested (supply.next + 4) (.word (NativeWord64.encode value))
    let declared := targetDeclareLocal initialized state name .word (.word (NativeWord64.encode value))
    TargetRun interface heap calls result (localBreakLoopOutput [] supply name value).code
      (localBreakLoopOutput [] supply name value).code frame state out ↔
      out = ⟨.normal,
        (targetCloseBlock frame ⟨.jumped (freshLoopLabels supply).exit, declared.1, declared.2⟩).frame,
        (targetCloseBlock frame ⟨.jumped (freshLoopLabels supply).exit, declared.1, declared.2⟩).state⟩ := by
  dsimp only
  let tested := targetDeclareTemporary frame (supply.next + 3) (.bool true)
  let initialized := targetDeclareTemporary tested (supply.next + 4) (.word (NativeWord64.encode value))
  let declared := targetDeclareLocal initialized state name .word (.word (NativeWord64.encode value))
  let entry := (freshLoopLabels supply).entry
  let exit := (freshLoopLabels supply).exit
  let iteration : List Instruction :=
    [.temporary (supply.next + 3) .bool (.bool true),
      .branch (.negated (.temporary (supply.next + 3) .bool)) [.jump exit] [],
      .temporary (supply.next + 4) .word (.word (NativeWord64.encode value)),
      .declareLocal name .word (.temporary (supply.next + 4) .word), .jump exit, .jump entry]
  have testFresh := temporary_bound_fresh bounded (identity := supply.next + 3) (by omega)
  have testedBound : TemporaryNamesBound tested (supply.next + 3) :=
    declared_temporary_bound bounded (by omega) (Nat.le_refl _) _
  have valueFresh := temporary_bound_fresh testedBound (identity := supply.next + 4) (by omega)
  have testedScoped : TemporariesScoped tested := declared_temporaries_completeNames hscope _ _
  have testRead := declared_temporary_atom interface frame state (supply.next + 3) .bool (.bool true)
  have valueRead := declared_temporary_atom interface tested state (supply.next + 4) .word
    (.word (NativeWord64.encode value))
  have innerExact : ∀ inner, TargetRun interface heap calls result iteration iteration frame state inner ↔
      inner = ⟨.jumped exit, declared.1, declared.2⟩ := by
    intro inner
    change TargetRun interface heap calls result iteration
      (.temporary (supply.next + 3) .bool (.bool true) :: _) frame state inner ↔ _
    rw [target_normal_then_exact (target_temporary_instruction_exact testFresh (TargetPureEval.bool true)),
      target_normal_then_exact (target_loop_guard_instruction_exact testRead testedScoped exit),
      target_normal_then_exact (target_temporary_instruction_exact valueFresh (TargetPureEval.word _)),
      target_normal_then_exact (target_declare_local_instruction_exact valueRead), target_run_cons_exact]
    constructor
    · rintro ⟨firstOut, first, following⟩
      cases first with
      | jump => simpa only [iteration, targetAfterLabel?] using following
    · intro same
      subst inner
      exact ⟨_, .jump exit declared.1 declared.2, rfl⟩
  constructor
  · intro ran
    obtain ⟨inner, body, following⟩ :=
      (target_scoped_loop_iteration_exact entry exit iteration frame state out).mp ran
    cases (innerExact inner).mp body
    have different : entry ≠ exit := by
      intro equal
      have kinds := congrArg NativeIR.Label.kind equal
      cases kinds
    simpa only [if_neg different, if_true] using following
  · intro same
    subst out
    exact local_break_loop_target interface heap calls result name value frame state supply bounded hscope

/-- A completed execution of the actual compiler output reflects to the
source declaration/break loop. The compiler equality fixes the code; the
separate target inversion fixes its complete observed outcome. -/
theorem local_break_loop_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) (loops : List NativeIR.LoopLabels) (default : TargetValue)
    (name : String) (value : NativeWord64.Word)
    {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (supply : Supply) (bounded : TemporaryNamesBound targetFrame supply.next)
    (hscope : TemporariesScoped targetFrame)
    (fresh : lookupVariable (sourceFrameScope sourceFrame) name = none)
    {output : NativeLowering.Block}
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (localBreakLoop name value) supply = some output) {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target out) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (localBreakLoop name value)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut out ∧
      sourceOut.frame.nextLocal = sourceFrame.nextLocal + 1 := by
  obtain ⟨generated, sourceOut, chosen, lowered, sourceRan, targetRan, related, counter⟩ :=
    local_break_loop_preservation interface sourceHeap sourceCalls targetHeap targetCalls result loops default
      name value frames states supply bounded hscope fresh
  cases Option.some.inj (lowered.symm.trans compiled)
  have shape : output = localBreakLoopOutput (sourceFrameScope sourceFrame) supply name value :=
    Option.some.inj (compiled.symm.trans
      (local_break_loop_actual_lowering interface result loops _ supply name value fresh))
  subst output
  have chosenExact := (local_break_loop_target_exact interface targetHeap targetCalls result
    name value targetFrame target supply bounded hscope chosen).mp targetRan
  have outExact := (local_break_loop_target_exact interface targetHeap targetCalls result
    name value targetFrame target supply bounded hscope out).mp ran
  cases chosenExact.trans outExact.symm
  exact ⟨sourceOut, sourceRan, related, counter⟩

theorem local_break_cannot_reset_counter {World : Type} (name : String) (value : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) :
    (sourceCloseBlock frame
      ⟨.broke, (sourceDeclareLocal frame state name .word (.word value)).1,
        (sourceDeclareLocal frame state name .word (.word value)).2⟩).frame.nextLocal ≠ frame.nextLocal := by
  rw [local_break_source_counter]
  omega

/-- Leaving the condition temporary live cannot realize the next test.
The target's freshness check rejects redeclaration of that same identity. -/
theorem live_condition_cannot_be_redeclared {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (out : TargetBlockOutcome World) :
    ¬ TargetInstructionEval interface heap calls result (.temporary identity .bool (.bool true))
      (targetDeclareTemporary frame identity (.bool false)) state out := by
  intro ran
  cases ran with
  | temporary unused _ =>
      simp only [targetDeclareTemporary, List.contains_cons, beq_self_eq_true, Bool.true_or] at unused
      cases unused

theorem local_break_loop_profile {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (name : String) (value : NativeWord64.Word) (storage : Nat) (state : SourceState World)
    (clear : state.fault = none) :
    SourceLocalOutcomeProfile ⟨storage, 0, []⟩ []
      { sourceCloseBlock ⟨storage, 0, []⟩
        ⟨.broke, (sourceDeclareLocal ⟨storage, 0, []⟩ state name .word (.word value)).1,
          (sourceDeclareLocal ⟨storage, 0, []⟩ state name .word (.word value)).2⟩
        with flow := .normal } := by
  apply source_local_control_statement_profiles (result := .unit) (loops := 0)
    (local_break_loop_source interface heap calls name value ⟨storage, 0, []⟩ state)
    (.while (.guarded (.leaf (.bool true))) (.cons (.declare name .word (.guarded (.leaf (.word value))))
      (.cons .break .nil)))
  · intro binding member; cases member
  · exact local_types_empty
  · intro binding member; cases member
  · exact clear
  · simp [localBreakLoop, checkStatement, checkBlock, inferExpr, sourceFrameScope,
      lookupVariable, validType]

theorem early_return_tail_checked_scope (interface : Interface) :
    checkBlock interface .unit 0 [] [.return none, .declare "unreachable" .word (.word 1)] =
      some [("unreachable", .word)] := by
  simp [checkBlock, checkStatement, inferExpr, lookupVariable, validType]

/-- Static checking covers the whole block. An actual early return does not
    execute its tail or acquire the tail's declared scope. -/
theorem early_return_tail_keeps_initial_scope {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (storage : Nat)
    (state : SourceState World) :
    SourceBlockEval interface heap calls [.return none, .declare "unreachable" .word (.word 1)]
    ⟨storage, 0, []⟩ state ⟨.returned .unit, ⟨storage, 0, []⟩, state⟩ ∧
      sourceFrameScope ⟨storage, 0, []⟩ ≠ [("unreachable", .word)] := by
  refine ⟨first_return_skips_remaining_statements interface heap calls _ _ state, ?_⟩
  simp [sourceFrameScope]

theorem conflicting_alias_types_rejected :
    ¬ LocalTypesCoherent [⟨"number", .word, 0⟩, ⟨"flag", .bool, 0⟩] := by
  intro coherent
  have impossible := coherent ⟨"number", .word, 0⟩ List.mem_cons_self
    ⟨"flag", .bool, 0⟩ (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  cases impossible

def invalidCallerMarker : SourceFrame := ⟨0, 0, [⟨"caller", .word, 0⟩]⟩

theorem missing_caller_bound_not_below : ¬ SourceLocalsBelow invalidCallerMarker := by
  intro below
  exact Nat.not_lt_zero 0 (below _ List.mem_cons_self)

/-- A marker falsely placing a live caller cell in the new scope loses it.
    Frame extension alone cannot justify the cleanup law. -/
theorem missing_caller_bound_drops_caller_cell {World : Type} (state : SourceState World) :
    let stored := { state with memory := sourceStoreCell state.memory 0 0 (.word 7) }
    let current := { invalidCallerMarker with nextLocal := 1 }
    SourceFrameExtends invalidCallerMarker current ∧
      stored.memory.cells 0 0 = some (.word 7) ∧
      (sourceCloseBlock invalidCallerMarker ⟨.normal, current, stored⟩).state.memory.cells 0 0 = none := by
  refine ⟨⟨rfl, Nat.zero_le _, fun _ member => member⟩, ?_, ?_⟩
  · simp [sourceStoreCell]
  · simp [sourceCloseBlock, sourceLeaveScope, sourceDropLocals, invalidCallerMarker]

theorem false_loop_jump_origins (interface : Interface) (result : NativeType)
    (scope : Scope) (supply : Supply) :
    CodeJumpsRespect (CompilerJumpOrigin [] supply.next) (falseLoopOutput scope supply).code :=
  statement_lowering_jump_origins (fun _ impossible => by cases impossible)
    (false_loop_actual_lowering interface result [] scope supply)

/-- The tail loop runs under both actual compiled siblings without borrowing
    the first loop's entry or exit. Its temporary cleanup is retained. -/
theorem two_false_loops_target {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) (supply : Supply) :
    TargetRun interface heap calls result
      ((falseLoopOutput [] supply).code ++ (falseLoopOutput [] (falseLoopOutput [] supply).supply).code)
      ((falseLoopOutput [] supply).code ++ (falseLoopOutput [] (falseLoopOutput [] supply).supply).code)
      (targetEmptyFrame storage) state ⟨.normal, targetEmptyFrame storage, state⟩ := by
  have firstCompiled := false_loop_actual_lowering interface result [] [] supply
  have tailCompiled : NativeLowering.block? interface result [] [] [falseLoop]
      (falseLoopOutput [] supply).supply =
      some (falseLoopOutput [] (falseLoopOutput [] supply).supply) := by
    rw [NativeLowering.block?, false_loop_actual_lowering]
    simp only [bind, Option.bind_some, NativeLowering.block?, List.append_nil]
  have tailRun := compiled_tail_root_prefix_preserves (fun _ impossible => by cases impossible)
    firstCompiled tailCompiled
    (false_loop_target interface heap calls result storage state (falseLoopOutput [] supply).supply)
  have firstBounds := false_loop_labels_derived interface result [] supply
  have tailFresh := (false_loop_labels_derived interface result [] (falseLoopOutput [] supply).supply).2.2
  exact target_extend_continuation firstBounds.2.1 firstBounds.2.1 tailFresh
    (false_loop_target interface heap calls result storage state supply) (.normal tailRun)

theorem older_label_not_fresh_origin : ¬ CompilerJumpOrigin [] 1 captured := by
  rintro (⟨active, impossible, _⟩ | newer)
  · cases impossible
  · exact Nat.lt_irrefl 1 newer

/-- An unqualified earlier root can intercept an outward jump even though
    the executed instruction itself is unchanged. -/
theorem earlier_label_intercepts_jump {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    TargetRun interface heap calls result [.label captured] [.jump captured] frame state
      ⟨.normal, frame, state⟩ :=
  .resume (.jump captured frame state) rfl (.nil _ frame state)

theorem earlier_label_does_not_preserve_escape {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    ¬ TargetRun interface heap calls result [.label captured] [.jump captured] frame state
      ⟨.jumped captured, frame, state⟩ := by
  intro ran
  cases ran with
  | next first rest => cases first
  | resume first found rest =>
      cases first
      cases Option.some.inj found
      cases rest
  | escape first absent =>
      cases first
      simp only [targetAfterLabel?, if_true] at absent
      cases absent

/-- A tail with real loop back-edges reflects under the two compiled roots.
    Earlier loop jumps are unrelated to the tail's fresh-label predicate. -/
theorem two_false_loops_tail_reflects {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) (supply : Supply)
    (out : TargetBlockOutcome World) :
    let first := falseLoopOutput [] supply
    let second := falseLoopOutput [] first.supply
    TargetRun interface heap calls result (first.code ++ second.code) second.code frame state out ↔
      TargetRun interface heap calls result second.code second.code frame state out := by
  dsimp only
  have firstCompiled := false_loop_actual_lowering interface result [] [] supply
  have secondCompiled : NativeLowering.block? interface result [] [] [falseLoop]
      (falseLoopOutput [] supply).supply =
      some (falseLoopOutput [] (falseLoopOutput [] supply).supply) := by
    simp only [NativeLowering.block?, false_loop_actual_lowering, bind, Option.bind_some,
      falseLoopOutput, List.append_nil]
  exact (compiled_tail_root_prefix_iff (fun _ impossible => by cases impossible)
    firstCompiled secondCompiled frame state out).symm

def suffixForeign : Label := ⟨.entry, 1⟩

def reachableSuffixRoot : List Instruction := [.label captured, .jump suffixForeign]

def suffixCapturingPrefix : List Instruction := [.label suffixForeign, .return .unit]

/-- The directly queried label has identical lookups in these two roots. -/
theorem captured_lookup_matches_with_unchecked_suffix (label : Label) (selected : label = captured) :
    targetAfterLabel? (suffixCapturingPrefix ++ reachableSuffixRoot) label =
      targetAfterLabel? reachableSuffixRoot label := by
  subst label
  rfl

/-- The first jump respects the predicate, but its actual target suffix does
    not. This is the missing closure premise in a one-lookup argument. -/
theorem captured_suffix_is_not_closed :
    CodeJumpsRespect (fun label => label = captured) [.jump captured] ∧
      ¬ (∀ label, label = captured → ∀ suffix,
        targetAfterLabel? reachableSuffixRoot label = some suffix →
        CodeJumpsRespect (fun target => target = captured) suffix) := by
  constructor
  · simp only [CodeJumpsRespect, InstructionJumpsRespect, and_true]
  · intro closed
    have impossible := closed captured rfl [.jump suffixForeign] rfl
    simp only [CodeJumpsRespect, InstructionJumpsRespect, and_true] at impossible
    have kinds := congrArg Label.kind impossible
    cases kinds

/-- Without reachable-suffix closure, preserving the directly queried lookup
    admits two actual finite executions with distinct outward observations. -/
theorem unchecked_suffix_changes_execution {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (frame : TargetFrame) (state : TargetState World) :
    TargetRun interface heap calls result reachableSuffixRoot [.jump captured] frame state
        ⟨.jumped suffixForeign, frame, state⟩ ∧
      TargetRun interface heap calls result (suffixCapturingPrefix ++ reachableSuffixRoot)
        [.jump captured] frame state ⟨.returned .unit, frame, state⟩ := by
  constructor
  · exact .resume (.jump captured frame state) rfl
      (.escape (.jump suffixForeign frame state) rfl)
  · exact .resume (.jump captured frame state) rfl
      (.resume (.jump suffixForeign frame state) rfl (.return (.return .unit)))

def branchCallerFrame (storage : Nat) : TargetFrame :=
  targetDeclareTemporary (targetEmptyFrame storage) 2 (.bool true)

def branchEscapeCode : List Instruction :=
  [.branch (.value (.temporary 2 .bool)) [.jump captured] []]

def branchCapturingPrefix : List Instruction := [.label captured, .return .unit]

/-- The escape fragment is the actual branch tail emitted with an enclosing
    loop. Its condition is freshly produced before the selected break. -/
theorem branch_escape_actual_lowering (interface : Interface) (result : NativeType) (scope : Scope) :
    NativeLowering.statement? interface result [⟨suffixForeign, captured⟩] scope
      (.branch (.bool true) [.break] []) ⟨1⟩ =
      some ⟨[.temporary 2 .bool (.bool true)] ++ branchEscapeCode, scope, ⟨2⟩⟩ := by
  simp [NativeLowering.statement?, NativeLowering.block?, NativeLowering.expression?,
    NativeLowering.pureTemporary, NativeIR.fresh, checkStatement, checkBlock, inferExpr,
    branchEscapeCode]

theorem branch_escape_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (frame : SourceFrame) (state : SourceState World) :
    SourceStatementEval interface heap calls (.branch (.bool true) [.break] []) frame state
      (sourceCloseBlock frame ⟨.broke, frame, state⟩) :=
  .branch (.strict rfl (.nil state) rfl) (.stop (.break frame state) (by intro impossible; cases impossible))

theorem branch_escape_target {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) :
    TargetRun interface heap calls result branchEscapeCode branchEscapeCode
      (branchCallerFrame storage) state ⟨.jumped captured, branchCallerFrame storage, state⟩ := by
  have hscope : TemporariesScoped (branchCallerFrame storage) :=
    declared_temporaries_completeNames (target_empty_frame_scoped storage) 2 (.bool true)
  have tested : TargetConditionEval interface (branchCallerFrame storage) state
      (.value (.temporary 2 .bool)) true :=
    .value (declared_temporary_atom interface (targetEmptyFrame storage) state 2 .bool (.bool true))
  apply (target_branch_body_exact tested _).mpr
  refine ⟨⟨.jumped captured, branchCallerFrame storage, state⟩,
    .escape (.jump captured _ _) rfl, ?_⟩
  exact (target_close_self _ state hscope (.jumped captured)).symm

/-- Running the complete emitted condition/branch code exposes the selected
    outward jump, including the exact freshly allocated condition frame. -/
theorem compiled_branch_escape_target {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) :
    TargetRun interface heap calls result
      ([.temporary 2 .bool (.bool true)] ++ branchEscapeCode)
      ([.temporary 2 .bool (.bool true)] ++ branchEscapeCode)
      (targetEmptyFrame storage) state ⟨.jumped captured, branchCallerFrame storage, state⟩ := by
  have branchRan := branch_escape_target interface heap calls result storage state
  have instruction := (target_single_nonlabel_exact _ (fun _ impossible => by cases impossible)
    (branchCallerFrame storage) state _).mp branchRan
  exact .next (.temporary rfl (.bool true)) (.escape instruction rfl)

theorem branch_label_free_prefix_keeps_escape {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) :
    TargetRun interface heap calls result ([.return .unit] ++ branchEscapeCode) branchEscapeCode
      (branchCallerFrame storage) state ⟨.jumped captured, branchCallerFrame storage, state⟩ := by
  apply (target_label_free_prefix_root_iff
    (top_label_free_singleton (.return .unit) (fun _ impossible => by cases impossible))
    branchEscapeCode branchEscapeCode _ _ _).mpr
  exact branch_escape_target interface heap calls result storage state

/-- A visible earlier label intercepts the same branch's outward jump and
    actually returns. The condition and selected inner body are unchanged. -/
theorem branch_label_prefix_changes_escape {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (storage : Nat) (state : TargetState World) :
    TargetRun interface heap calls result (branchCapturingPrefix ++ branchEscapeCode) branchEscapeCode
      (branchCallerFrame storage) state ⟨.returned .unit, branchCallerFrame storage, state⟩ := by
  have branchRan := branch_escape_target interface heap calls result storage state
  have instruction := (target_single_nonlabel_exact _ (fun _ impossible => by cases impossible)
    (branchCallerFrame storage) state _).mp branchRan
  exact .resume instruction rfl (.return (.return .unit))

/-- The compositional while law constructs the concrete false loop's actual
target execution from its source run, including an arbitrary valid caller. -/
theorem false_loop_compositional_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {supply : Supply}
    (loopBounds : LoopLabelsWithin supply.next loops) (zero : TargetZero interface result default)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result
        (falseLoopOutput (sourceFrameScope sourceFrame) supply).code
        (falseLoopOutput (sourceFrameScope sourceFrame) supply).code targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated loops default ⟨.normal, sourceFrame, source⟩ nativeOut ∧
      TemporaryNamesBound nativeOut.frame supply.next ∧ TemporariesScoped nativeOut.frame := by
  apply short_circuit_while_child_preservation loopBounds (.guarded (.leaf (.bool false))) .nil zero
    (false_loop_actual_lowering interface result loops (sourceFrameScope sourceFrame) supply)
    ?_ below coherent tagged clear frames states bounded hscope
    (false_loop_source interface sourceHeap sourceCalls sourceFrame source)
  intro frame state nativeFrame native bodySupply iteration sourceOut sameScope compiled _bodyLoops
    below coherent tagged clear frames states bounded hscope ran
  simp only [NativeLowering.block?] at compiled
  cases Option.some.inj compiled
  cases ran
  exact ⟨⟨.normal, nativeFrame, native⟩, .nil _ _ _, ⟨states, frames, .normal⟩, bounded, hscope⟩

/-- A genuine divergent source loop has no finite derivation. The induction
would require a strictly earlier finite derivation at every repetition. -/
theorem true_empty_loop_has_no_finite_source_run {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World) :
    ¬ SourceStatementEval interface heap calls (.while (.bool true) []) frame state out := by
  intro ran
  refine source_while_run_induction (.bool true) [] (fun _ _ _ => False) ?_ ?_ ?_ ?_ ?_ ran
  · intro frame state after tested
    cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
  · intro frame state after fault tested
    cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
  · intro frame state middle inner out tested bodyRan again ih
    exact ih
  · intro frame state middle inner tested bodyRan broke
    cases bodyRan
    cases broke
  · intro frame state middle inner tested bodyRan stopped
    cases bodyRan
    rcases stopped with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

/-- Actual compiled output for the divergent empty loop cannot falsely
terminate. Reflection fills the empty-body implementation from the target's
own nil constructor before applying the source divergence control. -/
theorem true_empty_compiled_loop_has_no_finite_run {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {supply : Supply}
    {output : NativeLowering.Block} {nativeOut : TargetBlockOutcome TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops) (zero : TargetZero interface result default)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.while (.bool true) []) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame) :
    ¬ TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target nativeOut := by
  intro ran
  have reflected := short_circuit_while_child_reflection
    (sourceHeap := sourceHeap) (sourceCalls := sourceCalls)
    loopBounds (.guarded (.leaf (.bool true))) .nil zero
    compiled (bodyBackward := ?_) below coherent tagged clear frames states bounded hscope ran
  · obtain ⟨sourceOut, actual, _, _, _⟩ := reflected
    exact true_empty_loop_has_no_finite_source_run interface sourceHeap sourceCalls sourceFrame source sourceOut actual
  · intro frame state nativeFrame native bodySupply iteration nativeOut sameScope compiled _bodyLoops
      below coherent tagged clear frames states bounded hscope ran
    simp only [NativeLowering.block?] at compiled
    cases Option.some.inj compiled
    cases ran
    exact ⟨⟨.normal, frame, state⟩, .nil _ _, ⟨states, frames, .normal⟩, bounded, hscope⟩

/-- The inner break belongs to the inner loop. The outer loop reaches the
return, and both scope closures retain the inner allocation counter. -/
def nestedLocalReturn (name : String) (innerValue returnValue : NativeWord64.Word) : Statement :=
  .while (.bool true) [localBreakLoop name innerValue, .return (some (.word returnValue))]

def nestedLocalReturnOutcome {World : Type} (name : String)
    (innerValue returnValue : NativeWord64.Word) (frame : SourceFrame)
    (state : SourceState World) : SourceBlockOutcome World :=
  let inner := sourceCloseBlock frame
    ⟨.broke, (sourceDeclareLocal frame state name .word (.word innerValue)).1,
      (sourceDeclareLocal frame state name .word (.word innerValue)).2⟩
  sourceCloseBlock frame ⟨.returned (.word returnValue), inner.frame, inner.state⟩

theorem nested_local_return_supported (name : String) (innerValue returnValue : NativeWord64.Word) :
    SourceLocalControlStatement (nestedLocalReturn name innerValue returnValue) :=
  .while (.guarded (.leaf (.bool true)))
    (.cons (.while (.guarded (.leaf (.bool true)))
      (.cons (.declare name .word (.guarded (.leaf (.word innerValue)))) (.cons .break .nil)))
      (.cons (.returnValue (.guarded (.leaf (.word returnValue)))) .nil))

theorem nested_local_return_lowering_exists (interface : Interface)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply)
    (name : String) (innerValue returnValue : NativeWord64.Word)
    (fresh : lookupVariable scope name = none) :
    ∃ output, NativeLowering.statement? interface .word loops scope
      (nestedLocalReturn name innerValue returnValue) supply = some output := by
  simp [nestedLocalReturn, localBreakLoop, NativeLowering.statement?, NativeLowering.block?,
    NativeLowering.expression?, NativeLowering.pureTemporary, NativeIR.fresh,
    checkStatement, checkBlock, inferExpr, fresh, validType]

theorem nested_local_return_source {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (name : String) (innerValue returnValue : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) :
    SourceStatementEval interface heap calls (nestedLocalReturn name innerValue returnValue) frame state
      (nestedLocalReturnOutcome name innerValue returnValue frame state) := by
  apply SourceStatementEval.whileStop (source_bool_evaluates interface heap calls frame true state)
  · exact .cons (local_break_loop_source interface heap calls name innerValue frame state)
      (.stop (.returnValue (.strict rfl (.nil _) rfl)) (by intro impossible; cases impossible))
  · exact .inl ⟨.word returnValue, rfl⟩

theorem nested_local_return_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (nestedLocalReturn name innerValue returnValue) frame state out ↔
      out = nestedLocalReturnOutcome name innerValue returnValue frame state := by
  rw [nestedLocalReturn, source_while_iteration_exact]
  constructor
  · rintro (⟨after, tested, same⟩ | ⟨fault, after, tested, same⟩ | ⟨middle, inner, tested, body, following⟩)
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
    · cases (source_operand_free_expression_exact (.bool true) rfl state _).mp tested
      rcases (source_statements_cons_exact _ _ _ _ _).mp body with
        ⟨bodyFrame, post, first, tail⟩ | ⟨first, abrupt⟩
      · cases (local_break_loop_source_exact name innerValue frame state _).mp first
        cases (source_return_word_block_exact returnValue _ _ []).mp tail
        exact following
      · cases (local_break_loop_source_exact name innerValue frame state _).mp first
        exact False.elim (abrupt rfl)
  · intro same
    subst out
    exact (source_while_iteration_exact _ _ _ _ _).mp
      (nested_local_return_source interface heap calls name innerValue returnValue frame state)

theorem nested_local_return_counter {World : Type} (name : String)
    (innerValue returnValue : NativeWord64.Word) (frame : SourceFrame) (state : SourceState World) :
    (nestedLocalReturnOutcome name innerValue returnValue frame state).frame.nextLocal = frame.nextLocal + 1 := rfl

/-- A nearest-loop break cannot become an outer break and silently skip
its following return. This control inverts the independent source relation. -/
theorem nested_local_return_is_not_normal {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World)
    (normal : out.flow = .normal) :
    ¬ SourceStatementEval interface heap calls (nestedLocalReturn name innerValue returnValue) frame state out := by
  intro ran
  cases (nested_local_return_source_exact name innerValue returnValue frame state out).mp ran
  cases normal

/-- The family factory constructs this nested program's actual native run
without an independent loop-body implementation premise. -/
theorem nested_local_return_family_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (nestedLocalReturn name innerValue returnValue) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated loops (.word 0)
        (nestedLocalReturnOutcome name innerValue returnValue sourceFrame source) nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  exact (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls .word .unsignedWord (nested_local_return_supported name innerValue returnValue)).forward
    loopBounds compiled below coherent tagged clear frames states bounded hscope
    (nested_local_return_source interface sourceHeap sourceCalls name innerValue returnValue sourceFrame source)

/-- Reflection uses the actual native execution and the independent source
inversion; an implementation producing normal completion is rejected. -/
theorem nested_local_return_family_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (nestedLocalReturn name innerValue returnValue) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut) :
    ControlOutcomeRelated worldRelated loops (.word 0)
      (nestedLocalReturnOutcome name innerValue returnValue sourceFrame source) nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨sourceOut, origin, related, finalBound, finalScoped⟩ :=
    (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls .word .unsignedWord (nested_local_return_supported name innerValue returnValue)).backward
      loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  cases (nested_local_return_source_exact name innerValue returnValue sourceFrame source sourceOut).mp origin
  exact ⟨related, finalBound, finalScoped⟩

/-- Every actual lowered execution returns the authored word and retains the
allocation performed by the inner loop in its monotone local counter. -/
theorem nested_local_return_target_observations {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (nestedLocalReturn name innerValue returnValue) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut) :
    nativeOut.flow = .returned (encodeValue (.word returnValue)) ∧
      nativeOut.frame.nextLocal = sourceFrame.nextLocal + 1 ∧ nativeOut.flow ≠ .normal := by
  obtain ⟨related, _, _⟩ := nested_local_return_family_reflection
    sourceHeap sourceCalls targetHeap targetCalls name innerValue returnValue
    loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  have returned : nativeOut.flow = .returned (encodeValue (.word returnValue)) := by
    have flow := related.flow
    change ControlFlowRelated loops (.word 0) (.returned (.word returnValue)) nativeOut.flow at flow
    generalize nativeOut.flow = targetFlow at flow ⊢
    cases flow
    rfl
  refine ⟨returned, related.frame.nextLocal.trans
    (nested_local_return_counter name innerValue returnValue sourceFrame source), ?_⟩
  rw [returned]
  intro impossible
  cases impossible

/-- The first arm diverges, the second allocates through nested loop scopes,
    and the fallback returns without allocating a local cell. -/
def structuredDispatch (selector : Expr) (name : String)
    (innerValue returnValue fallback : NativeWord64.Word) : Statement :=
  .switch selector
    [(0, [.while (.bool true) []]), (1, [nestedLocalReturn name innerValue returnValue])]
    [.return (some (.word fallback))]

def dispatchSelectedOutcome {World : Type} (name : String)
    (innerValue returnValue : NativeWord64.Word) (frame : SourceFrame)
    (state : SourceState World) : SourceBlockOutcome World :=
  sourceCloseBlock frame (nestedLocalReturnOutcome name innerValue returnValue frame state)

theorem structured_dispatch_supported {selector : Expr}
    (pure : SourceShortCircuitExpression selector) (name : String)
    (innerValue returnValue fallback : NativeWord64.Word) :
    SourceLocalControlStatement (structuredDispatch selector name innerValue returnValue fallback) := by
  refine .switch pure ?_ (.cons (.returnValue (.guarded (.leaf (.word fallback)))) .nil)
  intro arm member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with first | second
  · subst arm
    exact .cons (.while (.guarded (.leaf (.bool true))) .nil) .nil
  · subst arm
    exact .cons (nested_local_return_supported name innerValue returnValue) .nil

theorem structured_dispatch_literal_lowering_exists (interface : Interface)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply)
    (key : NativeWord64.Word) (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (fresh : lookupVariable scope name = none) :
    ∃ output, NativeLowering.statement? interface .word loops scope
      (structuredDispatch (.word key) name innerValue returnValue fallback) supply = some output := by
  simp [structuredDispatch, nestedLocalReturn, localBreakLoop, NativeLowering.statement?,
    NativeLowering.cases?, NativeLowering.block?, NativeLowering.expression?, NativeLowering.pureTemporary,
    NativeIR.fresh, checkStatement, checkCases, checkBlock, inferExpr, fresh, validType]

theorem structured_dispatch_selected_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls
      (structuredDispatch (.word 1) name innerValue returnValue fallback) frame state out ↔
      out = dispatchSelectedOutcome name innerValue returnValue frame state := by
  rw [structuredDispatch, source_switch_statement_exact]
  constructor
  · rintro (⟨key, middle, inner, read, body, same⟩ | ⟨fault, after, read, same⟩)
    · cases (source_word_expression_exact 1 state _).mp read
      change SourceBlockEval interface heap calls [nestedLocalReturn name innerValue returnValue]
        frame state inner at body
      rcases (source_statements_cons_exact _ _ _ _ _).mp body with
        ⟨bodyFrame, post, first, tail⟩ | ⟨first, abrupt⟩
      · cases (nested_local_return_source_exact name innerValue returnValue frame state _).mp first
      · cases (nested_local_return_source_exact name innerValue returnValue frame state _).mp first
        exact same
    · cases (source_word_expression_exact 1 state _).mp read
  · intro same
    subst out
    refine Or.inl ⟨1, state, nestedLocalReturnOutcome name innerValue returnValue frame state,
      (source_word_expression_exact 1 state _).mpr rfl, ?_, rfl⟩
    change SourceBlockEval interface heap calls [nestedLocalReturn name innerValue returnValue]
      frame state (nestedLocalReturnOutcome name innerValue returnValue frame state)
    exact .stop (nested_local_return_source interface heap calls name innerValue returnValue frame state)
      (by intro impossible; cases impossible)

theorem structured_dispatch_fallback_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls
      (structuredDispatch (.word 2) name innerValue returnValue fallback) frame state out ↔
      out = ⟨.returned (.word fallback), frame, state⟩ := by
  rw [structuredDispatch, source_switch_statement_exact]
  constructor
  · rintro (⟨key, middle, inner, read, body, same⟩ | ⟨fault, after, read, same⟩)
    · cases (source_word_expression_exact 2 state _).mp read
      change SourceBlockEval interface heap calls [.return (some (.word fallback))] frame state inner at body
      cases (source_return_word_block_exact fallback state _ []).mp body
      exact same.trans (source_close_unchanged_block frame state _)
    · cases (source_word_expression_exact 2 state _).mp read
  · intro same
    subst out
    refine Or.inl ⟨2, state, ⟨.returned (.word fallback), frame, state⟩,
      (source_word_expression_exact 2 state _).mpr rfl, ?_, ?_⟩
    · exact (source_return_word_block_exact fallback state _ []).mpr rfl
    · exact (source_close_unchanged_block frame state _).symm

theorem structured_dispatch_divergent_source_refused {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (out : SourceBlockOutcome World) :
    ¬ SourceStatementEval interface heap calls
      (structuredDispatch (.word 0) name innerValue returnValue fallback) frame state out := by
  intro ran
  rcases (source_switch_statement_exact _ _ _ _ _ _).mp ran with
    ⟨key, middle, inner, read, body, same⟩ | ⟨fault, after, read, same⟩
  · cases (source_word_expression_exact 0 state _).mp read
    change SourceBlockEval interface heap calls [.while (.bool true) []] frame state inner at body
    cases body with
    | cons first tail => exact true_empty_loop_has_no_finite_source_run interface heap calls frame state _ first
    | stop first abrupt => exact true_empty_loop_has_no_finite_source_run interface heap calls frame state _ first
  · cases (source_word_expression_exact 0 state _).mp read

theorem structured_dispatch_fault_source_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (frame : SourceFrame) (state : SourceState World) (clear : state.fault = none)
    (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls
      (structuredDispatch (GuardedExpressionControls.wordBinary .div 7 0)
        name innerValue returnValue fallback) frame state out ↔
      out = ⟨.fault .divisionByZero, frame, sourcePoison state .divisionByZero⟩ := by
  rw [structuredDispatch, source_switch_statement_exact]
  have selector : ∀ result, SourceExprEval interface heap calls frame
      (GuardedExpressionControls.wordBinary .div 7 0) state result ↔
      result = ⟨.error .divisionByZero, sourcePoison state .divisionByZero⟩ := by
    intro result
    simpa only [show NativeWord64.sourceBinary .div 7 0 = .error .divisionByZero from rfl,
      Except.map, sourceFinish, sourceObserve, sourcePoison, clear] using
      GuardedExpressionControls.word_binary_source_exact interface heap calls frame .div 7 0 state clear result
  constructor
  · rintro (⟨key, middle, inner, read, body, same⟩ | ⟨fault, after, read, same⟩)
    · cases (selector _).mp read
    · cases (selector _).mp read
      exact same
  · intro same
    subst out
    exact Or.inr ⟨.divisionByZero, sourcePoison state .divisionByZero, (selector _).mpr rfl, rfl⟩

theorem duplicate_switch_keys_checked_refused (interface : Interface) (result : NativeType)
    (loops : Nat) (scope : Scope) :
    checkStatement interface result loops scope (.switch (.word 0) [(0, []), (0, [])] []) = none := by
  simp [checkStatement, inferExpr]

theorem duplicate_switch_keys_lowering_refused (interface : Interface) (result : NativeType)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply) :
    NativeLowering.statement? interface result loops scope
      (.switch (.word 0) [(0, []), (0, [])] []) supply = none := by
  rw [NativeLowering.statement?, duplicate_switch_keys_checked_refused]
  rfl

theorem structured_dispatch_fault_lowering_exists (interface : Interface)
    (loops : List NativeIR.LoopLabels) (scope : Scope) (supply : Supply)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    (fresh : lookupVariable scope name = none) :
    ∃ output, NativeLowering.statement? interface .word loops scope
      (structuredDispatch (GuardedExpressionControls.wordBinary .div 7 0)
        name innerValue returnValue fallback) supply = some output := by
  simp [structuredDispatch, nestedLocalReturn, localBreakLoop, GuardedExpressionControls.wordBinary,
    NativeLowering.statement?, NativeLowering.cases?, NativeLowering.block?, NativeLowering.expression?,
    NativeLowering.pureTemporary, NativeLowering.prependCode, NativeLowering.numericGuard,
    NativeIR.fresh, checkStatement, checkCases, checkBlock, inferExpr, binaryType, fresh, validType]

theorem structured_dispatch_selected_target_execution {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (.word 1) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    : ∃ nativeOut, TargetRun interface targetHeap targetCalls .word output.code output.code
        targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated loops (.word 0)
        (dispatchSelectedOutcome name innerValue returnValue sourceFrame source) nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  exact (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls .word .unsignedWord
    (structured_dispatch_supported (.guarded (.leaf (.word 1))) name innerValue returnValue fallback)).forward
    loopBounds compiled below coherent tagged clear frames states bounded hscope
    ((structured_dispatch_selected_source_exact name innerValue returnValue fallback sourceFrame source _).mpr rfl)


theorem structured_dispatch_selected_target_observations {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (.word 1) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut) :
    nativeOut.flow = .returned (encodeValue (.word returnValue)) ∧
      nativeOut.frame.nextLocal = sourceFrame.nextLocal + 1 ∧
      nativeOut.frame.bindings = sourceFrame.bindings := by
  obtain ⟨sourceOut, sourceRan, related, _, _⟩ :=
    (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls .word .unsignedWord
      (structured_dispatch_supported (.guarded (.leaf (.word 1))) name innerValue returnValue fallback)).backward
      loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  cases (structured_dispatch_selected_source_exact name innerValue returnValue fallback sourceFrame source _).mp sourceRan
  have returned : nativeOut.flow = .returned (encodeValue (.word returnValue)) := by
    have flow := related.flow
    change ControlFlowRelated loops (.word 0) (.returned (.word returnValue)) nativeOut.flow at flow
    generalize nativeOut.flow = targetFlow at flow ⊢
    cases flow
    rfl
  exact ⟨returned, related.frame.nextLocal, related.frame.bindings⟩


theorem structured_dispatch_fallback_target_observations {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (.word 2) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut) :
    nativeOut.flow = .returned (encodeValue (.word fallback)) ∧
      nativeOut.frame.nextLocal = sourceFrame.nextLocal ∧
      StateRelated worldRelated source nativeOut.state := by
  obtain ⟨sourceOut, sourceRan, related, _, _⟩ :=
    (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls .word .unsignedWord
      (structured_dispatch_supported (.guarded (.leaf (.word 2))) name innerValue returnValue fallback)).backward
      loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  cases (structured_dispatch_fallback_source_exact name innerValue returnValue fallback sourceFrame source _).mp sourceRan
  have returned : nativeOut.flow = .returned (encodeValue (.word fallback)) := by
    have flow := related.flow
    generalize nativeOut.flow = targetFlow at flow ⊢
    cases flow
    rfl
  exact ⟨returned, related.frame.nextLocal, related.state⟩


theorem structured_dispatch_divergent_target_refused {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (.word 0) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (nativeOut : TargetBlockOutcome TargetWorld) :
    ¬ TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut := by
  intro ran
  obtain ⟨sourceOut, sourceRan, related, _, _⟩ :=
    (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls .word .unsignedWord
      (structured_dispatch_supported (.guarded (.leaf (.word 0))) name innerValue returnValue fallback)).backward
      loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  exact structured_dispatch_divergent_source_refused name innerValue returnValue fallback
    sourceFrame source sourceOut sourceRan


theorem structured_dispatch_fault_target_execution {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (GuardedExpressionControls.wordBinary .div 7 0) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    : ∃ nativeOut, TargetRun interface targetHeap targetCalls .word output.code output.code
        targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated loops (.word 0)
        ⟨.fault .divisionByZero, sourceFrame, sourcePoison source .divisionByZero⟩ nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  exact (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
    targetHeap targetCalls .word .unsignedWord
    (structured_dispatch_supported (.guarded (GuardedExpressionControls.word_binary_guarded .div 7 0))
      name innerValue returnValue fallback)).forward
    loopBounds compiled below coherent tagged clear frames states bounded hscope
    ((structured_dispatch_fault_source_exact name innerValue returnValue fallback
      sourceFrame source clear _).mpr rfl)

theorem structured_dispatch_fault_target_observations {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (name : String) (innerValue returnValue fallback : NativeWord64.Word)
    {loops : List NativeIR.LoopLabels} {supply : Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface .word loops (sourceFrameScope sourceFrame)
      (structuredDispatch (GuardedExpressionControls.wordBinary .div 7 0) name innerValue returnValue fallback) supply = some output)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls .word output.code output.code targetFrame target nativeOut) :
    nativeOut.flow = .returned (.word 0) ∧ nativeOut.state.fault = some .divisionByZero ∧
      nativeOut.frame.nextLocal = sourceFrame.nextLocal ∧
      StateRelated worldRelated (sourcePoison source .divisionByZero) nativeOut.state := by
  obtain ⟨sourceOut, sourceRan, related, _, _⟩ :=
    (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
      targetHeap targetCalls .word .unsignedWord
      (structured_dispatch_supported (.guarded (GuardedExpressionControls.word_binary_guarded .div 7 0)) name innerValue returnValue fallback)).backward
      loopBounds compiled below coherent tagged clear frames states bounded hscope ran
  cases (structured_dispatch_fault_source_exact name innerValue returnValue fallback
    sourceFrame source clear _).mp sourceRan
  have returned : nativeOut.flow = .returned (.word 0) := by
    have flow := related.flow
    generalize nativeOut.flow = targetFlow at flow ⊢
    cases flow
    rfl
  exact ⟨returned, related.state.fault.trans (by simp [sourcePoison, clear]),
    related.frame.nextLocal, related.state⟩


def orderedParameterFunction : Function :=
  ⟨⟨"ordered-parameters", [⟨"first", .word⟩, ⟨"second", .word⟩], .word⟩,
    [.return (some (.variable "first")), .set (.variable "second") (.word 99)]⟩

def orderedParameterTarget : NativeIR.Function :=
  ⟨orderedParameterFunction.header,
    [.checkContextExists, .checkContext,
      .temporary 1 .word (.readLocal "first"), .return (.temporary 1 .word),
      .temporary 2 .word (.word (NativeWord64.encode 99)),
      .write (.localAddress "second" .word) (.temporary 2 .word)], 2⟩

/-- The compiler really emits the tail write. Its omission at runtime must
    follow from the preceding return, rather than from removing the source tail. -/
theorem ordered_parameter_function_actual_lowering (interface : Interface) :
    NativeLowering.function? interface orderedParameterFunction = some orderedParameterTarget := by
  simp only [NativeLowering.function?, orderedParameterFunction, orderedParameterTarget,
    checkFunction, checkBlock, checkStatement, inferExpr, inferLocation, lookupVariable,
    validType, returnsBlock, returnsStatement, NativeLowering.block?, NativeLowering.statement?,
    NativeLowering.expression?, NativeLowering.location?, NativeLowering.pureTemporary, NativeIR.fresh,
    List.all_cons, List.all_nil, List.map_cons, List.map_nil]
  have namesDistinct : decide ["first", "second"].Nodup = true := by decide +kernel
  rw [namesDistinct]
  rfl

theorem ordered_parameter_function_supported : SourceLocalControlBlock orderedParameterFunction.body :=
  .cons (.returnValue (.guarded (.leaf (.variable _))))
    (.cons (.set "second" (.guarded (.leaf (.word _)))) .nil)

def orderedParameterSourceFrame (storage : Nat) : SourceFrame :=
  ⟨storage, 2, [⟨"second", .word, 1⟩, ⟨"first", .word, 0⟩]⟩

def orderedParameterSourceState {World : Type} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World) : SourceState World :=
  { state with memory := (sourceStoreCell (sourceStoreCell state.memory storage 0 (.word first))
      storage 1 (.word second)) }

theorem ordered_parameter_source_binding {World : Type} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World) :
    sourceBindParameters orderedParameterFunction.header.parameters [.word first, .word second]
      ⟨storage, 0, []⟩ state =
      some (orderedParameterSourceFrame storage, orderedParameterSourceState storage first second state) := rfl

theorem ordered_parameter_source_readback {World : Type} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World) :
    sourceLocalValue (orderedParameterSourceFrame storage)
      (orderedParameterSourceState storage first second state) "first" = some (.word first) := by
  change (if storage = storage ∧ (0 : Nat) = 1 then some (.word second)
    else if storage = storage ∧ (0 : Nat) = 0 then some (.word first)
    else state.memory.cells storage 0).bind (sourceReadPath []) = some (.word first)
  simp only [and_self, if_false, if_true, Nat.zero_ne_one, and_false,
    eq_self, Option.bind_some, sourceReadPath]

theorem ordered_parameter_source_teardown {World : Type} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World)
    (fresh : sourceFreshFrame state.memory storage) :
    (sourceLeaveScope ⟨storage, 0, []⟩ (orderedParameterSourceFrame storage)
      (orderedParameterSourceState storage first second state)).2 = state := by
  have cells : (sourceDropLocals (orderedParameterSourceState storage first second state).memory
      storage 0 2).cells = state.memory.cells := by
    funext candidate position
    by_cases same : candidate = storage
    · subst candidate
      by_cases inside : position < 2
      · simp [sourceDropLocals, inside, fresh.1]
      · have notFirst : position ≠ 0 := by omega
        have notSecond : position ≠ 1 := by omega
        simp [sourceDropLocals, inside, orderedParameterSourceState, sourceStoreCell,
          notFirst, notSecond]
    · simp [sourceDropLocals, orderedParameterSourceState, sourceStoreCell, same]
  have memory : sourceDropLocals (orderedParameterSourceState storage first second state).memory
      storage 0 2 = state.memory :=
    congrArg (fun contents => SourceMemory.mk contents state.memory.owned) cells
  change { state with memory := (sourceDropLocals
    (orderedParameterSourceState storage first second state).memory storage 0 2) } = state
  rw [memory]

theorem ordered_parameter_source_expression_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls (orderedParameterSourceFrame storage) (.variable "first")
      (orderedParameterSourceState storage first second state) out ↔
      out = ⟨.ok (.word first), orderedParameterSourceState storage first second state⟩ := by
  rw [source_operand_free_expression_exact _ rfl]
  change (∃ value, sourceLocalValue _ _ "first" = some value ∧ out = ⟨.ok value, _⟩) ↔ _
  rw [ordered_parameter_source_readback]
  constructor
  · rintro ⟨value, same, exactOut⟩
    cases Option.some.inj same
    exact exactOut
  · intro exactOut
    exact ⟨.word first, rfl, exactOut⟩

theorem ordered_parameter_source_body_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceBlockEval interface heap calls orderedParameterFunction.body (orderedParameterSourceFrame storage)
      (orderedParameterSourceState storage first second state) out ↔
      out = ⟨.returned (.word first), orderedParameterSourceFrame storage,
        orderedParameterSourceState storage first second state⟩ := by
  constructor
  · intro ran
    cases ran with
    | cons returned _ => cases returned
    | stop returned _ =>
        cases returned with
        | returnValue evaluated =>
            cases (ordered_parameter_source_expression_exact storage first second state _).mp evaluated
            rfl
        | returnFault evaluated =>
            cases (ordered_parameter_source_expression_exact storage first second state _).mp evaluated
  · intro same
    subst out
    exact .stop (.returnValue
      ((ordered_parameter_source_expression_exact storage first second state _).mpr rfl))
      (by intro impossible; cases impossible)

theorem ordered_parameter_source_function {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (storage : Nat)
    (first second : NativeWord64.Word) (state : SourceState World)
    (clear : state.fault = none) (fresh : sourceFreshFrame state.memory storage) :
    SourceFunctionBody interface heap calls orderedParameterFunction [.word first, .word second]
      state ⟨.word first, state⟩ := by
  have ran := SourceFunctionBody.run (interface := interface) (heap := heap) (calls := calls)
    (function := orderedParameterFunction) clear fresh
    (ordered_parameter_source_binding storage first second state)
    ((ordered_parameter_source_body_exact storage first second state _).mpr rfl) rfl
  simpa only [ordered_parameter_source_teardown storage first second state fresh] using ran

theorem ordered_parameter_source_function_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (first second : NativeWord64.Word) (state : SourceState World) (clear : state.fault = none)
    {raw : SourceRawResult World}
    (ran : SourceFunctionBody interface heap calls orderedParameterFunction [.word first, .word second]
      state raw) : raw = ⟨.word first, state⟩ := by
  cases ran with
  | entryFault _arity failed _zero => rw [clear] at failed; cases failed
  | run _clear fresh parameters body returned =>
      rename_i storage frame bound out value
      have same := (ordered_parameter_source_binding storage first second state).symm.trans parameters
      cases Option.some.inj same
      cases (ordered_parameter_source_body_exact storage first second state _).mp body
      have sameValue : value = .word first := returned
      subst value
      rw [ordered_parameter_source_teardown storage first second state fresh]

/-- Reflection rules out a second parameter value or a tail write as an
    alternative successful observation of this actual compiled function. -/
theorem ordered_parameter_target_observations {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (first second : NativeWord64.Word) {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (clear : source.fault = none) (states : StateRelated worldRelated source target)
    {raw : TargetRawResult TargetWorld}
    (ran : TargetFunctionBody interface targetHeap targetCalls orderedParameterTarget
      [.word (NativeWord64.encode first), .word (NativeWord64.encode second)] target raw) :
    raw.value = .word (NativeWord64.encode first) ∧ StateRelated worldRelated source raw.state := by
  obtain ⟨sourceRaw, actualSource, related⟩ := local_control_function_reflection
    (sourceHeap := sourceHeap) (sourceCalls := sourceCalls)
    (ordered_parameter_function_actual_lowering interface) ordered_parameter_function_supported
    (SourceZero.word (interface := interface))
    (List.Forall₂.cons (SourceOuterTag.word first) (List.Forall₂.cons (SourceOuterTag.word second) .nil))
    states ran
  cases ordered_parameter_source_function_exact first second source clear actualSource
  exact ⟨related.value, related.state⟩

theorem ordered_parameter_target_execution {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (storage : Nat) (first second : NativeWord64.Word)
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (clear : source.fault = none) (fresh : sourceFreshFrame source.memory storage)
    (states : StateRelated worldRelated source target) :
    ∃ raw, TargetFunctionBody interface targetHeap targetCalls orderedParameterTarget
      [.word (NativeWord64.encode first), .word (NativeWord64.encode second)] target raw ∧
      raw.value = .word (NativeWord64.encode first) ∧ StateRelated worldRelated source raw.state := by
  obtain ⟨raw, actual, related⟩ := local_control_function_preservation
    (targetHeap := targetHeap) (targetCalls := targetCalls)
    (ordered_parameter_function_actual_lowering interface) ordered_parameter_function_supported
    (SourceZero.word (interface := interface))
    (List.Forall₂.cons (SourceOuterTag.word first) (List.Forall₂.cons (SourceOuterTag.word second) .nil))
    states (by intro failed; exact False.elim (failed clear))
    (ordered_parameter_source_function interface sourceHeap sourceCalls storage first second source clear fresh)
  exact ⟨raw, actual, related.value, related.state⟩

theorem duplicate_parameter_lookup_changes_on_reversal :
    ¬ ScopeLookupAgreement [("same", .word), ("same", .bool)]
      [("same", .bool), ("same", .word)] := by
  intro same
  have impossible := same "same"
  cases impossible

def duplicateParameterFunction : Function :=
  ⟨⟨"duplicate-parameters", [⟨"same", .word⟩, ⟨"same", .bool⟩], .unit⟩, []⟩

theorem duplicate_parameter_function_refused (interface : Interface) :
    NativeLowering.function? interface duplicateParameterFunction = none := rfl

theorem nonunit_fallthrough_function_refused (interface : Interface) :
    NativeLowering.function? interface ⟨⟨"missing-return", [], .word⟩, []⟩ = none := by
  simp [NativeLowering.function?, checkFunction, checkBlock, validType, returnsBlock]

theorem unit_fallthrough_function_lowering (interface : Interface) :
    NativeLowering.function? interface ⟨⟨"unit-fallthrough", [], .unit⟩, []⟩ =
      some ⟨⟨"unit-fallthrough", [], .unit⟩,
        [.checkContextExists, .checkContext, .return .unit], 0⟩ := by
  simp [NativeLowering.function?, checkFunction, checkBlock, validType, NativeLowering.block?]

/-- A source entry fault does not itself supply target invocation storage. -/
theorem faulted_source_entry_without_storage {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (state : SourceState World)
    (first second : NativeWord64.Word) :
    let occupied := { state with
      memory := ⟨fun _ _ => some (.word 7), fun _ => none⟩
      fault := some .divisionByZero }
    SourceFunctionBody interface heap calls orderedParameterFunction [.word first, .word second]
      occupied ⟨.word 0, occupied⟩ ∧
      ¬ ∃ storage, sourceFreshFrame occupied.memory storage := by
  constructor
  · exact .entryFault rfl rfl .word
  · rintro ⟨storage, fresh⟩
    have impossible := fresh.1 0
    cases impossible

theorem occupied_target_function_has_no_run {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (function : NativeIR.Function) (arguments : List TargetValue) (state : TargetState World)
    (raw : TargetRawResult World) :
    ¬ TargetFunctionBody interface heap calls function arguments
      { state with memory := ⟨fun _ _ => some (.word 7), fun _ => none⟩ } raw := by
  intro ran
  cases ran with
  | run fresh _parameters _body _returned =>
      have impossible := fresh.2 0
      cases impossible

end Mettapedia.GSLT.LanguageDef.NativeOps.ControlControls
