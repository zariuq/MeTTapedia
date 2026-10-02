import Mettapedia.GSLT.LanguageDef.NativeOpsStatementBoundaries

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

end Mettapedia.GSLT.LanguageDef.NativeOps.ControlControls
