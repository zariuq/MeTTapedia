import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval

/-!
# Lexical statements and finite source loops

Every loop derivation contains its actual finite iterations. Break and
continue are loop flows; a switch preserves them. Lexical scope exit drops
only that scope's local cells, retaining caller writes, heap effects, external
effects and the sticky context fault. Assignment resolves its location before
evaluating its value. These relations impose no execution fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word Fault)

inductive SourceFlow where
  | normal | broke | continued
  | returned (value : SourceValue)
  | fault (fault : Fault)
  deriving Repr

structure SourceBlockOutcome (World : Type) where
  flow : SourceFlow
  frame : SourceFrame
  state : SourceState World

def sourceCloseBlock {World : Type} (marker : SourceFrame)
    (out : SourceBlockOutcome World) : SourceBlockOutcome World :=
  let closed := sourceLeaveScope marker out.frame out.state
  ⟨out.flow, closed.1, closed.2⟩

def sourceSelectCase (selector : Word) (cases : List (Word × List Statement))
    (otherwise : List Statement) : List Statement :=
  match cases.find? (fun arm => arm.1 == selector) with
  | some arm => arm.2
  | none => otherwise

/-- A property of every arm and the fallback holds for the source's actual
    ordered selection, without assuming that a matching key exists. -/
theorem source_select_case_property (property : List Statement → Prop)
    (value : Word) {arms : List (Word × List Statement)} {otherwise : List Statement}
    (supported : ∀ arm ∈ arms, property arm.2) (fallback : property otherwise) :
    property (sourceSelectCase value arms otherwise) := by
  induction arms with
  | nil => exact fallback
  | cons arm rest ih =>
      by_cases selected : arm.1 == value
      · simpa [sourceSelectCase, selected] using supported arm List.mem_cons_self
      · simpa [sourceSelectCase, selected] using
          ih (fun item member => supported item (List.mem_cons_of_mem _ member))

def sourceFreeFlow {World : Type} (frame : SourceFrame)
    (raw : SourceRawResult World) : SourceBlockOutcome World :=
  match raw.state.fault with
  | some fault => ⟨.fault fault, frame, raw.state⟩
  | none => ⟨.normal, frame, raw.state⟩

mutual
  inductive SourceStatementEval {World : Type} (interface : Interface)
      (heap : SourceHeapSemantics World) (calls : SourceCalls World) :
      Statement → SourceFrame → SourceState World → SourceBlockOutcome World → Prop where
    | declare {name : String} {type : NativeType} {initializer : Expr}
        {frame : SourceFrame} {before after : SourceState World} {value : SourceValue}
        (evaluated : SourceExprEval interface heap calls frame initializer before ⟨.ok value, after⟩) :
        SourceStatementEval interface heap calls (.declare name type initializer) frame before
          ⟨.normal, (sourceDeclareLocal frame after name type value).1,
            (sourceDeclareLocal frame after name type value).2⟩
    | declareFault {name : String} {type : NativeType} {initializer : Expr}
        {frame : SourceFrame} {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame initializer before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.declare name type initializer) frame before
          ⟨.fault fault, frame, after⟩
    | set {location value : Expr} {frame : SourceFrame}
        {before middle after : SourceState World} {address : Address} {replacement : SourceValue}
        {memory : SourceMemory}
        (located : SourceLocationEval interface heap calls frame location before ⟨.ok address, middle⟩)
        (evaluated : SourceExprEval interface heap calls frame value middle ⟨.ok replacement, after⟩)
        (written : sourceWrite after.memory address replacement = some memory) :
        SourceStatementEval interface heap calls (.set location value) frame before
          ⟨.normal, frame, { after with memory := memory }⟩
    | setLocationFault {location value : Expr} {frame : SourceFrame}
        {before after : SourceState World} {fault : Fault}
        (located : SourceLocationEval interface heap calls frame location before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.set location value) frame before
          ⟨.fault fault, frame, after⟩
    | setValueFault {location value : Expr} {frame : SourceFrame}
        {before middle after : SourceState World} {address : Address} {fault : Fault}
        (located : SourceLocationEval interface heap calls frame location before ⟨.ok address, middle⟩)
        (evaluated : SourceExprEval interface heap calls frame value middle ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.set location value) frame before
          ⟨.fault fault, frame, after⟩
    | branch {condition : Expr} {whenTrue whenFalse : List Statement} {selected : Bool}
        {frame : SourceFrame} {before middle : SourceState World} {out : SourceBlockOutcome World}
        (evaluated : SourceExprEval interface heap calls frame condition before ⟨.ok (.bool selected), middle⟩)
        (body : SourceBlockEval interface heap calls
          (if selected then whenTrue else whenFalse) frame middle out) :
        SourceStatementEval interface heap calls (.branch condition whenTrue whenFalse) frame before
          (sourceCloseBlock frame out)
    | branchFault {condition : Expr} {whenTrue whenFalse : List Statement}
        {frame : SourceFrame} {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame condition before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.branch condition whenTrue whenFalse) frame before
          ⟨.fault fault, frame, after⟩
    | whileDone {condition : Expr} {body : List Statement} {frame : SourceFrame}
        {before after : SourceState World}
        (tested : SourceExprEval interface heap calls frame condition before ⟨.ok (.bool false), after⟩) :
        SourceStatementEval interface heap calls (.while condition body) frame before
          ⟨.normal, frame, after⟩
    | whileFault {condition : Expr} {body : List Statement} {frame : SourceFrame}
        {before after : SourceState World} {fault : Fault}
        (tested : SourceExprEval interface heap calls frame condition before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.while condition body) frame before
          ⟨.fault fault, frame, after⟩
    | whileRepeat {condition : Expr} {body : List Statement} {frame : SourceFrame}
        {before middle : SourceState World} {iteration out : SourceBlockOutcome World}
        (tested : SourceExprEval interface heap calls frame condition before ⟨.ok (.bool true), middle⟩)
        (ran : SourceBlockEval interface heap calls body frame middle iteration)
        (again : iteration.flow = .normal ∨ iteration.flow = .continued)
        (rest : SourceStatementEval interface heap calls (.while condition body)
          (sourceCloseBlock frame iteration).frame (sourceCloseBlock frame iteration).state out) :
        SourceStatementEval interface heap calls (.while condition body) frame before out
    | whileBreak {condition : Expr} {body : List Statement} {frame : SourceFrame}
        {before middle : SourceState World} {iteration : SourceBlockOutcome World}
        (tested : SourceExprEval interface heap calls frame condition before ⟨.ok (.bool true), middle⟩)
        (ran : SourceBlockEval interface heap calls body frame middle iteration)
        (broke : iteration.flow = .broke) :
        SourceStatementEval interface heap calls (.while condition body) frame before
          { sourceCloseBlock frame iteration with flow := .normal }
    | whileStop {condition : Expr} {body : List Statement} {frame : SourceFrame}
        {before middle : SourceState World} {iteration : SourceBlockOutcome World}
        (tested : SourceExprEval interface heap calls frame condition before ⟨.ok (.bool true), middle⟩)
        (ran : SourceBlockEval interface heap calls body frame middle iteration)
        (stopped : (∃ value, iteration.flow = .returned value) ∨
          (∃ fault, iteration.flow = .fault fault)) :
        SourceStatementEval interface heap calls (.while condition body) frame before
          (sourceCloseBlock frame iteration)
    | switch {selector : Expr} {cases : List (Word × List Statement)} {otherwise : List Statement}
        {frame : SourceFrame} {before middle : SourceState World} {value : Word}
        {out : SourceBlockOutcome World}
        (evaluated : SourceExprEval interface heap calls frame selector before ⟨.ok (.word value), middle⟩)
        (selected : SourceBlockEval interface heap calls (sourceSelectCase value cases otherwise)
          frame middle out) :
        SourceStatementEval interface heap calls (.switch selector cases otherwise) frame before
          (sourceCloseBlock frame out)
    | switchFault {selector : Expr} {cases : List (Word × List Statement)} {otherwise : List Statement}
        {frame : SourceFrame} {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame selector before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.switch selector cases otherwise) frame before
          ⟨.fault fault, frame, after⟩
    | break (frame : SourceFrame) (state : SourceState World) :
        SourceStatementEval interface heap calls .break frame state ⟨.broke, frame, state⟩
    | continue (frame : SourceFrame) (state : SourceState World) :
        SourceStatementEval interface heap calls .continue frame state ⟨.continued, frame, state⟩
    | effect {expression : Expr} {frame : SourceFrame}
        {before after : SourceState World} {value : SourceValue}
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.ok value, after⟩) :
        SourceStatementEval interface heap calls (.effect expression) frame before
          ⟨.normal, frame, after⟩
    | effectFault {expression : Expr} {frame : SourceFrame}
        {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.effect expression) frame before
          ⟨.fault fault, frame, after⟩
    | free {expression : Expr} {frame : SourceFrame} {element : NativeType}
        {before middle : SourceState World} {value : SourceValue} {raw : SourceRawResult World}
        (type : inferExpr interface (sourceFrameScope frame) expression = some (.ref element) ∨
          inferExpr interface (sourceFrameScope frame) expression = some (.array element))
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.ok value, middle⟩)
        (released : heap.release element value middle raw) :
        SourceStatementEval interface heap calls (.free expression) frame before (sourceFreeFlow frame raw)
    | freeFault {expression : Expr} {frame : SourceFrame}
        {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.free expression) frame before ⟨.fault fault, frame, after⟩
    | returnUnit (frame : SourceFrame) (state : SourceState World) :
        SourceStatementEval interface heap calls (.return none) frame state ⟨.returned .unit, frame, state⟩
    | returnValue {expression : Expr} {frame : SourceFrame}
        {before after : SourceState World} {value : SourceValue}
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.ok value, after⟩) :
        SourceStatementEval interface heap calls (.return (some expression)) frame before
          ⟨.returned value, frame, after⟩
    | returnFault {expression : Expr} {frame : SourceFrame}
        {before after : SourceState World} {fault : Fault}
        (evaluated : SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩) :
        SourceStatementEval interface heap calls (.return (some expression)) frame before
          ⟨.fault fault, frame, after⟩
    | block {body : List Statement} {frame : SourceFrame} {before : SourceState World}
        {out : SourceBlockOutcome World} (ran : SourceBlockEval interface heap calls body frame before out) :
        SourceStatementEval interface heap calls (.block body) frame before (sourceCloseBlock frame out)

  inductive SourceBlockEval {World : Type} (interface : Interface)
      (heap : SourceHeapSemantics World) (calls : SourceCalls World) :
      List Statement → SourceFrame → SourceState World → SourceBlockOutcome World → Prop where
    | nil (frame : SourceFrame) (state : SourceState World) :
        SourceBlockEval interface heap calls [] frame state ⟨.normal, frame, state⟩
    | cons {first : Statement} {rest : List Statement}
        {beforeFrame middleFrame : SourceFrame} {before middle : SourceState World}
        {out : SourceBlockOutcome World}
        (firstRun : SourceStatementEval interface heap calls first beforeFrame before
          ⟨.normal, middleFrame, middle⟩)
        (restRun : SourceBlockEval interface heap calls rest middleFrame middle out) :
        SourceBlockEval interface heap calls (first :: rest) beforeFrame before out
    | stop {first : Statement} {rest : List Statement}
        {beforeFrame : SourceFrame} {before : SourceState World} {out : SourceBlockOutcome World}
        (firstRun : SourceStatementEval interface heap calls first beforeFrame before out)
        (abrupt : out.flow ≠ .normal) :
        SourceBlockEval interface heap calls (first :: rest) beforeFrame before out
end

theorem source_close_block_preserves_flow {World : Type} (marker : SourceFrame)
    (out : SourceBlockOutcome World) : (sourceCloseBlock marker out).flow = out.flow := rfl

theorem source_close_block_preserves_context_fault {World : Type} (marker : SourceFrame)
    (out : SourceBlockOutcome World) : (sourceCloseBlock marker out).state.fault = out.state.fault := rfl

theorem source_close_block_preserves_external {World : Type} (marker : SourceFrame)
    (out : SourceBlockOutcome World) : (sourceCloseBlock marker out).state.external = out.state.external := rfl

theorem false_while_skips_body {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (body : List Statement) (frame : SourceFrame) (state : SourceState World) :
    SourceStatementEval interface heap calls (.while (.bool false) body) frame state
      ⟨.normal, frame, state⟩ :=
  .whileDone (source_bool_evaluates interface heap calls frame false state)

theorem first_return_skips_remaining_statements {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World)
    (rest : List Statement) (frame : SourceFrame) (state : SourceState World) :
    SourceBlockEval interface heap calls (.return none :: rest) frame state
      ⟨.returned .unit, frame, state⟩ :=
  .stop (.returnUnit frame state) (by intro impossible; cases impossible)

/-- A finite while run either finishes at its current test or contains the
actual first body execution. Repetition uses the cleaned post-frame and
state, including the body's writes and monotone local counter. -/
theorem source_while_iteration_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (condition : Expr) (body : List Statement) (frame : SourceFrame)
    (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.while condition body) frame state out ↔
      (∃ after, SourceExprEval interface heap calls frame condition state
          ⟨.ok (.bool false), after⟩ ∧ out = ⟨.normal, frame, after⟩) ∨
      (∃ fault after, SourceExprEval interface heap calls frame condition state
          ⟨.error fault, after⟩ ∧ out = ⟨.fault fault, frame, after⟩) ∨
      (∃ middle inner,
        SourceExprEval interface heap calls frame condition state ⟨.ok (.bool true), middle⟩ ∧
        SourceBlockEval interface heap calls body frame middle inner ∧
        match inner.flow with
        | .normal | .continued => SourceStatementEval interface heap calls (.while condition body)
            (sourceCloseBlock frame inner).frame (sourceCloseBlock frame inner).state out
        | .broke => out = { sourceCloseBlock frame inner with flow := .normal }
        | .returned _ | .fault _ => out = sourceCloseBlock frame inner) := by
  constructor
  · intro ran
    cases ran with
    | whileDone tested => exact .inl ⟨_, tested, rfl⟩
    | whileFault tested => exact .inr (.inl ⟨_, _, tested, rfl⟩)
    | whileRepeat tested bodyRan again rest =>
        refine .inr (.inr ⟨_, _, tested, bodyRan, ?_⟩)
        rcases again with normal | continued
        · rw [normal]
          exact rest
        · rw [continued]
          exact rest
    | whileBreak tested bodyRan broke =>
        exact .inr (.inr ⟨_, _, tested, bodyRan, by rw [broke]⟩)
    | whileStop tested bodyRan stopped =>
        refine .inr (.inr ⟨_, _, tested, bodyRan, ?_⟩)
        rcases stopped with ⟨value, returned⟩ | ⟨fault, failed⟩
        · rw [returned]
        · rw [failed]
  · rintro (⟨after, tested, same⟩ | ⟨fault, after, tested, same⟩ |
      ⟨middle, ⟨flow, after, post⟩, tested, bodyRan, following⟩)
    · subst out
      exact .whileDone tested
    · subst out
      exact .whileFault tested
    · cases flow with
      | normal => exact .whileRepeat tested bodyRan (.inl rfl) following
      | continued => exact .whileRepeat tested bodyRan (.inr rfl) following
      | broke => cases following; exact .whileBreak tested bodyRan rfl
      | returned value =>
          cases following
          exact .whileStop tested bodyRan (.inl ⟨value, rfl⟩)
      | fault fault =>
          cases following
          exact .whileStop tested bodyRan (.inr ⟨fault, rfl⟩)

/-- Normal body completion and an explicit continue both request the next
loop iteration. Break, return and fault retain their original distinction. -/
def sourceLoopBackedge {World : Type} (out : SourceBlockOutcome World) : SourceBlockOutcome World :=
  match out.flow with
  | .normal => { out with flow := .continued }
  | _ => out

theorem source_close_backedge_frame_state {World : Type} (marker : SourceFrame)
    (out : SourceBlockOutcome World) :
    (sourceCloseBlock marker (sourceLoopBackedge out)).frame = (sourceCloseBlock marker out).frame ∧
      (sourceCloseBlock marker (sourceLoopBackedge out)).state = (sourceCloseBlock marker out).state := by
  cases h : out.flow <;> simp [sourceLoopBackedge, h, sourceCloseBlock]

theorem source_loop_backedge_not_normal {World : Type} (out : SourceBlockOutcome World) :
    (sourceLoopBackedge out).flow ≠ .normal := by
  cases h : out.flow <;> simp [sourceLoopBackedge, h]

theorem source_loop_backedge_continue_iff {World : Type} (out : SourceBlockOutcome World) :
    (sourceLoopBackedge out).flow = .continued ↔ out.flow = .normal ∨ out.flow = .continued := by
  cases h : out.flow <;> simp [sourceLoopBackedge, h]

theorem source_loop_backedge_break_iff {World : Type} (out : SourceBlockOutcome World) :
    (sourceLoopBackedge out).flow = .broke ↔ out.flow = .broke := by
  cases h : out.flow <;> simp [sourceLoopBackedge, h]

theorem source_loop_backedge_stopping_iff {World : Type} (out : SourceBlockOutcome World) :
    ((∃ value, (sourceLoopBackedge out).flow = .returned value) ∨
      (∃ fault, (sourceLoopBackedge out).flow = .fault fault)) ↔
      ((∃ value, out.flow = .returned value) ∨ (∃ fault, out.flow = .fault fault)) := by
  cases h : out.flow <;> simp [sourceLoopBackedge, h]

/-- Induction keeps each finite source iteration and the actual cleaned
entry to its following run. The body is supplied as its original derivation. -/
theorem source_while_run_induction {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (condition : Expr) (body : List Statement)
    (P : SourceFrame → SourceState World → SourceBlockOutcome World → Prop)
    (doneCase : ∀ frame state after,
      SourceExprEval interface heap calls frame condition state ⟨.ok (.bool false), after⟩ →
      P frame state ⟨.normal, frame, after⟩)
    (faultCase : ∀ frame state after fault,
      SourceExprEval interface heap calls frame condition state ⟨.error fault, after⟩ →
      P frame state ⟨.fault fault, frame, after⟩)
    (repeatCase : ∀ frame state middle inner out,
      SourceExprEval interface heap calls frame condition state ⟨.ok (.bool true), middle⟩ →
      SourceBlockEval interface heap calls body frame middle inner →
      (inner.flow = .normal ∨ inner.flow = .continued) →
      P (sourceCloseBlock frame inner).frame (sourceCloseBlock frame inner).state out → P frame state out)
    (breakCase : ∀ frame state middle inner,
      SourceExprEval interface heap calls frame condition state ⟨.ok (.bool true), middle⟩ →
      SourceBlockEval interface heap calls body frame middle inner → inner.flow = .broke →
      P frame state { sourceCloseBlock frame inner with flow := .normal })
    (stopCase : ∀ frame state middle inner,
      SourceExprEval interface heap calls frame condition state ⟨.ok (.bool true), middle⟩ →
      SourceBlockEval interface heap calls body frame middle inner →
      ((∃ value, inner.flow = .returned value) ∨ (∃ fault, inner.flow = .fault fault)) →
      P frame state (sourceCloseBlock frame inner))
    {frame : SourceFrame} {state : SourceState World} {out : SourceBlockOutcome World}
    (ran : SourceStatementEval interface heap calls (.while condition body) frame state out) :
    P frame state out := by
  generalize loopEq : Statement.while condition body = statement at ran
  induction ran using SourceStatementEval.rec
    (motive_2 := fun _ _ _ _ _ => True) with
  | whileDone tested => cases loopEq; exact doneCase _ _ _ tested
  | whileFault tested => cases loopEq; exact faultCase _ _ _ _ tested
  | whileRepeat tested bodyRan again following bodyIH followingIH =>
      cases loopEq
      exact repeatCase _ _ _ _ _ tested bodyRan again (followingIH rfl)
  | whileBreak tested bodyRan broke bodyIH =>
      cases loopEq
      exact breakCase _ _ _ _ tested bodyRan broke
  | whileStop tested bodyRan stopped bodyIH =>
      cases loopEq
      exact stopCase _ _ _ _ tested bodyRan stopped
  | nil => exact True.intro
  | cons => exact True.intro
  | stop => exact True.intro
  | _ => cases loopEq

end Mettapedia.GSLT.LanguageDef.NativeOps
