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

end Mettapedia.GSLT.LanguageDef.NativeOps
