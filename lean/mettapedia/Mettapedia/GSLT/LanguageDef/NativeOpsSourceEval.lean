import Mettapedia.GSLT.LanguageDef.NativeOpsStack
import Mettapedia.GSLT.LanguageDef.NativeOpsDataHelpers
import Mettapedia.GSLT.LanguageDef.NativeOpsZero
import Mettapedia.GSLT.LanguageDef.NativeOpsTyping

/-!
# Finite evaluation of authored operational expressions

Evaluation is a finite relation, without execution fuel or a recursion limit.
Expressions evaluate operands from left to right. Locations are evaluated
before assignment values. Missing live cells and ill-typed dynamic operands
have no transition. Context faults preserve the exact post-state. Allocation
and release are separate raw shared-runtime relations: their concrete guards,
table effects and physical allocator contracts must be instantiated, rather
than assumed to provide a compiler or a guest-kernel theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word Fault)

structure SourceHeapSemantics (World : Type) where
  width : NativeType → Word
  allocate : NativeType → Word → SourceState World → SourceRawResult World → Prop
  release : NativeType → SourceValue → SourceState World → SourceRawResult World → Prop

abbrev SourceCalls (World : Type) :=
  String → List SourceValue → SourceState World → SourceValue → SourceState World → Prop

structure SourceLocationOutcome (World : Type) where
  result : Except Fault Address
  state : SourceState World

structure SourceArgumentsOutcome (World : Type) where
  result : Except Fault (List SourceValue)
  state : SourceState World

def sourceNext {World : Type} (first : SourceOutcome World)
    (success : SourceValue → SourceState World → Prop) (out : SourceOutcome World) : Prop :=
  match first.result with
  | .ok value => success value first.state
  | .error fault => out = ⟨.error fault, first.state⟩

def sourceLocationNext {World : Type} (first : SourceLocationOutcome World)
    (success : Address → SourceState World → Prop) (out : SourceOutcome World) : Prop :=
  match first.result with
  | .ok address => success address first.state
  | .error fault => out = ⟨.error fault, first.state⟩

def sourceArgumentsNext {World : Type} (first : SourceArgumentsOutcome World)
    (success : List SourceValue → SourceState World → Prop) (out : SourceOutcome World) : Prop :=
  match first.result with
  | .ok values => success values first.state
  | .error fault => out = ⟨.error fault, first.state⟩

def sourceReferenceLocation {World : Type} (raw : SourceRawResult World)
    (out : SourceLocationOutcome World) : Prop :=
  match raw.state.fault with
  | some fault => out = ⟨.error fault, raw.state⟩
  | none => ∃ address, raw.value = .reference (some address) ∧ out = ⟨.ok address, raw.state⟩

def sourceMemberIndex? : List Parameter → String → Option Nat
  | [], _ => none
  | field :: rest, name =>
      if field.name = name then some 0 else (sourceMemberIndex? rest name).map Nat.succ

def sourceFieldIndex? (interface : Interface) (record member : String) : Option Nat := do
  let declaration ← lookupRecord interface record
  sourceMemberIndex? declaration.fields member

def sourceFrameScope (frame : SourceFrame) : Scope :=
  frame.bindings.map (fun binding => (binding.name, binding.type))

def sourceFieldAddress (address : Address) (index : Nat) : Address :=
  { address with fields := address.fields ++ [index] }

/-- The initialization loop writes only through defined live locations. -/
inductive SourceInitialize : Option Address → Nat → SourceValue → SourceMemory → SourceMemory → Prop
  | empty (address : Option Address) (value : SourceValue) (memory : SourceMemory) :
      SourceInitialize address 0 value memory memory
  | next {address : Address} {count : Nat} {value : SourceValue}
      {before middle after : SourceMemory}
      (wrote : sourceWrite before address value = some middle)
      (rest : SourceInitialize (some (advanceAddress address 1)) count value middle after) :
      SourceInitialize (some address) (count + 1) value before after

def sourceInitializeResult {World : Type} (interface : Interface) (element : NativeType)
    (count : Word) (raw : SourceRawResult World) (array : Bool) (out : SourceOutcome World) : Prop :=
  match raw.state.fault with
  | some fault => out = ⟨.error fault, raw.state⟩
  | none => ∃ address zero memory,
      raw.value = .reference address ∧ SourceZero interface element zero ∧
      SourceInitialize address count.val zero raw.state.memory memory ∧
      out = ⟨.ok (if array then .array element address count else .reference address),
        { raw.state with memory := memory }⟩


def sourceStrictOperands? : Expr → Option (List Expr)
  | .word _ | .byte _ | .bool _ | .variable _ | .zero _ | .null _ | .new _ => some []
  | .newArray _ count | .length count | .load count | .unary _ count => some [count]
  | .field base _ => some [base]
  | .index array index => some [array, index]
  | .slice array start count => some [array, start, count]
  | .call _ arguments => some arguments
  | .binary .and _ _ | .binary .or _ _ | .address _ => none
  | .binary _ left right => some [left, right]

def sourceStrictLocationOperands? (interface : Interface) (frame : SourceFrame) :
    Expr → Option (List Expr)
  | .variable _ => some []
  | .index array index => some [array, index]
  | .load reference => some [reference]
  | .field base _ => do
      match ← inferExpr interface (sourceFrameScope frame) base with
      | .ref (.named _) => some [base]
      | _ => none
  | _ => none

def sourcePrimitiveLocation {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (frame : SourceFrame)
    (location : Expr) (arguments : List SourceValue) (state : SourceState World)
    (out : SourceLocationOutcome World) : Prop :=
  match location, arguments with
  | .variable name, [] => ∃ address, sourceLocalAddress frame name = some address ∧
      out = ⟨.ok address, state⟩
  | .field base member, [.reference pointer] => ∃ record,
      inferExpr interface (sourceFrameScope frame) base = some (.ref (.named record)) ∧
      let raw := sourceReferenceCall state pointer
      match raw.state.fault with
      | some fault => out = ⟨.error fault, raw.state⟩
      | none => ∃ address index, pointer = some address ∧
        sourceFieldIndex? interface record member = some index ∧
        out = ⟨.ok (sourceFieldAddress address index), raw.state⟩
  | .index _ _, [.array element pointer length, .word index] =>
      sourceReferenceLocation (sourceIndexCall state length (heap.width element) index pointer) out
  | .load _, [.reference pointer] =>
      let raw := sourceReferenceCall state pointer
      match raw.state.fault with
      | some fault => out = ⟨.error fault, raw.state⟩
      | none => ∃ address, pointer = some address ∧ out = ⟨.ok address, raw.state⟩
  | _, _ => False

def sourcePrimitive {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (expression : Expr) (arguments : List SourceValue) (state : SourceState World)
    (out : SourceOutcome World) : Prop :=
  match expression, arguments with
  | .word value, [] => out = ⟨.ok (.word value), state⟩
  | .byte value, [] => out = ⟨.ok (.byte value), state⟩
  | .bool value, [] => out = ⟨.ok (.bool value), state⟩
  | .variable name, [] => ∃ value, sourceLocalValue frame state name = some value ∧
      out = ⟨.ok value, state⟩
  | .zero type, [] => ∃ value, SourceZero interface type value ∧ out = ⟨.ok value, state⟩
  | .null (.ref _), [] => out = ⟨.ok (.reference none), state⟩
  | .new element, [] => ∃ raw, heap.allocate element 1 state raw ∧
      sourceInitializeResult interface element 1 raw false out
  | .newArray element _, [.word count] => ∃ raw, heap.allocate element count state raw ∧
      sourceInitializeResult interface element count raw true out
  | .field _ member, [.record name fields] => ∃ index value,
      sourceFieldIndex? interface name member = some index ∧ fields[index]? = some value ∧
      out = ⟨.ok value, state⟩
  | .field _ _, [.reference _] | .index _ _, _ | .load _, _ => ∃ location,
      sourcePrimitiveLocation interface heap frame expression arguments state location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ out = ⟨.ok value, post⟩) out
  | .length _, [.array _ _ length] => out = ⟨.ok (.word length), state⟩
  | .slice _ _ _, [.array element pointer length, .word start, .word count] =>
      let raw := sourceSliceCall state length (heap.width element) start count pointer
      match raw.state.fault with
      | some fault => out = ⟨.error fault, raw.state⟩
      | none => ∃ pointer, raw.value = .reference pointer ∧
        out = ⟨.ok (.array element pointer count), raw.state⟩
  | .call name _, values => ∃ raw final, calls name values state raw final ∧
      out = sourceObserve final raw
  | .unary operation _, [value] => ∃ result, sourceUnaryOp operation value = some result ∧
      out = ⟨.ok result, state⟩
  | .binary operation _ _, [left, right] => ∃ result,
      operation ≠ .and ∧ operation ≠ .or ∧ sourceBinaryOp operation left right = some result ∧
      out = sourceFinish state result
  | _, _ => False

mutual
  inductive SourceExprEval {World : Type} (interface : Interface)
      (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame) :
      Expr → SourceState World → SourceOutcome World → Prop where
    | strict {expression : Expr} {arguments : List Expr} {values : List SourceValue}
        {before middle : SourceState World} {out : SourceOutcome World}
        (operands : sourceStrictOperands? expression = some arguments)
        (evaluated : SourceArgumentsEval interface heap calls frame arguments before ⟨.ok values, middle⟩)
        (operation : sourcePrimitive interface heap calls frame expression values middle out) :
        SourceExprEval interface heap calls frame expression before out
    | strictFault {expression : Expr} {arguments : List Expr} {fault : Fault}
        {before after : SourceState World}
        (operands : sourceStrictOperands? expression = some arguments)
        (evaluated : SourceArgumentsEval interface heap calls frame arguments before ⟨.error fault, after⟩) :
        SourceExprEval interface heap calls frame expression before ⟨.error fault, after⟩
    | address {expression : Expr} {before after : SourceState World} {address : Address}
        (located : SourceLocationEval interface heap calls frame expression before ⟨.ok address, after⟩) :
        SourceExprEval interface heap calls frame (.address expression) before
          ⟨.ok (.reference (some address)), after⟩
    | addressFault {expression : Expr} {before after : SourceState World} {fault : Fault}
        (located : SourceLocationEval interface heap calls frame expression before ⟨.error fault, after⟩) :
        SourceExprEval interface heap calls frame (.address expression) before ⟨.error fault, after⟩
    | andFalse {left right : Expr} {before after : SourceState World}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.ok (.bool false), after⟩) :
        SourceExprEval interface heap calls frame (.binary .and left right) before ⟨.ok (.bool false), after⟩
    | andTrue {left right : Expr} {before middle : SourceState World} {out : SourceOutcome World}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.ok (.bool true), middle⟩)
        (rightRun : SourceExprEval interface heap calls frame right middle out) :
        SourceExprEval interface heap calls frame (.binary .and left right) before out
    | andFault {left right : Expr} {before after : SourceState World} {fault : Fault}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩) :
        SourceExprEval interface heap calls frame (.binary .and left right) before ⟨.error fault, after⟩
    | orTrue {left right : Expr} {before after : SourceState World}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.ok (.bool true), after⟩) :
        SourceExprEval interface heap calls frame (.binary .or left right) before ⟨.ok (.bool true), after⟩
    | orFalse {left right : Expr} {before middle : SourceState World} {out : SourceOutcome World}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.ok (.bool false), middle⟩)
        (rightRun : SourceExprEval interface heap calls frame right middle out) :
        SourceExprEval interface heap calls frame (.binary .or left right) before out
    | orFault {left right : Expr} {before after : SourceState World} {fault : Fault}
        (leftRun : SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩) :
        SourceExprEval interface heap calls frame (.binary .or left right) before ⟨.error fault, after⟩

  inductive SourceLocationEval {World : Type} (interface : Interface)
      (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame) :
      Expr → SourceState World → SourceLocationOutcome World → Prop where
    | strict {expression : Expr} {arguments : List Expr} {values : List SourceValue}
        {before middle : SourceState World} {out : SourceLocationOutcome World}
        (operands : sourceStrictLocationOperands? interface frame expression = some arguments)
        (evaluated : SourceArgumentsEval interface heap calls frame arguments before ⟨.ok values, middle⟩)
        (operation : sourcePrimitiveLocation interface heap frame expression values middle out) :
        SourceLocationEval interface heap calls frame expression before out
    | strictFault {expression : Expr} {arguments : List Expr} {fault : Fault}
        {before after : SourceState World}
        (operands : sourceStrictLocationOperands? interface frame expression = some arguments)
        (evaluated : SourceArgumentsEval interface heap calls frame arguments before ⟨.error fault, after⟩) :
        SourceLocationEval interface heap calls frame expression before ⟨.error fault, after⟩
    | fieldValue {base : Expr} {member record : String} {before after : SourceState World}
        {address : Address} {index : Nat}
        (type : inferExpr interface (sourceFrameScope frame) base = some (.named record))
        (located : SourceLocationEval interface heap calls frame base before ⟨.ok address, after⟩)
        (field : sourceFieldIndex? interface record member = some index) :
        SourceLocationEval interface heap calls frame (.field base member) before
          ⟨.ok (sourceFieldAddress address index), after⟩
    | fieldValueFault {base : Expr} {member record : String} {before after : SourceState World}
        {fault : Fault}
        (type : inferExpr interface (sourceFrameScope frame) base = some (.named record))
        (located : SourceLocationEval interface heap calls frame base before ⟨.error fault, after⟩) :
        SourceLocationEval interface heap calls frame (.field base member) before ⟨.error fault, after⟩

  inductive SourceArgumentsEval {World : Type} (interface : Interface)
      (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame) :
      List Expr → SourceState World → SourceArgumentsOutcome World → Prop where
    | nil (state : SourceState World) :
        SourceArgumentsEval interface heap calls frame [] state ⟨.ok [], state⟩
    | cons {first : Expr} {rest : List Expr} {value : SourceValue}
        {before middle : SourceState World} {out : SourceArgumentsOutcome World}
        (firstRun : SourceExprEval interface heap calls frame first before ⟨.ok value, middle⟩)
        (restRun : SourceArgumentsEval interface heap calls frame rest middle out) :
        SourceArgumentsEval interface heap calls frame (first :: rest) before
          ⟨out.result.map (value :: ·), out.state⟩
    | consFault {first : Expr} {rest : List Expr} {fault : Fault}
        {before after : SourceState World}
        (firstRun : SourceExprEval interface heap calls frame first before ⟨.error fault, after⟩) :
        SourceArgumentsEval interface heap calls frame (first :: rest) before ⟨.error fault, after⟩
end

theorem source_bool_evaluates {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (value : Bool) (state : SourceState World) :
    SourceExprEval interface heap calls frame (.bool value) state ⟨.ok (.bool value), state⟩ :=
  .strict rfl (.nil state) rfl

theorem initialize_nonempty_null_is_stuck (count : Nat) (value : SourceValue)
    (before after : SourceMemory) : ¬ SourceInitialize none (count + 1) value before after := by
  intro initialized
  cases initialized

theorem false_and_does_not_evaluate_right {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (right : Expr) (state : SourceState World) :
    SourceExprEval interface heap calls frame (.binary .and (.bool false) right) state
      ⟨.ok (.bool false), state⟩ :=
  .andFalse (source_bool_evaluates interface heap calls frame false state)

theorem true_or_does_not_evaluate_right {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (right : Expr) (state : SourceState World) :
    SourceExprEval interface heap calls frame (.binary .or (.bool true) right) state
      ⟨.ok (.bool true), state⟩ :=
  .orTrue (source_bool_evaluates interface heap calls frame true state)

end Mettapedia.GSLT.LanguageDef.NativeOps
