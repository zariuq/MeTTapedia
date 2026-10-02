import Mettapedia.GSLT.LanguageDef.NativeOpsTargetValues

/-!
# Finite execution of independently admitted native control

The target is the typed IR admitted from the actual C fragment. Operations,
context checks, lexical scopes and label transfers retain their emitted order.
A faulting helper first returns its raw default and exact post-state; the
following context check returns the function's typed default. Jumps unwind
inner scopes before they resume at an enclosing label. Undefined reads/writes
have no derivation. This calculus describes live-context function invocation,
the explicit ABI domain of the generated header, and adds no execution fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction Condition Label)

inductive TargetFlow where
  | normal
  | jumped (label : Label)
  | returned (value : TargetValue)
  deriving Repr

structure TargetBlockOutcome (World : Type) where
  flow : TargetFlow
  frame : TargetFrame
  state : TargetState World

def targetCloseBlock {World : Type} (marker : TargetFrame)
    (out : TargetBlockOutcome World) : TargetBlockOutcome World :=
  let closed := targetLeaveScope marker out.frame out.state
  ⟨out.flow, closed.1, closed.2⟩

def targetAfterLabel? : List Instruction → Label → Option (List Instruction)
  | [], _ => none
  | .label found :: rest, label => if found = label then some rest else targetAfterLabel? rest label
  | _ :: rest, label => targetAfterLabel? rest label

def targetSelectCase (selector : BitVec 64) (cases : List (BitVec 64 × List Instruction))
    (otherwise : List Instruction) : List Instruction :=
  match cases.find? (fun arm => arm.1 == selector) with
  | some arm => arm.2
  | none => otherwise

inductive TargetConditionEval {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) : Condition → Bool → Prop where
  | value {atom : Atom} {value : Bool}
      (read : TargetAtomEval interface frame state atom (.bool value)) :
      TargetConditionEval interface frame state (.value atom) value
  | negated {atom : Atom} {value : Bool}
      (read : TargetAtomEval interface frame state atom (.bool value)) :
      TargetConditionEval interface frame state (.negated atom) (!value)

mutual
  inductive TargetInstructionEval {World : Type} (interface : Interface)
      (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType) :
      Instruction → TargetFrame → TargetState World → TargetBlockOutcome World → Prop where
    | temporary {identity : Nat} {type : NativeType} {operation : NativeIR.PureOperation}
        {frame : TargetFrame} {state : TargetState World} {value : TargetValue}
        (unused : frame.temporaryNames.contains identity = false)
        (computed : TargetPureEval interface frame state operation value) :
        TargetInstructionEval interface heap calls result (.temporary identity type operation) frame state
          ⟨.normal, targetDeclareTemporary frame identity value, state⟩
    | assign {place : NativeIR.Place} {atom : Atom} {value : TargetValue}
        {before after : TargetFrame} {pre post : TargetState World}
        (read : TargetAtomEval interface before pre atom value)
        (stored : TargetPlaceStore interface place value before pre after post) :
        TargetInstructionEval interface heap calls result (.assign place atom) before pre
          ⟨.normal, after, post⟩
    | helper {destination : Option NativeIR.Place} {operation : NativeIR.MemoryOperation}
        {before after : TargetFrame} {pre post : TargetState World} {raw : TargetRawResult World}
        (called : TargetMemoryCall interface heap before operation pre raw)
        (stored : TargetResultStore interface destination raw.value before raw.state after post) :
        TargetInstructionEval interface heap calls result (.helper destination operation) before pre
          ⟨.normal, after, post⟩
    | call {destination : Option NativeIR.Place} {target : NativeIR.CallTarget} {arguments : List Atom}
        {values : List TargetValue} {raw : TargetValue}
        {before after : TargetFrame} {pre middle post : TargetState World}
        (operands : TargetAtomsEval interface before pre arguments values)
        (called : calls target values pre raw middle)
        (stored : TargetResultStore interface destination raw before middle after post) :
        TargetInstructionEval interface heap calls result (.call destination target arguments) before pre
          ⟨.normal, after, post⟩
    | contextExists (frame : TargetFrame) (state : TargetState World) :
        TargetInstructionEval interface heap calls result .checkContextExists frame state
          ⟨.normal, frame, state⟩
    | contextClear {frame : TargetFrame} {state : TargetState World} (clear : state.fault = none) :
        TargetInstructionEval interface heap calls result .checkContext frame state ⟨.normal, frame, state⟩
    | contextFault {frame : TargetFrame} {state : TargetState World}
        {fault : NativeWord64.Fault} {default : TargetValue}
        (failed : state.fault = some fault) (zero : TargetZero interface result default) :
        TargetInstructionEval interface heap calls result .checkContext frame state
          ⟨.returned default, frame, state⟩
    | numericClear {operation : NativeWord64.WordOp} {right : Atom} {value : BitVec 64}
        {frame : TargetFrame} {state : TargetState World}
        (read : TargetAtomEval interface frame state right (.word value))
        (clear : targetNumericFault operation value = none) :
        TargetInstructionEval interface heap calls result (.checkedNumericGuard operation right) frame state
          ⟨.normal, frame, state⟩
    | numericFault {operation : NativeWord64.WordOp} {right : Atom} {value : BitVec 64}
        {frame : TargetFrame} {state : TargetState World} {fault : NativeWord64.Fault}
        {default : TargetValue}
        (read : TargetAtomEval interface frame state right (.word value))
        (failed : targetNumericFault operation value = some fault)
        (zero : TargetZero interface result default) :
        TargetInstructionEval interface heap calls result (.checkedNumericGuard operation right) frame state
          ⟨.returned default, frame, targetPoison state fault⟩
    | declareLocal {name : String} {type : NativeType} {atom : Atom} {value : TargetValue}
        {frame : TargetFrame} {state : TargetState World}
        (read : TargetAtomEval interface frame state atom value) :
        TargetInstructionEval interface heap calls result (.declareLocal name type atom) frame state
          ⟨.normal, (targetDeclareLocal frame state name type value).1,
            (targetDeclareLocal frame state name type value).2⟩
    | write {pointer replacement : Atom} {address : Address} {value : TargetValue}
        {frame : TargetFrame} {state : TargetState World} {memory : TargetMemory}
        (located : TargetAtomEval interface frame state pointer (.reference (some address)))
        (read : TargetAtomEval interface frame state replacement value)
        (stored : targetWrite state.memory address value = some memory) :
        TargetInstructionEval interface heap calls result (.write pointer replacement) frame state
          ⟨.normal, frame, { state with memory := memory }⟩
    | writeElement {array index replacement : Atom} {element : NativeType} {address : Address}
        {length offset : BitVec 64} {value : TargetValue}
        {frame : TargetFrame} {state : TargetState World} {memory : TargetMemory}
        (view : TargetAtomEval interface frame state array (.array element (some address) length))
        (indexed : TargetAtomEval interface frame state index (.word offset))
        (within : offset < length)
        (read : TargetAtomEval interface frame state replacement value)
        (stored : targetWrite state.memory (advanceAddress address offset.toNat) value = some memory) :
        TargetInstructionEval interface heap calls result (.writeElement array index replacement) frame state
          ⟨.normal, frame, { state with memory := memory }⟩
    | forWord {counter : Nat} {bound : Atom} {body : List Instruction}
        {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
        (unused : frame.temporaryNames.contains counter = false)
        (loop : TargetForEval interface heap calls result counter bound body
          (targetDeclareTemporary frame counter (.word 0)) state out) :
        TargetInstructionEval interface heap calls result (.forWord counter bound body) frame state
          (targetCloseBlock frame out)
    | branch {condition : Condition} {whenTrue whenFalse : List Instruction} {selected : Bool}
        {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
        (tested : TargetConditionEval interface frame state condition selected)
        (ran : TargetRun interface heap calls result (if selected then whenTrue else whenFalse)
          (if selected then whenTrue else whenFalse) frame state out) :
        TargetInstructionEval interface heap calls result (.branch condition whenTrue whenFalse) frame state
          (targetCloseBlock frame out)
    | switch {selector : Atom} {cases : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
        {value : BitVec 64} {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
        (read : TargetAtomEval interface frame state selector (.word value))
        (ran : TargetRun interface heap calls result (targetSelectCase value cases otherwise)
          (targetSelectCase value cases otherwise) frame state out) :
        TargetInstructionEval interface heap calls result (.switch selector cases otherwise) frame state
          (targetCloseBlock frame out)
    | scope {body : List Instruction} {frame : TargetFrame} {state : TargetState World}
        {out : TargetBlockOutcome World}
        (ran : TargetRun interface heap calls result body body frame state out) :
        TargetInstructionEval interface heap calls result (.scope body) frame state (targetCloseBlock frame out)
    | label (label : Label) (frame : TargetFrame) (state : TargetState World) :
        TargetInstructionEval interface heap calls result (.label label) frame state ⟨.normal, frame, state⟩
    | jump (label : Label) (frame : TargetFrame) (state : TargetState World) :
        TargetInstructionEval interface heap calls result (.jump label) frame state ⟨.jumped label, frame, state⟩
    | return {atom : Atom} {value : TargetValue} {frame : TargetFrame} {state : TargetState World}
        (read : TargetAtomEval interface frame state atom value) :
        TargetInstructionEval interface heap calls result (.return atom) frame state ⟨.returned value, frame, state⟩

  inductive TargetRun {World : Type} (interface : Interface)
      (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType) :
      List Instruction → List Instruction → TargetFrame → TargetState World → TargetBlockOutcome World → Prop where
    | nil (root : List Instruction) (frame : TargetFrame) (state : TargetState World) :
        TargetRun interface heap calls result root [] frame state ⟨.normal, frame, state⟩
    | next {root rest : List Instruction} {first : Instruction}
        {before middle : TargetFrame} {pre post : TargetState World} {out : TargetBlockOutcome World}
        (firstRun : TargetInstructionEval interface heap calls result first before pre ⟨.normal, middle, post⟩)
        (restRun : TargetRun interface heap calls result root rest middle post out) :
        TargetRun interface heap calls result root (first :: rest) before pre out
    | return {root rest : List Instruction} {first : Instruction} {value : TargetValue}
        {before : TargetFrame} {pre : TargetState World} {after : TargetFrame} {post : TargetState World}
        (firstRun : TargetInstructionEval interface heap calls result first before pre ⟨.returned value, after, post⟩) :
        TargetRun interface heap calls result root (first :: rest) before pre ⟨.returned value, after, post⟩
    | resume {root rest suffix : List Instruction} {first : Instruction} {label : Label}
        {before middle : TargetFrame} {pre post : TargetState World} {out : TargetBlockOutcome World}
        (firstRun : TargetInstructionEval interface heap calls result first before pre ⟨.jumped label, middle, post⟩)
        (found : targetAfterLabel? root label = some suffix)
        (restRun : TargetRun interface heap calls result root suffix middle post out) :
        TargetRun interface heap calls result root (first :: rest) before pre out
    | escape {root rest : List Instruction} {first : Instruction} {label : Label}
        {before after : TargetFrame} {pre post : TargetState World}
        (firstRun : TargetInstructionEval interface heap calls result first before pre ⟨.jumped label, after, post⟩)
        (outside : targetAfterLabel? root label = none) :
        TargetRun interface heap calls result root (first :: rest) before pre ⟨.jumped label, after, post⟩

  inductive TargetForEval {World : Type} (interface : Interface)
      (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType) :
      Nat → Atom → List Instruction → TargetFrame → TargetState World → TargetBlockOutcome World → Prop where
    | done {counter : Nat} {bound : Atom} {body : List Instruction}
        {frame : TargetFrame} {state : TargetState World} {index limit : BitVec 64}
        (readCounter : TargetAtomEval interface frame state (.iterationCounter counter) (.word index))
        (readBound : TargetAtomEval interface frame state bound (.word limit))
        (finished : ¬ index < limit) :
        TargetForEval interface heap calls result counter bound body frame state ⟨.normal, frame, state⟩
    | next {counter : Nat} {bound : Atom} {body : List Instruction}
        {frame : TargetFrame} {state : TargetState World} {index limit afterCounter : BitVec 64}
        {iteration out : TargetBlockOutcome World}
        (readCounter : TargetAtomEval interface frame state (.iterationCounter counter) (.word index))
        (readBound : TargetAtomEval interface frame state bound (.word limit))
        (within : index < limit)
        (ran : TargetRun interface heap calls result body body frame state iteration)
        (normal : iteration.flow = .normal)
        (counterAfter : TargetAtomEval interface (targetCloseBlock frame iteration).frame
          (targetCloseBlock frame iteration).state (.iterationCounter counter) (.word afterCounter))
        (rest : TargetForEval interface heap calls result counter bound body
          (targetUpdateTemporary (targetCloseBlock frame iteration).frame counter (.word (afterCounter + 1)))
          (targetCloseBlock frame iteration).state out) :
        TargetForEval interface heap calls result counter bound body frame state out
    | stop {counter : Nat} {bound : Atom} {body : List Instruction}
        {frame : TargetFrame} {state : TargetState World} {index limit : BitVec 64}
        {iteration : TargetBlockOutcome World}
        (readCounter : TargetAtomEval interface frame state (.iterationCounter counter) (.word index))
        (readBound : TargetAtomEval interface frame state bound (.word limit))
        (within : index < limit)
        (ran : TargetRun interface heap calls result body body frame state iteration)
        (abrupt : iteration.flow ≠ .normal) :
        TargetForEval interface heap calls result counter bound body frame state (targetCloseBlock frame iteration)
end

theorem target_scope_exit_preserves_return {World : Type} (marker : TargetFrame)
    (value : TargetValue) (frame : TargetFrame) (state : TargetState World) :
    (targetCloseBlock marker ⟨.returned value, frame, state⟩).flow = .returned value := rfl

theorem target_scope_exit_preserves_jump {World : Type} (marker : TargetFrame)
    (label : Label) (frame : TargetFrame) (state : TargetState World) :
    (targetCloseBlock marker ⟨.jumped label, frame, state⟩).flow = .jumped label := rfl

theorem target_scope_exit_preserves_fault {World : Type} (marker : TargetFrame)
    (out : TargetBlockOutcome World) : (targetCloseBlock marker out).state.fault = out.state.fault := rfl

theorem missing_label_does_not_resume (label : Label) : targetAfterLabel? [] label = none := rfl

theorem scope_jump_unwinds_before_propagation {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (label : Label) (frame : TargetFrame) (state : TargetState World) :
    TargetInstructionEval interface heap calls result (.scope [.jump label]) frame state
      (targetCloseBlock frame ⟨.jumped label, frame, state⟩) := by
  apply TargetInstructionEval.scope
  exact .escape (.jump label frame state) rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
