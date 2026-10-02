import Mettapedia.GSLT.LanguageDef.NativeOpsIR
import Mettapedia.GSLT.LanguageDef.NativeOpsStack
import Mettapedia.GSLT.LanguageDef.NativeOpsDataHelpers
import Mettapedia.GSLT.LanguageDef.NativeOpsZero

/-!
# Values and checked storage calls of the native target

Target operations consume already evaluated atoms. Private C temporaries have
no address constructor. Source-visible local addresses remain ordinary aliased
live cells. The numeric operation itself is undefined when its explicit C
division or shift guard was skipped; a guard refusal is a separate context
effect. Raw helper results and sticky faults are retained independently.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Place PureOperation MemoryOperation)
open NativeWord64 (Fault)

structure TargetHeapSemantics (World : Type) where
  width : NativeType → BitVec 64
  allocate : NativeType → BitVec 64 → TargetState World → TargetRawResult World → Prop
  release : NativeType → TargetValue → TargetState World → TargetRawResult World → Prop

abbrev TargetCalls (World : Type) :=
  NativeIR.CallTarget → List TargetValue → TargetState World → TargetValue → TargetState World → Prop

inductive TargetAtomEval {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) : Atom → TargetValue → Prop where
  | temporary {identity : Nat} {type : NativeType} {value : TargetValue}
      (found : frame.temporaries identity = some value)
      (live : frame.temporaryNames.contains identity = true) :
      TargetAtomEval interface frame state (.temporary identity type) value
  | iterationCounter {identity : Nat} {value : BitVec 64}
      (found : frame.temporaries identity = some (.word value))
      (live : frame.temporaryNames.contains identity = true) :
      TargetAtomEval interface frame state (.iterationCounter identity) (.word value)
  | localAddress {name : String} {type : NativeType} {address : Address}
      (found : targetLocalAddress frame name = some address) :
      TargetAtomEval interface frame state (.localAddress name type) (.reference (some address))
  | word (value : BitVec 64) : TargetAtomEval interface frame state (.word value) (.word value)
  | zero {type : NativeType} {value : TargetValue} (initialized : TargetZero interface type value) :
      TargetAtomEval interface frame state (.zero type) value
  | unit : TargetAtomEval interface frame state .unit .unit

inductive TargetAtomsEval {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) : List Atom → List TargetValue → Prop where
  | nil : TargetAtomsEval interface frame state [] []
  | cons {atom : Atom} {rest : List Atom} {value : TargetValue} {values : List TargetValue}
      (head : TargetAtomEval interface frame state atom value)
      (tail : TargetAtomsEval interface frame state rest values) :
      TargetAtomsEval interface frame state (atom :: rest) (value :: values)

def targetUncheckedBinary (operation : Binary) (left right : TargetValue) : Option TargetValue :=
  (targetBinaryOp operation left right).bind Except.toOption

def targetNumericFault : NativeWord64.WordOp → BitVec 64 → Option Fault
  | .div, right | .mod, right => if right = 0 then some .divisionByZero else none
  | .shl, right | .shr, right => if 64 ≤ right.toNat then some .shiftOutOfRange else none
  | _, _ => none

inductive TargetPureEval {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) : PureOperation → TargetValue → Prop where
  | word (value : BitVec 64) : TargetPureEval interface frame state (.word value) (.word value)
  | byte (value : BitVec 8) : TargetPureEval interface frame state (.byte value) (.byte value)
  | bool (value : Bool) : TargetPureEval interface frame state (.bool value) (.bool value)
  | zero {type : NativeType} {value : TargetValue} (initialized : TargetZero interface type value) :
      TargetPureEval interface frame state (.zero type) value
  | copy {atom : Atom} {value : TargetValue} (read : TargetAtomEval interface frame state atom value) :
      TargetPureEval interface frame state (.copy atom) value
  | local {name : String} {value : TargetValue} (read : targetLocalValue frame state name = some value) :
      TargetPureEval interface frame state (.readLocal name) value
  | fieldValue {atom : Atom} {name : String} {fields : List TargetValue} {index : Nat} {value : TargetValue}
      (read : TargetAtomEval interface frame state atom (.record name fields))
      (field : fields[index]? = some value) :
      TargetPureEval interface frame state (.fieldValue atom name index) value
  | fieldAddress {atom : Atom} {name : String} {address : Address} {index : Nat}
      (read : TargetAtomEval interface frame state atom (.reference (some address))) :
      TargetPureEval interface frame state (.fieldAddress atom name index)
        (.reference (some { address with fields := address.fields ++ [index] }))
  | elementAddress {array index : Atom} {element : NativeType} {address : Address}
      {length value : BitVec 64}
      (view : TargetAtomEval interface frame state array (.array element (some address) length))
      (offset : TargetAtomEval interface frame state index (.word value)) :
      TargetPureEval interface frame state (.elementAddress array index element)
        (.reference (some (advanceAddress address value.toNat)))
  | indirect {atom : Atom} {address : Address} {value : TargetValue}
      (pointer : TargetAtomEval interface frame state atom (.reference (some address)))
      (read : targetRead state.memory address = some value) :
      TargetPureEval interface frame state (.indirectRead atom) value
  | length {atom : Atom} {element : NativeType} {address : Option Address} {length : BitVec 64}
      (view : TargetAtomEval interface frame state atom (.array element address length)) :
      TargetPureEval interface frame state (.length atom) (.word length)
  | unary {operation : Unary} {atom : Atom} {operand value : TargetValue}
      (read : TargetAtomEval interface frame state atom operand)
      (computed : targetUnaryOp operation operand = some value) :
      TargetPureEval interface frame state (.unary operation atom) value
  | binary {operation : Binary} {left right : Atom} {first second value : TargetValue}
      (readLeft : TargetAtomEval interface frame state left first)
      (readRight : TargetAtomEval interface frame state right second)
      (computed : targetUncheckedBinary operation first second = some value) :
      TargetPureEval interface frame state (.binary operation left right) value

def targetDeclareTemporary (frame : TargetFrame) (identity : Nat) (value : TargetValue) : TargetFrame :=
  { frame with
    temporaryNames := identity :: frame.temporaryNames
    temporaries := fun candidate => if candidate = identity then some value else frame.temporaries candidate }

def targetUpdateTemporary (frame : TargetFrame) (identity : Nat) (value : TargetValue) : TargetFrame :=
  { frame with temporaries := fun candidate =>
      if candidate = identity then some value else frame.temporaries candidate }

inductive TargetPlaceStore {World : Type} (interface : Interface) :
    Place → TargetValue → TargetFrame → TargetState World → TargetFrame → TargetState World → Prop where
  | temporary {identity : Nat} {type : NativeType} {value : TargetValue}
      {frame : TargetFrame} {state : TargetState World}
      (live : frame.temporaryNames.contains identity = true) :
      TargetPlaceStore interface (.temporary identity type) value frame state
        (targetUpdateTemporary frame identity value) state
  | local {name : String} {type : NativeType} {value : TargetValue}
      {frame : TargetFrame} {state : TargetState World} {address : Address} {memory : TargetMemory}
      (found : targetLocalAddress frame name = some address)
      (written : targetWrite state.memory address value = some memory) :
      TargetPlaceStore interface (.local name type) value frame state frame { state with memory := memory }
  | arrayData {identity : Nat} {element : NativeType} {pointer previous : Option Address}
      {length : BitVec 64} {frame : TargetFrame} {state : TargetState World}
      (read : TargetAtomEval interface frame state (.temporary identity (.array element))
        (.array element previous length)) :
      TargetPlaceStore interface (.arrayData (.temporary identity (.array element)) element)
        (.reference pointer) frame state
        (targetUpdateTemporary frame identity (.array element pointer length)) state
  | arrayLength {identity : Nat} {element : NativeType} {pointer : Option Address}
      {oldLength length : BitVec 64} {frame : TargetFrame} {state : TargetState World}
      (read : TargetAtomEval interface frame state (.temporary identity (.array element))
        (.array element pointer oldLength)) :
      TargetPlaceStore interface (.arrayLength (.temporary identity (.array element)))
        (.word length) frame state
        (targetUpdateTemporary frame identity (.array element pointer length)) state

/-- Helpers and calls declare their fresh result temporary before the emitted context check. -/
inductive TargetResultStore {World : Type} (interface : Interface) :
    Option Place → TargetValue → TargetFrame → TargetState World → TargetFrame → TargetState World → Prop where
  | discard (value : TargetValue) (frame : TargetFrame) (state : TargetState World) :
      TargetResultStore interface none value frame state frame state
  | fresh {identity : Nat} {type : NativeType} {value : TargetValue}
      {frame : TargetFrame} {state : TargetState World}
      (unused : frame.temporaryNames.contains identity = false) :
      TargetResultStore interface (some (.temporary identity type)) value frame state
        (targetDeclareTemporary frame identity value) state
  | existing {place : Place} {value : TargetValue} {before after : TargetFrame}
      {pre post : TargetState World}
      (notTemporary : ∀ identity type, place ≠ .temporary identity type)
      (stored : TargetPlaceStore interface place value before pre after post) :
      TargetResultStore interface (some place) value before pre after post

inductive TargetMemoryCall {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (frame : TargetFrame) :
    MemoryOperation → TargetState World → TargetRawResult World → Prop where
  | reference {atom : Atom} {address : Option Address} {state : TargetState World}
      (read : TargetAtomEval interface frame state atom (.reference address)) :
      TargetMemoryCall interface heap frame (.reference atom) state (targetReferenceCall state address)
  | index {array index : Atom} {element : NativeType} {address : Option Address}
      {length value : BitVec 64} {state : TargetState World}
      (readArray : TargetAtomEval interface frame state array (.array element address length))
      (readIndex : TargetAtomEval interface frame state index (.word value)) :
      TargetMemoryCall interface heap frame (.index array index element) state
        (targetIndexCall state length (heap.width element) value address)
  | slice {array start count : Atom} {element : NativeType} {address : Option Address}
      {length first amount : BitVec 64} {state : TargetState World}
      (readArray : TargetAtomEval interface frame state array (.array element address length))
      (readStart : TargetAtomEval interface frame state start (.word first))
      (readCount : TargetAtomEval interface frame state count (.word amount)) :
      TargetMemoryCall interface heap frame (.slice array start count element) state
        (targetSliceCall state length (heap.width element) first amount address)
  | allocate {count : Atom} {element : NativeType} {amount : BitVec 64}
      {state : TargetState World} {raw : TargetRawResult World}
      (read : TargetAtomEval interface frame state count (.word amount))
      (allocated : heap.allocate element amount state raw) :
      TargetMemoryCall interface heap frame (.allocate count element) state raw
  | release {atom : Atom} {element : NativeType} {value : TargetValue}
      {state : TargetState World} {raw : TargetRawResult World}
      (read : TargetAtomEval interface frame state atom value)
      (released : heap.release element value state raw) :
      TargetMemoryCall interface heap frame (.release atom element) state raw

theorem declare_temporary_is_private (frame : TargetFrame) (identity : Nat) (value : TargetValue) :
    (targetDeclareTemporary frame identity value).storage = frame.storage ∧
      (targetDeclareTemporary frame identity value).bindings = frame.bindings := ⟨rfl, rfl⟩

theorem declare_temporary_read (frame : TargetFrame) (identity : Nat) (value : TargetValue) :
    (targetDeclareTemporary frame identity value).temporaries identity = some value := by
  simp [targetDeclareTemporary]

/-- Declaring a private value preserves the absence of stale temporary values. -/
theorem declare_temporary_scoped (frame : TargetFrame) (identity : Nat) (value : TargetValue)
    (completeNames : ∀ candidate, frame.temporaryNames.contains candidate = false →
      frame.temporaries candidate = none) :
    ∀ candidate, (targetDeclareTemporary frame identity value).temporaryNames.contains candidate =
      false → (targetDeclareTemporary frame identity value).temporaries candidate = none := by
  intro candidate absent
  by_cases same : candidate = identity
  · subst candidate
    simp [targetDeclareTemporary] at absent
  · have wasAbsent : frame.temporaryNames.contains candidate = false := by
      simpa [targetDeclareTemporary, same, beq_iff_eq] using absent
    simp [targetDeclareTemporary, same, completeNames candidate wasAbsent]

theorem unchecked_division_zero_is_undefined (left : BitVec 64) :
    targetUncheckedBinary (.word .div) (.word left) (.word 0) = none := by
  simp [targetUncheckedBinary, targetBinaryOp, NativeWord64.targetBinary, Except.toOption, Except.map]

theorem explicit_division_guard_faults : targetNumericFault .div 0 = some .divisionByZero := by
  simp [targetNumericFault]

theorem checked_shift_boundary_refuses : targetNumericFault .shl 64 = some .shiftOutOfRange := by
  decide +kernel

theorem last_checked_shift_accepts : targetNumericFault .shr 63 = none := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps
