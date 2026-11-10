import Mettapedia.GSLT.LanguageDef.CheckedByteModules
import Mettapedia.Machines.CMemory.PermissionFlow

/-!
# Scalar span permissions and counted extents

Element types refine the existing buffer permission machine. Transitions
independently check type-preserving borrowing, moves, calls and returns before
applying the existing ownership operation. The generic control-flow checker
includes explicit failed transitions and checks all finite loop executions.

The extent laws justify element-to-byte arithmetic. Scalar expressions, actual
allocation/initialization and the C/source projection remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedScalarSpans

open Mettapedia.Machines.CMemory

inductive Element where
  | boolean | u8 | u16 | u32 | u64 | usize
  deriving DecidableEq, Repr

def Element.bytes (wordBytes : Nat) : Element → Nat
  | .boolean | .u8 => 1
  | .u16 => 2
  | .u32 => 4
  | .u64 => 8
  | .usize => wordBytes

def allocationBytes (stride limit count : Nat) : Option Nat :=
  if 0 < stride ∧ count ≤ limit / stride then some (count * stride) else none

theorem allocationBytes_exact {stride limit count bytes : Nat}
    (accepted : allocationBytes stride limit count = some bytes) :
    bytes = count * stride ∧ bytes ≤ limit ∧ 0 < stride := by
  unfold allocationBytes at accepted
  split at accepted
  next bounds =>
    have same := Option.some.inj accepted
    subst bytes
    exact ⟨rfl, (Nat.le_div_iff_mul_le bounds.1).mp bounds.2, bounds.1⟩
  next => cases accepted

theorem allocationBytes_complete {stride limit count : Nat}
    (positive : 0 < stride) (bounded : count * stride ≤ limit) :
    allocationBytes stride limit count = some (count * stride) := by
  simp [allocationBytes, positive, (Nat.le_div_iff_mul_le positive).mpr bounded]

theorem slice_byte_bounds {stride length start count index : Nat}
    (startBound : start ≤ length) (countBound : count ≤ length - start)
    (indexBound : index < count) :
    (start + index) * stride + stride ≤ length * stride := by
  have inside := CheckedBytes.slice_index_in_range startBound countBound indexBound
  have bounded := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt inside)
  simpa [Nat.succ_mul] using bounded

inductive Slot where
  | scalar (slot : CheckedBytes.Slot)
  | span (element : Element) (kind : CheckedBytes.Kind)
  deriving DecidableEq, Repr

def Slot.erase : Slot → CheckedBytes.Slot
  | .scalar slot => slot
  | .span _ .read => .read
  | .span _ .write => .write
  | .span _ .own => .own
  | .span _ .local => .unit

def Slot.element? : Slot → Option Element
  | .span element _ => some element
  | .scalar _ => none

def Slot.valid : Slot → Bool
  | .scalar slot => slot.permission.isNone
  | .span _ .local => false
  | .span _ _ => true

structure Signature where
  name : String
  params : List Slot
  result : Slot
  sourceParameter : Option Nat := none
  effects : List String := []
  obligation : Option String := none
  allocator : Option (String × String) := none
  deriving DecidableEq, Repr

def Signature.erase (s : Signature) : CheckedBytes.Signature :=
  ⟨s.name, s.params.map Slot.erase, s.result.erase, s.sourceParameter,
    s.effects, s.obligation, s.allocator⟩

def signatureValid (s : Signature) : Bool :=
  s.params.all Slot.valid && s.result.valid && CheckedBytes.signatureValid s.erase &&
    (match s.sourceParameter with
     | none => true
     | some index => (s.params[index]?.bind Slot.element?) == s.result.element?)

structure State where
  permissions : CheckedBytes.State
  elements : List (Nat × Element)
  ownedResult : Option Element := none
  deriving DecidableEq, Repr

instance : BEq State := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq State where
  eq_of_beq := by simp
  rfl := by simp

def initial (signature : Signature) : State :=
  ⟨CheckedBytes.initial signature.erase, signature.params.zipIdx.filterMap (fun (slot, id) =>
    slot.element?.map (id, ·)), none⟩

def State.find (s : State) (id : Nat) : Option Element := s.elements.lookup id

def Valid (s : State) : Prop :=
  CheckedBytes.Valid s.permissions ∧ (s.elements.map Prod.fst).Nodup ∧
    s.elements.map Prod.fst = s.permissions.cells.map CheckedBytes.Binding.id ∧
    (∀ first ∈ s.permissions.cells, ∀ second ∈ s.permissions.cells,
      first.root = second.root → s.find first.id = s.find second.id) ∧
    s.ownedResult.isSome = s.permissions.ownedResult

instance (s : State) : Decidable (Valid s) := by unfold Valid; infer_instance

structure Action where
  permission : CheckedBytes.Action
  element : Option Element := none
  arguments : List Element := []
  deriving DecidableEq, Repr

def typedTransition (caller : Signature)
    (s : State) (a : Action) : Option State := do
  CheckedBytes.require a.arguments.isEmpty
  let e ← a.element
  let found (id : Nat) := CheckedBytes.require (s.find id == some e)
  let add (id : Nat) := pure { s with elements := (id, e) :: s.elements }
  let erase (id : Nat) := { s with elements := s.elements.filter (fun p => p.1 != id) }
  match a.permission with
  | .acquire id _ => add id
  | .borrow id source _ _ => found source; add id
  | .move id source _ => found source; pure { (erase source) with elements := (id, e) :: (erase source).elements }
  | .read id _ => found id; pure s
  | .endView id _ | .drop id _ => found id; pure (erase id)
  | .take id =>
      found id
      CheckedBytes.require (caller.result.element? == some e)
      pure { (erase id) with ownedResult := some e }
  | .ownResult id =>
      CheckedBytes.require (s.ownedResult == some e)
      pure { s with elements := (id, e) :: s.elements, ownedResult := none }
  | .borrowResult id _ _ => found id; CheckedBytes.require (caller.result.element? == some e); pure s
  | .invoke .. => none

def callTransition (environment : List Signature) (s : State)
    (name : String) (arguments : List (Nat × CheckedBytes.Kind)) (elements : List Element) : Option State := do
  let target ← environment.find? (fun signature => signature.name == name)
  let expected := target.params.filterMap Slot.element?
  CheckedBytes.require (elements == expected)
  CheckedBytes.require (arguments.length == expected.length)
  CheckedBytes.require ((arguments.zip expected).all fun ((id, _), element) => s.find id == some element)
  let consumed := arguments.filterMap fun (id, mode) => if mode == .own then some id else none
  pure { s with elements := s.elements.filter (fun p => !consumed.contains p.1)
                ownedResult := if target.result.erase == .own then target.result.element? else none }

def checkTypes (environment : List Signature) (caller : Signature) (s : State) (a : Action) : Option State :=
  match a.permission with
    | .invoke name arguments =>
        if a.element.isNone then callTransition environment s name arguments a.arguments else none
    | _ => typedTransition caller s a

def transition (environment : List Signature) (caller : Signature) (s : State) (a : Action) : Option State := do
  CheckedBytes.require (decide (Valid s))
  let typed ← checkTypes environment caller s a
  let permissions ← CheckedBytes.apply (environment.map Signature.erase) caller.erase s.permissions a.permission
  let after := { typed with permissions := permissions }
  CheckedBytes.require (decide (Valid after))
  pure after

theorem transition_valid {environment : List Signature} {caller : Signature} {s after : State} {a : Action}
    (accepted : transition environment caller s a = some after) : Valid after := by
  simp only [transition, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨_, _, _, _, _, _, _, checked, same⟩ := accepted
  cases same
  simpa using CheckedBytes.require_passed checked

theorem transition_erases {environment : List Signature} {caller : Signature} {s after : State} {a : Action}
    (accepted : transition environment caller s a = some after) :
    CheckedBytes.apply (environment.map Signature.erase) caller.erase s.permissions a.permission = some after.permissions := by
  simp only [transition, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨_, _, _, _, _, step, _, _, same⟩ := accepted
  cases same
  exact step

def returnAllowed (signature : Signature) (s : State) : Bool :=
  CheckedBytes.returnAllowed signature.erase s.permissions && s.elements.isEmpty &&
    (signature.result.erase != .own || s.ownedResult == signature.result.element?)

structure Function where
  signature : Signature
  parameters : List (Nat × Slot)
  body : PermissionFlow.Plan Action
  deriving DecidableEq, Repr

structure Module where
  foreign : List Signature
  functions : List Function
  deriving DecidableEq, Repr

def checkFunction (environment : List Signature) (f : Function) : Bool :=
  signatureValid f.signature && f.signature.obligation.isNone &&
  f.parameters == (f.signature.params.zipIdx.map fun (slot, id) => (id, slot)) &&
  decide (Valid (initial f.signature)) &&
  match PermissionFlow.check (transition environment f.signature) (returnAllowed f.signature) f.body (initial f.signature) with
  | none => false
  | some outputs => !outputs.isEmpty && outputs.all fun exit =>
      (exit.kind == .normal || exit.kind == .returned) && returnAllowed f.signature exit.state

def admit (m : Module) : Bool :=
  let signatures := m.foreign ++ m.functions.map Function.signature
  !m.functions.isEmpty && (signatures.map Signature.name).Nodup &&
    m.foreign.all (fun signature => signatureValid signature && signature.obligation.isSome) &&
    m.functions.all (checkFunction signatures)

theorem checked_no_fault {environment : List Signature} {f : Function} {outcome : PermissionFlow.Exit State}
    (accepted : checkFunction environment f = true)
    (execution : PermissionFlow.Execution (transition environment f.signature) f.body (initial f.signature) outcome) :
    outcome.kind ≠ .fault := by
  unfold checkFunction at accepted
  obtain ⟨_, _, _, _, rest⟩ := (by simpa only [Bool.and_eq_true, and_assoc] using accepted)
  cases checked : PermissionFlow.check (transition environment f.signature) (returnAllowed f.signature) f.body (initial f.signature) with
  | none => simp [checked] at rest
  | some outputs => exact PermissionFlow.admitted_no_fault ⟨outputs, checked⟩ execution

theorem checked_valid {environment : List Signature} {f : Function} {outcome : PermissionFlow.Exit State}
    (accepted : checkFunction environment f = true)
    (execution : PermissionFlow.Execution (transition environment f.signature) f.body (initial f.signature) outcome) :
    Valid outcome.state := by
  unfold checkFunction at accepted
  obtain ⟨_, _, _, valid, _⟩ := (by simpa only [Bool.and_eq_true, and_assoc] using accepted)
  apply execution.invariant (fun _ _ _ step _ => transition_valid step)
  simpa using valid

theorem checked_return {environment : List Signature} {f : Function} {outcome : PermissionFlow.Exit State}
    (accepted : checkFunction environment f = true)
    (execution : PermissionFlow.Execution (transition environment f.signature) f.body (initial f.signature) outcome)
    (returned : outcome.kind = .returned) : returnAllowed f.signature outcome.state = true := by
  unfold checkFunction at accepted
  obtain ⟨_, _, _, _, rest⟩ := (by simpa only [Bool.and_eq_true, and_assoc] using accepted)
  cases checked : PermissionFlow.check (transition environment f.signature) (returnAllowed f.signature) f.body (initial f.signature) with
  | none => simp [checked] at rest
  | some outputs =>
      exact PermissionFlow.checked_returns checked outcome
        (PermissionFlow.covers_execution execution checked) returned

namespace Controls

theorem count_not_bytes : allocationBytes 4 1024 7 = some 28 := by decide
theorem overflow_refused : allocationBytes 8 2147483647 268435456 = none := by decide
theorem zero_length : allocationBytes 8 1024 0 = some 0 := by decide
theorem mismatched_result : signatureValid
    { name := "bad", params := [.span .u32 .read], result := .span .u16 .read,
      sourceParameter := some 0 } = false := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.CheckedScalarSpans
