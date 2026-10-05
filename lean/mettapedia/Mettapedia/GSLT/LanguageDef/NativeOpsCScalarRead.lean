import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex

/-!
# Typed scalar reads and counted local loops in retained C syntax

This fragment executes immutable identity-array reads, UInt32 comparisons,
pointer equality, Boolean conversion and short-circuit conditions. Statement
execution retains the supplied body. Local assignments cannot write a field or
array; counter increments use the actual unsigned operation. A loop counter's
previous binding is restored at the declaration's scope boundary.

Field readers provide logical typed values. Their relation to physical storage,
layout and synchronized access is a separate service obligation. Unsupported
syntax and undefined reads have no completed execution. Proof-fuel exhaustion
is a separate result and is not a C failure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead

variable {Ptr : Type} [DecidableEq Ptr]

inductive Value (Ptr : Type) where
  | boolean (value : Bool)
  | unsigned (value : UInt32)
  | identity (value : Option Ptr)
  | identities (values : List (Option Ptr))
  deriving DecidableEq, Repr

abbrev Environment (Ptr : Type) := Name → Option (Value Ptr)
abbrev FieldReader (Ptr : Type) := Ptr → Name → Option (Value Ptr)

def truth? : Value Ptr → Option Bool
  | .boolean value => some value
  | .unsigned value => some (value != 0)
  | .identity value => some value.isSome
  | .identities _ => none

def equal? : Value Ptr → Value Ptr → Option Bool
  | .boolean left, .boolean right => some (left == right)
  | .unsigned left, .unsigned right => some (left == right)
  | .identity left, .identity right => some (decide (left = right))
  | _, _ => none

/-- All operand reads in this fragment are pure. Short-circuit selection is
retained even when the unselected operand would have no defined read. -/
def expression (environment : Environment Ptr) (fields : FieldReader Ptr) :
    CExpr → Option (Value Ptr)
  | .identifier name => environment name
  | .unsignedInteger value =>
      if value < 2 ^ 32 then some (.unsigned (UInt32.ofNat value)) else none
  | .bool value => some (.boolean value)
  | .null => some (.identity none)
  | .unary .not operand => do
      let value ← expression environment fields operand
      let truth ← truth? value
      some (.boolean (!truth))
  | .field record name true => do
      let .identity (some owner) ← expression environment fields record | none
      fields owner name
  | .index array index => do
      let .identities values ← expression environment fields array | none
      let .unsigned position ← expression environment fields index | none
      (values[position.toNat]?).map Value.identity
  | .binary .and left right => do
      let first ← expression environment fields left
      let selected ← truth? first
      if selected then do
        let second ← expression environment fields right
        let selectedSecond ← truth? second
        some (.boolean selectedSecond)
      else some (.boolean false)
  | .binary .or left right => do
      let first ← expression environment fields left
      let selected ← truth? first
      if selected then some (.boolean true) else do
        let second ← expression environment fields right
        let selectedSecond ← truth? second
        some (.boolean selectedSecond)
  | .binary .eq left right => do
      let first ← expression environment fields left
      let second ← expression environment fields right
      (equal? first second).map Value.boolean
  | .binary .ne left right => do
      let first ← expression environment fields left
      let second ← expression environment fields right
      (equal? first second).map (fun value => Value.boolean (!value))
  | .binary .lt left right => do
      let .unsigned first ← expression environment fields left | none
      let .unsigned second ← expression environment fields right | none
      some (.boolean (decide (first < second)))
  | _ => none

def assignValue? : Value Ptr → Value Ptr → Option (Value Ptr)
  | .boolean _, value => (truth? value).map Value.boolean
  | .unsigned _, .unsigned value => some (.unsigned value)
  | .identity _, .identity value => some (.identity value)
  | _, _ => none

def assignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (location value : CExpr) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let previous ← environment name
  let evaluated ← expression environment fields value
  let converted ← assignValue? previous evaluated
  some (Function.update environment name (some converted))

def statements (fields : FieldReader Ptr) (environment : Environment Ptr) :
    List CStatement → Option (Environment Ptr)
  | [] => some environment
  | .empty :: rest => statements fields environment rest
  | .assign location value :: rest =>
      (assignment environment fields location value).bind fun updated =>
        statements fields updated rest
  | _ => none

def increment (environment : Environment Ptr) : CExpr → Option (Environment Ptr)
  | .postIncrement (.identifier name) => do
      let .unsigned value ← environment name | none
      some (Function.update environment name (some (.unsigned (value + 1))))
  | _ => none

inductive Result (Ptr : Type) where
  | finished (result : Option (Environment Ptr))
  | exhausted

def run (fields : FieldReader Ptr) (condition step : CExpr)
    (body : List CStatement) (fuel : Nat) (environment : Environment Ptr) : Result Ptr :=
  match (expression environment fields condition).bind truth? with
  | none => .finished none
  | some false => .finished (some environment)
  | some true => match fuel with
    | 0 => .exhausted
    | fuel + 1 => match statements fields environment body with
      | none => .finished none
      | some updated => match increment updated step with
        | none => .finished none
        | some advanced => run fields condition step body fuel advanced

def restore (result : Result Ptr) (name : Name) (old : Option (Value Ptr)) : Result Ptr :=
  match result with
  | .finished completed => .finished (completed.map fun environment =>
      Function.update environment name old)
  | .exhausted => .exhausted

/-- Header admission returns and executes the actual body. It does not compare
that body to a successful scan template or synthesize missing assignments. -/
def countedLoop (fields : FieldReader Ptr) (fuel : Nat) (environment : Environment Ptr) :
    CStatement → Option (Result Ptr)
  | .forLoop type counter initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let .unsigned first ← expression environment fields initial | none
        let initialized := Function.update environment counter (some (.unsigned first))
        some (restore (run fields condition step body fuel initialized)
          counter (environment counter))
      else none
  | _ => none

namespace Controls

def environment : Environment Nat := fun name =>
  if name = "present".toList then some (.boolean false)
  else if name = "j".toList then some (.unsigned 0)
  else if name = "items".toList then some (.identities [some 7])
  else none

def noFields : FieldReader Nat := fun _ _ => none

theorem false_short_circuit_does_not_read_missing_operand :
    expression environment noFields
      (.binary .and (.bool false) (.identifier "missing".toList)) =
      some (.boolean false) := rfl

theorem true_short_circuit_does_not_read_missing_operand :
    expression environment noFields
      (.binary .or (.bool true) (.identifier "missing".toList)) =
      some (.boolean true) := rfl

theorem selected_missing_operand_has_no_execution :
    expression environment noFields
      (.binary .and (.bool true) (.identifier "missing".toList)) = none := rfl

theorem missing_slot_has_no_execution :
    expression environment noFields
      (.index (.identifier "items".toList) (.unsignedInteger 1)) = none := rfl

theorem incompatible_equality_has_no_execution :
    expression environment noFields (.binary .eq (.bool true) .null) = none := rfl

theorem omitted_body_does_not_invent_assignment :
    (statements noFields environment []).bind (fun after => after "present".toList) =
      some (.boolean false) := rfl

theorem changed_rhs_changes_observation :
    (statements noFields environment
      [.assign (.identifier "present".toList) (.bool true)]).bind
      (fun after => after "present".toList) = some (.boolean true) := by
  decide +kernel

theorem counter_unsigned_wrap_is_not_silent_bound_proof :
    (increment (Function.update environment "j".toList (some (.unsigned 4294967295)))
      (.postIncrement (.identifier "j".toList))).bind
        (fun after => after "j".toList) = some (.unsigned 0) := by
  decide +kernel

theorem insufficient_fuel_is_not_undefined_read :
    run noFields (.bool true) (.postIncrement (.identifier "j".toList)) [] 0 environment =
      .exhausted ∧
    run noFields (.identifier "missing".toList)
      (.postIncrement (.identifier "j".toList)) [] 1 environment = .finished none := by
  constructor <;> rfl

end Controls

#print axioms Controls.false_short_circuit_does_not_read_missing_operand
#print axioms Controls.true_short_circuit_does_not_read_missing_operand
#print axioms Controls.selected_missing_operand_has_no_execution
#print axioms Controls.missing_slot_has_no_execution
#print axioms Controls.incompatible_equality_has_no_execution
#print axioms Controls.omitted_body_does_not_invent_assignment
#print axioms Controls.changed_rhs_changes_observation
#print axioms Controls.counter_unsigned_wrap_is_not_silent_bound_proof
#print axioms Controls.insufficient_fuel_is_not_undefined_read

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead
