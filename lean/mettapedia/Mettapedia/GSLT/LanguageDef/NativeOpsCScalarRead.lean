import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex
import Init.Data.SInt.Lemmas
import Init.Data.UInt.Lemmas

/-!
# Typed scalar reads and counted local loops in retained C syntax

This fragment executes immutable identity-array reads, signed 32-bit scalar
transport, comparisons and nonoverflowing negation, UInt32/UInt64 comparisons,
pointer equality, Boolean conversion and short-circuit conditions. Inline word
records retain the widths of their members; they are not pointers or arbitrary
recursive C structures. Statement
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
  | signed (value : Int32)
  | unsigned (value : UInt32)
  | unsigned64 (value : UInt64)
  | identity (value : Option Ptr)
  | identities (values : List (Option Ptr))
  | wordRecord (fields : List (Name × UInt64))
  deriving DecidableEq, Repr

abbrev Environment (Ptr : Type) := Name → Option (Value Ptr)
abbrev FieldReader (Ptr : Type) := Ptr → Name → Option (Value Ptr)

def truth? : Value Ptr → Option Bool
  | .boolean value => some value
  | .signed value => some (value != 0)
  | .unsigned value => some (value != 0)
  | .unsigned64 value => some (value != 0)
  | .identity value => some value.isSome
  | .identities _ | .wordRecord _ => none

def equal? : Value Ptr → Value Ptr → Option Bool
  | .boolean left, .boolean right => some (left == right)
  | .signed left, .signed right => some (left == right)
  | .unsigned left, .unsigned right => some (left == right)
  | .unsigned64 left, .unsigned64 right => some (left == right)
  | .unsigned left, .unsigned64 right => some (UInt64.ofNat left.toNat == right)
  | .unsigned64 left, .unsigned right => some (left == UInt64.ofNat right.toNat)
  | .identity left, .identity right => some (decide (left = right))
  | _, _ => none

/-- The admitted operands already have the common unsigned 32-bit type.
Arithmetic uses the machine operation, including modular addition, subtraction
and multiplication. A zero divisor has no defined execution. Unsigned widening
is handled separately; signed integer promotions are outside this fragment. -/
def unsignedBinary (operator : BinaryOperator) (left right : UInt32) : Option (Value Ptr) :=
  match operator with
  | .add => some (.unsigned (left + right))
  | .sub => some (.unsigned (left - right))
  | .mul => some (.unsigned (left * right))
  | .div => if right = 0 then none else some (.unsigned (left / right))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (right < left)))
  | .ge => some (.boolean (decide (right ≤ left)))
  | _ => none

/-- Unsigned 64-bit operands retain their width and modular arithmetic.
The 32-bit fragment remains separate, so widening a read does not erase wrap. -/
def unsigned64Binary (operator : BinaryOperator) (left right : UInt64) : Option (Value Ptr) :=
  match operator with
  | .add => some (.unsigned64 (left + right))
  | .sub => some (.unsigned64 (left - right))
  | .mul => some (.unsigned64 (left * right))
  | .div => if right = 0 then none else some (.unsigned64 (left / right))
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (right < left)))
  | .ge => some (.boolean (decide (right ≤ left)))
  | _ => none

/-- Same-type signed comparisons preserve order, including negative values.
Binary signed arithmetic and mixed signed/unsigned promotions are not admitted by
this read fragment; modular machine arithmetic is not a C signed-overflow law. -/
def signedComparison (operator : BinaryOperator) (left right : Int32) : Option (Value Ptr) :=
  match operator with
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (right < left)))
  | .ge => some (.boolean (decide (right ≤ left)))
  | _ => none

/-- Only an actual 64-bit unsigned operand selects unsigned widening. In particular,
two unsigned 32-bit operands do not silently acquire a larger carrier. -/
def numericBinary (operator : BinaryOperator) : Value Ptr → Value Ptr → Option (Value Ptr)
  | .signed left, .signed right => signedComparison operator left right
  | .unsigned left, .unsigned right =>
      if operator = .lt then some (.boolean (decide (left < right)))
      else unsignedBinary operator left right
  | .unsigned64 left, .unsigned64 right => unsigned64Binary operator left right
  | .unsigned left, .unsigned64 right =>
      unsigned64Binary operator (UInt64.ofNat left.toNat) right
  | .unsigned64 left, .unsigned right =>
      unsigned64Binary operator left (UInt64.ofNat right.toNat)
  | _, _ => none

/-- This signed-int profile admits exactly the nonnegative decimal magnitudes
that C can represent as its supplied 32-bit int type. Larger decimal constants
need a separately admitted wider signed type. -/
def signedDecimal? (magnitude : Nat) : Option (Value Ptr) :=
  if magnitude < 2 ^ 31 then some (.signed (Int32.ofNat magnitude)) else none

/-- Unary minus performs the admitted integer promotions. Signed overflow has
no result; unsigned subtraction retains the operand's modular width. -/
def numericNegation? : Value Ptr → Option (Value Ptr)
  | .boolean value => some (.signed (if value then -1 else 0))
  | .signed value =>
      if value = Int32.minValue then none else some (.signed (Int32.ofInt (-value.toInt)))
  | .unsigned value => some (.unsigned (0 - value))
  | .unsigned64 value => some (.unsigned64 (0 - value))
  | .identity _ | .identities _ | .wordRecord _ => none

omit [DecidableEq Ptr] in
theorem decimal_signed_value (magnitude : Nat) (inRange : magnitude < 2 ^ 31) :
    (signedDecimal? (Ptr := Ptr) magnitude).map (fun value => match value with
      | .signed value => value.toInt
      | _ => 0) = some (magnitude : Int) := by
  simp only [signedDecimal?, if_pos inRange, Option.map_some]
  exact congrArg some (Int32.toInt_ofNat_of_lt inRange)

omit [DecidableEq Ptr] in
theorem signed_negation_preserves_integer (value : Int32) (nonoverflow : value ≠ Int32.minValue) :
    (numericNegation? (Ptr := Ptr) (.signed value)).map (fun value => match value with
      | .signed value => value.toInt
      | _ => 0) = some (-value.toInt) := by
  have minimum : value.toInt ≠ -(2 ^ 31 : Int) := by
    intro equality
    apply nonoverflow
    apply Int32.toInt.inj
    simpa only [Int32.toInt_minValue] using equality
  have lower := Int32.le_toInt value
  have upper := Int32.toInt_lt value
  simp only [numericNegation?, if_neg nonoverflow, Option.map_some]
  exact congrArg some (Int32.toInt_ofInt_of_le (by omega) (by omega))

omit [DecidableEq Ptr] in
theorem signed_negation_is_machine_negation (value : Int32)
    (nonoverflow : value ≠ Int32.minValue) :
    numericNegation? (Ptr := Ptr) (.signed value) = some (.signed (-value)) := by
  simp only [numericNegation?, if_neg nonoverflow]
  have operation : -value = Int32.ofInt (-value.toInt) := by
    calc
      -value = -(Int32.ofInt value.toInt) := congrArg Neg.neg (Int32.ofInt_toInt value).symm
      _ = Int32.ofInt (-value.toInt) := Int32.neg_ofInt
  rw [← operation]

omit [DecidableEq Ptr] in
theorem unsigned32_negation_keeps_modulus (value : UInt32) :
    (numericNegation? (Ptr := Ptr) (.unsigned value)).map (fun value => match value with
      | .unsigned value => value.toNat
      | _ => 0) = some ((2 ^ 32 - value.toNat) % 2 ^ 32) := by
  simp only [numericNegation?, Option.map_some, UInt32.toNat_sub]
  rfl

omit [DecidableEq Ptr] in
theorem unsigned64_negation_keeps_modulus (value : UInt64) :
    (numericNegation? (Ptr := Ptr) (.unsigned64 value)).map (fun value => match value with
      | .unsigned64 value => value.toNat
      | _ => 0) = some ((2 ^ 64 - value.toNat) % 2 ^ 64) := by
  simp only [numericNegation?, Option.map_some, UInt64.toNat_sub]
  rfl

/-- All operand reads in this fragment are pure. Short-circuit selection is
retained even when the unselected operand would have no defined read. -/
def expression (environment : Environment Ptr) (fields : FieldReader Ptr) :
    CExpr → Option (Value Ptr)
  | .identifier name => environment name
  | .decimal value => signedDecimal? value
  | .unsignedInteger value =>
      if value < 2 ^ 32 then some (.unsigned (UInt32.ofNat value)) else none
  | .word value => some (.unsigned64 (UInt64.ofNat value.toNat))
  | .bool value => some (.boolean value)
  | .null => some (.identity none)
  | .unary .negate operand => do
      let value ← expression environment fields operand
      numericNegation? value
  | .unary .not operand => do
      let value ← expression environment fields operand
      let truth ← truth? value
      some (.boolean (!truth))
  | .field record name true => do
      let .identity (some owner) ← expression environment fields record | none
      fields owner name
  | .field record name false => do
      let .wordRecord members ← expression environment fields record | none
      (members.find? (fun member => member.1 == name)).map
        (fun member => .unsigned64 member.2)
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
      let first ← expression environment fields left
      let second ← expression environment fields right
      numericBinary .lt first second
  | .binary operator left right => do
      let first ← expression environment fields left
      let second ← expression environment fields right
      numericBinary operator first second
  | .conditional condition yes no => do
      let value ← expression environment fields condition
      let selected ← truth? value
      if selected then expression environment fields yes else expression environment fields no
  | _ => none

/-- A declared local pointer supplies the owner; the reader supplies the
selected live member. Neither a spelling nor non-nullness supplies layout. -/
theorem pointer_field_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (localName member : Name) (owner : Ptr) (value : Value Ptr)
    (localRead : locals localName = some (.identity (some owner)))
    (memberRead : reader owner member = some value) :
    expression locals reader (.field (.identifier localName) member true) = some value := by
  change (locals localName).bind (fun v => match v with
    | .identity (some p) => reader p member
    | _ => none) = some value
  rw [localRead]
  exact memberRead

/-- Pure Boolean operands compose without inventing a read of the skipped
branch. Undefined selected operands still have no execution. -/
theorem boolean_and_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool)
    (readLeft : expression locals reader left = some (.boolean first))
    (readRight : expression locals reader right = some (.boolean second)) :
    expression locals reader (.binary .and left right) = some (.boolean (first && second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]

theorem boolean_or_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool)
    (readLeft : expression locals reader left = some (.boolean first))
    (readRight : expression locals reader right = some (.boolean second)) :
    expression locals reader (.binary .or left right) = some (.boolean (first || second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]

def assignValue? : Value Ptr → Value Ptr → Option (Value Ptr)
  | .boolean _, value => (truth? value).map Value.boolean
  | .signed _, .signed value => some (.signed value)
  | .unsigned _, .unsigned value => some (.unsigned value)
  | .unsigned64 _, .unsigned64 value => some (.unsigned64 value)
  | .unsigned64 _, .unsigned value => some (.unsigned64 (UInt64.ofNat value.toNat))
  | .identity _, .identity value => some (.identity value)
  | _, _ => none

def assignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (location value : CExpr) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let previous ← environment name
  let evaluated ← expression environment fields value
  let converted ← assignValue? previous evaluated
  some (Function.update environment name (some converted))

/-- Boolean operands undergo the C integer promotions before bitwise OR and
conversion back to bool. Both operands are read; logical short circuit is not
an implementation of this compound assignment. Other operand types are not
admitted by this Boolean fragment. -/
def booleanOrAssignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (location value : CExpr) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let .boolean previous ← environment name | none
  let .boolean evaluated ← expression environment fields value | none
  some (Function.update environment name (some (.boolean (previous || evaluated))))

/-- Compound unsigned arithmetic reads the local lvalue once and stores the
actual machine result. A Boolean comparison is not an arithmetic assignment. -/
def unsignedCompoundAssignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (operator : BinaryOperator) (location value : CExpr) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let .unsigned previous ← environment name | none
  let .unsigned evaluated ← expression environment fields value | none
  let .unsigned combined ← unsignedBinary (Ptr := Ptr) operator previous evaluated | none
  some (Function.update environment name (some (.unsigned combined)))

theorem unsigned_multiply_assignment_reads_actual_operands (environment : Environment Ptr)
    (fields : FieldReader Ptr) (name : Name) (value : CExpr) (previous evaluated : UInt32)
    (oldRead : environment name = some (.unsigned previous))
    (valueRead : expression environment fields value = some (.unsigned evaluated)) :
    unsignedCompoundAssignment environment fields .mul (.identifier name) value =
      some (Function.update environment name (some (.unsigned (previous * evaluated)))) := by
  simp only [unsignedCompoundAssignment, oldRead, valueRead, unsignedBinary, bind, Option.bind]

theorem boolean_or_assignment_reads_both_operands (environment : Environment Ptr)
    (fields : FieldReader Ptr) (name : Name) (value : CExpr) (previous evaluated : Bool)
    (oldRead : environment name = some (.boolean previous))
    (valueRead : expression environment fields value = some (.boolean evaluated)) :
    booleanOrAssignment environment fields (.identifier name) value =
      some (Function.update environment name (some (.boolean (previous || evaluated)))) := by
  simp only [booleanOrAssignment, oldRead, valueRead, bind, Option.bind]

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

theorem signed_negative_is_less_than_zero :
    numericBinary (Ptr := Nat) .lt (.signed (-1)) (.signed 0) =
      some (.boolean true) := by decide +kernel

theorem signed_minimum_is_retained :
    assignValue? (Ptr := Nat) (.signed 0) (.signed (-2147483648)) =
      some (.signed (-2147483648)) := rfl

theorem signed_maximum_is_retained :
    assignValue? (Ptr := Nat) (.signed 0) (.signed 2147483647) =
      some (.signed 2147483647) := rfl

theorem signed_overflow_is_not_unsigned_wrap :
    numericBinary (Ptr := Nat) .add (.signed 2147483647) (.signed 1) = none := rfl

theorem mixed_signed_unsigned_order_is_not_guessed :
    numericBinary (Ptr := Nat) .lt (.signed (-1)) (.unsigned 0) = none := rfl

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

theorem compound_or_can_set_a_false_flag :
    (booleanOrAssignment environment noFields (.identifier "present".toList) (.bool true)).bind
      (fun after => after "present".toList) = some (.boolean true) := rfl

theorem compound_or_true_lhs_still_reads_rhs :
    booleanOrAssignment
      (Function.update environment "present".toList (some (.boolean true))) noFields
      (.identifier "present".toList) (.identifier "missing".toList) = none := rfl

theorem compound_or_rejects_nonboolean_rhs :
    booleanOrAssignment environment noFields (.identifier "present".toList)
      (.unsignedInteger 1) = none := rfl

theorem unsigned_multiplication_retains_wrap :
    expression environment noFields
      (.binary .mul (.unsignedInteger 2147483648) (.unsignedInteger 2)) =
      some (.unsigned 0) := by decide +kernel

theorem unsigned_division_by_zero_is_undefined :
    expression environment noFields
      (.binary .div (.unsignedInteger 17) (.unsignedInteger 0)) = none := rfl

theorem conditional_skips_unselected_undefined_read :
    expression environment noFields
      (.conditional (.bool true) (.unsignedInteger 4) (.identifier ['m'])) =
      some (.unsigned 4) := rfl

theorem conditional_selected_undefined_read_is_not_zero :
    expression environment noFields
      (.conditional (.bool false) (.unsignedInteger 4) (.identifier ['m'])) = none := rfl

def wideEnvironment : Environment Nat := fun name =>
  if name = "cursor".toList then some (.unsigned64 4294967296)
  else if name = "child".toList then
    some (.wordRecord [("len".toList, 4294967297)])
  else none

theorem wide_cursor_keeps_unread_occurrence :
    expression wideEnvironment noFields
      (.binary .lt (.identifier "cursor".toList)
        (.field (.identifier "child".toList) "len".toList false)) =
      some (.boolean true) := by decide +kernel

theorem truncating_wide_cursor_changes_zero_observation :
    expression wideEnvironment noFields
      (.binary .eq (.identifier "cursor".toList) (.unsignedInteger 0)) =
      some (.boolean false) ∧
    equal? (Ptr := Nat) (.unsigned (UInt32.ofNat 4294967296)) (.unsigned 0) =
      some true := by constructor <;> decide +kernel

theorem mixed_unsigned_comparison_widens :
    numericBinary (Ptr := Nat) .lt (.unsigned 4294967295) (.unsigned64 4294967296) =
      some (.boolean true) := by decide +kernel

theorem wide_arithmetic_retains_wrap :
    numericBinary (Ptr := Nat) .add (.unsigned64 18446744073709551615) (.unsigned 1) =
      some (.unsigned64 0) := by decide +kernel

theorem inline_word_record_missing_member_is_undefined :
    expression wideEnvironment noFields
      (.field (.identifier "child".toList) "missing".toList false) = none := rfl

theorem inline_word_record_cannot_be_dereferenced :
    expression wideEnvironment noFields
      (.field (.identifier "child".toList) "len".toList true) = none := rfl


theorem negative_one :
    (signedDecimal? (Ptr := Nat) 1).bind numericNegation? = some (.signed (-1)) := by
  decide +kernel

theorem signed_minimum_is_not_wrapped :
    numericNegation? (Ptr := Nat) (.signed (-2147483648)) = none := rfl

theorem larger_decimal_is_not_narrowed :
    signedDecimal? (Ptr := Nat) 2147483648 = none := rfl

theorem pointer_negation_has_no_execution :
    numericNegation? (Ptr := Nat) (.identity (some 1)) = none := rfl

theorem unsigned_widths_remain_distinct :
    numericNegation? (Ptr := Nat) (.unsigned 1) = some (.unsigned 4294967295) ∧
    numericNegation? (Ptr := Nat) (.unsigned64 1) = some (.unsigned64 18446744073709551615) := by
  constructor <;> decide +kernel

theorem boolean_negation_promotes_to_signed_int :
    numericNegation? (Ptr := Nat) (.boolean true) = some (.signed (-1)) ∧
    numericNegation? (Ptr := Nat) (.boolean false) = some (.signed 0) := by
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
#print axioms boolean_or_assignment_reads_both_operands
#print axioms Controls.compound_or_can_set_a_false_flag
#print axioms Controls.compound_or_true_lhs_still_reads_rhs
#print axioms Controls.compound_or_rejects_nonboolean_rhs
#print axioms unsigned_multiply_assignment_reads_actual_operands
#print axioms Controls.unsigned_multiplication_retains_wrap
#print axioms Controls.unsigned_division_by_zero_is_undefined
#print axioms Controls.conditional_skips_unselected_undefined_read
#print axioms Controls.conditional_selected_undefined_read_is_not_zero
#print axioms Controls.wide_cursor_keeps_unread_occurrence
#print axioms Controls.truncating_wide_cursor_changes_zero_observation
#print axioms Controls.mixed_unsigned_comparison_widens
#print axioms Controls.wide_arithmetic_retains_wrap
#print axioms Controls.inline_word_record_missing_member_is_undefined
#print axioms Controls.inline_word_record_cannot_be_dereferenced

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead
