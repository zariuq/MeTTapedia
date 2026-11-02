import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex
import Init.Data.SInt.Lemmas
import Init.Data.UInt.Lemmas
import Mettapedia.Languages.C11.IntegerOperators
import Init.Data.UInt.Bitwise
import Mettapedia.Languages.C11.TypedIntegerArithmetic
import Mettapedia.Languages.C11.IntegerProfiles

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
  | byte (value : UInt8)
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

/-- A declared pure service receives every evaluated operand in source order.
Its implementation checks the name, arity and argument types. -/
abbrev CallReader (Ptr : Type) := Name → List (Value Ptr) → Option (Value Ptr)

def noCalls : CallReader Ptr := fun _ _ => none

def truth? : Value Ptr → Option Bool
  | .byte value => some (value != 0)
  | .boolean value => some value
  | .signed value => some (value != 0)
  | .unsigned value => some (value != 0)
  | .unsigned64 value => some (value != 0)
  | .identity value => some value.isSome
  | .identities _ | .wordRecord _ => none

def equal? : Value Ptr → Value Ptr → Option Bool
  | .byte left, .byte right => some (left == right)
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
and multiplication. Division and remainder reject a zero divisor. Unsigned
widening and mixed signed-int addition use the separately proved conversions. -/
def unsignedBinary (operator : BinaryOperator) (left right : UInt32) : Option (Value Ptr) :=
  match operator with
  | .add => some (.unsigned (left + right))
  | .sub => some (.unsigned (left - right))
  | .mul => some (.unsigned (left * right))
  | .div => if right = 0 then none else some (.unsigned (left / right))
  | .mod => if right = 0 then none else some (.unsigned (left % right))
  | .shiftRight =>
      if right.toNat < 32 then some (.unsigned (left >>> right)) else none
  | .shiftLeft =>
      if right.toNat < 32 then some (.unsigned (left <<< right)) else none
  | .bitAnd => some (.unsigned (left &&& right))
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
  | .mod => if right = 0 then none else some (.unsigned64 (left % right))
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (right < left)))
  | .ge => some (.boolean (decide (right ≤ left)))
  | _ => none

/-- Same-type signed comparisons preserve order, including negative values.
Binary signed arithmetic is not admitted by this read fragment. Mixed addition
uses a separate unsigned conversion; modular arithmetic is not a signed-overflow law. -/
def signedComparison (operator : BinaryOperator) (left right : Int32) : Option (Value Ptr) :=
  match operator with
  | .lt => some (.boolean (decide (left < right)))
  | .le => some (.boolean (decide (left ≤ right)))
  | .gt => some (.boolean (decide (right < left)))
  | .ge => some (.boolean (decide (right ≤ left)))
  | _ => none

/-- A shift promotes its operands independently. A signed count is checked
before conversion to the machine count; a negative or excessive count has
no defined shift and cannot be rescued by the host machine's masking. -/
def unsignedSignedShift (operator : BinaryOperator) (left : UInt32) (right : Int32) :
    Option (Value Ptr) :=
  match operator with
  | .shiftLeft | .shiftRight =>
      if 0 ≤ right.toInt ∧ right.toInt < 32 then
        unsignedBinary operator left (UInt32.ofNat right.toInt.toNat)
      else none
  | _ => none

/-- Only an actual 64-bit unsigned operand selects unsigned widening. In particular,
two unsigned 32-bit operands do not silently acquire a larger carrier. -/
def numericBinary (operator : BinaryOperator) : Value Ptr → Value Ptr → Option (Value Ptr)
  | .signed left, .signed right => signedComparison operator left right
  | .unsigned left, .unsigned right =>
      if operator = .lt then some (.boolean (decide (left < right)))
      else unsignedBinary operator left right
  | .unsigned left, .signed right =>
      if operator = .add then some (.unsigned (left + UInt32.ofInt right.toInt))
      else unsignedSignedShift operator left right
  | .signed left, .unsigned right =>
      if operator = .add then some (.unsigned (UInt32.ofInt left.toInt + right)) else none
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
  | .byte _ | .identity _ | .identities _ | .wordRecord _ => none

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

mutual
/-- All operand reads in this fragment are pure. Short-circuit selection is
retained even when the unselected operand would have no defined read. -/
def expression (environment : Environment Ptr) (fields : FieldReader Ptr)
    (operand : CExpr) (calls : CallReader Ptr := noCalls) : Option (Value Ptr) :=
  match operand with
  | .identifier name => environment name
  | .decimal value => signedDecimal? value
  | .unsignedInteger value =>
      if value < 2 ^ 32 then some (.unsigned (UInt32.ofNat value)) else none
  | .word value => some (.unsigned64 (UInt64.ofNat value.toNat))
  | .bool value => some (.boolean value)
  | .null => some (.identity none)
  | .call name operands => do
      let values ← arguments environment fields operands calls
      calls name values
  | .unary .negate operand => do
      let value ← expression environment fields operand calls
      numericNegation? value
  | .unary .not operand => do
      let value ← expression environment fields operand calls
      let truth ← truth? value
      some (.boolean (!truth))
  | .field record name true => do
      let .identity (some owner) ← expression environment fields record calls | none
      fields owner name
  | .field record name false => do
      let .wordRecord members ← expression environment fields record calls | none
      (members.find? (fun member => member.1 == name)).map
        (fun member => .unsigned64 member.2)
  | .index array index => do
      let .identities values ← expression environment fields array calls | none
      let .unsigned position ← expression environment fields index calls | none
      (values[position.toNat]?).map Value.identity
  | .binary .and left right => do
      let first ← expression environment fields left calls
      let selected ← truth? first
      if selected then do
        let second ← expression environment fields right calls
        let selectedSecond ← truth? second
        some (.boolean selectedSecond)
      else some (.boolean false)
  | .binary .or left right => do
      let first ← expression environment fields left calls
      let selected ← truth? first
      if selected then some (.boolean true) else do
        let second ← expression environment fields right calls
        let selectedSecond ← truth? second
        some (.boolean selectedSecond)
  | .binary .eq left right => do
      let first ← expression environment fields left calls
      let second ← expression environment fields right calls
      (equal? first second).map Value.boolean
  | .binary .ne left right => do
      let first ← expression environment fields left calls
      let second ← expression environment fields right calls
      (equal? first second).map (fun value => Value.boolean (!value))
  | .binary .lt left right => do
      let first ← expression environment fields left calls
      let second ← expression environment fields right calls
      numericBinary .lt first second
  | .binary operator left right => do
      let first ← expression environment fields left calls
      let second ← expression environment fields right calls
      numericBinary operator first second
  | .conditional condition yes no => do
      let value ← expression environment fields condition calls
      let selected ← truth? value
      if selected then expression environment fields yes calls else expression environment fields no calls
  | _ => none
termination_by structural operand

def arguments (environment : Environment Ptr) (fields : FieldReader Ptr)
    (operands : List CExpr) (calls : CallReader Ptr := noCalls) : Option (List (Value Ptr)) :=
  match operands with
  | [] => some []
  | operand :: rest => do
      let first ← expression environment fields operand calls
      let remaining ← arguments environment fields rest calls
      some (first :: remaining)
termination_by structural operands
end

/-- Calls retain the ordered values of the complete actual operand list. -/
theorem call_reads_all_arguments (environment : Environment Ptr) (fields : FieldReader Ptr)
    (name : Name) (operands : List CExpr) (calls : CallReader Ptr) :
    expression environment fields (.call name operands) calls =
      (arguments environment fields operands calls).bind (calls name) := rfl

theorem undefined_call_argument_refuses (environment : Environment Ptr)
    (fields : FieldReader Ptr) (name : Name) (operands : List CExpr) (calls : CallReader Ptr)
    (undefined : arguments environment fields operands calls = none) :
    expression environment fields (.call name operands) calls = none := by
  rw [call_reads_all_arguments, undefined]
  rfl

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
theorem boolean_and_read_with_calls (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool) {calls : CallReader Ptr}
    (readLeft : expression locals reader left calls = some (.boolean first))
    (readRight : expression locals reader right calls = some (.boolean second)) :
    expression locals reader (.binary .and left right) calls = some (.boolean (first && second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]

theorem boolean_and_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool)
    (readLeft : expression locals reader left = some (.boolean first))
    (readRight : expression locals reader right = some (.boolean second)) :
    expression locals reader (.binary .and left right) = some (.boolean (first && second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]


theorem boolean_or_read_with_calls (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool) {calls : CallReader Ptr}
    (readLeft : expression locals reader left calls = some (.boolean first))
    (readRight : expression locals reader right calls = some (.boolean second)) :
    expression locals reader (.binary .or left right) calls = some (.boolean (first || second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]

theorem boolean_or_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool)
    (readLeft : expression locals reader left = some (.boolean first))
    (readRight : expression locals reader right = some (.boolean second)) :
    expression locals reader (.binary .or left right) = some (.boolean (first || second)) := by
  rw [expression, readLeft]
  cases first <;> simp [truth?, readRight]


/-- Conditions use their admitted C truth conversion, including wide words
and nullable identities, rather than requiring Boolean-valued operands. -/
theorem boolean_and_truth_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool) {calls : CallReader Ptr}
    (readLeft : (expression locals reader left calls).bind truth? = some first)
    (readRight : (expression locals reader right calls).bind truth? = some second) :
    expression locals reader (.binary .and left right) calls =
      some (.boolean (first && second)) := by
  cases hl : expression locals reader left calls with
  | none => simp [hl] at readLeft
  | some lv =>
      have lt : truth? lv = some first := by simpa [hl] using readLeft
      cases hr : expression locals reader right calls with
      | none => simp [hr] at readRight
      | some rv =>
          have rt : truth? rv = some second := by simpa [hr] using readRight
          cases first <;> simp [expression, hl, hr, lt, rt]

theorem boolean_or_truth_read (locals : Environment Ptr) (reader : FieldReader Ptr)
    (left right : CExpr) (first second : Bool) {calls : CallReader Ptr}
    (readLeft : (expression locals reader left calls).bind truth? = some first)
    (readRight : (expression locals reader right calls).bind truth? = some second) :
    expression locals reader (.binary .or left right) calls =
      some (.boolean (first || second)) := by
  cases hl : expression locals reader left calls with
  | none => simp [hl] at readLeft
  | some lv =>
      have lt : truth? lv = some first := by simpa [hl] using readLeft
      cases hr : expression locals reader right calls with
      | none => simp [hr] at readRight
      | some rv =>
          have rt : truth? rv = some second := by simpa [hr] using readRight
          cases first <;> simp [expression, hl, hr, lt, rt]

def assignValue? : Value Ptr → Value Ptr → Option (Value Ptr)
  | .byte _, .byte value => some (.byte value)
  | .boolean _, value => (truth? value).map Value.boolean
  | .signed _, .signed value => some (.signed value)
  | .unsigned _, .unsigned value => some (.unsigned value)
  | .unsigned64 _, .unsigned64 value => some (.unsigned64 value)
  | .unsigned64 _, .unsigned value => some (.unsigned64 (UInt64.ofNat value.toNat))
  | .identity _, .identity value => some (.identity value)
  | _, _ => none

def assignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (location value : CExpr) (calls : CallReader Ptr := noCalls) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let previous ← environment name
  let evaluated ← expression environment fields value calls
  let converted ← assignValue? previous evaluated
  some (Function.update environment name (some converted))

/-- Boolean operands undergo the C integer promotions before bitwise OR and
conversion back to bool. Both operands are read; logical short circuit is not
an implementation of this compound assignment. Other operand types are not
admitted by this Boolean fragment. -/
def booleanOrAssignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (location value : CExpr) (calls : CallReader Ptr := noCalls) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let .boolean previous ← environment name | none
  let .boolean evaluated ← expression environment fields value calls | none
  some (Function.update environment name (some (.boolean (previous || evaluated))))

/-- Compound unsigned arithmetic reads the local lvalue once and stores the
actual machine result. A Boolean comparison is not an arithmetic assignment. -/
def unsignedCompoundAssignment (environment : Environment Ptr) (fields : FieldReader Ptr)
    (operator : BinaryOperator) (location value : CExpr) (calls : CallReader Ptr := noCalls) : Option (Environment Ptr) := do
  let .identifier name := location | none
  let .unsigned previous ← environment name | none
  let .unsigned evaluated ← expression environment fields value calls | none
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

def statements (fields : FieldReader Ptr) (environment : Environment Ptr)
    (body : List CStatement) (calls : CallReader Ptr := noCalls) : Option (Environment Ptr) :=
  match body with
  | [] => some environment
  | .empty :: rest => statements fields environment rest calls
  | .assign location value :: rest =>
      (assignment environment fields location value calls).bind fun updated =>
        statements fields updated rest calls
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
    (body : List CStatement) (fuel : Nat) (environment : Environment Ptr) (calls : CallReader Ptr := noCalls) : Result Ptr :=
  match (expression environment fields condition calls).bind truth? with
  | none => .finished none
  | some false => .finished (some environment)
  | some true => match fuel with
    | 0 => .exhausted
    | fuel + 1 => match statements fields environment body calls with
      | none => .finished none
      | some updated => match increment updated step with
        | none => .finished none
        | some advanced => run fields condition step body fuel advanced calls

def restore (result : Result Ptr) (name : Name) (old : Option (Value Ptr)) : Result Ptr :=
  match result with
  | .finished completed => .finished (completed.map fun environment =>
      Function.update environment name old)
  | .exhausted => .exhausted

/-- Header admission returns and executes the actual body. It does not compare
that body to a successful scan template or synthesize missing assignments. -/
def countedLoop (fields : FieldReader Ptr) (fuel : Nat) (environment : Environment Ptr)
    (statement : CStatement) (calls : CallReader Ptr := noCalls) : Option (Result Ptr) :=
  match statement with
  | .forLoop type counter initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let .unsigned first ← expression environment fields initial calls | none
        let initialized := Function.update environment counter (some (.unsigned first))
        some (restore (run fields condition step body fuel initialized calls)
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

private def orderedCalls : CallReader Nat := fun name values =>
  if name = "ordered".toList then
    match values with
    | [.unsigned first, .unsigned second] => some (.boolean (decide (first < second)))
    | _ => none
  else if name = "constant".toList then
    match values with
    | [] => some (.unsigned 7)
    | _ => none
  else none

theorem declared_call_keeps_two_ordered_arguments :
    expression environment noFields
      (.call "ordered".toList [.unsignedInteger 1, .unsignedInteger 2]) orderedCalls =
      some (.boolean true) := rfl

theorem reversing_call_arguments_changes_the_answer :
    expression environment noFields
      (.call "ordered".toList [.unsignedInteger 2, .unsignedInteger 1]) orderedCalls =
      some (.boolean false) := rfl

theorem declared_zero_argument_call_is_admitted :
    expression environment noFields (.call "constant".toList []) orderedCalls =
      some (.unsigned 7) := rfl

theorem extra_call_argument_is_not_discarded :
    expression environment noFields
      (.call "ordered".toList [.unsignedInteger 1, .unsignedInteger 2, .unsignedInteger 3])
      orderedCalls = none := rfl

theorem undefined_argument_is_not_replaced_by_a_call_result :
    expression environment noFields
      (.call "ordered".toList [.identifier "missing".toList, .unsignedInteger 2])
      orderedCalls = none := rfl

theorem unselected_call_is_not_read :
    expression environment noFields
      (.binary .and (.bool false) (.call "unknown".toList [])) orderedCalls =
      some (.boolean false) := rfl

theorem selected_unknown_call_is_not_a_false_return :
    expression environment noFields
      (.binary .and (.bool true) (.call "unknown".toList [])) orderedCalls = none := rfl

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

open Mettapedia.Languages.C11
open Mettapedia.Languages.C11.IntegerOperators

/-- The promoted unsigned operand keeps its actual 32-bit value. This
adapter supplies C11's independent integer and representation judgments. -/
def unsigned32Value (value : UInt32) : IntegerValue (.unsigned 32 (by decide)) :=
  ⟨value.toNat, by
    have bounded := value.toNat_lt
    change 0 ≤ (value.toNat : Int) ∧ (value.toNat : Int) ≤ 2 ^ 32 - 1
    omega⟩

def unsigned32Word (value : UInt32) : RepresentationValue (.unsigned 32 (by decide)) :=
  ⟨value.toNat, value.toNat, false,
    .unsigned 32 (by decide) .normal value.toNat value.toNat_lt⟩

/-- Unsigned right shift is division by the declared power of two. The
count guard excludes C's excessive-count undefined behavior before UInt32's
masked machine shift is used. -/
theorem unsigned32_shift_right_c11 (value count : UInt32)
    (within : count.toNat < 32) (policy : RightShiftPolicy) :
    ShiftEvaluation (.unsigned 32 (by decide)) policy .right
      (unsigned32Value value) count.toNat (.value ((value >>> count).toNat : Int) false) := by
  have numeric : ((value >>> count).toNat : Int) =
      (value.toNat : Int) / powerOfTwo count.toNat := by
    rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt within, Nat.shiftRight_eq_div_pow]
    simp only [Int.natCast_ediv, Int.natCast_pow, powerOfTwo]
    rfl
  rw [numeric]
  exact .rightNonnegative (by simpa [validShiftCount, IntegerBits.width] using within)
    (by simp [unsigned32Value]) rfl

theorem unsigned32_shift_right_excessive_c11 (value count : UInt32)
    (outside : 32 ≤ count.toNat) (policy : RightShiftPolicy) :
    ShiftEvaluation (.unsigned 32 (by decide)) policy .right
      (unsigned32Value value) count.toNat (.undefined .shiftCountTooLarge) :=
  .excessiveCount (by omega) (by simpa [IntegerBits.width] using outside)

/-- Every result bit is the conjunction of the corresponding unsigned input
bits. This is the independent bit judgment, not a restatement of the host
operation's result type. -/
theorem unsigned32_bit_and_c11 (left right : UInt32) (policy : NegativeZeroPolicy) :
    BitwiseEvaluation (.unsigned 32 (by decide)) policy .and
      (unsigned32Word left) (unsigned32Word right)
      (.value ((left &&& right).toNat : Int) false) := by
  refine .bits (left &&& right).toNat _ ?_ ?_
  · change WordBinary .and left.toNat right.toNat (left &&& right).toNat
    rw [UInt32.toNat_and]
    exact wordBinary_sound .and left.toNat right.toNat
  · exact .read (.value (left &&& right).toNat false) _
      (.unsigned 32 (by decide) .normal _ (left &&& right).toNat_lt)
      (.ordinary _)


omit [DecidableEq Ptr] in
theorem unsigned_shift_right_success_iff (value count result : UInt32) :
    unsignedBinary (Ptr := Ptr) .shiftRight value count = some (.unsigned result) ↔
      count.toNat < 32 ∧ value >>> count = result := by
  simp only [unsignedBinary]
  split <;> simp_all

omit [DecidableEq Ptr] in
theorem unsigned_shift_right_refused_iff (value count : UInt32) :
    unsignedBinary (Ptr := Ptr) .shiftRight value count = none ↔ 32 ≤ count.toNat := by
  simp only [unsignedBinary]
  split <;> simp_all

omit [DecidableEq Ptr] in
theorem unsigned_shift_right_implements_c11 (value count : UInt32)
    (within : count.toNat < 32) (policy : RightShiftPolicy) :
    unsignedBinary (Ptr := Ptr) .shiftRight value count =
        some (.unsigned (value >>> count)) ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .right
        (unsigned32Value value) count.toNat
        (.value ((value >>> count).toNat : Int) false) := by
  exact ⟨by simp only [unsignedBinary, if_pos within],
    unsigned32_shift_right_c11 value count within policy⟩

omit [DecidableEq Ptr] in
theorem unsigned_bit_and_implements_c11 (left right : UInt32)
    (policy : NegativeZeroPolicy) :
    unsignedBinary (Ptr := Ptr) .bitAnd left right =
        some (.unsigned (left &&& right)) ∧
      BitwiseEvaluation (.unsigned 32 (by decide)) policy .and
        (unsigned32Word left) (unsigned32Word right)
        (.value ((left &&& right).toNat : Int) false) :=
  ⟨rfl, unsigned32_bit_and_c11 left right policy⟩


namespace Controls

theorem unsigned_shift_keeps_high_bit :
    numericBinary (Ptr := Nat) .shiftRight (.unsigned 4294967295) (.unsigned 31) =
      some (.unsigned 1) := by decide +kernel

theorem excessive_shift_is_not_masked :
    numericBinary (Ptr := Nat) .shiftRight (.unsigned 7) (.unsigned 32) = none ∧
    numericBinary (Ptr := Nat) .shiftRight (.unsigned 7) (.unsigned 64) = none := by
  constructor <;> decide +kernel

theorem unsigned_mask_keeps_only_selected_bits :
    numericBinary (Ptr := Nat) .bitAnd (.unsigned 4294967295) (.unsigned 3) =
      some (.unsigned 3) := by decide +kernel

theorem hash_product_wraps_before_shift :
    expression environment noFields
      (.binary .shiftRight
        (.binary .mul (.unsignedInteger 2147483648) (.unsignedInteger 2654435761))
        (.unsignedInteger 31)) = some (.unsigned 1) := by decide +kernel

theorem signed_shift_is_not_unsigned_shift :
    numericBinary (Ptr := Nat) .shiftRight (.signed (-1)) (.signed 1) = none := rfl

theorem byte_shift_needs_explicit_integer_promotion :
    numericBinary (Ptr := Nat) .shiftRight (.byte 255) (.byte 1) = none := rfl

end Controls


section MixedCountShifts
variable {Ptr : Type}

theorem unsigned32_shift_left_c11 (value count : UInt32)
    (within : count.toNat < 32) (policy : RightShiftPolicy) :
    ShiftEvaluation (.unsigned 32 (by decide)) policy .left
      (unsigned32Value value) count.toNat (.value ((value <<< count).toNat : Int) false) := by
  have numeric : ((value <<< count).toNat : Int) =
      ((value.toNat : Int) * powerOfTwo count.toNat) % powerOfTwo 32 := by
    rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt within, Nat.shiftLeft_eq]
    simp only [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, powerOfTwo]
    rfl
  rw [numeric]
  refine .unsignedLeft 32 (by decide) rfl ?_ _ ?_ rfl
  · simpa [validShiftCount, IntegerBits.width] using within
  · exact reduceNumeric_sound (.unsigned 32 (by decide)) _

theorem unsigned32_shift_left_excessive_c11 (value count : UInt32)
    (outside : 32 ≤ count.toNat) (policy : RightShiftPolicy) :
    ShiftEvaluation (.unsigned 32 (by decide)) policy .left
      (unsigned32Value value) count.toNat (.undefined .shiftCountTooLarge) :=
  .excessiveCount (by omega) (by simpa [IntegerBits.width] using outside)

theorem unsigned32_signed_count_value (count : Int32)
    (within : 0 ≤ count.toInt ∧ count.toInt < 32) :
    (UInt32.ofNat count.toInt.toNat).toNat = count.toInt.toNat ∧
      ((UInt32.ofNat count.toInt.toNat).toNat : Int) = count.toInt := by
  have below : count.toInt.toNat < 2 ^ 32 := by omega
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt below]
  exact ⟨rfl, Int.toNat_of_nonneg within.1⟩

theorem unsigned32_signed_right_c11 (value : UInt32) (count : Int32)
    (within : 0 ≤ count.toInt ∧ count.toInt < 32) (policy : RightShiftPolicy) :
    numericBinary (Ptr := Ptr) .shiftRight (.unsigned value) (.signed count) =
        some (.unsigned (value >>> UInt32.ofNat count.toInt.toNat)) ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .right
        (unsigned32Value value) count.toInt
        (.value ((value >>> UInt32.ofNat count.toInt.toNat).toNat : Int) false) := by
  obtain ⟨same, signed⟩ := unsigned32_signed_count_value count within
  have small : (UInt32.ofNat count.toInt.toNat).toNat < 32 := by omega
  constructor
  · simp only [numericBinary, reduceCtorEq, ↓reduceIte, unsignedSignedShift, if_pos within, unsignedBinary, if_pos small]
  · simpa only [signed] using unsigned32_shift_right_c11 value _ small policy

theorem unsigned32_signed_left_c11 (value : UInt32) (count : Int32)
    (within : 0 ≤ count.toInt ∧ count.toInt < 32) (policy : RightShiftPolicy) :
    numericBinary (Ptr := Ptr) .shiftLeft (.unsigned value) (.signed count) =
        some (.unsigned (value <<< UInt32.ofNat count.toInt.toNat)) ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .left
        (unsigned32Value value) count.toInt
        (.value ((value <<< UInt32.ofNat count.toInt.toNat).toNat : Int) false) := by
  obtain ⟨same, signed⟩ := unsigned32_signed_count_value count within
  have small : (UInt32.ofNat count.toInt.toNat).toNat < 32 := by omega
  constructor
  · simp only [numericBinary, reduceCtorEq, ↓reduceIte, unsignedSignedShift, if_pos within, unsignedBinary, if_pos small]
  · simpa only [signed] using unsigned32_shift_left_c11 value _ small policy

theorem signed_count_negative_refuses (value : UInt32) (count : Int32)
    (negative : count.toInt < 0) (policy : RightShiftPolicy) :
    numericBinary (Ptr := Ptr) .shiftRight (.unsigned value) (.signed count) = none ∧
      numericBinary (Ptr := Ptr) .shiftLeft (.unsigned value) (.signed count) = none ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .right
        (unsigned32Value value) count.toInt (.undefined .negativeShiftCount) ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .left
        (unsigned32Value value) count.toInt (.undefined .negativeShiftCount) := by
  have invalid : ¬ (0 ≤ count.toInt ∧ count.toInt < 32) := by omega
  exact ⟨by simp [numericBinary, unsignedSignedShift, invalid],
    by simp [numericBinary, unsignedSignedShift, invalid],
    .negativeCount negative, .negativeCount negative⟩

theorem signed_count_excessive_refuses (value : UInt32) (count : Int32)
    (excessive : 32 ≤ count.toInt) (policy : RightShiftPolicy) :
    numericBinary (Ptr := Ptr) .shiftRight (.unsigned value) (.signed count) = none ∧
      numericBinary (Ptr := Ptr) .shiftLeft (.unsigned value) (.signed count) = none ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .right
        (unsigned32Value value) count.toInt (.undefined .shiftCountTooLarge) ∧
      ShiftEvaluation (.unsigned 32 (by decide)) policy .left
        (unsigned32Value value) count.toInt (.undefined .shiftCountTooLarge) := by
  have invalid : ¬ (0 ≤ count.toInt ∧ count.toInt < 32) := by omega
  exact ⟨by simp [numericBinary, unsignedSignedShift, invalid],
    by simp [numericBinary, unsignedSignedShift, invalid],
    .excessiveCount (by omega) (by simpa [IntegerBits.width] using excessive),
    .excessiveCount (by omega) (by simpa [IntegerBits.width] using excessive)⟩

namespace IdentityShiftControls

theorem signed_literal_extracts_high_bit :
    numericBinary (Ptr := Nat) .shiftRight (.unsigned 4294967295) (.signed 31) =
      some (.unsigned 1) := by decide +kernel

theorem class_macro_shift_keeps_unsigned_type :
    numericBinary (Ptr := Nat) .shiftLeft (.unsigned 1) (.signed 20) =
      some (.unsigned 1048576) := by decide +kernel

theorem left_shift_wraps_at_operand_width :
    numericBinary (Ptr := Nat) .shiftLeft (.unsigned 2147483648) (.signed 1) =
      some (.unsigned 0) := by decide +kernel

theorem negative_count_is_not_host_masking :
    numericBinary (Ptr := Nat) .shiftRight (.unsigned 7) (.signed (-1)) = none := by
  decide +kernel

theorem excessive_count_is_not_host_masking :
    numericBinary (Ptr := Nat) .shiftLeft (.unsigned 7) (.signed 32) = none := by
  decide +kernel

theorem mixed_add_uses_unsigned_conversion :
    numericBinary (Ptr := Nat) .add (.unsigned 7) (.signed 1) =
      some (.unsigned 8) := by decide +kernel

end IdentityShiftControls

end MixedCountShifts

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead.SymbolLookupArithmetic
open Mettapedia.Languages.C11

theorem unsigned32_remainder_c11 (left right : UInt32) (nonzero : right ≠ 0) :
    IntegerBinaryEvaluation (.unsigned 32 (by decide))
      (unsigned32Value left) (unsigned32Value right) .remainder
      (.value ((left % right).toNat : Int)) := by
  have rightNonzero : (unsigned32Value right).value ≠ 0 := by
    intro zero
    apply nonzero
    apply UInt32.toNat.inj
    change right.toNat = 0
    simpa only [unsigned32Value, Int.natCast_eq_zero] using zero
  simpa only [unsigned32Value, UInt32.toNat_mod, Int.ofNat_tmod] using
    unsigned_remainder_c11 32 (by decide) (unsigned32Value left)
      (unsigned32Value right) rightNonzero

def unsigned64Value (value : UInt64) : IntegerValue (.unsigned 64 (by decide)) :=
  ⟨value.toNat, by
    have bounded := value.toNat_lt
    change 0 ≤ (value.toNat : Int) ∧ (value.toNat : Int) ≤ 2 ^ 64 - 1
    omega⟩

theorem unsigned64_remainder_c11 (left right : UInt64) (nonzero : right ≠ 0) :
    IntegerBinaryEvaluation (.unsigned 64 (by decide))
      (unsigned64Value left) (unsigned64Value right) .remainder
      (.value ((left % right).toNat : Int)) := by
  have rightNonzero : (unsigned64Value right).value ≠ 0 := by
    intro zero
    apply nonzero
    apply UInt64.toNat.inj
    change right.toNat = 0
    simpa only [unsigned64Value, Int.natCast_eq_zero] using zero
  simpa only [unsigned64Value, UInt64.toNat_mod, Int.ofNat_tmod] using
    unsigned_remainder_c11 64 (by decide) (unsigned64Value left)
      (unsigned64Value right) rightNonzero

/-- The signed addend is converted modulo the unsigned target width before
addition. Negative values therefore require their full signed integer meaning. -/
theorem ofInt32_value (integer : Int) :
    ((UInt32.ofInt integer).toNat : Int) = integer % powerOfTwo 32 := by
  have lower : 0 ≤ integer % (2 ^ 32) := Int.emod_nonneg _ (by decide)
  have upper : integer % (2 ^ 32) < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have natUpper : (integer % (2 ^ 32)).toNat < 2 ^ 32 := by omega
  simp only [UInt32.ofInt, UInt32.toNat_ofNat_of_lt' natUpper,
    Int.toNat_of_nonneg lower, powerOfTwo]

/-- The native fragment declares a 32-bit signed int and its unsigned peer.
All three existing data models agree on these two types. -/
def signed32Value (model : IntegerDataModel) (value : Int32) :
    IntegerValue ((IntegerType.int).format (integerValueProfile model)) :=
  ⟨value.toInt, by
    have lower := value.le_toInt
    have upper := value.toInt_lt
    change -(2 ^ 31) ≤ value.toInt ∧ value.toInt ≤ 2 ^ 31 - 1
    omega⟩

def promotedUnsigned32Value (model : IntegerDataModel) (value : UInt32) :
    IntegerValue ((IntegerType.unsignedInt).format (integerValueProfile model)) :=
  unsigned32Value value

theorem mixed_add_target (model : IntegerDataModel) :
    usualIntegerType (integerValueProfile model) .unsignedInt .int = .unsignedInt := by
  rfl

theorem unsigned_signed_add_c11 (model : IntegerDataModel) (policy : SignedConversionPolicy)
    (left : UInt32) (right : Int32) :
    TypedIntegerBinaryEvaluation (integerValueProfile model) policy .add .unsignedInt .int
      (promotedUnsigned32Value model left) (signed32Value model right)
      ⟨.unsignedInt, .value ((left + UInt32.ofInt right.toInt).toNat : Int)⟩ := by
  apply (evaluateTypedIntegerBinary_iff (integerValueProfile model) policy .add
    .unsignedInt .int (promotedUnsigned32Value model left)
    (signed32Value model right) _).mp
  change (⟨.unsignedInt, .value (((left.toNat : Int) % powerOfTwo 32 +
    right.toInt % powerOfTwo 32) % powerOfTwo 32)⟩ : TypedIntegerOutcome IntegerExtension) = _
  have leftRange : 0 ≤ (left.toNat : Int) ∧ (left.toNat : Int) < powerOfTwo 32 := by
    have bound := left.toNat_lt
    simp only [powerOfTwo]
    omega
  rw [Int.emod_eq_of_lt leftRange.1 leftRange.2]
  congr 2
  rw [UInt32.toNat_add, Int.natCast_emod, Int.natCast_add, ofInt32_value]
  rfl

theorem signed_unsigned_add_c11 (model : IntegerDataModel) (policy : SignedConversionPolicy)
    (left : Int32) (right : UInt32) :
    TypedIntegerBinaryEvaluation (integerValueProfile model) policy .add .int .unsignedInt
      (signed32Value model left) (promotedUnsigned32Value model right)
      ⟨.unsignedInt, .value ((UInt32.ofInt left.toInt + right).toNat : Int)⟩ := by
  apply (evaluateTypedIntegerBinary_iff (integerValueProfile model) policy .add
    .int .unsignedInt (signed32Value model left)
    (promotedUnsigned32Value model right) _).mp
  change (⟨.unsignedInt, .value ((left.toInt % powerOfTwo 32 +
    (right.toNat : Int) % powerOfTwo 32) % powerOfTwo 32)⟩ : TypedIntegerOutcome IntegerExtension) = _
  have rightRange : 0 ≤ (right.toNat : Int) ∧ (right.toNat : Int) < powerOfTwo 32 := by
    have bound := right.toNat_lt
    simp only [powerOfTwo]
    omega
  rw [Int.emod_eq_of_lt rightRange.1 rightRange.2]
  congr 2
  rw [UInt32.toNat_add, Int.natCast_emod, Int.natCast_add, ofInt32_value]
  rfl

/-- The table capacity is widened before the hash remainder. Its nonzero
bound proves that the subsequent UInt32 cast loses no result bits. -/
theorem hash_remainder_narrowing_exact (hash : UInt64) (capacity : UInt32)
    (nonzero : capacity ≠ 0) :
    (UInt32.ofNat ((hash % UInt64.ofNat capacity.toNat).toNat)).toNat =
      hash.toNat % capacity.toNat := by
  have capacityBound : capacity.toNat < 2 ^ 64 :=
    Nat.lt_trans capacity.toNat_lt (by decide)
  have positive : 0 < capacity.toNat := by
    have notZero : capacity.toNat ≠ 0 := by
      intro zero
      exact nonzero (UInt32.toNat.inj zero)
    omega
  have bounded : hash.toNat % capacity.toNat < 2 ^ 32 :=
    Nat.lt_trans (Nat.mod_lt _ positive) capacity.toNat_lt
  simp only [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' capacityBound,
    UInt32.toNat_ofNat_of_lt' bounded]

/-- Probe increment follows C's unsigned width before the table modulus.
For a valid slot, this increment cannot wrap before reaching the capacity. -/
theorem probe_successor_no_word_wrap (slot capacity : UInt32)
    (within : slot.toNat < capacity.toNat) :
    ((slot + 1) % capacity).toNat = (slot.toNat + 1) % capacity.toNat := by
  have below : slot.toNat + 1 < 2 ^ 32 := by
    have bound := capacity.toNat_lt
    omega
  simp only [UInt32.toNat_mod, UInt32.toNat_add, UInt32.toNat_ofNat,
    Nat.mod_eq_of_lt below]

theorem unsigned32_widens_to64 (value : UInt32) (policy : SignedConversionPolicy) :
    IntegerConverts policy (value.toNat : Int) (.integer (.unsigned 64 (by decide)))
      (.value ((UInt64.ofNat value.toNat).toNat : Int)) := by
  have bound : value.toNat < 2 ^ 64 := Nat.lt_trans value.toNat_lt (by decide)
  rw [UInt64.toNat_ofNat_of_lt' bound]
  apply (convertInteger_iff policy _ _ _).mp
  exact convertInteger_preserves_representable policy _ _ (by
    change 0 ≤ (value.toNat : Int) ∧ (value.toNat : Int) ≤ 2 ^ 64 - 1
    omega)

theorem unsigned64_and_uint_target (model : IntegerDataModel) :
    usualIntegerType (integerValueProfile model)
      (.unsigned (.standard .longLong)) .unsignedInt =
      .unsigned (.standard .longLong) := by
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead.SymbolLookupArithmetic

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead.SymbolLookupArithmetic
open Mettapedia.Languages.C11
variable {Ptr : Type}

theorem unsigned32_remainder_success_iff (left right result : UInt32) :
    unsignedBinary (Ptr := Ptr) .mod left right = some (.unsigned result) ↔
      right ≠ 0 ∧ left % right = result := by
  simp only [unsignedBinary]
  split <;> simp_all

theorem unsigned64_remainder_success_iff (left right result : UInt64) :
    unsigned64Binary (Ptr := Ptr) .mod left right = some (.unsigned64 result) ↔
      right ≠ 0 ∧ left % right = result := by
  simp only [unsigned64Binary]
  split <;> simp_all

theorem unsigned32_remainder_refused_iff (left right : UInt32) :
    unsignedBinary (Ptr := Ptr) .mod left right = none ↔ right = 0 := by
  simp only [unsignedBinary]
  split <;> simp_all

theorem unsigned64_remainder_refused_iff (left right : UInt64) :
    unsigned64Binary (Ptr := Ptr) .mod left right = none ↔ right = 0 := by
  simp only [unsigned64Binary]
  split <;> simp_all

theorem unsigned32_remainder_implements_c11 (left right : UInt32) (nonzero : right ≠ 0) :
    unsignedBinary (Ptr := Ptr) .mod left right = some (.unsigned (left % right)) ∧
      IntegerBinaryEvaluation (.unsigned 32 (by decide))
        (unsigned32Value left) (unsigned32Value right) .remainder
        (.value ((left % right).toNat : Int)) :=
  ⟨by simp only [unsignedBinary, if_neg nonzero],
    unsigned32_remainder_c11 left right nonzero⟩

theorem unsigned64_remainder_implements_c11 (left right : UInt64) (nonzero : right ≠ 0) :
    unsigned64Binary (Ptr := Ptr) .mod left right = some (.unsigned64 (left % right)) ∧
      IntegerBinaryEvaluation (.unsigned 64 (by decide))
        (unsigned64Value left) (unsigned64Value right) .remainder
        (.value ((left % right).toNat : Int)) :=
  ⟨by simp only [unsigned64Binary, if_neg nonzero],
    unsigned64_remainder_c11 left right nonzero⟩

theorem unsigned32_zero_remainder_implements_undefined (left : UInt32) :
    unsignedBinary (Ptr := Ptr) .mod left 0 = none ∧
      IntegerBinaryEvaluation (.unsigned 32 (by decide))
        (unsigned32Value left) (unsigned32Value 0) .remainder (.undefined .divisionByZero) :=
  ⟨rfl, unsigned_remainder_zero_c11 32 (by decide) _ _ rfl⟩

theorem unsigned64_zero_remainder_implements_undefined (left : UInt64) :
    unsigned64Binary (Ptr := Ptr) .mod left 0 = none ∧
      IntegerBinaryEvaluation (.unsigned 64 (by decide))
        (unsigned64Value left) (unsigned64Value 0) .remainder (.undefined .divisionByZero) :=
  ⟨rfl, unsigned_remainder_zero_c11 64 (by decide) _ _ rfl⟩

theorem unsigned_signed_add_implements_c11 (model : IntegerDataModel)
    (policy : SignedConversionPolicy) (left : UInt32) (right : Int32) :
    numericBinary (Ptr := Ptr) .add (.unsigned left) (.signed right) =
        some (.unsigned (left + UInt32.ofInt right.toInt)) ∧
      TypedIntegerBinaryEvaluation (integerValueProfile model) policy .add .unsignedInt .int
        (promotedUnsigned32Value model left) (signed32Value model right)
        ⟨.unsignedInt, .value ((left + UInt32.ofInt right.toInt).toNat : Int)⟩ :=
  ⟨rfl, unsigned_signed_add_c11 model policy left right⟩

theorem signed_unsigned_add_implements_c11 (model : IntegerDataModel)
    (policy : SignedConversionPolicy) (left : Int32) (right : UInt32) :
    numericBinary (Ptr := Ptr) .add (.signed left) (.unsigned right) =
        some (.unsigned (UInt32.ofInt left.toInt + right)) ∧
      TypedIntegerBinaryEvaluation (integerValueProfile model) policy .add .int .unsignedInt
        (signed32Value model left) (promotedUnsigned32Value model right)
        ⟨.unsignedInt, .value ((UInt32.ofInt left.toInt + right).toNat : Int)⟩ :=
  ⟨rfl, signed_unsigned_add_c11 model policy left right⟩

theorem hash_capacity_remainder_implements_c11 (hash : UInt64) (capacity : UInt32)
    (nonzero : capacity ≠ 0) (policy : SignedConversionPolicy) :
    numericBinary (Ptr := Ptr) .mod (.unsigned64 hash) (.unsigned capacity) =
        some (.unsigned64 (hash % UInt64.ofNat capacity.toNat)) ∧
      IntegerConverts policy (capacity.toNat : Int) (.integer (.unsigned 64 (by decide)))
        (.value ((UInt64.ofNat capacity.toNat).toNat : Int)) ∧
      IntegerBinaryEvaluation (.unsigned 64 (by decide))
        (unsigned64Value hash) (unsigned64Value (UInt64.ofNat capacity.toNat)) .remainder
        (.value ((hash % UInt64.ofNat capacity.toNat).toNat : Int)) := by
  have bound : capacity.toNat < 2 ^ 64 := Nat.lt_trans capacity.toNat_lt (by decide)
  have notZero : UInt64.ofNat capacity.toNat ≠ 0 := by
    intro zero
    have equality := congrArg UInt64.toNat zero
    rw [UInt64.toNat_ofNat_of_lt' bound] at equality
    exact nonzero (UInt32.toNat.inj equality)
  exact ⟨by simp only [numericBinary, unsigned64Binary, if_neg notZero],
    unsigned32_widens_to64 capacity policy,
    unsigned64_remainder_c11 hash (UInt64.ofNat capacity.toNat) notZero⟩

namespace Controls

theorem ordinary_unsigned_remainder :
    numericBinary (Ptr := Nat) .mod (.unsigned 17) (.unsigned 5) =
      some (.unsigned 2) := by decide +kernel

theorem hash_is_not_narrowed_before_remainder :
    numericBinary (Ptr := Nat) .mod (.unsigned64 4294967301) (.unsigned 7) =
        some (.unsigned64 2) ∧
      numericBinary (Ptr := Nat) .mod (.unsigned (UInt32.ofNat 4294967301)) (.unsigned 7) =
        some (.unsigned 5) := by constructor <;> decide +kernel

theorem mixed_wide_remainder_retains_widening :
    numericBinary (Ptr := Nat) .mod (.unsigned64 18446744073709551615)
      (.unsigned 4294967295) = some (.unsigned64 0) := by decide +kernel

theorem negative_addend_is_converted_before_addition :
    numericBinary (Ptr := Nat) .add (.unsigned 7) (.signed (-1)) =
      some (.unsigned 6) := by decide +kernel

theorem negative_left_addend_has_same_conversion :
    numericBinary (Ptr := Nat) .add (.signed (-1)) (.unsigned 1) =
      some (.unsigned 0) := by decide +kernel

theorem mixed_addition_wraps_at_unsigned_width :
    numericBinary (Ptr := Nat) .add (.unsigned 4294967295) (.signed 1) =
      some (.unsigned 0) := by decide +kernel

theorem minimum_signed_addend_keeps_all_bits :
    numericBinary (Ptr := Nat) .add (.unsigned 0) (.signed (-2147483648)) =
      some (.unsigned 2147483648) := by decide +kernel

theorem zero_divisors_do_not_return_host_remainders :
    numericBinary (Ptr := Nat) .mod (.unsigned 17) (.unsigned 0) = none ∧
    numericBinary (Ptr := Nat) .mod (.unsigned64 17) (.unsigned 0) = none := by
  constructor <;> rfl

/-- Signed remainder is outside this bounded reader profile, rather than
silently assigned unsigned remainder semantics. -/
theorem signed_remainder_requires_its_own_admission :
    numericBinary (Ptr := Nat) .mod (.signed (-7)) (.signed 3) = none := rfl

theorem byte_remainder_needs_integer_promotion :
    numericBinary (Ptr := Nat) .mod (.byte 255) (.byte 7) = none := rfl

theorem pointer_modulus_is_not_address_arithmetic :
    numericBinary (Ptr := Nat) .mod (.identity (some 17)) (.unsigned 7) = none := rfl

theorem mixed_multiplication_remains_outside_the_profile :
    numericBinary (Ptr := Nat) .mul (.unsigned 7) (.signed 1) = none ∧
    numericBinary (Ptr := Nat) .mul (.signed 1) (.unsigned 7) = none := by
  constructor <;> rfl

def slotEnvironment : Environment Nat := fun name =>
  if name = "slot".toList then some (.unsigned 6)
  else if name = "capacity".toList then some (.unsigned 7)
  else none

theorem actual_probe_literal_is_a_signed_int :
    expression slotEnvironment (fun _ _ => none)
      (.binary .mod
        (.binary .add (.identifier "slot".toList) (.decimal 1))
        (.identifier "capacity".toList)) = some (.unsigned 0) := by
  decide +kernel

end Controls
end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.ScalarRead.SymbolLookupArithmetic
