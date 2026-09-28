import Mettapedia.OSLF.Syntax.FreeBindingTerms
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents

/-!
# The terms-only JSON rung

This many-sorted first-order signature makes the source's implicit list
structure explicit. Booleans, rational numbers, and strings are host-valued
nullary operators; value and field lists have their own constructors. The
independent four-sorted data type below is used to test the claim that the
closed, equation-free terms are exactly algebraic data values.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.JsonTermRung

inductive Srt where
  | value | field | values | fields
  deriving DecidableEq

inductive Op : Srt → Type where
  | null : Op .value
  | bool (value : Bool) : Op .value
  | num (value : Rat) : Op .value
  | str (value : String) : Op .value
  | arr : Op .value
  | obj : Op .value
  | member (key : String) : Op .field
  | valuesNil : Op .values
  | valuesCons : Op .values
  | fieldsNil : Op .fields
  | fieldsCons : Op .fields

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} op => match op with
    | .null | .bool _ | .num _ | .str _ |
      .valuesNil | .fieldsNil => []
    | .arr => [([], .values)]
    | .obj => [([], .fields)]
    | .member _ => [([], .value)]
    | .valuesCons => [([], .value), ([], .values)]
    | .fieldsCons => [([], .field), ([], .fields)]

mutual
inductive Value where
  | null
  | bool (value : Bool)
  | num (value : Rat)
  | str (value : String)
  | arr (values : Values)
  | obj (fields : Fields)

inductive Field where
  | member (key : String) (value : Value)

inductive Values where
  | nil
  | cons (head : Value) (tail : Values)

inductive Fields where
  | nil
  | cons (head : Field) (tail : Fields)
end

mutual
def encodeValue : Value → Term sig [] .value
  | .null => .op .null .nil
  | .bool value => .op (.bool value) .nil
  | .num value => .op (.num value) .nil
  | .str value => .op (.str value) .nil
  | .arr values => .op .arr (.cons (encodeValues values) .nil)
  | .obj fields => .op .obj (.cons (encodeFields fields) .nil)

def encodeField : Field → Term sig [] .field
  | .member key value => .op (.member key) (.cons (encodeValue value) .nil)

def encodeValues : Values → Term sig [] .values
  | .nil => .op .valuesNil .nil
  | .cons head tail =>
      .op .valuesCons (.cons (encodeValue head) (.cons (encodeValues tail) .nil))

def encodeFields : Fields → Term sig [] .fields
  | .nil => .op .fieldsNil .nil
  | .cons head tail =>
      .op .fieldsCons (.cons (encodeField head) (.cons (encodeFields tail) .nil))
end

mutual
def decodeValue : Term sig [] .value → Value
  | .var v => nomatch v
  | .op .null .nil => .null
  | .op (.bool value) .nil => .bool value
  | .op (.num value) .nil => .num value
  | .op (.str value) .nil => .str value
  | .op .arr (.cons values .nil) => .arr (decodeValues values)
  | .op .obj (.cons fields .nil) => .obj (decodeFields fields)
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

def decodeField : Term sig [] .field → Field
  | .var v => nomatch v
  | .op (.member key) (.cons value .nil) => .member key (decodeValue value)
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

def decodeValues : Term sig [] .values → Values
  | .var v => nomatch v
  | .op .valuesNil .nil => .nil
  | .op .valuesCons (.cons head (.cons tail .nil)) =>
      .cons (decodeValue head) (decodeValues tail)
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

def decodeFields : Term sig [] .fields → Fields
  | .var v => nomatch v
  | .op .fieldsNil .nil => .nil
  | .op .fieldsCons (.cons head (.cons tail .nil)) =>
      .cons (decodeField head) (decodeFields tail)
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]
end

mutual
theorem decode_encode_value : ∀ value : Value,
    decodeValue (encodeValue value) = value
  | .null => by simp only [encodeValue, decodeValue]
  | .bool _ => by simp only [encodeValue, decodeValue]
  | .num _ => by simp only [encodeValue, decodeValue]
  | .str _ => by simp only [encodeValue, decodeValue]
  | .arr values => by
      simp only [encodeValue, decodeValue, decode_encode_values values]
  | .obj fields => by
      simp only [encodeValue, decodeValue, decode_encode_fields fields]

theorem decode_encode_field : ∀ field : Field,
    decodeField (encodeField field) = field
  | .member key value => by
      simp only [encodeField, decodeField, decode_encode_value value]

theorem decode_encode_values : ∀ values : Values,
    decodeValues (encodeValues values) = values
  | .nil => by simp only [encodeValues, decodeValues]
  | .cons head tail => by
      simp only [encodeValues, decodeValues,
        decode_encode_value head, decode_encode_values tail]

theorem decode_encode_fields : ∀ fields : Fields,
    decodeFields (encodeFields fields) = fields
  | .nil => by simp only [encodeFields, decodeFields]
  | .cons head tail => by
      simp only [encodeFields, decodeFields,
        decode_encode_field head, decode_encode_fields tail]
end

mutual
theorem encode_decode_value : ∀ term : Term sig [] .value,
    encodeValue (decodeValue term) = term
  | .var v => nomatch v
  | .op .null .nil => by simp only [decodeValue, encodeValue]
  | .op (.bool value) .nil => by simp only [decodeValue, encodeValue]
  | .op (.num value) .nil => by simp only [decodeValue, encodeValue]
  | .op (.str value) .nil => by simp only [decodeValue, encodeValue]
  | .op .arr (.cons values .nil) => by
      simp only [decodeValue, encodeValue, encode_decode_values values]
  | .op .obj (.cons fields .nil) => by
      simp only [decodeValue, encodeValue, encode_decode_fields fields]
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

theorem encode_decode_field : ∀ term : Term sig [] .field,
    encodeField (decodeField term) = term
  | .var v => nomatch v
  | .op (.member key) (.cons value .nil) => by
      simp only [decodeField, encodeField, encode_decode_value value]
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

theorem encode_decode_values : ∀ term : Term sig [] .values,
    encodeValues (decodeValues term) = term
  | .var v => nomatch v
  | .op .valuesNil .nil => by simp only [decodeValues, encodeValues]
  | .op .valuesCons (.cons head (.cons tail .nil)) => by
      simp only [decodeValues, encodeValues,
        encode_decode_value head, encode_decode_values tail]
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]

theorem encode_decode_fields : ∀ term : Term sig [] .fields,
    encodeFields (decodeFields term) = term
  | .var v => nomatch v
  | .op .fieldsNil .nil => by simp only [decodeFields, encodeFields]
  | .op .fieldsCons (.cons head (.cons tail .nil)) => by
      simp only [decodeFields, encodeFields,
        encode_decode_field head, encode_decode_fields tail]
termination_by term => termSize term
decreasing_by
  all_goals simp [termSize, argsSize]
end

/-- The independent JSON value datatype and the closed, sorted raw terms
are isomorphic, with no quotient or equations. -/
def closedValueEquiv : Value ≃ Term sig [] .value where
  toFun := encodeValue
  invFun := decodeValue
  left_inv := decode_encode_value
  right_inv := encode_decode_value

def closedFieldEquiv : Field ≃ Term sig [] .field where
  toFun := encodeField
  invFun := decodeField
  left_inv := decode_encode_field
  right_inv := encode_decode_field

def closedValuesEquiv : Values ≃ Term sig [] .values where
  toFun := encodeValues
  invFun := decodeValues
  left_inv := decode_encode_values
  right_inv := encode_decode_values

def closedFieldsEquiv : Fields ≃ Term sig [] .fields where
  toFun := encodeFields
  invFun := decodeFields
  left_inv := decode_encode_fields
  right_inv := encode_decode_fields

/-- The general free binding-term algebra supplies the terms-only universal
property for this concrete JSON signature. -/
def termsInitial : CategoryTheory.Limits.IsInitial
    (FreeBindingTerms.terms sig) :=
  FreeBindingTerms.termsIsInitial sig

/-- No equations and no operational rules are authored at this rung. -/
def termsOnly : UnpositionedPresentation sig where
  metas := []
  eqs := []
  rules := []

theorem no_closed_reduction {sort : Srt}
    (source target : Term sig [] sort) :
    ¬ termsOnly.StepModE source target := by
  rintro ⟨ruleIndex, _⟩
  exact ruleIndex.elim0

/-- Object member occurrences are retained in this exact algebraic-data
presentation, including duplicate keys. -/
def oneMember : Value :=
  .obj (.cons (.member "x" .null) .nil)

def twoMembers : Value :=
  .obj (.cons (.member "x" .null)
    (.cons (.member "x" .null) .nil))

theorem duplicate_members_distinct :
    encodeValue twoMembers ≠ encodeValue oneMember := by
  intro equal
  change closedValueEquiv twoMembers = closedValueEquiv oneMember at equal
  have impossible := closedValueEquiv.injective equal
  cases impossible

end Mettapedia.OSLF.Binding.JsonTermRung
