import Mettapedia.OSLF.Syntax.JsonCollectionRepresentationBoundary

/-!
# Tagged closed JSON data in the authored pattern carrier

The authored JSON declaration has two vector-valued constructors with one
result sort. This encoding keeps their labels on the pattern nodes. External
scalar values are encoded as data under their respective constructor tags;
the raw `Pattern` type itself has no built-in rational literal node. The
encoding is a representation of closed JSON data, not a claim that the current
bare-collection `HasType` judgment already admits every encoded pattern.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.JsonTaggedDataEncoding

open Mettapedia.OSLF.Binding.JsonTermRung
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Natural numbers are represented structurally, independently of decimal
printing or a host parser. -/
def encodeNat : Nat → Pattern
  | 0 => .apply "scalar:nat-zero" []
  | n + 1 => .apply "scalar:nat-succ" [encodeNat n]

/-- The integer sign is explicit; `negSucc` avoids a duplicate zero code. -/
def encodeInt : Int → Pattern
  | .ofNat n => .apply "scalar:int-pos" [encodeNat n]
  | .negSucc n => .apply "scalar:int-neg-succ" [encodeNat n]

/-- A rational is represented by its canonical numerator and denominator. -/
def encodeRat (q : Rat) : Pattern :=
  .apply "scalar:rat" [encodeInt q.num, encodeNat q.den]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro a b equal
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [encodeNat] at equal
  | succ a inductionHypothesis =>
      cases b with
      | zero => simp [encodeNat] at equal
      | succ b =>
          have inner : encodeNat a = encodeNat b := by
            simpa [encodeNat] using equal
          exact congrArg Nat.succ (inductionHypothesis inner)

theorem encodeInt_injective : Function.Injective encodeInt := by
  intro a b equal
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          have inner : encodeNat a = encodeNat b := by
            simpa [encodeInt] using equal
          exact congrArg Int.ofNat (encodeNat_injective inner)
      | negSucc b => simp [encodeInt] at equal
  | negSucc a =>
      cases b with
      | ofNat b => simp [encodeInt] at equal
      | negSucc b =>
          have inner : encodeNat a = encodeNat b := by
            simpa [encodeInt] using equal
          exact congrArg Int.negSucc (encodeNat_injective inner)

theorem encodeRat_injective : Function.Injective encodeRat := by
  intro a b equal
  have components :
      [encodeInt a.num, encodeNat a.den] =
        [encodeInt b.num, encodeNat b.den] := by
    simpa [encodeRat] using equal
  have numerator : a.num = b.num :=
    encodeInt_injective (List.head_eq_of_cons_eq components)
  have denominator : a.den = b.den := by
    have tails := congrArg List.tail components
    exact encodeNat_injective (List.head_eq_of_cons_eq tails)
  exact Rat.ext numerator denominator

mutual

/-- Preserve all seven authored JSON constructor labels. -/
def encodeValue : Value → Pattern
  | .null => .apply "JNull" []
  | .bool true => .apply "JBool" [.apply "scalar:true" []]
  | .bool false => .apply "JBool" [.apply "scalar:false" []]
  | .num q => .apply "JNum" [encodeRat q]
  | .str s => .apply "JStr" [.apply s []]
  | .arr values => .apply "JArr" [.collection .vec (encodeValues values) none]
  | .obj fields => .apply "JObj" [.collection .vec (encodeFields fields) none]

def encodeField : Field → Pattern
  | .member key value =>
      .apply "Field" [.apply key [], encodeValue value]

def encodeValues : Values → List Pattern
  | .nil => []
  | .cons head tail => encodeValue head :: encodeValues tail

def encodeFields : Fields → List Pattern
  | .nil => []
  | .cons head tail => encodeField head :: encodeFields tail

end

mutual

theorem encodeValue_injective : ∀ a b : Value,
    encodeValue a = encodeValue b → a = b
  | .null, .null, _ => rfl
  | .bool p, .bool q, equal => by
      cases p <;> cases q <;> simp [encodeValue] at equal ⊢
  | .num p, .num q, equal => by
      have scalar : encodeRat p = encodeRat q := by
        simpa [encodeValue] using equal
      exact congrArg Value.num (encodeRat_injective scalar)
  | .str p, .str q, equal => by
      have scalar : p = q := by simpa [encodeValue] using equal
      exact congrArg Value.str scalar
  | .arr p, .arr q, equal => by
      have elements : encodeValues p = encodeValues q := by
        simpa [encodeValue] using equal
      exact congrArg Value.arr (encodeValues_injective p q elements)
  | .obj p, .obj q, equal => by
      have elements : encodeFields p = encodeFields q := by
        simpa [encodeValue] using equal
      exact congrArg Value.obj (encodeFields_injective p q elements)
  | .null, .bool q, equal => by cases q <;> simp [encodeValue] at equal
  | .null, .num q, equal => by simp [encodeValue] at equal
  | .null, .str q, equal => by simp [encodeValue] at equal
  | .null, .arr q, equal => by simp [encodeValue] at equal
  | .null, .obj q, equal => by simp [encodeValue] at equal
  | .bool p, .null, equal => by cases p <;> simp [encodeValue] at equal
  | .bool p, .num q, equal => by cases p <;> simp [encodeValue] at equal
  | .bool p, .str q, equal => by cases p <;> simp [encodeValue] at equal
  | .bool p, .arr q, equal => by cases p <;> simp [encodeValue] at equal
  | .bool p, .obj q, equal => by cases p <;> simp [encodeValue] at equal
  | .num p, .null, equal => by simp [encodeValue] at equal
  | .num p, .bool q, equal => by cases q <;> simp [encodeValue] at equal
  | .num p, .str q, equal => by simp [encodeValue] at equal
  | .num p, .arr q, equal => by simp [encodeValue] at equal
  | .num p, .obj q, equal => by simp [encodeValue] at equal
  | .str p, .null, equal => by simp [encodeValue] at equal
  | .str p, .bool q, equal => by cases q <;> simp [encodeValue] at equal
  | .str p, .num q, equal => by simp [encodeValue] at equal
  | .str p, .arr q, equal => by simp [encodeValue] at equal
  | .str p, .obj q, equal => by simp [encodeValue] at equal
  | .arr p, .null, equal => by simp [encodeValue] at equal
  | .arr p, .bool q, equal => by cases q <;> simp [encodeValue] at equal
  | .arr p, .num q, equal => by simp [encodeValue] at equal
  | .arr p, .str q, equal => by simp [encodeValue] at equal
  | .arr p, .obj q, equal => by simp [encodeValue] at equal
  | .obj p, .null, equal => by simp [encodeValue] at equal
  | .obj p, .bool q, equal => by cases q <;> simp [encodeValue] at equal
  | .obj p, .num q, equal => by simp [encodeValue] at equal
  | .obj p, .str q, equal => by simp [encodeValue] at equal
  | .obj p, .arr q, equal => by simp [encodeValue] at equal

theorem encodeField_injective : ∀ a b : Field,
    encodeField a = encodeField b → a = b
  | .member key value, .member key' value', equal => by
      have parts : [Pattern.apply key [], encodeValue value] =
          [Pattern.apply key' [], encodeValue value'] := by
        simpa [encodeField] using equal
      have keys : key = key' := by
        have heads := List.head_eq_of_cons_eq parts
        simpa using heads
      have values : value = value' :=
        encodeValue_injective value value'
          (List.head_eq_of_cons_eq (congrArg List.tail parts))
      cases keys
      cases values
      rfl

theorem encodeValues_injective : ∀ a b : Values,
    encodeValues a = encodeValues b → a = b
  | .nil, .nil, _ => rfl
  | .cons head tail, .cons head' tail', equal => by
      have heads : head = head' :=
        encodeValue_injective head head' (List.head_eq_of_cons_eq equal)
      have tails : tail = tail' :=
        encodeValues_injective tail tail'
          (List.tail_eq_of_cons_eq equal)
      cases heads
      cases tails
      rfl
  | .nil, .cons _ _, equal => by simp [encodeValues] at equal
  | .cons _ _, .nil, equal => by simp [encodeValues] at equal

theorem encodeFields_injective : ∀ a b : Fields,
    encodeFields a = encodeFields b → a = b
  | .nil, .nil, _ => rfl
  | .cons head tail, .cons head' tail', equal => by
      have heads : head = head' :=
        encodeField_injective head head' (List.head_eq_of_cons_eq equal)
      have tails : tail = tail' :=
        encodeFields_injective tail tail'
          (List.tail_eq_of_cons_eq equal)
      cases heads
      cases tails
      rfl
  | .nil, .cons _ _, equal => by simp [encodeFields] at equal
  | .cons _ _, .nil, equal => by simp [encodeFields] at equal

end

/-- The tagged encoding represents every closed term of the intrinsic JSON
signature, rather than only a selected set of example values. -/
def encodeClosedValueTerm : Term JsonTermRung.sig [] .value → Pattern :=
  fun term => encodeValue (JsonTermRung.closedValueEquiv.symm term)

theorem encodeClosedValueTerm_injective :
    Function.Injective encodeClosedValueTerm := by
  intro left right equal
  have valuesEqual :
      JsonTermRung.closedValueEquiv.symm left =
        JsonTermRung.closedValueEquiv.symm right :=
    encodeValue_injective _ _ equal
  exact JsonTermRung.closedValueEquiv.symm.injective valuesEqual

/-- Array encoding uses the actual authored array label. -/
theorem encode_array_has_authored_label (values : Values) :
    encodeValue (.arr values) =
      .apply (JsonAuthoredComparison.authored.terms.get ⟨4, by decide⟩).label
        [.collection .vec (encodeValues values) none] := by
  rfl

/-- Object encoding uses the distinct actual authored object label. -/
theorem encode_object_has_authored_label (fields : Fields) :
    encodeValue (.obj fields) =
      .apply (JsonAuthoredComparison.authored.terms.get ⟨5, by decide⟩).label
        [.collection .vec (encodeFields fields) none] := by
  rfl

theorem encodeClosedValueTerm_exact (value : Value) :
    encodeClosedValueTerm (JsonTermRung.encodeValue value) =
      encodeValue value := by
  change encodeValue (JsonTermRung.decodeValue
    (JsonTermRung.encodeValue value)) = encodeValue value
  rw [JsonTermRung.decode_encode_value]

theorem empty_array_ne_empty_object :
    encodeValue (.arr .nil) ≠ encodeValue (.obj .nil) := by
  intro equal
  simp [encodeValue] at equal

theorem duplicate_object_members_remain_distinct :
    encodeValue JsonTermRung.oneMember ≠
      encodeValue JsonTermRung.twoMembers := by
  intro equal
  cases equal

end Mettapedia.OSLF.Binding.JsonTaggedDataEncoding
