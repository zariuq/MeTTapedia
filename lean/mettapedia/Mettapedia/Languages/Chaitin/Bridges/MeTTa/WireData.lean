import Mettapedia.Languages.Chaitin.Syntax
import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mathlib.Logic.Function.Basic

/-!
# Historical Lisp data in the shared MeTTa wire carrier

Words and natural numbers retain their distinct physical tags. A tagged
application stores a proper Lisp list, including its order and multiplicity.
The decoder rejects strings and unrelated application heads. These maps
transport program syntax as data; they do not identify either language's
evaluation or substitution operation.

The wire operations below inspect the representation directly. Their
commuting laws include Chaitin's atomic `car`/`cdr` and permissive `cons`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.Bridges.MeTTa.WireData

abbrev Wire := Mettapedia.GSLT.LanguageDef.CettaWire.Term

mutual

def encode : SExpr → Wire
  | .symbol name => .symbol name
  | .number value => .natural value
  | .list values => .application "Chaitin.List" (encodeValues values)
termination_by expression => sizeOf expression

def encodeValues : List SExpr → List Wire
  | [] => []
  | value :: values => encode value :: encodeValues values
termination_by values => sizeOf values

end

mutual

def decode : Wire → Option SExpr
  | .symbol name => some (.symbol name)
  | .natural value => some (.number value)
  | .application "Chaitin.List" values => (decodeValues values).map SExpr.list
  | _ => none
termination_by wire => sizeOf wire

def decodeValues : List Wire → Option (List SExpr)
  | [] => some []
  | value :: values => do
      let first ← decode value
      let rest ← decodeValues values
      pure (first :: rest)
termination_by values => sizeOf values

end

mutual

@[simp] theorem decode_encode (expression : SExpr) :
    decode (encode expression) = some expression := by
  cases expression with
  | symbol name => simp only [encode, decode]
  | number value => simp only [encode, decode]
  | list values =>
      rw [encode, decode, decodeValues_encodeValues values]
      rfl
termination_by sizeOf expression

@[simp] theorem decodeValues_encodeValues (values : List SExpr) :
    decodeValues (encodeValues values) = some values := by
  cases values with
  | nil => simp only [encodeValues, decodeValues]
  | cons value values =>
      rw [encodeValues, decodeValues, decode_encode value, decodeValues_encodeValues values]
      rfl
termination_by sizeOf values

end

mutual

/-- Every accepted physical value is an exact canonical encoding. -/
theorem encode_of_decode (wire : Wire) (expression : SExpr)
    (accepted : decode wire = some expression) : encode expression = wire := by
  cases wire with
  | symbol name =>
      have same : .symbol name = expression := by simpa only [decode, Option.some.injEq] using accepted
      subst expression
      simp only [encode]
  | natural value =>
      have same : .number value = expression := by simpa only [decode, Option.some.injEq] using accepted
      subst expression
      simp only [encode]
  | string value => simp [decode] at accepted
  | application head values =>
      by_cases tag : head = "Chaitin.List"
      · subst head
        cases decoded : decodeValues values with
        | none => simp [decode, decoded] at accepted
        | some expressions =>
            have same : SExpr.list expressions = expression := by
              simpa only [decode, decoded, Option.map_some, Option.some.injEq] using accepted
            subst expression
            rw [encode, encodeValues_of_decode values expressions decoded]
      · simp [decode, tag] at accepted
termination_by sizeOf wire

theorem encodeValues_of_decode (wires : List Wire) (expressions : List SExpr)
    (accepted : decodeValues wires = some expressions) : encodeValues expressions = wires := by
  cases wires with
  | nil =>
      have same : [] = expressions := by simpa only [decodeValues, Option.some.injEq] using accepted
      subst expressions
      simp only [encodeValues]
  | cons wire wires =>
      cases first : decode wire with
      | none => simp [decodeValues, first] at accepted
      | some expression =>
          cases rest : decodeValues wires with
          | none => simp [decodeValues, first, rest] at accepted
          | some expressions' =>
              have same : expression :: expressions' = expressions := by
                simpa [decodeValues, first, rest] using accepted
              subst expressions
              rw [encodeValues, encode_of_decode wire expression first,
                encodeValues_of_decode wires expressions' rest]
termination_by sizeOf wires

end

theorem decode_eq_some_iff (wire : Wire) (expression : SExpr) :
    decode wire = some expression ↔ wire = encode expression := by
  constructor
  · intro accepted
    exact (encode_of_decode wire expression accepted).symm
  · rintro rfl
    exact decode_encode expression

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- A physical string is not a historical Lisp word. -/
@[simp] theorem decode_string (value : String) : decode (.string value) = none := by
  simp only [decode]

def car? : Wire → Option Wire
  | .symbol name => some (.symbol name)
  | .natural value => some (.natural value)
  | .application "Chaitin.List" values =>
      some (values.headD (.application "Chaitin.List" []))
  | _ => none

def cdr? : Wire → Option Wire
  | .symbol name => some (.symbol name)
  | .natural value => some (.natural value)
  | .application "Chaitin.List" values => some (.application "Chaitin.List" values.tail)
  | _ => none

def cons? (head : Wire) : Wire → Option Wire
  | .symbol _ | .natural _ => some head
  | .application "Chaitin.List" values => some (.application "Chaitin.List" (head :: values))
  | _ => none

@[simp] theorem car?_encode (expression : SExpr) :
    car? (encode expression) = some (encode expression.car) := by
  cases expression with
  | symbol name => simp only [encode, car?, SExpr.car]
  | number value => simp only [encode, car?, SExpr.car]
  | list values => cases values <;> simp [encode, encodeValues, car?, SExpr.car]

@[simp] theorem cdr?_encode (expression : SExpr) :
    cdr? (encode expression) = some (encode expression.cdr) := by
  cases expression with
  | symbol name => simp only [encode, cdr?, SExpr.cdr]
  | number value => simp only [encode, cdr?, SExpr.cdr]
  | list values => cases values <;> simp [encode, encodeValues, cdr?, SExpr.cdr]

@[simp] theorem cons?_encode (head tail : SExpr) :
    cons? (encode head) (encode tail) = some (encode (SExpr.cons head tail)) := by
  cases tail <;> simp [encode, encodeValues, cons?, SExpr.cons]

theorem equal_encodings_iff (first second : SExpr) :
    encode first = encode second ↔ first = second :=
  ⟨fun same => encode_injective same, congrArg encode⟩

/-- A word that looks numeric and a natural literal remain different. -/
theorem numeric_word_distinct (value : Nat) :
    encode (.symbol (toString value)) ≠ encode (.number value) := by
  intro same
  cases encode_injective same

theorem list_order_retained :
    encode (.list [.number 0, .number 1]) ≠ encode (.list [.number 1, .number 0]) := by
  intro same
  cases encode_injective same

theorem list_multiplicity_retained :
    encode (.list [.number 0, .number 0]) ≠ encode (.list [.number 0]) := by
  intro same
  cases encode_injective same

theorem unrelated_application_rejected :
    decode (.application "eval" [.symbol "x"]) = none := by simp [decode]

/-- Words are transported as literal data, even when their spelling resembles
a variable of a MeTTa surface language. -/
theorem variable_spelling_is_data (name : String) :
    decode (encode (.symbol ("$" ++ name))) = some (.symbol ("$" ++ name)) :=
  decode_encode _

end Mettapedia.Languages.Chaitin.Bridges.MeTTa.WireData
