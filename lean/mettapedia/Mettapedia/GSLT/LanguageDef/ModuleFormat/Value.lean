import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

/-!
# Structured values at the MeTTaIL module boundary

The constructors follow the public `RhoValue` carrier at mettail-rust commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`, `mettail-elab/src/canonical.rs`.
Record fields are retained as occurrences before schema admission. This is a
structural value boundary, not a byte parser or a BLAKE3 implementation.
Integers use `Int`; machine-width and canonical-value resource admission belong
to the host boundary, outside the structural envelope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

inductive Value where
  | record : List (String × Value) → Value
  | list : List Value → Value
  | string : String → Value
  | bytes : List UInt8 → Value
  | integer : Int → Value
  | floatBits : UInt64 → Value
  | boolean : Bool → Value
  | nil : Value
  deriving Repr

mutual

private def decEqValue : (first second : Value) → Decidable (first = second)
  | .record a, .record b =>
      match decEqFields a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .list a, .list b =>
      match decEqValues a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .string a, .string b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .bytes a, .bytes b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .integer a, .integer b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .floatBits a, .floatBits b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .boolean a, .boolean b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .nil, .nil => isTrue rfl
  | .record _, .list _ => isFalse Value.noConfusion
  | .record _, .string _ => isFalse Value.noConfusion
  | .record _, .bytes _ => isFalse Value.noConfusion
  | .record _, .integer _ => isFalse Value.noConfusion
  | .record _, .floatBits _ => isFalse Value.noConfusion
  | .record _, .boolean _ => isFalse Value.noConfusion
  | .record _, .nil => isFalse Value.noConfusion
  | .list _, .record _ => isFalse Value.noConfusion
  | .list _, .string _ => isFalse Value.noConfusion
  | .list _, .bytes _ => isFalse Value.noConfusion
  | .list _, .integer _ => isFalse Value.noConfusion
  | .list _, .floatBits _ => isFalse Value.noConfusion
  | .list _, .boolean _ => isFalse Value.noConfusion
  | .list _, .nil => isFalse Value.noConfusion
  | .string _, .record _ => isFalse Value.noConfusion
  | .string _, .list _ => isFalse Value.noConfusion
  | .string _, .bytes _ => isFalse Value.noConfusion
  | .string _, .integer _ => isFalse Value.noConfusion
  | .string _, .floatBits _ => isFalse Value.noConfusion
  | .string _, .boolean _ => isFalse Value.noConfusion
  | .string _, .nil => isFalse Value.noConfusion
  | .bytes _, .record _ => isFalse Value.noConfusion
  | .bytes _, .list _ => isFalse Value.noConfusion
  | .bytes _, .string _ => isFalse Value.noConfusion
  | .bytes _, .integer _ => isFalse Value.noConfusion
  | .bytes _, .floatBits _ => isFalse Value.noConfusion
  | .bytes _, .boolean _ => isFalse Value.noConfusion
  | .bytes _, .nil => isFalse Value.noConfusion
  | .integer _, .record _ => isFalse Value.noConfusion
  | .integer _, .list _ => isFalse Value.noConfusion
  | .integer _, .string _ => isFalse Value.noConfusion
  | .integer _, .bytes _ => isFalse Value.noConfusion
  | .integer _, .floatBits _ => isFalse Value.noConfusion
  | .integer _, .boolean _ => isFalse Value.noConfusion
  | .integer _, .nil => isFalse Value.noConfusion
  | .floatBits _, .record _ => isFalse Value.noConfusion
  | .floatBits _, .list _ => isFalse Value.noConfusion
  | .floatBits _, .string _ => isFalse Value.noConfusion
  | .floatBits _, .bytes _ => isFalse Value.noConfusion
  | .floatBits _, .integer _ => isFalse Value.noConfusion
  | .floatBits _, .boolean _ => isFalse Value.noConfusion
  | .floatBits _, .nil => isFalse Value.noConfusion
  | .boolean _, .record _ => isFalse Value.noConfusion
  | .boolean _, .list _ => isFalse Value.noConfusion
  | .boolean _, .string _ => isFalse Value.noConfusion
  | .boolean _, .bytes _ => isFalse Value.noConfusion
  | .boolean _, .integer _ => isFalse Value.noConfusion
  | .boolean _, .floatBits _ => isFalse Value.noConfusion
  | .boolean _, .nil => isFalse Value.noConfusion
  | .nil, .record _ => isFalse Value.noConfusion
  | .nil, .list _ => isFalse Value.noConfusion
  | .nil, .string _ => isFalse Value.noConfusion
  | .nil, .bytes _ => isFalse Value.noConfusion
  | .nil, .integer _ => isFalse Value.noConfusion
  | .nil, .floatBits _ => isFalse Value.noConfusion
  | .nil, .boolean _ => isFalse Value.noConfusion

private def decEqValues : (first second : List Value) → Decidable (first = second)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      match decEqValue x y, decEqValues xs ys with
      | isTrue head, isTrue tail => isTrue (by subst head; subst tail; rfl)
      | isFalse head, _ => isFalse (by intro equal; cases equal; exact head rfl)
      | _, isFalse tail => isFalse (by intro equal; cases equal; exact tail rfl)
  | [], _ :: _ => isFalse (by intro equal; cases equal)
  | _ :: _, [] => isFalse (by intro equal; cases equal)

private def decEqFields :
    (first second : List (String × Value)) → Decidable (first = second)
  | [], [] => isTrue rfl
  | (k, x) :: xs, (l, y) :: ys =>
      match decEq k l, decEqValue x y, decEqFields xs ys with
      | isTrue key, isTrue head, isTrue tail =>
          isTrue (by subst key; subst head; subst tail; rfl)
      | isFalse key, _, _ => isFalse (by intro equal; cases equal; exact key rfl)
      | _, isFalse head, _ => isFalse (by intro equal; cases equal; exact head rfl)
      | _, _, isFalse tail => isFalse (by intro equal; cases equal; exact tail rfl)
  | [], _ :: _ => isFalse (by intro equal; cases equal)
  | _ :: _, [] => isFalse (by intro equal; cases equal)

end

instance : DecidableEq Value := decEqValue

namespace Value

def field? (fields : List (String × Value)) (key : String) : Option Value :=
  (fields.find? fun field => field.1 == key).map Prod.snd

def record? (keys : List String) : Value → Option (List (String × Value))
  | .record fields => if (fields.map Prod.fst).Perm keys then some fields else none
  | _ => none

def string? : Value → Option String
  | .string value => some value
  | _ => none

def list? : Value → Option (List Value)
  | .list values => some values
  | _ => none

def bytes? : Value → Option (List UInt8)
  | .bytes values => some values
  | _ => none

@[simp] theorem field?_nil (key : String) : field? [] key = none := rfl

@[simp] theorem field?_cons (key name : String) (value : Value)
    (rest : List (String × Value)) :
    field? ((name, value) :: rest) key =
      if name = key then some value else field? rest key := by
  by_cases equal : name = key
  · simp [field?, equal]
  · simp [field?, equal]

theorem record?_some_iff (keys : List String) (value : Value)
    (fields : List (String × Value)) :
    record? keys value = some fields ↔
      value = .record fields ∧ (fields.map Prod.fst).Perm keys := by
  cases value <;> simp [record?]
  constructor
  · rintro ⟨permutation, rfl⟩
    exact ⟨rfl, permutation⟩
  · rintro ⟨rfl, permutation⟩
    exact ⟨permutation, rfl⟩

end Value

/-- Registry references retain their suffix; file references retain the exact
path. Parsing a bare file path and its `file:` spelling yields the same key. -/
inductive ModuleRef where
  | registry : String → ModuleRef
  | file : String → ModuleRef
  deriving Repr, DecidableEq

namespace ModuleRef

def valid : ModuleRef → Prop
  | .registry name => name ≠ ""
  | .file path => path ≠ ""

instance (reference : ModuleRef) : Decidable reference.valid := by
  cases reference <;> unfold valid <;> infer_instance

def external : ModuleRef → String
  | .registry name => "rho:" ++ name
  | .file path => "file:" ++ path

def parseChars? : List Char → Option ModuleRef
  | 'r' :: 'h' :: 'o' :: ':' :: name =>
      if name = [] then none else some (.registry (String.ofList name))
  | 'f' :: 'i' :: 'l' :: 'e' :: ':' :: path =>
      if path = [] then none else some (.file (String.ofList path))
  | chars =>
      if chars = [] ∨ ':' ∈ chars then none else some (.file (String.ofList chars))

def parse? (text : String) : Option ModuleRef := parseChars? text.toList

@[simp] theorem parse_external (reference : ModuleRef) (accepted : reference.valid) :
    parse? reference.external = some reference := by
  cases reference with
  | registry name =>
      simp only [valid] at accepted
      simp [parse?, external, parseChars?, String.toList_append, accepted]
  | file path =>
      simp only [valid] at accepted
      simp [parse?, external, parseChars?, String.toList_append, accepted]

end ModuleRef

/-- The ASCII identifier rule used for module and exported-language names. -/
def identifier (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_') &&
        rest.all (fun c => c.isAlphanum || c == '_')

end Mettapedia.GSLT.LanguageDef.ModuleFormat
