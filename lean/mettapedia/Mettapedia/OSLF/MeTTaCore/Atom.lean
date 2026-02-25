import Mathlib.Data.Multiset.Basic

/-!
# MeTTaCore Atom Datatype

Core atom datatype for the MeTTa interpreter specification, following the
Hyperon Experimental documentation and Meta-MeTTa paper.

## Main Definitions

* `GroundedValue` - Grounded (external) value variants
* `Atom` - Core 4-constructor atom type: Symbol, Variable, Grounded, Expression
* `GroundedType` - Typeclass for extensible grounded value support

## References

* [Hyperon Experimental Spec](https://trueagi-io.github.io/hyperon-experimental/metta/)
* Meta-MeTTa paper (Meredith, Goertzel, Warrell, Vandervorst)
-/

namespace Mettapedia.OSLF.MeTTaCore

/-! ## Grounded Values -/

/-- Grounded value variants (external/computed values).
    Extensible via custom constructor for user-defined types. -/
inductive GroundedValue where
  | int : Int → GroundedValue
  | string : String → GroundedValue
  | bool : Bool → GroundedValue
  | custom : (typeName : String) → (data : String) → GroundedValue
deriving Repr, Inhabited, DecidableEq

namespace GroundedValue

/-- Get the type name of a grounded value -/
def typeName : GroundedValue → String
  | .int _ => "Int"
  | .string _ => "String"
  | .bool _ => "Bool"
  | .custom name _ => name

/-- Display a grounded value as a string -/
def toString : GroundedValue → String
  | .int n => s!"{n}"
  | .string s => s!"\"{s}\""
  | .bool b => if b then "True" else "False"
  | .custom name data => s!"({name} {data})"

instance : ToString GroundedValue := ⟨toString⟩

end GroundedValue

/-! ## Core Atom Type -/

/-- Core atom type for MeTTa (Hyperon spec: Symbol, Variable, Grounded, Expression).

    The four constructors correspond to:
    - `symbol`: Named constants like `"+"`, `"if"`, `"foo"`
    - `var`: Pattern variables like `$x`, `$y` (named `var` to avoid keyword conflict)
    - `grounded`: External/computed values (integers, strings, etc.)
    - `expression`: S-expressions `(head arg1 arg2 ...)` -/
inductive Atom where
  | symbol : String → Atom
  | var : String → Atom           -- renamed from `variable` to avoid keyword
  | grounded : GroundedValue → Atom
  | expression : List Atom → Atom
deriving Repr, Inhabited

/-! ### DecidableEq for nested inductive -/

/-- Boolean equality for Atom (handles nested List Atom) -/
def Atom.beq : Atom → Atom → Bool
  | .symbol s₁, .symbol s₂ => s₁ == s₂
  | .var v₁, .var v₂ => v₁ == v₂
  | .grounded g₁, .grounded g₂ => g₁ == g₂
  | .expression es₁, .expression es₂ => beqList es₁ es₂
  | _, _ => false
where
  beqList : List Atom → List Atom → Bool
    | [], [] => true
    | a :: as, b :: bs => Atom.beq a b && beqList as bs
    | _, _ => false

instance : BEq Atom := ⟨Atom.beq⟩

/-- Helper: beqList is reflexive -/
theorem Atom.beqList_self_eq_true (as : List Atom) (ih : ∀ x ∈ as, (x == x) = true) :
    Atom.beq.beqList as as = true := by
  induction as with
  | nil => simp [Atom.beq.beqList]
  | cons a as ih' =>
    simp only [Atom.beq.beqList, Bool.and_eq_true]
    constructor
    · exact ih a (List.Mem.head as)
    · exact ih' (fun x hx => ih x (List.Mem.tail a hx))

/-- beq is reflexive -/
theorem Atom.beq_self_eq_true (a : Atom) : (a == a) = true := by
  match a with
  | .symbol _ => simp [Atom.beq, BEq.beq]
  | .var _ => simp [Atom.beq, BEq.beq]
  | .grounded _ => simp only [BEq.beq, Atom.beq]; decide
  | .expression es =>
    simp only [BEq.beq, Atom.beq]
    exact Atom.beqList_self_eq_true es (fun x _ => Atom.beq_self_eq_true x)
termination_by sizeOf a

/-- Helper: beqList true implies equal -/
theorem Atom.beqList_eq_true_imp (as bs : List Atom) (h : Atom.beq.beqList as bs = true)
    (ih : ∀ x ∈ as, ∀ y, (x == y) = true → x = y) : as = bs := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp [Atom.beq.beqList] at h
    rfl
  | cons a as ih' =>
    cases bs with
    | nil => simp [Atom.beq.beqList] at h
    | cons b bs =>
      simp only [Atom.beq.beqList, Bool.and_eq_true] at h
      congr
      · exact ih a (List.Mem.head as) b h.1
      · exact ih' bs h.2 (fun x hx => ih x (List.Mem.tail a hx))

/-- beq true implies equal -/
theorem Atom.eq_of_beq_eq_true {a b : Atom} (h : (a == b) = true) : a = b := by
  match a, b with
  | .symbol s, .symbol t => simp [Atom.beq, BEq.beq] at h; exact congrArg _ h
  | .symbol _, .var _ => simp [Atom.beq, BEq.beq] at h
  | .symbol _, .grounded _ => simp [Atom.beq, BEq.beq] at h
  | .symbol _, .expression _ => simp [Atom.beq, BEq.beq] at h
  | .var _, .symbol _ => simp [Atom.beq, BEq.beq] at h
  | .var _, .var w => simp [Atom.beq, BEq.beq] at h; exact congrArg _ h
  | .var _, .grounded _ => simp [Atom.beq, BEq.beq] at h
  | .var _, .expression _ => simp [Atom.beq, BEq.beq] at h
  | .grounded _, .symbol _ => simp [Atom.beq, BEq.beq] at h
  | .grounded _, .var _ => simp [Atom.beq, BEq.beq] at h
  | .grounded g₁, .grounded g₂ =>
      simp only [BEq.beq, Atom.beq] at h
      exact congrArg _ (of_decide_eq_true h)
  | .grounded _, .expression _ => simp [Atom.beq, BEq.beq] at h
  | .expression _, .symbol _ => simp [Atom.beq, BEq.beq] at h
  | .expression _, .var _ => simp [Atom.beq, BEq.beq] at h
  | .expression _, .grounded _ => simp [Atom.beq, BEq.beq] at h
  | .expression as, .expression bs =>
      simp only [BEq.beq, Atom.beq] at h
      congr
      exact Atom.beqList_eq_true_imp as bs h (fun x _ y hy => Atom.eq_of_beq_eq_true hy)
termination_by sizeOf a

instance : DecidableEq Atom := fun a b =>
  if h : a == b then
    isTrue (Atom.eq_of_beq_eq_true h)
  else
    isFalse (fun heq => h (heq ▸ Atom.beq_self_eq_true a))

namespace Atom

/-! ### Special Atoms (Hyperon spec) -/

/-- Empty result (evaluation produced no results) -/
def empty : Atom := .symbol "Empty"

/-- Term is not reducible (no matching equations) -/
def notReducible : Atom := .symbol "NotReducible"

/-- Error atom with source and message -/
def error (atom msg : Atom) : Atom := .expression [.symbol "Error", atom, msg]

/-- Undefined type marker -/
def undefinedType : Atom := .symbol "%Undefined%"

/-- Unit value -/
def unit : Atom := .expression []

/-! ### Meta-type Symbols -/

/-- The Atom meta-type -/
def atomType : Atom := .symbol "Atom"

/-- The Symbol meta-type -/
def symbolType : Atom := .symbol "Symbol"

/-- The Variable meta-type -/
def variableType : Atom := .symbol "Variable"

/-- The Expression meta-type -/
def expressionType : Atom := .symbol "Expression"

/-- The Grounded meta-type -/
def groundedType : Atom := .symbol "Grounded"

/-- The Type meta-type -/
def typeType : Atom := .symbol "Type"

/-! ### Predicates -/

/-- Check if atom is a symbol -/
def isSymbol : Atom → Bool
  | .symbol _ => true
  | _ => false

/-- Check if atom is a variable -/
def isVariable : Atom → Bool
  | .var _ => true
  | _ => false

/-- Check if atom is a grounded value -/
def isGrounded : Atom → Bool
  | .grounded _ => true
  | _ => false

/-- Check if atom is an expression -/
def isExpression : Atom → Bool
  | .expression _ => true
  | _ => false

/-- Check if atom is the Empty symbol -/
def isEmpty : Atom → Bool
  | .symbol "Empty" => true
  | _ => false

/-- Check if atom is an Error expression -/
def isError : Atom → Bool
  | .expression (.symbol "Error" :: _) => true
  | _ => false

/-! ### Constructors -/

/-- Create a type annotation: (: atom type) -/
def typeAnnotation (a ty : Atom) : Atom :=
  .expression [.symbol ":", a, ty]

/-- Create a function type: (-> arg1 arg2 ... ret) -/
def functionType (args : List Atom) (ret : Atom) : Atom :=
  .expression (.symbol "->" :: args ++ [ret])

/-- Create an equality atom: (= lhs rhs) -/
def equality (lhs rhs : Atom) : Atom :=
  .expression [.symbol "=", lhs, rhs]

/-! ### Display -/

/-- Convert atom to string representation -/
partial def toString : Atom → String
  | .symbol s => s
  | .var v => "$" ++ v
  | .grounded g => g.toString
  | .expression [] => "()"
  | .expression atoms => "(" ++ " ".intercalate (atoms.map toString) ++ ")"

instance : ToString Atom := ⟨toString⟩

end Atom

/-! ## GroundedType Typeclass -/

/-- Typeclass for types that can be represented as grounded atoms.
    Provides bidirectional conversion and operation execution. -/
class GroundedType (α : Type*) where
  /-- Convert a value to an atom -/
  toAtom : α → Atom
  /-- Try to extract a value from an atom -/
  fromAtom : Atom → Option α
  /-- The type name for this grounded type -/
  typeName : String
  /-- Execute a grounded operation if applicable -/
  execute : (op : String) → List Atom → Option Atom := fun _ _ => none

namespace GroundedType

/-- Concrete instance for Int -/
instance : GroundedType Int where
  toAtom n := .grounded (.int n)
  fromAtom
    | .grounded (.int n) => some n
    | _ => none
  typeName := "Int"
  execute op args := match op, args with
    | "+", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.int (a + b)))
    | "-", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.int (a - b)))
    | "*", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.int (a * b)))
    | "/", [.grounded (.int a), .grounded (.int b)] =>
        if b ≠ 0 then some (.grounded (.int (a / b))) else none
    | "%", [.grounded (.int a), .grounded (.int b)] =>
        if b ≠ 0 then some (.grounded (.int (a % b))) else none
    | "<", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.bool (a < b)))
    | "<=", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.bool (a ≤ b)))
    | ">", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.bool (a > b)))
    | ">=", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.bool (a ≥ b)))
    | "==", [.grounded (.int a), .grounded (.int b)] => some (.grounded (.bool (a == b)))
    | _, _ => none

/-- Concrete instance for String -/
instance : GroundedType String where
  toAtom s := .grounded (.string s)
  fromAtom
    | .grounded (.string s) => some s
    | _ => none
  typeName := "String"
  execute op args := match op, args with
    | "concat", [.grounded (.string a), .grounded (.string b)] =>
        some (.grounded (.string (a ++ b)))
    | "length", [.grounded (.string s)] =>
        some (.grounded (.int s.length))
    | "==", [.grounded (.string a), .grounded (.string b)] =>
        some (.grounded (.bool (a == b)))
    | _, _ => none

/-- Concrete instance for Bool -/
instance : GroundedType Bool where
  toAtom b := .grounded (.bool b)
  fromAtom
    | .grounded (.bool b) => some b
    | _ => none
  typeName := "Bool"
  execute op args := match op, args with
    | "and", [.grounded (.bool a), .grounded (.bool b)] => some (.grounded (.bool (a && b)))
    | "or", [.grounded (.bool a), .grounded (.bool b)] => some (.grounded (.bool (a || b)))
    | "not", [.grounded (.bool a)] => some (.grounded (.bool (!a)))
    | "==", [.grounded (.bool a), .grounded (.bool b)] => some (.grounded (.bool (a == b)))
    | _, _ => none

end GroundedType

/-! ## Unit Tests -/

section Tests

-- Basic atom construction
#check Atom.symbol "foo"
#check Atom.var "x"
#check Atom.grounded (.int 42)
#check Atom.expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]

-- Special atoms
example : Atom.empty = .symbol "Empty" := rfl
example : Atom.notReducible = .symbol "NotReducible" := rfl
example : Atom.undefinedType = .symbol "%Undefined%" := rfl

-- Type annotation
example : Atom.typeAnnotation (.symbol "x") (.symbol "Int") =
          .expression [.symbol ":", .symbol "x", .symbol "Int"] := rfl

-- Function type
example : Atom.functionType [.symbol "Int", .symbol "Int"] (.symbol "Int") =
          .expression [.symbol "->", .symbol "Int", .symbol "Int", .symbol "Int"] := rfl

-- Predicates
example : Atom.isSymbol (.symbol "x") = true := rfl
example : Atom.isVariable (.var "x") = true := rfl
example : Atom.isGrounded (.grounded (.int 42)) = true := rfl
example : Atom.isExpression (.expression []) = true := rfl
example : Atom.isEmpty Atom.empty = true := rfl
example : Atom.isError (Atom.error (.symbol "x") (.symbol "msg")) = true := rfl

-- Grounded type operations
example : GroundedType.execute (α := Int) "+" [.grounded (.int 2), .grounded (.int 3)] =
          some (.grounded (.int 5)) := rfl
example : GroundedType.execute (α := String) "concat"
            [.grounded (.string "Hello"), .grounded (.string " World")] =
          some (.grounded (.string "Hello World")) := rfl
example : GroundedType.execute (α := Bool) "and"
            [.grounded (.bool true), .grounded (.bool false)] =
          some (.grounded (.bool false)) := rfl

-- DecidableEq works
example : (.symbol "x" : Atom) = .symbol "x" := rfl
example : (.symbol "x" : Atom) ≠ .symbol "y" := by decide

end Tests

end Mettapedia.OSLF.MeTTaCore
