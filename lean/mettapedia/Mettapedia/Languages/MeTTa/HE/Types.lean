import Mettapedia.Languages.MeTTa.OSLFCore.Bindings

/-!
# HE MeTTa Types

Foundation types for the Hyperon Experimental MeTTa interpreter formalization.

## Source Precedence
1. `hyperon-experimental/lib/src/metta/interpreter.rs` (ground truth)
2. `hyperon-experimental/docs/metta.md` (spec prose)

## Main Definitions
* `ErrorCode` - Structured error codes (normative from HE spec)
* `Bindings` - Variable bindings with assignments AND equalities
* `ResultPair` / `ResultSet` - Interpreter output types
* `ResultEqBag` / `ResultEqOrdered` - Result equivalence relations
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Error Codes

Normative from HE spec. Error *text* is non-normative; only these
constructors/shapes are normative. -/

/-- Structured error codes from the HE interpreter.
    Ref: `metta.md` lines 125-148, `interpreter.rs` error branches. -/
inductive ErrorCode where
  | stackOverflow
  | noReturn
  | incorrectNumberOfArguments
  | badArgType (pos : Nat) (expected actual : Atom)
  | badType (expected actual : Atom)
  deriving Repr, DecidableEq, Inhabited

/-- Convert an error code to its atom representation.
    Ref: `metta.md` line 253 `(Error $atom ...)` shape. -/
def ErrorCode.toAtom : ErrorCode → Atom
  | .stackOverflow => .symbol "StackOverflow"
  | .noReturn => .symbol "NoReturn"
  | .incorrectNumberOfArguments => .symbol "IncorrectNumberOfArguments"
  | .badArgType pos expected actual =>
    .expression [.symbol "BadArgType", .grounded (.int pos), expected, actual]
  | .badType expected actual =>
    .expression [.symbol "BadType", expected, actual]

/-- Construct an `(Error source errorCode)` atom.
    Ref: `metta.md` line 253. -/
def mkError (source : Atom) (code : ErrorCode) : Atom :=
  Atom.error source code.toAtom

/-! ## Bindings

The HE spec (metta.md lines 562-576) defines bindings as a set of two kinds
of relations:
1. Assignment: `$x <- value`
2. Equality: `$a = $b`

We use sorted lists for canonical representation and `DecidableEq`. -/

/-- Variable bindings for HE MeTTa.

    `assignments` maps variable names to values (`$x <- val`).
    `equalities` records variable-variable equalities (`$a = $b`).

    Invariant: no duplicate variable names in assignments (maintained by operations).
    Ref: metta.md lines 562-576. -/
structure Bindings where
  assignments : List (String × Atom)
  equalities : List (String × String)
  deriving Repr, Inhabited, DecidableEq

namespace Bindings

/-- Empty bindings. -/
def empty : Bindings := ⟨[], []⟩

instance : EmptyCollection Bindings := ⟨empty⟩

/-- Look up a variable's assigned value. -/
def lookup (b : Bindings) (v : String) : Option Atom :=
  b.assignments.lookup v

/-- Check if a variable has an assignment. -/
def isBound (b : Bindings) (v : String) : Bool :=
  (b.lookup v).isSome

/-- Add or update a variable assignment. Replaces existing if present. -/
def assign (b : Bindings) (v : String) (val : Atom) : Bindings :=
  let assignments' := if b.isBound v then
    b.assignments.map fun (k, a) => if k == v then (k, val) else (k, a)
  else
    b.assignments ++ [(v, val)]
  { b with assignments := assignments' }

/-- Add a variable equality. -/
def addEquality (b : Bindings) (a c : String) : Bindings :=
  { b with equalities := b.equalities ++ [(a, c)] }

/-- Remove a variable assignment. -/
def removeAssignment (b : Bindings) (v : String) : Bindings :=
  { b with assignments := b.assignments.filter fun (k, _) => k != v }

/-- Resolve a variable to its final value, following variable chains.
    Uses explicit fuel to handle potential cycles in the trusted path. -/
def resolve (b : Bindings) (v : String) (fuel : Nat) : Option Atom :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match b.lookup v with
    | none => none
    | some (.var w) => b.resolve w n
    | some a => some a

/-- Convenience wrapper for callers outside the trusted theorem boundary. -/
def resolveDefault (b : Bindings) (v : String) : Option Atom :=
  b.resolve v 100

/-- Get all variable names that are bound (have assignments). -/
def boundVars (b : Bindings) : List String :=
  b.assignments.map Prod.fst

/-- Apply bindings to an atom, substituting variables with their values.
    Uses explicit fuel in the trusted path. -/
def apply (b : Bindings) (a : Atom) (fuel : Nat) : Atom :=
  match fuel with
  | 0 => a
  | n + 1 =>
    match a with
    | .var v =>
      match b.resolve v n with
      | some val => val
      | none => a
    | .expression es => .expression (es.map (b.apply · n))
    | other => other

/-- Convenience wrapper for callers outside the trusted theorem boundary. -/
def applyDefault (b : Bindings) (a : Atom) : Atom :=
  b.apply a 100

/-- Check if bindings contain a variable loop.
    Ref: metta.md line 616 "filter(lambda $b: <$b doesn't have variable loops>)". -/
def hasLoop (b : Bindings) : Bool :=
  b.assignments.any fun (v, _) => hasLoopFrom b v [v] 100
where
  hasLoopFrom (b : Bindings) (v : String) (visited : List String) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true  -- conservative: assume loop on fuel exhaustion
    | n + 1 =>
      match b.lookup v with
      | none => false
      | some (.var w) =>
        if visited.contains w then true
        else hasLoopFrom b w (w :: visited) n
      | some _ => false

/-- Convert to MeTTaCore.Bindings (only when equalities are empty/discharged).
    Returns `none` if equalities are present. -/
def toCore? (b : Bindings) : Option Mettapedia.Languages.MeTTa.OSLFCore.Bindings :=
  if b.equalities.isEmpty then
    some ⟨fun v => b.lookup v⟩
  else
    none

/-- Convert from MeTTaCore.Bindings (given a finite list of known variables). -/
def fromCore (cb : Mettapedia.Languages.MeTTa.OSLFCore.Bindings) (vars : List String) : Bindings :=
  let assignments := vars.filterMap fun v =>
    match cb.map v with
    | some a => some (v, a)
    | none => none
  ⟨assignments, []⟩

/-! ### Bindings ↔ Atom Encoding

The minimal-metta spec says collapse-bind returns results as `(<atom> <bindings>)`
pairs where bindings are "represented in a form of a grounded atom." We use
structural encoding as nested expressions for a provable round-trip.

Hypercube connection (Stay–Meredith–Wells, Section 5.12): this is the reflection
operator — bindings become first-class citizens in the term language. The
collapse-bind/superpose-bind pair is a modal operator (□/◇) acting on the full
(term, context) pair. -/

private def encodeAssignment : String × Atom → Atom
  | (v, a) => .expression [.symbol v, a]

private def decodeAssignment? : Atom → Option (String × Atom)
  | .expression [.symbol v, a] => some (v, a)
  | _ => none

private def encodeEquality : String × String → Atom
  | (a, c) => .expression [.symbol a, .symbol c]

private def decodeEquality? : Atom → Option (String × String)
  | .expression [.symbol a, .symbol c] => some (a, c)
  | _ => none

/-- Encode bindings as an Atom expression for collapse-bind/superpose-bind. -/
def toAtom (b : Bindings) : Atom :=
  .expression [.symbol "Bindings",
    .expression (b.assignments.map encodeAssignment),
    .expression (b.equalities.map encodeEquality)]

/-- Decode bindings from an Atom expression. Inverse of `toAtom`. -/
def ofAtom? : Atom → Option Bindings
  | .expression [.symbol "Bindings", .expression assigns, .expression eqs] =>
    let assignments := assigns.filterMap decodeAssignment?
    let equalities := eqs.filterMap decodeEquality?
    if assignments.length = assigns.length && equalities.length = eqs.length then
      some ⟨assignments, equalities⟩
    else none
  | _ => none

private theorem filterMap_decode_encode_assignments (xs : List (String × Atom)) :
    (xs.map encodeAssignment).filterMap decodeAssignment? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [List.map, encodeAssignment, decodeAssignment?, ih]

private theorem filterMap_decode_encode_equalities (xs : List (String × String)) :
    (xs.map encodeEquality).filterMap decodeEquality? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [List.map, encodeEquality, decodeEquality?, ih]

theorem ofAtom_toAtom (b : Bindings) : ofAtom? (toAtom b) = some b := by
  simp only [toAtom, ofAtom?]
  rw [filterMap_decode_encode_assignments, filterMap_decode_encode_equalities]
  simp [List.length_map]

end Bindings

/-! ## Result Types -/

/-- A single result from the HE interpreter: an atom paired with bindings.
    Ref: metta.md line 250 "[(Atom, Bindings)]". -/
abbrev ResultPair := Atom × Bindings

/-- The result set from the HE interpreter.
    Ref: metta.md line 250. -/
abbrev ResultSet := List ResultPair

/-! ## Result Equivalence

The HE spec is partially ambiguous about result ordering.
`interpret_expression` explicitly returns `$tuples + $errors` (ordered).
But within each group, order depends on type-list iteration (unspecified).

We define two equivalences:
- `ResultEqOrdered`: exact list equality (where spec mandates order)
- `ResultEqBag`: multiset equivalence (where spec is silent on order)
-/

/-- Ordered result equivalence (list equality). -/
def ResultEqOrdered (r1 r2 : ResultSet) : Prop := r1 = r2

/-- Multiset (bag) result equivalence, ignoring order.
    Two result sets are bag-equivalent when they are permutations. -/
def ResultEqBag (r1 r2 : ResultSet) : Prop :=
  r1.Perm r2

/-! ## Function Type Utilities

Ref: metta.md lines 98-104 `(-> arg1_type ... argN_type ret_type)`. -/

/-- Check if an atom is a function type `(-> ...)`. -/
def isFunctionType : Atom → Bool
  | .expression (.symbol "->" :: _ :: _) => true
  | _ => false

/-- Extract argument types from a function type `(-> t1 t2 ... tN ret)`.
    Returns all types except the last (which is the return type). -/
def getFunctionArgTypes : Atom → Option (List Atom)
  | .expression (.symbol "->" :: rest) =>
    if rest.length ≥ 2 then some (rest.dropLast)
    else none
  | _ => none

/-- Extract the return type from a function type `(-> ... ret)`. -/
def getFunctionRetType : Atom → Option Atom
  | .expression (.symbol "->" :: rest) =>
    if rest.length ≥ 2 then rest.getLast?
    else none
  | _ => none

/-- Get the number of arguments a function type expects. -/
def getFunctionArity : Atom → Option Nat :=
  fun a => (getFunctionArgTypes a).map List.length

/-! ## Atom Predicates (HE-specific) -/

/-- Check if atom is Empty.
    Ref: metta.md line 253. -/
def isEmptyAtom (a : Atom) : Bool := a == Atom.empty

/-- Check if atom is an Error expression.
    Ref: metta.md line 253. -/
def isErrorAtom : Atom → Bool
  | .expression (.symbol "Error" :: _) => true
  | _ => false

/-- Check if atom is Empty or Error.
    Used in short-circuit conditions throughout the interpreter. -/
def isEmptyOrError (a : Atom) : Bool :=
  isEmptyAtom a || isErrorAtom a

/-! ## Convenience Constructors (for tests) -/

/-- Shorthand for symbol atom. -/
abbrev sym := Atom.symbol

/-- Shorthand for variable atom. -/
abbrev vr := Atom.var

/-- Shorthand for expression atom. -/
abbrev expr := Atom.expression

/-! ## Meta-type of an atom

Returns the meta-type as a symbol atom.
Ref: metta.md line 252 `<meta-type of the $atom>`. -/

/-- Get the meta-type of an atom as a symbol.
    Ref: metta.md implicit in interpreter, explicit in `types.rs:get_meta_type`. -/
def getMetaType : Atom → Atom
  | .symbol _ => Atom.symbolType
  | .var _ => Atom.variableType
  | .grounded _ => Atom.groundedType
  | .expression _ => Atom.expressionType

/-! ## Unit Tests -/

section Tests

-- Error code construction
example : (ErrorCode.stackOverflow).toAtom = .symbol "StackOverflow" := rfl
example : (ErrorCode.badType (.symbol "Int") (.symbol "Bool")).toAtom =
    .expression [.symbol "BadType", .symbol "Int", .symbol "Bool"] := rfl

-- mkError
example : mkError (.symbol "x") .stackOverflow =
    .expression [.symbol "Error", .symbol "x", .symbol "StackOverflow"] := rfl

-- Bindings
example : Bindings.empty.assignments = [] := rfl
example : Bindings.empty.equalities = [] := rfl
example : (Bindings.empty.assign "x" (.symbol "a")).lookup "x" = some (.symbol "a") := rfl
example : (Bindings.empty.assign "x" (.symbol "a")).lookup "y" = none := rfl

-- Function type utilities
example : isFunctionType (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) = true := rfl
example : isFunctionType (.symbol "Int") = false := rfl
example : getFunctionArgTypes (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) =
    some [.symbol "Int"] := rfl
example : getFunctionRetType (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) =
    some (.symbol "Bool") := rfl

-- Meta-type
example : getMetaType (.symbol "x") = Atom.symbolType := rfl
example : getMetaType (.var "x") = Atom.variableType := rfl
example : getMetaType (.expression []) = Atom.expressionType := rfl
example : getMetaType (.grounded (.int 42)) = Atom.groundedType := rfl

-- Predicates
example : isEmptyAtom Atom.empty = true := rfl
example : isErrorAtom (Atom.error (.symbol "x") (.symbol "msg")) = true := rfl
example : isEmptyOrError Atom.empty = true := rfl
example : isEmptyOrError (Atom.error (.symbol "x") (.symbol "msg")) = true := rfl
example : isEmptyOrError (.symbol "foo") = false := rfl

-- ResultEqBag reflexivity
example : ResultEqBag ([] : ResultSet) [] := List.Perm.nil

end Tests

end Mettapedia.Languages.MeTTa.HE
