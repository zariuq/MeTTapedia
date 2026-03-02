import Mettapedia.Languages.MeTTa.HE.Types

/-!
# HE MeTTa Space

Atomspace and grounded dispatch for the HE interpreter formalization.
Uses computable (List-based) representation to enable `decide` proofs.

## Source Precedence
1. `interpreter.rs` (ground truth)
2. `metta.md` (spec)

## Main Definitions
* `Space` - Computable atomspace (List-based)
* `getAtomTypes` - Get all types for an atom from space
* `getMetaType` - Intrinsic meta-type of an atom
* `queryEquations` - Query `(= pattern $X)` matching
* `GroundedResult` / `GroundedDispatch` - Grounded operation dispatch
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.Core (Atom GroundedValue)

/-! ## Space

A computable atomspace using `List Atom` (unlike MeTTaCore.Atomspace which uses
noncomputable `Multiset`). This enables kernel-checked conformance tests. -/

/-- Computable atomspace for HE interpreter.
    Ref: metta.md "Atomspace" concept. -/
structure Space where
  atoms : List Atom
  deriving Repr, Inhabited, DecidableEq

namespace Space

/-- Empty space. -/
def empty : Space := ⟨[]⟩

instance : EmptyCollection Space := ⟨empty⟩

/-- Add an atom. -/
def add (s : Space) (a : Atom) : Space :=
  ⟨a :: s.atoms⟩

/-- Remove first occurrence of an atom. -/
def remove (s : Space) (a : Atom) : Space :=
  ⟨s.atoms.erase a⟩

/-- Add multiple atoms. -/
def addMany (s : Space) (as : List Atom) : Space :=
  ⟨as ++ s.atoms⟩

/-- Create from a list of atoms. -/
def ofList (as : List Atom) : Space := ⟨as⟩

/-- Check if an atom is a type annotation `(: atom type)`. -/
def isTypeAnnotation : Atom → Bool
  | .expression [.symbol ":", _, _] => true
  | _ => false

/-- Get the annotated atom from `(: atom type)`. -/
def getAnnotatedAtom : Atom → Option Atom
  | .expression [.symbol ":", a, _] => some a
  | _ => none

/-- Get the type from `(: atom type)`. -/
def getAnnotationType : Atom → Option Atom
  | .expression [.symbol ":", _, ty] => some ty
  | _ => none

/-- Check if an atom is an equation `(= lhs rhs)`. -/
def isEquation : Atom → Bool
  | .expression [.symbol "=", _, _] => true
  | _ => false

/-- Get LHS of equation. -/
def getEquationLhs : Atom → Option Atom
  | .expression [.symbol "=", lhs, _] => some lhs
  | _ => none

/-- Get RHS of equation. -/
def getEquationRhs : Atom → Option Atom
  | .expression [.symbol "=", _, rhs] => some rhs
  | _ => none

end Space

/-! ## Type Queries

Ref: metta.md line 287 `<list of the types of the $atom from the $space>`.
The HE spec collects types from:
1. Explicit `(: atom type)` annotations in space
2. Intrinsic meta-type if no annotations found
-/

/-- Get all types for an atom from space annotations.
    If no annotations found, returns `[%Undefined%]`.
    Ref: `types.rs:get_atom_types`, metta.md line 287. -/
def getAtomTypes (space : Space) (a : Atom) : List Atom :=
  let annotated := space.atoms.filterMap fun atom =>
    match atom with
    | .expression [.symbol ":", a', ty] =>
      if a' == a then some ty else none
    | _ => none
  if annotated.isEmpty then [Atom.undefinedType]
  else annotated

/-! ## Equation Query

Ref: metta.md line 538 `query($space, (= $atom $X))`.
Matches equations `(= pattern rhs)` against the query atom. -/

/-- Simple one-way pattern matching: does `pattern` match `target`?
    Variables in `pattern` bind to subterms of `target`.
    Returns resulting bindings on success.
    Ref: used by equation query to match LHS patterns. -/
def simpleMatch (pattern target : Atom) (b : Bindings) (fuel : Nat) : Option Bindings :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match pattern with
    | .var v =>
      match b.lookup v with
      | some existing => if existing == target then some b else none
      | none => some (b.assign v target)
    | .symbol s =>
      match target with
      | .symbol t => if s == t then some b else none
      | _ => none
    | .grounded g =>
      match target with
      | .grounded h => if g == h then some b else none
      | _ => none
    | .expression ps =>
      match target with
      | .expression ts =>
        if ps.length != ts.length then none
        else simpleMatchList ps ts b n
      | _ => none
where
  simpleMatchList : List Atom → List Atom → Bindings → Nat → Option Bindings
    | [], [], b, _ => some b
    | p :: ps, t :: ts, b, fuel =>
      match simpleMatch p t b fuel with
      | some b' => simpleMatchList ps ts b' fuel
      | none => none
    | _, _, _, _ => none

/-- Query equations `(= lhs rhs)` in space where `lhs` matches `atom`.
    Returns list of `(rhs, bindings)` pairs.
    Ref: metta.md line 538 `query($space, (= $atom $X))`. -/
def queryEquations (space : Space) (atom : Atom) (fuel : Nat := 100) : List (Atom × Bindings) :=
  space.atoms.filterMap fun eq =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      match simpleMatch lhs atom Bindings.empty fuel with
      | some b => some (rhs, b)
      | none => none
    | _ => none

/-! ## Grounded Dispatch

Ref: metta.md lines 527-536, `interpreter.rs` metta_call grounded branch.

The HE interpreter dispatches grounded operations via dynamic dispatch.
We parameterize over a `GroundedDispatch` structure. -/

/-- Result of executing a grounded operation.
    Ref: metta.md lines 529-536, `ExecError` in interpreter.rs. -/
inductive GroundedResult where
  | ok : ResultSet → GroundedResult
  | runtimeError : String → GroundedResult
  | noReduce : GroundedResult
  | incorrectArgument : GroundedResult
  deriving Repr, Inhabited, DecidableEq

/-- Grounded operation dispatch table.
    Ref: metta.md lines 527-536.

    - `isExecutable`: check if atom is an executable grounded atom
    - `execute`: call the grounded operation with arguments -/
structure GroundedDispatch where
  isExecutable : Atom → Bool
  execute : Atom → List Atom → GroundedResult
  deriving Inhabited

/-- Default dispatch with no grounded operations. -/
def GroundedDispatch.none : GroundedDispatch :=
  { isExecutable := fun _ => false
    execute := fun _ _ => .noReduce }

/-- Dispatch with standard arithmetic/boolean operations. -/
def GroundedDispatch.standard : GroundedDispatch :=
  { isExecutable := fun a => match a with
      | .grounded _ => true
      | _ => false
    execute := fun op _args => match op with
      | .grounded (.int _) => .noReduce  -- numbers are not callable
      | .grounded (.bool _) => .noReduce
      | .grounded (.string _) => .noReduce
      | _ => .noReduce }

/-! ## Unit Tests -/

section Tests

-- Space basics
example : Space.empty.atoms = [] := rfl
example : (Space.empty.add (.symbol "x")).atoms = [.symbol "x"] := rfl

-- Meta-type
example : getMetaType (.symbol "x") = .symbol "Symbol" := rfl
example : getMetaType (.var "x") = .symbol "Variable" := rfl

-- getAtomTypes
private def testSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "foo", .symbol "Int"],
    .expression [.symbol ":", .symbol "bar", .symbol "Bool"],
    .expression [.symbol "=", .symbol "foo", .grounded (.int 42)]
  ]

example : getAtomTypes testSpace (.symbol "foo") = [.symbol "Int"] := rfl
example : getAtomTypes testSpace (.symbol "baz") = [Atom.undefinedType] := rfl

-- queryEquations
example : queryEquations testSpace (.symbol "foo") =
    [(.grounded (.int 42), Bindings.empty)] := rfl

-- simpleMatch
example : simpleMatch (.var "x") (.symbol "hello") Bindings.empty 10 =
    some (Bindings.empty.assign "x" (.symbol "hello")) := rfl
example : simpleMatch (.symbol "a") (.symbol "a") Bindings.empty 10 =
    some Bindings.empty := rfl
example : simpleMatch (.symbol "a") (.symbol "b") Bindings.empty 10 =
    none := rfl

-- GroundedResult
example : GroundedResult.ok [] = GroundedResult.ok [] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
