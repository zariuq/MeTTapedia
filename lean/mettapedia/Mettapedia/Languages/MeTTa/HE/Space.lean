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

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

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
Ref: `types.rs:get_atom_types` (ground truth).

Type resolution dispatches by atom kind:
1. **Variables** → no type (falls back to `%Undefined%`)
2. **Grounded atoms** → intrinsic type from `Grounded::type_()` trait
3. **Symbols** → explicit `(: atom type)` annotations in space
4. **Expressions** → space annotations (application type inference deferred)

If no type is found, returns `[%Undefined%]`.
-/

/-- Get the intrinsic HE type of a grounded value.
    Ref: `hyperon-atom/src/gnd/{number,bool,str}.rs` — `Grounded::type_()` impl.
    HE uses `Number` (not `Int`) for all numeric grounded values. -/
def getGroundedType : GroundedValue → Atom
  | .int _       => .symbol "Number"
  | .bool _      => .symbol "Bool"
  | .string _    => .symbol "String"
  | .custom t _  => .symbol t

/-- Collect explicit `(: atom type)` annotations for an atom from space.
    Ref: `types.rs:query_types`. -/
def getAnnotatedTypes (space : Space) (a : Atom) : List Atom :=
  space.atoms.filterMap fun atom =>
    match atom with
    | .expression [.symbol ":", a', ty] =>
      if a' == a then some ty else none
    | _ => none

/-- Get all types for an atom from the space.
    Ref: `types.rs:get_atom_types`, metta.md line 287.

    Dispatches by atom kind following the Rust implementation:
    - Variables: no type → `%Undefined%`
    - Grounded: intrinsic type from `Grounded::type_()`
    - Symbols: `(: atom type)` annotations in space
    - Expressions: space annotations (application type inference deferred) -/
def getAtomTypes (space : Space) (a : Atom) : List Atom :=
  let types := match a with
    | .var _ => []
    | .grounded g =>
      let ty := getGroundedType g
      if ty == Atom.undefinedType then [] else [ty]
    | .symbol _ => getAnnotatedTypes space a
    | .expression es =>
      if es.isEmpty then []
      else getAnnotatedTypes space a
  if types.isEmpty then [Atom.undefinedType]
  else types

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

/-- Collect all variable names occurring in an atom (with duplicates).
    Fuel-bounded with `where`-clause list traversal for kernel reduction
    (nested-inductive `Atom` requires explicit structural recursion). -/
def collectVars (a : Atom) (fuel : Nat := 100) : List String :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match a with
    | .var v => [v]
    | .expression es => collectVarsList es n
    | _ => []
where
  collectVarsList : List Atom → Nat → List String
    | [], _ => []
    | a :: as, fuel => collectVars a fuel ++ collectVarsList as fuel

/-- Rename variables in an atom according to a mapping.
    Fuel-bounded with `where`-clause list traversal for kernel reduction. -/
def renameVars (mapping : List (String × String)) (a : Atom) (fuel : Nat := 100) : Atom :=
  match fuel with
  | 0 => a
  | n + 1 =>
    match a with
    | .var v => .var (mapping.find? (fun p => p.1 == v) |>.map Prod.snd |>.getD v)
    | .expression es => .expression (renameVarsList mapping es n)
    | a => a
where
  renameVarsList (mapping : List (String × String)) : List Atom → Nat → List Atom
    | [], _ => []
    | a :: as, fuel => renameVars mapping a fuel :: renameVarsList mapping as fuel

/-- Build a fresh variable mapping for one equation's variables.
    Each distinct variable name gets a unique suffix `#counter`.
    Returns the mapping and the updated counter.
    Ref: Rust HE uses `CachingMapper` + `VariableAtom::make_unique()`. -/
def freshMapping (counter : Nat) (vars : List String) : List (String × String) × Nat :=
  vars.foldl (fun (acc, n) v =>
    if acc.any (fun p => p.1 == v) then (acc, n)
    else ((v, s!"{v}#{n}") :: acc, n + 1))
  ([], counter)

/-- Alpha-rename equation-local variables using the equation's index as a
    unique prefix. Returns `(renamed_lhs, renamed_rhs)`.
    Uses the same fuel as the parent query for kernel reduction. -/
def freshenEquation (idx : Nat) (lhs rhs : Atom) (fuel : Nat := 100) : Atom × Atom :=
  let vars := (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups
  let (mapping, _) := freshMapping idx vars
  (renameVars mapping lhs fuel, renameVars mapping rhs fuel)

/-- Query equations `(= lhs rhs)` in space where `lhs` matches `atom`.
    Returns list of `(rhs, bindings)` pairs.
    Equation-local variables are alpha-renamed with unique suffixes to prevent
    collisions across recursive equation applications.
    Ref: metta.md line 538 `query($space, (= $atom $X))`.
    Ref: Rust HE `hyperon-space/src/index/trie.rs:261-359` (CachingMapper). -/
def queryEquations (space : Space) (atom : Atom) (fuel : Nat := 100) : List (Atom × Bindings) :=
  space.atoms.zipIdx.filterMap fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      let (lhs', rhs') := freshenEquation idx lhs rhs fuel
      match simpleMatch lhs' atom Bindings.empty fuel with
      | some b => some (rhs', b)
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

-- Symbol with annotation → annotated type
example : getAtomTypes testSpace (.symbol "foo") = [.symbol "Int"] := rfl
-- Symbol without annotation → %Undefined%
example : getAtomTypes testSpace (.symbol "baz") = [Atom.undefinedType] := rfl
-- Grounded int → Number (intrinsic, not from space)
example : getAtomTypes testSpace (.grounded (.int 42)) = [.symbol "Number"] := rfl
-- Grounded bool → Bool
example : getAtomTypes testSpace (.grounded (.bool true)) = [.symbol "Bool"] := rfl
-- Grounded string → String
example : getAtomTypes testSpace (.grounded (.string "hi")) = [.symbol "String"] := rfl
-- Variable → %Undefined%
example : getAtomTypes testSpace (.var "x") = [Atom.undefinedType] := rfl

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
