import Mettapedia.Languages.MeTTa.OSLFCore.Bindings
import Mathlib.Data.Multiset.Basic

/-!
# MeTTaCore Atomspace

The Atomspace is the queryable knowledge store in MeTTa. It holds atoms
(including equations of form `(= pattern result)`) and supports pattern matching queries.

## Main Definitions

* `Atomspace` - The knowledge store
* `Atomspace.query` - Pattern matching query
* `Atomspace.add` / `Atomspace.remove` - Space modifications

## References

* [Hyperon Experimental Spec](https://trueagi-io.github.io/hyperon-experimental/metta/)
* Meta-MeTTa paper: k (knowledge) register
-/

namespace Mettapedia.Languages.MeTTa.OSLFCore

/-! ## Atomspace Structure -/

/-- The Atomspace is the knowledge store in MeTTa.

    Following Meta-MeTTa, it contains:
    - A multiset of atoms
    - Equations are stored as `(= pattern result)` atoms

    The multiset semantics means order doesn't matter but multiplicity does. -/
structure Atomspace where
  /-- All atoms in the space -/
  atoms : Multiset Atom
  deriving Inhabited

namespace Atomspace

/-! ### Basic Operations -/

/-- Empty atomspace -/
def empty : Atomspace := ⟨∅⟩

instance : EmptyCollection Atomspace := ⟨empty⟩

/-- Add an atom to the space -/
def add (s : Atomspace) (a : Atom) : Atomspace :=
  ⟨a ::ₘ s.atoms⟩

/-- Remove an atom from the space (removes one occurrence) -/
def remove (s : Atomspace) (a : Atom) : Atomspace :=
  ⟨s.atoms.erase a⟩

/-- Check if atom is in space -/
def contains (s : Atomspace) (a : Atom) : Bool :=
  a ∈ s.atoms

/-- Number of atoms in space -/
def size (s : Atomspace) : Nat :=
  s.atoms.card

/-! ### Equations -/

/-- Check if an atom is an equation `(= lhs rhs)` -/
def isEquation : Atom → Bool
  | .expression [.symbol "=", _, _] => true
  | _ => false

/-- Extract LHS of an equation -/
def equationLhs : Atom → Option Atom
  | .expression [.symbol "=", lhs, _] => some lhs
  | _ => none

/-- Extract RHS of an equation -/
def equationRhs : Atom → Option Atom
  | .expression [.symbol "=", _, rhs] => some rhs
  | _ => none

/-- Get all equations in the space -/
def equations (s : Atomspace) : Multiset Atom :=
  s.atoms.filter (isEquation · = true)

/-- Add an equation `(= pattern result)` to the space -/
def addEquation (s : Atomspace) (pattern result : Atom) : Atomspace :=
  s.add (Atom.equality pattern result)

/-! ### Type Annotations -/

/-- Check if an atom is a type annotation `(: atom type)` -/
def isTypeAnnotation : Atom → Bool
  | .expression [.symbol ":", _, _] => true
  | _ => false

/-- Get the typed atom from annotation -/
def annotatedAtom : Atom → Option Atom
  | .expression [.symbol ":", a, _] => some a
  | _ => none

/-- Get the type from annotation -/
def annotationType : Atom → Option Atom
  | .expression [.symbol ":", _, ty] => some ty
  | _ => none

/-- Get all type annotations in the space -/
def typeAnnotations (s : Atomspace) : Multiset Atom :=
  s.atoms.filter (isTypeAnnotation · = true)

/-- Add a type annotation `(: atom type)` to the space -/
def addType (s : Atomspace) (a ty : Atom) : Atomspace :=
  s.add (Atom.typeAnnotation a ty)

/-! ### Pattern Matching Query -/

/-- Simple pattern matching: check if pattern matches atom.

    Variables in the pattern can match any atom.
    Returns bindings if match succeeds. -/
partial def matchPattern (pattern atom : Atom) (b : Bindings) : Option Bindings :=
  match pattern with
  | .var v =>
    -- Variable matches anything
    match b.lookup v with
    | some existing =>
        -- Already bound: must match
        if existing == atom then some b else none
    | none =>
        -- Unbound: create binding
        some (b.extend v atom)
  | .symbol s =>
    match atom with
    | .symbol t => if s == t then some b else none
    | _ => none
  | .grounded g =>
    match atom with
    | .grounded h => if g == h then some b else none
    | _ => none
  | .expression pats =>
    match atom with
    | .expression args =>
        if pats.length != args.length then none
        else matchPatternList pats args b
    | _ => none
where
  matchPatternList : List Atom → List Atom → Bindings → Option Bindings
    | [], [], b => some b
    | p :: ps, a :: as, b => do
        let b' ← matchPattern p a b
        matchPatternList ps as b'
    | _, _, _ => none

/-- Query the atomspace with a pattern.

    Returns all atoms that match the pattern, along with the bindings produced. -/
def query (s : Atomspace) (pattern : Atom) : Multiset (Atom × Bindings) :=
  s.atoms.filterMap fun a =>
    match matchPattern pattern a Bindings.empty with
    | some b => some (a, b)
    | none => none

/-- Query for equations matching a pattern on the LHS.

    Returns the RHS and bindings for each matching equation. -/
def queryEquations (s : Atomspace) (pattern : Atom) : Multiset (Atom × Bindings) :=
  s.equations.filterMap fun eq =>
    match equationLhs eq, equationRhs eq with
    | some lhs, some rhs =>
        match matchPattern pattern lhs Bindings.empty with
        | some b => some (rhs, b)
        | none => none
    | _, _ => none

/-! ### Insensitivity Predicate (Meta-MeTTa) -/

/-- A term is "insensitive" if no equation in knowledge matches it.

    From Meta-MeTTa paper: insensitive terms are fully reduced. -/
def insensitive (s : Atomspace) (t : Atom) : Bool :=
  (s.queryEquations t).card == 0

/-! ### Bulk Operations -/

/-- Add multiple atoms -/
def addMany (s : Atomspace) (as : List Atom) : Atomspace :=
  as.foldl add s

/-- Create atomspace from list of atoms -/
def ofList (as : List Atom) : Atomspace :=
  empty.addMany as

/-- Convert atomspace to list -/
noncomputable def toList (s : Atomspace) : List Atom :=
  s.atoms.toList

/-! ### Composition Operators -/

/-- Union of atomspaces (multiset sum) -/
def union (s1 s2 : Atomspace) : Atomspace := ⟨s1.atoms + s2.atoms⟩

instance : Union Atomspace := ⟨union⟩

/-- Intersection of atomspaces (keep elements in both) -/
def inter (s1 s2 : Atomspace) : Atomspace :=
  ⟨s1.atoms.filter (· ∈ s2.atoms)⟩

instance : Inter Atomspace := ⟨inter⟩

/-- Difference of atomspaces (multiset subtraction) -/
def diff (s1 s2 : Atomspace) : Atomspace := ⟨s1.atoms - s2.atoms⟩

instance : SDiff Atomspace := ⟨diff⟩

end Atomspace

/-! ## Theorems -/

/-- Empty space has no atoms -/
theorem empty_size : Atomspace.empty.size = 0 := rfl

/-- Adding increases size by 1 -/
theorem add_size (s : Atomspace) (a : Atom) :
    (s.add a).size = s.size + 1 := by
  simp [Atomspace.add, Atomspace.size, Multiset.card_cons]

/-- Empty space contains nothing -/
theorem empty_not_contains (a : Atom) : Atomspace.empty.contains a = false := by
  simp [Atomspace.contains, Atomspace.empty]

/-- Added atom is contained -/
theorem add_contains (s : Atomspace) (a : Atom) :
    (s.add a).contains a = true := by
  simp [Atomspace.add, Atomspace.contains]

/-! ## Composition Properties -/

/-- Union is associative -/
theorem union_assoc (s1 s2 s3 : Atomspace) :
    (s1 ∪ s2) ∪ s3 = s1 ∪ (s2 ∪ s3) := by
  simp only [Union.union, Atomspace.union]
  congr 1
  exact add_assoc _ _ _

/-- Union is commutative -/
theorem union_comm (s1 s2 : Atomspace) :
    s1 ∪ s2 = s2 ∪ s1 := by
  simp only [Union.union, Atomspace.union]
  congr 1
  exact add_comm _ _

/-- Empty is left identity for union -/
theorem union_empty_left (s : Atomspace) :
    ∅ ∪ s = s := by
  simp only [Union.union, Atomspace.union, EmptyCollection.emptyCollection, Atomspace.empty,
             zero_add]

/-- Empty is right identity for union -/
theorem union_empty_right (s : Atomspace) :
    s ∪ ∅ = s := by
  simp only [Union.union, Atomspace.union, EmptyCollection.emptyCollection, Atomspace.empty,
             add_zero]

/-- Union size is sum of sizes -/
theorem union_size (s1 s2 : Atomspace) :
    (s1 ∪ s2).size = s1.size + s2.size := by
  simp only [Union.union, Atomspace.union, Atomspace.size]
  exact Multiset.card_add _ _

/-- Containment in union iff containment in either -/
theorem contains_union_iff (s1 s2 : Atomspace) (a : Atom) :
    (s1 ∪ s2).contains a ↔ s1.contains a ∨ s2.contains a := by
  simp only [Union.union, Atomspace.union, Atomspace.contains]
  simp only [Multiset.mem_add, decide_eq_true_eq]

/-- Left containment implies union containment -/
theorem contains_union_left (s1 s2 : Atomspace) (a : Atom)
    (h : s1.contains a) : (s1 ∪ s2).contains a := by
  rw [contains_union_iff]
  left
  exact h

/-- Right containment implies union containment -/
theorem contains_union_right (s1 s2 : Atomspace) (a : Atom)
    (h : s2.contains a) : (s1 ∪ s2).contains a := by
  rw [contains_union_iff]
  right
  exact h

/-- Equations in union is union of equations -/
theorem equations_union (s1 s2 : Atomspace) :
    (s1 ∪ s2).equations = s1.equations + s2.equations := by
  simp only [Union.union, Atomspace.union, Atomspace.equations]
  exact Multiset.filter_add _ _ _

/-- Query distributes over union -/
theorem query_union (s1 s2 : Atomspace) (p : Atom) :
    (s1 ∪ s2).query p = s1.query p + s2.query p := by
  simp only [Union.union, Atomspace.union, Atomspace.query]
  exact Multiset.filterMap_add _ _ _

/-- Intersection size is at most minimum of sizes -/
theorem inter_size_le_left (s1 s2 : Atomspace) :
    (s1 ∩ s2).size ≤ s1.size := by
  simp only [Inter.inter, Atomspace.inter, Atomspace.size]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- Containment in intersection implies containment in both -/
theorem contains_inter_iff (s1 s2 : Atomspace) (a : Atom) :
    (s1 ∩ s2).contains a ↔ s1.contains a ∧ s2.contains a := by
  simp only [Inter.inter, Atomspace.inter, Atomspace.contains, Multiset.mem_filter,
             decide_eq_true_eq]

/-- Difference size is at most original size -/
theorem diff_size_le (s1 s2 : Atomspace) :
    (s1 \ s2).size ≤ s1.size := by
  simp only [SDiff.sdiff, Atomspace.diff, Atomspace.size]
  exact Multiset.card_le_card (Multiset.sub_le_self _ _)

/-- Query equations distributes over union -/
theorem queryEquations_union (s1 s2 : Atomspace) (t : Atom) :
    (s1 ∪ s2).queryEquations t = s1.queryEquations t + s2.queryEquations t := by
  unfold Atomspace.queryEquations
  -- First show equations distributes over union
  have heq : (s1 ∪ s2).equations = s1.equations + s2.equations := equations_union s1 s2
  rw [heq]
  exact Multiset.filterMap_add _ _ _

/-- If insensitive in both, insensitive in union -/
theorem insensitive_union {s1 s2 : Atomspace} {t : Atom}
    (h1 : s1.insensitive t) (h2 : s2.insensitive t) :
    (s1 ∪ s2).insensitive t := by
  simp only [Atomspace.insensitive, beq_iff_eq] at h1 h2 ⊢
  rw [queryEquations_union]
  simp only [Multiset.card_add, h1, h2, add_zero]

/-! ## Unit Tests -/

section Tests

-- Empty space
example : Atomspace.empty.size = 0 := rfl
example : Atomspace.empty.contains (.symbol "x") = false := by decide

-- Adding atoms
example : (Atomspace.empty.add (.symbol "x")).size = 1 := rfl
example : (Atomspace.empty.add (.symbol "x")).contains (.symbol "x") = true := by decide

-- Equations
example : Atomspace.isEquation (.expression [.symbol "=", .symbol "a", .symbol "b"]) = true := rfl
example : Atomspace.isEquation (.symbol "x") = false := rfl

-- Type annotations
example : Atomspace.isTypeAnnotation (.expression [.symbol ":", .symbol "x", .symbol "Int"]) = true := rfl

end Tests

end Mettapedia.Languages.MeTTa.OSLFCore
