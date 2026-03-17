/-
# Ontology CNL — Abstract Syntax

Controlled Natural Language for ontology declarations, axiom glosses,
and evidence citations. Every tree linearizes to exactly one English string.

This is Phase A of the GF-Aligned English plan: all ontology-facing English
is generated from these abstract trees, never written as free text.

## Design Principle

Trees are canonical. English is a generated view. Agents produce and consume
trees; linearization to English (or LaTeX, or Czech) is a separate step.

## Categories

- `ClassRef`    — reference to an ontology class (e.g., Pain, StateOfMind)
- `RelRef`      — reference to a relation (e.g., attribute, subclass)
- `OntStmt`     — ontology statement (the main sentence-level category)
- `EvidenceItem` — evidence citation with source and strength
- `OntDoc`      — sequence of statements (a documentation block)
-/

namespace Mettapedia.Languages.GF.OntologyCNL

/-! ## Atomic References -/

/-- Reference to an ontology class by name -/
structure ClassRef where
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a relation by name -/
structure RelRef where
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- BinaryEvidence strength levels -/
inductive Strength where
  | strong
  | moderate
  | weak
  deriving DecidableEq, Repr, Inhabited

/-- Source location: file and line -/
structure SourceLoc where
  file : String
  line : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## Ontology Statements -/

/-- Core ontology statement — the sentence-level abstract syntax.
    Each constructor corresponds to one unambiguous English pattern. -/
inductive OntStmt where
  /-- "X is a subclass of Y" -/
  | isSubclassOf (sub sup : ClassRef)
  /-- "X is an instance of Y" -/
  | isInstanceOf (inst cls : ClassRef)
  /-- "the domain of R at position N is C" -/
  | domainAt (rel : RelRef) (pos : Nat) (cls : ClassRef)
  /-- "the range of R is C" -/
  | rangeIs (rel : RelRef) (cls : ClassRef)
  /-- "every X satisfies P" -/
  | forAll (cls : ClassRef) (body : OntStmt)
  /-- "there exists an X such that P" -/
  | exists_ (cls : ClassRef) (body : OntStmt)
  /-- "if P then Q" -/
  | ifThen (hyp concl : OntStmt)
  /-- "P and Q" -/
  | and_ (left right : OntStmt)
  /-- "P or Q" -/
  | or_ (left right : OntStmt)
  /-- "it is not the case that P" -/
  | not_ (body : OntStmt)
  /-- "X has relation R to Y" -/
  | relatesTo (subj : ClassRef) (rel : RelRef) (obj : ClassRef)
  /-- "X is disjoint from Y" -/
  | disjointFrom (a b : ClassRef)
  /-- "R is a BinaryPredicate" (or Ternary, etc.) -/
  | relArity (rel : RelRef) (arity : Nat)
  deriving Repr

/-! ## BinaryEvidence Items -/

/-- An evidence citation: source, what it supports, and how strongly -/
structure EvidenceItem where
  source : SourceLoc
  supports : ClassRef
  strength : Strength
  note : String := ""
  deriving Repr

/-- BinaryEvidence-bearing statements -/
inductive EvidenceStmt where
  /-- "source S supports classification as C (strength)" -/
  | cite (item : EvidenceItem)
  /-- "N axioms use X as a Y" -/
  | usageCount (concept : ClassRef) (role : String) (count : Nat)
  /-- "the recommended classification is C" -/
  | recommendation (concept : ClassRef) (cls : ClassRef)
  deriving Repr

/-! ## Document Structure -/

/-- A documentation block: a sequence of ontology statements and evidence -/
inductive OntDoc where
  | stmt (s : OntStmt)
  | evidence (e : EvidenceStmt)
  | seq (first rest : OntDoc)
  | empty
  deriving Repr

/-! ## Smart Constructors -/

instance : Coe String ClassRef := ⟨ClassRef.mk⟩
instance : Coe String RelRef := ⟨RelRef.mk⟩

/-- Build a doc from a list of statements -/
def OntDoc.ofList : List OntDoc → OntDoc
  | [] => .empty
  | [d] => d
  | d :: ds => .seq d (ofList ds)

end Mettapedia.Languages.GF.OntologyCNL
