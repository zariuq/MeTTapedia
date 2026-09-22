import Mettapedia.OSLF.StructuralModal.Formula

/-!
# Indexed recursive structural-modal formulas

Finite `Formula` values describe finite constructor shapes. Recursive
constructor languages require a least fixed point. This module adds that
finitary polynomial layer without changing the existing modal semantics.

A recursive signature is indexed by guest-owned states. Every branch carries
an exact constructor/arity witness from the supplied `LanguageDef`; recursive
arguments name another state, while nonrecursive arguments use an ordinary
structural-modal formula. `Satisfies` is the initial algebra of this signature, exposed by
an unfolding theorem and a leastness theorem.
-/

namespace Mettapedia.OSLF.StructuralModal.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.StructuralModal
open Mettapedia.OSLF.Framework.DerivedModalities

universe uIndex uBranch

/-- One argument of a recursive spatial constructor. -/
inductive Argument (Index : Type uIndex) where
  | formula (formula : Formula)
  | recur (index : Index)
deriving Repr

/-- What a branch matches at the root.

A recursive spatial signature previously spoke only of application nodes, so a
collection former could not be a branch at all and the scope construction had to
be built beside this module rather than on it.  A collection is a term former
like any other and belongs here. -/
inductive BranchShape where
  /-- Headed by a named constructor. -/
  | headed (constructor : String)
  /-- A collection of the given kind, with no remainder. -/
  | collected (kind : CollType)
deriving Repr, DecidableEq

/-- What it is for a term to present a branch's shape with the given children. -/
def BranchShape.Matches : BranchShape → Pattern → List Pattern → Prop
  | .headed constructor, pattern, children => pattern = .apply constructor children
  | .collected kind, pattern, children => pattern = .collection kind children none

/-- The indexed spatial shape contributed by one constructor branch. -/
structure BranchDescription (Index : Type uIndex) where
  output : Index
  shape : BranchShape
  arguments : List (Argument Index)
deriving Repr

/-- A recursive spatial signature whose branches are witnessed constructors
of one supplied language specification. -/
structure Signature (Index : Type uIndex) where
  language : LanguageDef
  Branch : Type uBranch
  describe : Branch → BranchDescription Index
  declared : ∀ branch,
    match (describe branch).shape with
    | .headed constructor =>
        ∃ rule ∈ language.terms,
          rule.label = constructor ∧
          rule.params.length = (describe branch).arguments.length
    | .collected kind =>
        ∃ rule ∈ language.terms, ∃ parameterName elementType,
          rule.params = [.simple parameterName (.collection kind elementType)]

mutual

/-- Least-fixed-point inhabitation of an indexed recursive spatial signature. -/
inductive Satisfies {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) : Index → Pattern → Prop where
  | headed (branch : signature.Branch) (constructor : String)
      (children : List Pattern)
      (shape : (signature.describe branch).shape = .headed constructor)
      (childrenEvidence :
        SatisfiesAll span signature (signature.describe branch).arguments children) :
      Satisfies span signature (signature.describe branch).output
        (.apply constructor children)
  | collected (branch : signature.Branch) (kind : CollType)
      (children : List Pattern)
      (shape : (signature.describe branch).shape = .collected kind)
      (childrenEvidence :
        SatisfiesAll span signature (signature.describe branch).arguments children) :
      Satisfies span signature (signature.describe branch).output
        (.collection kind children none)

/-- Pointwise inhabitation of recursive and ordinary base formulas. -/
inductive SatisfiesAll {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) :
    List (Argument Index) → List Pattern → Prop where
  | nil : SatisfiesAll span signature [] []
  | formula {formula arguments child children}
      (head : satisfiesOver span formula child)
      (tail : SatisfiesAll span signature arguments children) :
      SatisfiesAll span signature
        (.formula formula :: arguments) (child :: children)
  | recur {index arguments child children}
      (head : Satisfies span signature index child)
      (tail : SatisfiesAll span signature arguments children) :
      SatisfiesAll span signature
        (.recur index :: arguments) (child :: children)

end

/-- One polynomial layer interpreted over a candidate indexed predicate. -/
def layerAll {Index : Type uIndex} (span : ReductionSpan Pattern)
    (predicate : Index → Pattern → Prop) :
    List (Argument Index) → List Pattern → Prop
  | [], [] => True
  | .formula formula :: arguments, child :: children =>
      satisfiesOver span formula child ∧
        layerAll span predicate arguments children
  | .recur index :: arguments, child :: children =>
      predicate index child ∧ layerAll span predicate arguments children
  | _, _ => False

/-- The polynomial endofunction determined by a recursive signature. -/
def layer {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) (predicate : Index → Pattern → Prop)
    (index : Index) (pattern : Pattern) : Prop :=
  ∃ branch : signature.Branch,
    (signature.describe branch).output = index ∧
    ∃ children : List Pattern,
      (signature.describe branch).shape.Matches pattern children ∧
      layerAll span predicate (signature.describe branch).arguments children

theorem SatisfiesAll.toLayerAll {Index : Type uIndex}
    {span : ReductionSpan Pattern} {signature : Signature Index}
    {arguments : List (Argument Index)} {children : List Pattern}
    (evidence : SatisfiesAll span signature arguments children) :
    layerAll span (Satisfies span signature) arguments children := by
  cases evidence with
  | nil => trivial
  | formula head tail =>
      exact ⟨head, tail.toLayerAll⟩
  | recur head tail =>
      exact ⟨head, tail.toLayerAll⟩
termination_by arguments.length
decreasing_by simp_wf; simp

theorem satisfiesAll_of_layerAll {Index : Type uIndex}
    {span : ReductionSpan Pattern} {signature : Signature Index}
    {arguments : List (Argument Index)} {children : List Pattern}
    (evidence :
      layerAll span (Satisfies span signature) arguments children) :
    SatisfiesAll span signature arguments children := by
  induction arguments generalizing children with
  | nil =>
      cases children with
      | nil => exact .nil
      | cons child children => cases evidence
  | cons argument arguments inductionHypothesis =>
      cases children with
      | nil => simp [layerAll] at evidence
      | cons child children =>
          cases argument with
          | formula formula =>
              exact .formula evidence.1 (inductionHypothesis evidence.2)
          | recur index =>
              exact .recur evidence.1 (inductionHypothesis evidence.2)

/-- Recursive inhabitation is a fixed point of the signature polynomial. -/
theorem satisfies_iff_layer {Index : Type uIndex}
    (span : ReductionSpan Pattern) (signature : Signature Index)
    (index : Index) (pattern : Pattern) :
    Satisfies span signature index pattern ↔
      layer span signature (Satisfies span signature) index pattern := by
  constructor
  · intro evidence
    cases evidence with
    | headed branch constructor children shape childrenEvidence =>
        refine ⟨branch, rfl, children, ?_, childrenEvidence.toLayerAll⟩
        simp [shape, BranchShape.Matches]
    | collected branch kind children shape childrenEvidence =>
        refine ⟨branch, rfl, children, ?_, childrenEvidence.toLayerAll⟩
        simp [shape, BranchShape.Matches]
  · rintro ⟨branch, output, children, shape, childrenEvidence⟩
    subst output
    revert shape
    cases hshape : (signature.describe branch).shape with
    | headed constructor =>
        intro shape
        simp only [BranchShape.Matches] at shape
        subst shape
        exact .headed branch constructor children hshape
          (satisfiesAll_of_layerAll childrenEvidence)
    | collected kind =>
        intro shape
        simp only [BranchShape.Matches] at shape
        subst shape
        exact .collected branch kind children hshape
          (satisfiesAll_of_layerAll childrenEvidence)

/-- A candidate interpretation is closed when it contains one complete
polynomial layer over itself. -/
def Closed {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) (predicate : Index → Pattern → Prop) : Prop :=
  ∀ index pattern, layer span signature predicate index pattern →
    predicate index pattern

mutual

/-- Leastness: recursive inhabitation is contained in every closed indexed
predicate. -/
theorem Satisfies.least {Index : Type uIndex}
    {span : ReductionSpan Pattern} {signature : Signature Index}
    {predicate : Index → Pattern → Prop}
    (closed : Closed span signature predicate)
    {index : Index} {pattern : Pattern}
    (evidence : Satisfies span signature index pattern) :
    predicate index pattern := by
  cases evidence with
  | headed branch constructor children shape childrenEvidence =>
      apply closed
      refine ⟨branch, rfl, children, ?_, childrenEvidence.least closed⟩
      simp [shape, BranchShape.Matches]
  | collected branch kind children shape childrenEvidence =>
      apply closed
      refine ⟨branch, rfl, children, ?_, childrenEvidence.least closed⟩
      simp [shape, BranchShape.Matches]

/-- Pointwise recursive part of the leastness proof. -/
theorem SatisfiesAll.least {Index : Type uIndex}
    {span : ReductionSpan Pattern} {signature : Signature Index}
    {predicate : Index → Pattern → Prop}
    (closed : Closed span signature predicate)
    {arguments : List (Argument Index)} {children : List Pattern}
    (evidence : SatisfiesAll span signature arguments children) :
    layerAll span predicate arguments children := by
  cases evidence with
  | nil => trivial
  | formula head tail => exact ⟨head, tail.least closed⟩
  | recur head tail => exact ⟨head.least closed, tail.least closed⟩

end


/-! ## A collection branch, inhabited

The extension is not decorative: a signature whose branch is a collection has a
term inhabiting it, and an application node of the same arity does not.  Before
it, no branch could match a collection at all, which is why the generated scope
construction was built beside this module instead of on it. -/

namespace CollectionBranch

/-- A presentation with a bag carrier and one nullary constructor. -/
def language : LanguageDef where
  name := "BagPair"
  types := [TypeDecl.plain "T"]
  terms :=
    [ { label := "Par"
        category := "T"
        params := [.simple "parts" (.collection .hashBag (.base "T"))]
        syntaxPattern := [.terminal "Par"] },
      { label := "A"
        category := "T"
        params := []
        syntaxPattern := [.terminal "A"] } ]
  equations := []
  rewrites := []

/-- One state. -/
inductive State where
  | pair
  deriving DecidableEq, Repr

/-- One branch, and it is a collection. -/
inductive Branch where
  | pairBranch
  deriving DecidableEq, Repr

/-- The branch: a bag of exactly two `A`s. -/
def describe : Branch → BranchDescription State
  | .pairBranch =>
      ⟨.pair, .collected .hashBag,
        [.formula (.headed "A" []), .formula (.headed "A" [])]⟩

/-- **The signature, with its collection branch witnessed by the
presentation.**  The obligation for a collection branch is that the language
declares a carrier of that kind, which this one does. -/
def signature : Signature State where
  language := language
  Branch := Branch
  describe := describe
  declared := by
    intro branch
    cases branch
    exact ⟨{ label := "Par"
             category := "T"
             params := [.simple "parts" (.collection .hashBag (.base "T"))]
             syntaxPattern := [.terminal "Par"] },
      by simp [language], "parts", .base "T", rfl⟩

/-- The `A` constructor as a term. -/
def atomA : Pattern := .apply "A" []

/-- A two-element bag of them. -/
def pairTerm : Pattern := .collection .hashBag [atomA, atomA] none

/-- Each element inhabits the branch's argument formula. -/
theorem atomA_satisfies (span : ReductionSpan Pattern) :
    satisfiesOver span (.headed "A" []) atomA :=
  ⟨[], rfl, trivial⟩

/-- **The bag inhabits the collection branch.** -/
theorem pairTerm_satisfies (span : ReductionSpan Pattern) :
    Satisfies span signature .pair pairTerm :=
  .collected (Branch.pairBranch) .hashBag [atomA, atomA] rfl
    (.formula (atomA_satisfies span) (.formula (atomA_satisfies span) .nil))

/-- **And an application node does not**, whatever its children: the branch's
shape is a collection, and the two shapes are different term formers. -/
theorem apply_not_satisfies (span : ReductionSpan Pattern)
    (constructor : String) (children : List Pattern) :
    ¬ Satisfies span signature .pair (.apply constructor children) := by
  intro evidence
  cases evidence with
  | headed branch label childrenList shape _ =>
      cases branch
      simp [signature, describe] at shape

end CollectionBranch

end Mettapedia.OSLF.StructuralModal.Recursive
