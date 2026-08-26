import Mettapedia.OSLF.Framework.NativeTypeTheory

/-!
# Indexed recursive spatial native types

Finite `NativeType` values describe finite constructor shapes. Recursive
constructor languages require a least fixed point. This module adds that
finitary polynomial layer without changing the existing modal semantics.

A recursive signature is indexed by guest-owned states. Every branch carries
an exact constructor/arity witness from the supplied `LanguageDef`; recursive
arguments name another state, while nonrecursive arguments use an ordinary
native type. `Satisfies` is the initial algebra of this signature, exposed by
an unfolding theorem and a leastness theorem.
-/

namespace Mettapedia.OSLF.Framework.RecursiveNativeType

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.NativeTypeTheory
open Mettapedia.OSLF.Framework.DerivedModalities

universe uIndex uBranch

/-- One argument of a recursive spatial constructor. -/
inductive Argument (Index : Type uIndex) where
  | native (nativeType : NativeType)
  | recur (index : Index)
deriving Repr

/-- The indexed spatial shape contributed by one constructor branch. -/
structure BranchDescription (Index : Type uIndex) where
  output : Index
  constructor : String
  arguments : List (Argument Index)
deriving Repr

/-- A recursive spatial signature whose branches are witnessed constructors
of one supplied language presentation. -/
structure Signature (Index : Type uIndex) where
  language : LanguageDef
  Branch : Type uBranch
  describe : Branch → BranchDescription Index
  declared : ∀ branch,
    ∃ rule ∈ language.terms,
      rule.label = (describe branch).constructor ∧
      rule.params.length = (describe branch).arguments.length

mutual

/-- Least-fixed-point inhabitation of an indexed recursive spatial signature. -/
inductive Satisfies {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) : Index → Pattern → Prop where
  | intro (branch : signature.Branch) (children : List Pattern)
      (shape : pattern = .apply (signature.describe branch).constructor children)
      (childrenEvidence :
        SatisfiesAll span signature (signature.describe branch).arguments children) :
      Satisfies span signature (signature.describe branch).output pattern

/-- Pointwise inhabitation of recursive and ordinary native arguments. -/
inductive SatisfiesAll {Index : Type uIndex} (span : ReductionSpan Pattern)
    (signature : Signature Index) :
    List (Argument Index) → List Pattern → Prop where
  | nil : SatisfiesAll span signature [] []
  | native {nativeType arguments child children}
      (head : satisfiesOver span nativeType child)
      (tail : SatisfiesAll span signature arguments children) :
      SatisfiesAll span signature
        (.native nativeType :: arguments) (child :: children)
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
  | .native nativeType :: arguments, child :: children =>
      satisfiesOver span nativeType child ∧
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
      pattern = .apply (signature.describe branch).constructor children ∧
      layerAll span predicate (signature.describe branch).arguments children

theorem SatisfiesAll.toLayerAll {Index : Type uIndex}
    {span : ReductionSpan Pattern} {signature : Signature Index}
    {arguments : List (Argument Index)} {children : List Pattern}
    (evidence : SatisfiesAll span signature arguments children) :
    layerAll span (Satisfies span signature) arguments children := by
  cases evidence with
  | nil => trivial
  | native head tail =>
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
          | native nativeType =>
              exact .native evidence.1 (inductionHypothesis evidence.2)
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
    | intro branch children shape childrenEvidence =>
        exact ⟨branch, rfl, children, shape,
          childrenEvidence.toLayerAll⟩
  · rintro ⟨branch, output, children, shape, childrenEvidence⟩
    subst output
    exact .intro branch children shape
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
  | intro branch children shape childrenEvidence =>
      apply closed
      exact ⟨branch, rfl, children, shape,
        childrenEvidence.least closed⟩

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
  | native head tail => exact ⟨head, tail.least closed⟩
  | recur head tail => exact ⟨head.least closed, tail.least closed⟩

end


end Mettapedia.OSLF.Framework.RecursiveNativeType
