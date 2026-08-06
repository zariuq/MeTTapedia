import Mettapedia.GSLT.LanguageDef.CostWholeLanguageDeterminism
import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment
import Mettapedia.GSLT.LanguageDef.CostStaticRootInversion
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# One structural layer of hereditary Cost alignment

Canonical equality is recursive, but a checked Cost tree may stop at a static
region before the raw syntax does.  This file handles exactly the complementary
case: when both retained roots are structural and reflective canonicalization
has proved their raw roots aligned, child alignments assemble into a parent
alignment.

The recursive child relation is supplied by the caller.  Static roots are
therefore never opened here, and no planner choice or normalization theorem is
assumed by this structural layer.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Constructor view of a retained tree known not to be static.  Keeping the
view Type-valued avoids attempting dependent elimination of a static node
whose indexed raw pattern is only propositionally known. -/
inductive CostRegionTree.StructuralRootView
    (source : CIGSLT) (targetFree : FreeTypeContext) :
    {available outer : List TypeExpr} → {pattern : Pattern} →
      {type : TypeExpr} →
      (tree : CostRegionTree source targetFree available outer pattern type) →
      Type where
  | bvar {available outer : List TypeExpr} {index : Nat} {type : TypeExpr}
      (lookup : (available ++ outer)[index]? = some type) :
      StructuralRootView source targetFree (CostRegionTree.bvar lookup)
  | fvar {available outer : List TypeExpr} {name : String} {type : TypeExpr}
      (lookup : targetFree name = some type) :
      StructuralRootView source targetFree (CostRegionTree.fvar lookup)
  | neutralApplicationOrdinary
      {available outer : List TypeExpr} {rule : GrammarRule}
      {arguments : List Pattern}
      (membership : rule ∈ source.costWholeLanguage.terms)
      (notBareCollection : ¬ UsesBareCollection rule)
      (constructor : source.DeclaredCostConstructor)
      (materializes :
        source.materializeDeclaredCostConstructor constructor = rule)
      (neutral : source.declaredCostConstructorRole constructor =
          .interactionPrincipal ∨
        ∃ kind, source.declaredCostConstructorRole constructor =
          .apparatus kind)
      (ordinary : ReflectiveContextSupport.isQuoteConstructor
        source.costWholeLanguage rule.label = false)
      (children : CostRegionArgumentTrees source targetFree available outer
        arguments rule.params) :
      StructuralRootView source targetFree
        (CostRegionTree.neutralApplicationOrdinary membership
          notBareCollection constructor materializes neutral ordinary children)
  | neutralApplicationQuote
      {available outer : List TypeExpr} {rule : GrammarRule}
      {arguments : List Pattern}
      (membership : rule ∈ source.costWholeLanguage.terms)
      (notBareCollection : ¬ UsesBareCollection rule)
      (constructor : source.DeclaredCostConstructor)
      (materializes :
        source.materializeDeclaredCostConstructor constructor = rule)
      (neutral : source.declaredCostConstructorRole constructor =
          .interactionPrincipal ∨
        ∃ kind, source.declaredCostConstructorRole constructor =
          .apparatus kind)
      (quoted : ReflectiveContextSupport.isQuoteConstructor
        source.costWholeLanguage rule.label = true)
      (children : CostRegionArgumentTrees source targetFree []
        (available ++ outer) arguments rule.params) :
      StructuralRootView source targetFree
        (CostRegionTree.neutralApplicationQuote membership notBareCollection
          constructor materializes neutral quoted children)
  | lambda {available outer : List TypeExpr} {binder : Option String}
      {body : Pattern} {domain codomain : TypeExpr}
      (bodyTree : CostRegionTree source targetFree (domain :: available)
        outer body codomain) :
      StructuralRootView source targetFree
        (CostRegionTree.lambda (binder := binder) bodyTree)
  | multiLambda {available outer : List TypeExpr} {arity : Nat}
      {binders : List String} {body : Pattern} {domain codomain : TypeExpr}
      (bodyTree : CostRegionTree source targetFree
        (List.replicate arity domain ++ available) outer body codomain) :
      StructuralRootView source targetFree
        (CostRegionTree.multiLambda (arity := arity) (binders := binders)
          bodyTree)
  | subst {available outer : List TypeExpr} {body replacement : Pattern}
      {domain codomain : TypeExpr}
      (bodyTree : CostRegionTree source targetFree (domain :: available)
        outer body codomain)
      (replacementTree : CostRegionTree source targetFree available outer
        replacement domain) :
      StructuralRootView source targetFree
        (CostRegionTree.subst bodyTree replacementTree)
  | collection {available outer : List TypeExpr}
      {collectionType : CollType} {elements : List Pattern}
      {rest : Option String} {elementType : TypeExpr}
      (children : CostRegionElementTrees source targetFree available outer
        elements elementType) :
      StructuralRootView source targetFree
        (CostRegionTree.collection (collectionType := collectionType)
          (rest := rest) children)

/-- Every tree whose retained root observation is false has an exact
structural constructor view. -/
def CostRegionTree.structuralRootView
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (structural : tree.rootIsStatic = false) :
    tree.StructuralRootView := by
  cases tree with
  | bvar lookup => exact .bvar lookup
  | fvar lookup =>
      exact .fvar (available := available) (outer := outer) lookup
  | static node children =>
      simp [CostRegionTree.rootIsStatic] at structural
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      exact .neutralApplicationOrdinary membership notBare constructor
        materializes neutral ordinary children
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      exact .neutralApplicationQuote membership notBare constructor
        materializes neutral quoted children
  | lambda body => exact .lambda body
  | multiLambda body => exact .multiLambda body
  | subst body replacement => exact .subst body replacement
  | collection children => exact .collection children

/-- Assemble an argument-spine alignment from childwise canonical equality and
one caller-supplied nonempty alignment for each child pair.  The result is
`Nonempty` because reflective root alignment is proposition-valued, while the
hereditary alignment itself retains proof-relevant trees. -/
theorem CostRegionArgumentTreesNormalizationAlignment.nonempty_ofCanonicalForall₂
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      (left : CostRegionTree source targetFree available outer leftPattern type) →
      (right : CostRegionTree source targetFree available outer rightPattern type) →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right)) :
    ∀ {available outer : List TypeExpr}
      {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam}
      (left : CostRegionArgumentTrees source targetFree available outer
        leftArguments parameters)
      (right : CostRegionArgumentTrees source targetFree available outer
        rightArguments parameters),
      List.Forall₂
        (fun leftPattern rightPattern =>
          canonicalize declaration leftPattern =
            canonicalize declaration rightPattern)
        leftArguments rightArguments →
      Nonempty (CostRegionArgumentTreesNormalizationAlignment source kernel
        targetFree left right) := by
  intro available outer leftArguments rightArguments parameters left
    right canonical
  induction leftArguments generalizing rightArguments parameters with
  | nil =>
      cases canonical
      cases left
      cases right
      exact ⟨.nil⟩
  | cons argument arguments inductionHypothesis =>
      cases canonical with
      | cons headCanonical tailCanonical =>
          cases left with
          | cons leftRepresentation leftParameterType leftHead leftTail =>
              cases right with
              | cons rightRepresentation rightParameterType rightHead rightTail =>
                  have expectedEq := Option.some.inj
                    (leftParameterType.symm.trans rightParameterType)
                  cases expectedEq
                  obtain ⟨headAlignment⟩ :=
                    alignChild leftHead rightHead headCanonical
                  obtain ⟨tailAlignment⟩ :=
                    inductionHypothesis leftTail rightTail tailCanonical
                  exact ⟨.cons leftRepresentation rightRepresentation
                    leftParameterType leftHead rightHead leftTail rightTail
                    headAlignment tailAlignment⟩

/-- Homogeneous-collection companion to
`CostRegionArgumentTreesNormalizationAlignment.nonempty_ofCanonicalForall₂`. -/
theorem CostRegionElementTreesNormalizationAlignment.nonempty_ofCanonicalForall₂
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      (left : CostRegionTree source targetFree available outer leftPattern type) →
      (right : CostRegionTree source targetFree available outer rightPattern type) →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right)) :
    ∀ {available outer : List TypeExpr}
      {leftElements rightElements : List Pattern} {elementType : TypeExpr}
      (left : CostRegionElementTrees source targetFree available outer
        leftElements elementType)
      (right : CostRegionElementTrees source targetFree available outer
        rightElements elementType),
      List.Forall₂
        (fun leftPattern rightPattern =>
          canonicalize declaration leftPattern =
            canonicalize declaration rightPattern)
        leftElements rightElements →
      Nonempty (CostRegionElementTreesNormalizationAlignment source kernel
        targetFree left right) := by
  intro available outer leftElements rightElements elementType left right
    canonical
  induction leftElements generalizing rightElements with
  | nil =>
      cases canonical
      cases left
      cases right
      exact ⟨.nil _ _ _⟩
  | cons leftElement leftElements inductionHypothesis =>
      cases canonical with
      | cons headCanonical tailCanonical =>
          cases left with
          | cons leftHead leftTail =>
              cases right with
              | cons rightHead rightTail =>
                  obtain ⟨headAlignment⟩ :=
                    alignChild leftHead rightHead headCanonical
                  obtain ⟨tailAlignment⟩ :=
                    inductionHypothesis leftTail rightTail tailCanonical
                  exact ⟨.cons leftHead rightHead leftTail rightTail
                    headAlignment tailAlignment⟩

/-- Assemble an ordinary neutral frame once typed inversion has selected one
shared generated rule.  This is the application arm used by the universal
classifier; rule sharing is established before this constructor is called,
so no dependent rule cast enters the alignment. -/
theorem CostRegionTreeNormalizationAlignment.nonempty_neutralOrdinary_ofCanonicalForall₂
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      (left : CostRegionTree source targetFree available outer leftPattern type) →
      (right : CostRegionTree source targetFree available outer rightPattern type) →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right))
    {available outer : List TypeExpr} {rule : GrammarRule}
    {leftArguments rightArguments : List Pattern}
    (membership : rule ∈ source.costWholeLanguage.terms)
    (notBareCollection : ¬ UsesBareCollection rule)
    (constructor : source.DeclaredCostConstructor)
    (materializes : source.materializeDeclaredCostConstructor constructor = rule)
    (neutral : source.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, source.declaredCostConstructorRole constructor = .apparatus kind)
    (ordinary : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeLanguage rule.label = false)
    (leftChildren : CostRegionArgumentTrees source targetFree available outer
      leftArguments rule.params)
    (rightChildren : CostRegionArgumentTrees source targetFree available outer
      rightArguments rule.params)
    (canonical : List.Forall₂
      (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
      leftArguments rightArguments) :
    Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
      (.neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary leftChildren)
      (.neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary rightChildren)) := by
  obtain ⟨arguments⟩ :=
    CostRegionArgumentTreesNormalizationAlignment.nonempty_ofCanonicalForall₂
      declaration alignChild leftChildren rightChildren canonical
  exact ⟨.neutralApplicationOrdinary membership notBareCollection constructor
    materializes neutral ordinary leftChildren rightChildren arguments⟩

/-- Quote-frame companion to
`nonempty_neutralOrdinary_ofCanonicalForall₂`; the reset binder fibre is
shared explicitly by both endpoint spines. -/
theorem CostRegionTreeNormalizationAlignment.nonempty_neutralQuote_ofCanonicalForall₂
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      (left : CostRegionTree source targetFree available outer leftPattern type) →
      (right : CostRegionTree source targetFree available outer rightPattern type) →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right))
    {available outer : List TypeExpr} {rule : GrammarRule}
    {leftArguments rightArguments : List Pattern}
    (membership : rule ∈ source.costWholeLanguage.terms)
    (notBareCollection : ¬ UsesBareCollection rule)
    (constructor : source.DeclaredCostConstructor)
    (materializes : source.materializeDeclaredCostConstructor constructor = rule)
    (neutral : source.declaredCostConstructorRole constructor =
        .interactionPrincipal ∨
      ∃ kind, source.declaredCostConstructorRole constructor = .apparatus kind)
    (quoted : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeLanguage rule.label = true)
    (leftChildren : CostRegionArgumentTrees source targetFree []
      (available ++ outer) leftArguments rule.params)
    (rightChildren : CostRegionArgumentTrees source targetFree []
      (available ++ outer) rightArguments rule.params)
    (canonical : List.Forall₂
      (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
      leftArguments rightArguments) :
    Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
      (.neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted leftChildren)
      (.neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted rightChildren)) := by
  obtain ⟨arguments⟩ :=
    CostRegionArgumentTreesNormalizationAlignment.nonempty_ofCanonicalForall₂
      declaration alignChild leftChildren rightChildren canonical
  exact ⟨.neutralApplicationQuote membership notBareCollection constructor
    materializes neutral quoted leftChildren rightChildren arguments⟩

/-- Assemble a homogeneous structural collection after typed inversion has
fixed its one shared element type. -/
theorem CostRegionTreeNormalizationAlignment.nonempty_collection_ofCanonicalForall₂
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext}
    (declaration : ReflectivePresentationDecl)
    (alignChild : ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      (left : CostRegionTree source targetFree available outer leftPattern type) →
      (right : CostRegionTree source targetFree available outer rightPattern type) →
      canonicalize declaration leftPattern = canonicalize declaration rightPattern →
      Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
        left right))
    {available outer : List TypeExpr} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    {elementType : TypeExpr}
    (leftChildren : CostRegionElementTrees source targetFree available outer
      leftElements elementType)
    (rightChildren : CostRegionElementTrees source targetFree available outer
      rightElements elementType)
    (canonical : List.Forall₂
      (fun leftPattern rightPattern =>
        canonicalize declaration leftPattern =
          canonicalize declaration rightPattern)
      leftElements rightElements) :
    Nonempty (CostRegionTreeNormalizationAlignment source kernel targetFree
      (.collection (collectionType := collectionType) (rest := rest)
        leftChildren)
      (.collection (collectionType := collectionType) (rest := rest)
        rightChildren)) := by
  obtain ⟨elements⟩ :=
    CostRegionElementTreesNormalizationAlignment.nonempty_ofCanonicalForall₂
      declaration alignChild leftChildren rightChildren canonical
  exact ⟨.collection leftChildren rightChildren elements⟩

end Mettapedia.GSLT.LanguageDef
