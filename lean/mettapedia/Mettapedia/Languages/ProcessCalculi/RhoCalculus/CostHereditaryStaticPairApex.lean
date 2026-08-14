import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm
import Mettapedia.GSLT.LanguageDef.CostRestorationCut
import Mettapedia.GSLT.LanguageDef.CostStaticHereditaryTyping
import Mettapedia.GSLT.LanguageDef.CostStaticRootView
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostEquationEndpointShape
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticRootClassification
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnostic

/-!
# Typed common-restoration apex for rho Cost

The generic reflective root dichotomy deliberately admits untyped collapsing
pairs.  Rho's generated typing rules remove the bad cases: Quote/Drop exposes
the exact generated name fibre, while the only base-typed bare collection is
the generated parallel constructor.  This module combines those typed facts
with the common-restoration relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan

namespace RhoCollapsingLeafExposure

/-- A collapsing exposure on the left endpoint supplies exactly the paired
elaboration required by static-pair closure.  The static-root view transports
the semantic bridge through the compiler's dependent indices; no bridge for a
preselected structural tree is assumed. -/
noncomputable def toLeftPairElaboration
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (leftView : left.StaticRootView color)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (exposure : RhoCollapsingLeafExposure leftView.node leftView.children
      right) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type :=
  { leftTree := left
    rightTree := right
    alignment :=
      (leftView.rootBridge_reindex_left exposure.toRootBridge).toTreeAlignment }

/-- Right-oriented companion of `toLeftPairElaboration`.  Symmetry reverses
the complete atom-or-rigid certificate before the static-root view restores
the right endpoint's dependent indices. -/
noncomputable def toRightPairElaboration
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (exposure : RhoCollapsingLeafExposure rightView.node rightView.children
      left) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type :=
  { leftTree := left
    rightTree := right
    alignment :=
      (rightView.rootBridge_reindex_right
        exposure.toRootBridge.symm).toTreeAlignment }

end RhoCollapsingLeafExposure

namespace RhoCommonRestorationApex

/-- The atomized generated target frame transported into a chosen common
semantic-key cospan.  The subtype retains the exact target support used by
restoration, so recursive rho inversion can consume ordinary typing and
object evidence without rebuilding either one. -/
noncomputable def commonReifiedTargetFrame
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    { commonTerm : ReflectiveWellSorted.OpenTerm
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        cospan.commonTargetFreeContext node.targetBound
        (color.mapLangSort rhoCIGSLT node.sourceSort) //
      commonTerm.2.1.1.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        node.targetBound } :=
  environment.reifyTargetTermToCommon cospan leg commutes
    (node.reifiedTargetFrame environment)
    (node.reifiedTargetFrame_supportSafe environment)

@[simp]
theorem commonReifiedTargetFrame_pattern
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    (commonReifiedTargetFrame node environment cospan leg commutes).1.1 =
      cospan.reifyWith environment.lookupAtom? leg
        (node.reifyTargetFrame environment) := by
  rfl

/-- The generated target frame retains the exact selected-colour hereditary
constructor witness, including the declaration that types a bare collection.
The explicit fibre equation is the only fact required of the semantic-atom
quotient; canonical inventories discharge it below. -/
theorem reifiedTargetFrame_hereditaryTyped
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (typeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType) :
    HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      environment.atomFreeContext node.targetBound
      (node.reifiedTargetFrame environment).1
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
  have mapped :=
    (node.reifiedSourceFrame_supported environment).mapCostStaticHereditary
      rhoCIGSLT color
  have mappedInTargetContext :
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        environment.atomFreeContext
        (node.sourceBound.map
          (mapTypeExpr (color.symbols rhoCIGSLT)))
        (mapPattern (color.symbols rhoCIGSLT)
          (node.reifiedSourceFrame environment).1)
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
    rw [environment.sourceAtomFreeContext_map_eq_atomFreeContext typeMap]
      at mapped
    simpa only [mapTypeExpr, CostStaticColor.mapLangSort_name] using mapped
  have thickened := mappedInTargetContext.thickenAmbientBVars
    (inner := []) node.thinning
  simpa only [List.nil_append, List.length_nil, node.reifiedTargetFrame_pattern,
    node.reifyTargetFrame_eq_map_reifiedSourceFrame] using thickened

/-- Moving an actual target frame into a common semantic namespace preserves
the proof-relevant selected-colour constructor invariant, not merely the raw
constructor alphabet. -/
theorem commonReifiedTargetFrame_hereditaryTyped
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    (typeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType) :
    HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext node.targetBound
      (commonReifiedTargetFrame node environment cospan leg commutes).1.1
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
  have renamed :=
    (reifiedTargetFrame_hereditaryTyped node environment typeMap).renameFVars
      (environment.targetReificationRenaming cospan leg commutes)
  change HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext node.targetBound
      (Pattern.renameFVars
        (environment.sourceReificationName cospan leg)
        (node.reifiedTargetFrame environment).1)
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) at renamed
  rw [environment.renameFVars_sourceReificationName_eq_reifyWith
    cospan leg (node.reifiedTargetFrame environment).1] at renamed
  simpa only [commonReifiedTargetFrame_pattern,
    node.reifiedTargetFrame_pattern] using renamed

/-- Transport into a common semantic-key namespace preserves the decisive
single-colour constructor fragment of an actual generated target frame.  This
is the invariant that excludes the mixed-colour Quote obstruction from the
compiler-produced hereditary rho terms. -/
theorem commonReifiedTargetFrame_constructorsWithinColor
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (commutes : forall slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key) :
    ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (commonReifiedTargetFrame node environment cospan leg commutes).1.1 := by
  apply environment.reifyTargetTermToCommon_constructorsWithin cospan leg
    commutes (node.reifiedTargetFrame environment)
    (node.reifiedTargetFrame_supportSafe environment)
  exact node.reifiedTargetFrame_constructorsWithinColor environment

/-- Inside one selected static constructor fragment, every language-level rho
Quote is the Quote of that same generated declaration.  The opposite-colour
Quote is a genuine language Quote, but its reserved prefix makes it
unrepresentable in this fragment. -/
theorem quote_eq_selected_of_decodesColor
    {color : CostStaticColor} {constructor : String}
    (supported : exists sourceConstructor,
      decodeCostStaticConstructor color constructor = some sourceConstructor)
    (quoted : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile constructor = true) :
    constructor =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor := by
  obtain ⟨sourceConstructor, decoded⟩ := supported
  have tagged := (decodeCostStaticConstructor_eq_some_iff color constructor
    sourceConstructor).mp decoded
  rcases rho_isQuoteConstructor_cases quoted with baseQuote | wrappedQuote
  · cases color with
    | base =>
        simpa [costStaticReflectivePresentationDecl_eq_map,
          ReflectionExtension.mapReflectivePresentation,
          CostStaticColor.reflectiveSymbols_constructor,
          CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
          costBaseConstructorName, rhoReflectivePresentation]
          using baseQuote
    | wrapped =>
        subst constructor
        simp only [CostStaticColor.constructorTag] at tagged
        exact (costBaseConstructorName_ne_wrapped "NQuote" sourceConstructor
          tagged).elim
  · cases color with
    | base =>
        subst constructor
        simp only [CostStaticColor.constructorTag] at tagged
        exact (costBaseConstructorName_ne_wrapped sourceConstructor "NQuote"
          tagged.symm).elim
    | wrapped =>
        simpa [costStaticReflectivePresentationDecl_eq_map,
          ReflectionExtension.mapReflectivePresentation,
          CostStaticColor.reflectiveSymbols_constructor,
          CostStaticColor.symbols_constructor, CostStaticColor.constructorTag,
          costWrappedConstructorName, rhoReflectivePresentation]
          using wrappedQuote

/-- A constructor fragment can contain the selected declaration's quote only
when the fragment and declaration have the same generated colour.  This is
the colour-indexed exclusion used before the recursive Quote/Drop arm: a
foreign quote remains an ordinary aligned application and cannot be mistaken
for a selected collapse. -/
theorem supportColor_eq_of_declarationQuote_supported
    (supportColor declarationColor : CostStaticColor)
    (supported : exists sourceConstructor,
      decodeCostStaticConstructor supportColor
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor =
        some sourceConstructor) :
    supportColor = declarationColor := by
  cases supportColor <;> cases declarationColor
  · rfl
  · obtain ⟨sourceConstructor, decoded⟩ := supported
    have tagged := (decodeCostStaticConstructor_eq_some_iff .base _
      sourceConstructor).mp decoded
    simp only [CostStaticColor.constructorTag] at tagged
    exact (costBaseConstructorName_ne_wrapped sourceConstructor "NQuote"
      tagged.symm).elim
  · obtain ⟨sourceConstructor, decoded⟩ := supported
    have tagged := (decodeCostStaticConstructor_eq_some_iff .wrapped _
      sourceConstructor).mp decoded
    simp only [CostStaticColor.constructorTag] at tagged
    exact (costBaseConstructorName_ne_wrapped "NQuote" sourceConstructor
      tagged).elim
  · rfl

/-- Keyed canonicalization of a typed generated rho name is independent of
the ambient depth inside one static colour.

This is deliberately a theorem about the selected reflective name fibre,
not about arbitrary typed terms or arbitrary restoration.  Free and bound
names are syntactically rigid; every constructor returning the name sort is
a language-level quote; the constructor-fragment premise identifies that
quote with the selected colour's quote; and no collection can inhabit the
name fibre.  Hence every potentially depth-sensitive child is below a quote
reset. -/
theorem canonicalizeByAt_depth_independent_of_typedNameWithin
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key)
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    {resultType : TypeExpr}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound name resultType)
    (resultType_eq : resultType =
      .base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort)
    (object : isObjectPattern name = true)
    (supported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      name)
    (leftDepth rightDepth : Nat) :
    canonicalizeByAt key
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth name =
      canonicalizeByAt key
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth name := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  cases typed with
  | bvar lookup => rfl
  | fvar lookup => rfl
  | @constructor bound rule arguments membership notBare argumentsTyped =>
      have categoryEquality : rule.category = declaration.nameSort :=
        TypeExpr.base.inj resultType_eq
      have quoted :=
        CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
          declarationMembership rule membership categoryEquality
      have selected : rule.label = declaration.quoteConstructor :=
        quote_eq_selected_of_decodesColor supported.1 quoted.1
      simp [declaration, canonicalizeByAt, selected]
  | lambda bodyTyped => cases resultType_eq
  | multiLambda bodyTyped => cases resultType_eq
  | subst bodyTyped replacementTyped =>
      simp [isObjectPattern] at object
  | collection elementsTyped => cases resultType_eq
  | @collectionConstructor bound rule parameterName collectionType elements
      rest elementType membership parameterShape elementsTyped =>
      have categoryEquality : rule.category = declaration.nameSort :=
        TypeExpr.base.inj resultType_eq
      have typedName : HasType rhoCIGSLT.costWholeLanguage free bound
          (.collection collectionType elements rest)
          (.base declaration.nameSort) := by
        rw [← categoryEquality]
        exact HasType.collectionConstructor membership parameterShape
          elementsTyped
      exact (CostCanonicalLaws.rho_no_collection_at_reflectiveNameSort
        declaration declarationMembership typedName).elim

mutual
  private def parallelLeaves
      (declaration : ReflectivePresentationDecl) : Pattern → List Pattern
    | pattern@(.apply constructor arguments) =>
        if constructor = declaration.parallelUnitConstructor ∧ arguments = []
        then [] else [pattern]
    | pattern@(.collection collectionType elements rest) =>
        if collectionType = declaration.parallelCollection ∧ rest = none
        then parallelLeavesList declaration elements else [pattern]
    | pattern => [pattern]

  private def parallelLeavesList
      (declaration : ReflectivePresentationDecl) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        parallelLeaves declaration pattern ++
          parallelLeavesList declaration patterns
end

mutual
  /-- Every recursively flattened parallel leaf retains a concrete occurrence
  context in the unflattened source pattern.  The witness is positional: no
  equality search through sibling leaves is used. -/
  private theorem parallelLeaves_context
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern →
        ∃ context : OneHoleContext, pattern = context.fill leaf
    | .bvar index, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact ⟨.hole, rfl⟩
    | .fvar name, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact ⟨.hole, rfl⟩
    | pattern@(.apply constructor arguments), leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · simp at membership
        · have leafEq := List.mem_singleton.mp membership
          subst leaf
          exact ⟨.hole, rfl⟩
    | pattern@(.lambda binder body), leaf, membership => by
        have leafEq := List.mem_singleton.mp membership
        subst leaf
        exact ⟨.hole, rfl⟩
    | pattern@(.multiLambda arity binders body), leaf, membership => by
        have leafEq := List.mem_singleton.mp membership
        subst leaf
        exact ⟨.hole, rfl⟩
    | pattern@(.subst body replacement), leaf, membership => by
        have leafEq := List.mem_singleton.mp membership
        subst leaf
        exact ⟨.hole, rfl⟩
    | pattern@(.collection collectionType elements rest), leaf,
        membership => by
        simp only [parallelLeaves] at membership
        split at membership
        next selected =>
          rcases selected with ⟨collectionEq, restEq⟩
          subst collectionType
          subst rest
          obtain ⟨before, middle, after, context, elementsEq, middleEq⟩ :=
            parallelLeavesList_context declaration elements leaf membership
          refine ⟨.collection declaration.parallelCollection before context
            after none, ?_⟩
          simp [OneHoleContext.fill, elementsEq, middleEq]
        next notSelected =>
          have leafEq := List.mem_singleton.mp membership
          subst leaf
          exact ⟨.hole, rfl⟩

  /-- List-level positional companion of `parallelLeaves_context`.  The
  before/after split distinguishes repeated equal leaves by their recursive
  occurrence path. -/
  private theorem parallelLeavesList_context
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns →
        ∃ before middle after context,
          patterns = before ++ middle :: after ∧
            middle = (context : OneHoleContext).fill leaf
    | [], leaf, membership => by
        simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · obtain ⟨context, patternEq⟩ :=
            parallelLeaves_context declaration pattern leaf head
          exact ⟨[], pattern, patterns, context, by simp, patternEq⟩
        · obtain ⟨before, middle, after, context, patternsEq, middleEq⟩ :=
            parallelLeavesList_context declaration patterns leaf tail
          exact ⟨pattern :: before, middle, after, context,
            by simp [patternsEq], middleEq⟩
end

mutual
  private theorem parallelLeaves_size_le
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern → sizeOf leaf ≤ sizeOf pattern
    | .bvar index, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact Nat.le_refl _
    | .fvar name, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact Nat.le_refl _
    | .apply constructor arguments, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · simp at membership
        · exact Nat.le_of_eq (congrArg sizeOf
            (List.mem_singleton.mp membership))
    | .lambda binder body, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .multiLambda arity binders body, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .subst body replacement, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .collection collectionType elements rest, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · have smaller := parallelLeavesList_size_lt declaration elements leaf
            membership
          simp_wf
          omega
        · exact Nat.le_of_eq (congrArg sizeOf
            (List.mem_singleton.mp membership))

  private theorem parallelLeavesList_size_lt
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns → sizeOf leaf < sizeOf patterns
    | [], leaf, membership => by simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · have bounded := parallelLeaves_size_le declaration pattern leaf head
          simp_wf
          omega
        · have bounded := parallelLeavesList_size_lt declaration patterns leaf tail
          simp_wf
          omega
end

private theorem elementsHaveType_of_mem
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType language free bound patterns type)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    HasType language free bound pattern type := by
  induction patterns with
  | nil => cases membership
  | cons head tail inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact headTyped
      · exact inductionHypothesis tailTyped membership

private theorem isObjectPattern_of_mem
    {patterns : List Pattern} (objects : isObjectPatternList patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    isObjectPattern pattern = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail inductionHypothesis =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact objects.1
      · exact inductionHypothesis objects.2 membership

private theorem parallelLeavesList_append
    (declaration : ReflectivePresentationDecl) : ∀ left right,
    parallelLeavesList declaration (left ++ right) =
      parallelLeavesList declaration left ++
        parallelLeavesList declaration right
  | [], right => rfl
  | pattern :: patterns, right => by
      simp only [List.cons_append, parallelLeavesList]
      rw [parallelLeavesList_append declaration patterns right,
        List.append_assoc]

private theorem parallelLeaves_parallelUnit
    (declaration : ReflectivePresentationDecl) :
    parallelLeaves declaration
        (.apply declaration.parallelUnitConstructor []) = [] := by
  simp [parallelLeaves]

private theorem parallelLeaves_parallel
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    parallelLeaves declaration
        (.collection declaration.parallelCollection patterns none) =
      parallelLeavesList declaration patterns := by
  simp [parallelLeaves]

private theorem parallelLeaves_of_not_unit_or_parallel
    (declaration : ReflectivePresentationDecl) (pattern : Pattern)
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ patterns,
      pattern ≠ .collection declaration.parallelCollection patterns none) :
    parallelLeaves declaration pattern = [pattern] := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments =>
      simp only [parallelLeaves]
      split
      · rename_i selected
        exact (notUnit (by rcases selected with ⟨rfl, rfl⟩; rfl)).elim
      · rfl
  | lambda binder body => rfl
  | multiLambda arity binders body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest =>
      simp only [parallelLeaves]
      split
      · rename_i selected
        exact (notParallel elements (by
          rcases selected with ⟨rfl, rfl⟩
          rfl)).elim
      · rfl

mutual
  private theorem parallelLeaves_noUnit
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern →
        leaf ≠ .apply declaration.parallelUnitConstructor []
    | .bvar index, leaf, membership => by
        intro equality
        subst leaf
        simp [parallelLeaves] at membership
    | .fvar name, leaf, membership => by
        intro equality
        subst leaf
        simp [parallelLeaves] at membership
    | .apply constructor arguments, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · simp at membership
        · rename_i notSelected
          rw [List.mem_singleton] at membership
          intro equality
          have patternEquality := membership.symm.trans equality
          injection patternEquality with constructorEquality argumentsEquality
          exact notSelected ⟨constructorEquality, argumentsEquality⟩
    | .lambda binder body, leaf, membership => by
        intro equality
        subst leaf
        simp [parallelLeaves] at membership
    | .multiLambda arity binders body, leaf, membership => by
        intro equality
        subst leaf
        simp [parallelLeaves] at membership
    | .subst body replacement, leaf, membership => by
        intro equality
        subst leaf
        simp [parallelLeaves] at membership
    | .collection collectionType elements rest, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · exact parallelLeavesList_noUnit declaration elements leaf membership
        · intro equality
          subst leaf
          simp at membership

  private theorem parallelLeavesList_noUnit
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns →
        leaf ≠ .apply declaration.parallelUnitConstructor []
    | [], _, membership => by
        simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · exact parallelLeaves_noUnit declaration pattern leaf head
        · exact parallelLeavesList_noUnit declaration patterns leaf tail

  private theorem parallelLeaves_noParallel
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern → ∀ nested,
        leaf ≠ .collection declaration.parallelCollection nested none
    | .bvar index, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .fvar name, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .apply constructor arguments, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .lambda binder body, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .multiLambda arity binders body, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .subst body replacement, leaf, membership => by
        intro nested equality
        subst leaf
        simp [parallelLeaves] at membership
    | .collection collectionType elements rest, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · exact parallelLeavesList_noParallel declaration elements leaf membership
        · rename_i notSelected
          rw [List.mem_singleton] at membership
          intro nested equality
          have patternEquality := membership.symm.trans equality
          injection patternEquality with collectionEquality elementsEquality restEquality
          exact notSelected ⟨collectionEquality, restEquality⟩

  private theorem parallelLeavesList_noParallel
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns → ∀ nested,
        leaf ≠ .collection declaration.parallelCollection nested none
    | [], _, membership => by
        simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · exact parallelLeaves_noParallel declaration pattern leaf head
        · exact parallelLeavesList_noParallel declaration patterns leaf tail
end

/-- A constructor application inhabiting a generated rho process fibre cannot
use that fibre's selected Quote constructor, whose validated result is the
distinct reflective-name sort. -/
private theorem rhoProc_typed_apply_ne_quote
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {arguments : List Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply constructor arguments)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort)) :
    constructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  change HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply constructor arguments) (.base declaration.processSort) at typed
  change constructor ≠ declaration.quoteConstructor
  obtain ⟨rule, membership, labelEq, notBare, typeEq, argumentsTyped⟩ :=
    hasType_apply_inversion typed
  subst constructor
  have categoryEq : declaration.processSort = rule.category :=
    TypeExpr.base.inj typeEq
  intro selected
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      rhoCIGSLT.costWholeAdmittedReflection.2 declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      rhoCIGSLT.costWholeLanguage declaration declarationValid
  have quoteFiltered : witness.quote ∈
      rhoCIGSLT.costWholeLanguage.terms.filter
        (fun candidate => candidate.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership : witness.quote ∈
      rhoCIGSLT.costWholeLanguage.terms :=
    (List.mem_filter.mp quoteFiltered).1
  have sameLabel : witness.quote.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2).trans selected.symm
  have sameRule : witness.quote = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate)
      quoteMembership membership sameLabel
  exact witness.sortsDistinct (by
    calc
      declaration.processSort = rule.category := categoryEq
      _ = witness.quote.category :=
        congrArg GrammarRule.category sameRule.symm
      _ = declaration.nameSort := witness.quoteCategory)

/-- A collapsing root in a generated rho process fibre is necessarily the
bare parallel representation; the selected Quote alternative returns the
distinct name fibre. -/
private theorem rhoProc_collapsingRoot_is_parallel
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) pattern) :
    ∃ elements, pattern = .collection
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelCollection elements none := by
  rcases collapsing with quoted | parallel
  · obtain ⟨arguments, shape⟩ := quoted
    subst pattern
    exact (rhoProc_typed_apply_ne_quote color typed rfl).elim
  · exact parallel

/-- Typing inversion for one selected generated rho Drop without requiring a
surrounding Quote shell. -/
private theorem rhoCostStatic_drop_inner_hasType
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [inner]) type) :
    HasType rhoCIGSLT.costWholeLanguage free bound inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  obtain ⟨argument, argumentTyped, argumentsShape, _argumentSafe⟩ :=
    typed.selectedOrdinaryDropArgument
      rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      (by simpa [declaration] using
        CostCanonicalLaws.rho_costStatic_drop_isOrdinary color)
      (typed.reflectiveSupportSafeAt_empty bound)
  have argumentEquality : inner = argument := by
    simpa [declaration] using (List.cons.inj argumentsShape).1
  subst argument
  exact argumentTyped

/-- Typing inversion for one selected generated rho Quote. -/
private theorem rhoCostStatic_quote_inner_hasType
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [inner]) type) :
    HasType rhoCIGSLT.costWholeLanguage free bound inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  obtain ⟨argument, argumentTyped, argumentsShape, _argumentSafe⟩ :=
    typed.selectedQuoteArgument rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      (typed.reflectiveSupportSafeAt_empty bound)
  have argumentEquality : inner = argument := by
    simpa [declaration] using (List.cons.inj argumentsShape).1
  subst argument
  exact argumentTyped

/-- Proof-relevant inversion of the selected generated rho Quote.  Unlike
ordinary typing inversion, this retains the hereditary declaration fragment
for the quoted process. -/
private theorem rhoCostStatic_quote_inner_hasTypeWithConstructors
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {inner : Pattern}
    {type : TypeExpr}
    (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [inner]) type) :
    HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨rule, _allowedRule, membership, selected, _notBare, _typeEq,
      argumentsTyped⟩ :=
    hasTypeWithConstructors_apply_inversion typed
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      rhoCIGSLT.costWholeAdmittedReflection.2 declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      rhoCIGSLT.costWholeLanguage declaration declarationValid
  have quoteFiltered : witness.quote ∈
      rhoCIGSLT.costWholeLanguage.terms.filter
        (fun candidate => candidate.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership : witness.quote ∈ rhoCIGSLT.costWholeLanguage.terms :=
    (List.mem_filter.mp quoteFiltered).1
  have sameLabel : witness.quote.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2).trans selected
  have sameRule : witness.quote = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate)
      quoteMembership membership sameLabel
  have parameterShape : rule.params =
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    rw [← sameRule, witness.quoteParameters]
  have exactTyped : ArgumentsHaveTypesWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound [inner]
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    simpa only [parameterShape] using argumentsTyped
  cases exactTyped with
  | @cons _ _ _ parameter parameters expected representation parameterType
      argumentTyped tailTyped =>
      cases tailTyped
      have expectedEq : expected = .base declaration.processSort := by
        simpa [parameterType?] using parameterType.symm
      subst expected
      exact argumentTyped

/-- Invert an arbitrary selected Quote application while retaining both its
exact unary spine and the hereditary typing of the process payload. -/
private theorem rhoCostStatic_quote_shapeWithConstructors
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor arguments) type) :
    ∃ inner,
      arguments = [inner] ∧
      type = .base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort ∧
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound inner
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨rule, _allowedRule, membership, selected, _notBare, typeEq,
      argumentsTyped⟩ :=
    hasTypeWithConstructors_apply_inversion typed
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      rhoCIGSLT.costWholeAdmittedReflection.2 declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      rhoCIGSLT.costWholeLanguage declaration declarationValid
  have quoteFiltered : witness.quote ∈
      rhoCIGSLT.costWholeLanguage.terms.filter
        (fun candidate => candidate.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership : witness.quote ∈ rhoCIGSLT.costWholeLanguage.terms :=
    (List.mem_filter.mp quoteFiltered).1
  have sameLabel : witness.quote.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2).trans selected
  have sameRule : witness.quote = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate)
      quoteMembership membership sameLabel
  have parameterShape : rule.params =
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    rw [← sameRule, witness.quoteParameters]
  have exactTyped : ArgumentsHaveTypesWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound arguments
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    simpa only [parameterShape] using argumentsTyped
  cases exactTyped with
  | @cons _ argument tail parameter parameters expected representation
      parameterType argumentTyped tailTyped =>
      cases tailTyped
      have expectedEq : expected = .base declaration.processSort := by
        simpa [parameterType?] using parameterType.symm
      subst expected
      have resultCategory : rule.category = declaration.nameSort := by
        calc
          rule.category = witness.quote.category :=
            congrArg GrammarRule.category sameRule.symm
          _ = declaration.nameSort := witness.quoteCategory
      refine ⟨argument, rfl, ?_, argumentTyped⟩
      exact typeEq.trans (congrArg TypeExpr.base resultCategory)

/-- Proof-relevant inversion of the selected generated rho Drop. -/
private theorem rhoCostStatic_drop_inner_hasTypeWithConstructors
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {inner : Pattern}
    {type : TypeExpr}
    (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [inner]) type) :
    HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨rule, _allowedRule, membership, selected, _notBare, _typeEq,
      argumentsTyped⟩ :=
    hasTypeWithConstructors_apply_inversion typed
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      rhoCIGSLT.costWholeAdmittedReflection.2 declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      rhoCIGSLT.costWholeLanguage declaration declarationValid
  have dropFiltered : witness.drop ∈
      rhoCIGSLT.costWholeLanguage.terms.filter
        (fun candidate => candidate.label == declaration.dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have dropMembership : witness.drop ∈ rhoCIGSLT.costWholeLanguage.terms :=
    (List.mem_filter.mp dropFiltered).1
  have sameLabel : witness.drop.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2).trans selected
  have sameRule : witness.drop = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeLanguage_validate)
      dropMembership membership sameLabel
  have parameterShape : rule.params =
      [.simple witness.dropParameter (.base declaration.nameSort)] := by
    rw [← sameRule, witness.dropParameters]
  have exactTyped : ArgumentsHaveTypesWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound [inner]
      [.simple witness.dropParameter (.base declaration.nameSort)] := by
    simpa only [parameterShape] using argumentsTyped
  cases exactTyped with
  | @cons _ _ _ parameter parameters expected representation parameterType
      argumentTyped tailTyped =>
      cases tailTyped
      have expectedEq : expected = .base declaration.nameSort := by
        simpa [parameterType?] using parameterType.symm
      subst expected
      exact argumentTyped

/-- The selected generated rho Quote and Drop labels are distinct by the
validated reflective presentation, uniformly in the Cost colour. -/
private theorem rhoCostStatic_quote_ne_drop (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).dropConstructor := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  apply quoteConstructor_ne_dropConstructor_of_validate
    rhoCIGSLT.costWholeLanguage declaration
  apply rhoCIGSLT.costStaticReflectivePresentation_validate declaration
  simpa [declaration] using
    costStaticReflectivePresentationDecl_mem rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
      (by
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile])

/-- The selected Quote label of either generated rho Cost colour is marked as
a quote boundary by the generated reflection profile. -/
private theorem rhoCostStatic_quote_isQuote (color : CostStaticColor) :
    ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor = true := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have membership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  change ReflectiveContextSupport.isQuoteConstructor
    rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor = true
  simp only [ReflectiveContextSupport.isQuoteConstructor, List.any_eq_true]
  exact ⟨declaration, membership, by simp⟩

/-- If ordinary canonicalization of a term has no Drop root, keyed
canonicalization cannot invent one.  Re-canonicalizing the keyed result
forgets only its parallel order, while Drop is an ordinary rigid head. -/
private theorem canonicalizeByAt_not_drop_of_canonicalize_not_drop
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {pattern : Pattern}
    (notDrop : ∀ name, canonicalize declaration pattern ≠
      .apply declaration.dropConstructor [name])
    (depth : Nat) :
    ∀ name, canonicalizeByAt key declaration depth pattern ≠
      .apply declaration.dropConstructor [name] := by
  intro name keyedDrop
  have recanonicalized := congrArg (canonicalize declaration) keyedDrop
  rw [canonicalize_canonicalizeByAt_unconditional,
    canonicalize_apply_of_ne_quote declaration quoteNeDrop.symm] at recanonicalized
  exact notDrop (canonicalize declaration name) recanonicalized

/-- A selected Quote survives the finishing phase exactly when its already
normalized child is not a selected Drop. -/
private theorem finishNormalizeReflectiveApply_quote_of_not_drop
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (notDrop : ∀ name, pattern ≠
      .apply declaration.dropConstructor [name]) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor [pattern] =
      .apply declaration.quoteConstructor [pattern] := by
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
  cases pattern with
  | apply constructor arguments =>
      cases arguments with
      | nil => rfl
      | cons argument tail =>
          cases tail with
          | nil =>
              by_cases selected : constructor = declaration.dropConstructor
              · subst constructor
                exact (notDrop argument rfl).elim
              · simp [selected]
          | cons second rest => rfl
  | _ => rfl

/-- If one selected Quote survives ordinary canonicalization, any
hereditarily typed selected-colour name with the same canonical form is
itself a selected Quote.  Its payload may still expose a Drop; that case is
handled separately by the asymmetric Quote/Drop terminal. -/
private theorem rhoCostStatic_name_eq_quote_of_canonical_quote_nonDrop
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {leftInner right : Pattern} {rightType : TypeExpr}
    (rightTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound right rightType)
    (rightType_eq : rightType =
      .base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort)
    (rightObject : isObjectPattern right = true)
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      right)
    (leftNotDrop : forall name,
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftInner ≠
        .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [name])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [leftInner]) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) right) :
    exists rightInner,
      right = .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [rightInner] := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have leftOuterForm : canonicalize declaration
      (.apply declaration.quoteConstructor [leftInner]) =
        .apply declaration.quoteConstructor
          [canonicalize declaration leftInner] := by
    rw [canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    exact finishNormalizeReflectiveApply_quote_of_not_drop declaration
      leftNotDrop
  cases rightTyped with
  | bvar lookup =>
      rw [leftOuterForm] at canonical
      simp [declaration, canonicalize] at canonical
  | fvar lookup =>
      rw [leftOuterForm] at canonical
      simp [declaration, canonicalize] at canonical
  | @constructor bound rule arguments allowedRule membership notBare
      argumentsTyped =>
      have categoryEquality : rule.category = declaration.nameSort :=
        TypeExpr.base.inj rightType_eq
      have quoted :=
        CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
          declarationMembership rule membership categoryEquality
      have selected : rule.label = declaration.quoteConstructor :=
        quote_eq_selected_of_decodesColor rightSupported.1 quoted.1
      have typedQuote : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          free bound (.apply declaration.quoteConstructor arguments)
          (.base rule.category) := by
        simpa only [selected] using
          (HasTypeWithConstructors.constructor allowedRule membership notBare
            argumentsTyped)
      obtain ⟨rightInner, argumentsEq, _typeEq, _innerTyped⟩ :=
        rhoCostStatic_quote_shapeWithConstructors color typedQuote
      exact ⟨rightInner, by simp [declaration, selected, argumentsEq]⟩
  | lambda bodyTyped => cases rightType_eq
  | multiLambda bodyTyped => cases rightType_eq
  | subst bodyTyped replacementTyped =>
      simp [isObjectPattern] at rightObject
  | collection elementsTyped => cases rightType_eq
  | @collectionConstructor bound rule parameterName collectionType elements
      rest elementType allowedRule membership parameterShape elementsTyped =>
      have categoryEquality : rule.category = declaration.nameSort :=
        TypeExpr.base.inj rightType_eq
      have typedName : HasType rhoCIGSLT.costWholeLanguage free bound
          (.collection collectionType elements rest)
          (.base declaration.nameSort) := by
        rw [← categoryEquality]
        exact HasType.collectionConstructor membership parameterShape
          elementsTyped.toElementsHaveType
      exact (CostCanonicalLaws.rho_no_collection_at_reflectiveNameSort
        declaration declarationMembership typedName).elim

private theorem rhoProc_canonicalizeByAt_parallelLeaf
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (notUnit : pattern ≠
      .apply (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor [])
    (notParallel : ∀ elements,
      pattern ≠ .collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none)
    (depth : Nat) :
    parallelContents
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        [canonicalizeByAt key
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          depth pattern] =
      [canonicalizeByAt key
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        depth pattern] := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  change HasType rhoCIGSLT.costWholeLanguage free bound pattern
    (.base declaration.processSort) at typed
  change pattern ≠ .apply declaration.parallelUnitConstructor [] at notUnit
  change (∀ elements,
    pattern ≠ .collection declaration.parallelCollection elements none) at notParallel
  change parallelContents declaration
      [canonicalizeByAt key declaration depth pattern] =
    [canonicalizeByAt key declaration depth pattern]
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments =>
      obtain ⟨rule, membership, labelEq, notBare, typeEq, argumentsTyped⟩ :=
        hasType_apply_inversion typed
      subst constructor
      have notQuote : rule.label ≠ declaration.quoteConstructor := by
        simpa [declaration] using rhoProc_typed_apply_ne_quote color typed
      have notQuoteBool : (rule.label == declaration.quoteConstructor) = false :=
        beq_eq_false_iff_ne.mpr notQuote
      have normalizedNotUnit :
          Pattern.apply rule.label
              (canonicalizeListByAt key declaration depth arguments) ≠
            Pattern.apply declaration.parallelUnitConstructor [] := by
        intro equality
        injection equality with labelEquality argumentsEquality
        apply notUnit
        rw [labelEquality]
        have argumentsNil : arguments = [] := by
          simpa [canonicalizeListByAt_eq_map] using argumentsEquality
        rw [argumentsNil]
      have canonicalEq : canonicalizeByAt key declaration depth
          (.apply rule.label arguments) =
          .apply rule.label
            (canonicalizeListByAt key declaration depth arguments) := by
        simp [canonicalizeByAt, notQuote]
      rw [canonicalEq]
      simp [parallelContents, parallelSplice, normalizedNotUnit]
  | lambda binder body =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | multiLambda arity binders body =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | subst body replacement =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simp [canonicalizeByAt, parallelContents,
            parallelSplice]
      | none =>
          by_cases selected : collectionType = declaration.parallelCollection
          · subst collectionType
            exact (notParallel _ rfl).elim
          · have selectedBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr selected
            have canonicalEq : canonicalizeByAt key declaration depth
                (.collection collectionType elements none) =
                .collection collectionType
                  (canonicalizeListByAt key declaration depth elements) none := by
              simp [canonicalizeByAt, selected]
            rw [canonicalEq]
            simp [parallelContents, parallelSplice, selected]

/-- A typed process which is not syntactically a bare parallel collection
cannot acquire a bare-parallel root under keyed canonicalization.  The proof
uses the exposed keyed frontier, rather than a false global idempotence law:
quote-visible depth resets make the latter unavailable in general. -/
private theorem rhoProc_canonicalizeByAt_notParallel
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (notParallel : ∀ elements,
      pattern ≠ .collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none)
    (depth : Nat) :
    ∀ elements,
      canonicalizeByAt key
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          depth pattern ≠
        .collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection elements none := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  change HasType rhoCIGSLT.costWholeLanguage free bound pattern
    (.base declaration.processSort) at typed
  change (∀ elements,
    pattern ≠ .collection declaration.parallelCollection elements none) at notParallel
  change ∀ elements,
    canonicalizeByAt key declaration depth pattern ≠
      .collection declaration.parallelCollection elements none
  intro elements equality
  by_cases isUnit : pattern =
      .apply declaration.parallelUnitConstructor []
  · subst pattern
    have unitCanonical : canonicalizeByAt key declaration depth
        (.apply declaration.parallelUnitConstructor []) =
        .apply declaration.parallelUnitConstructor [] := by
      simp only [canonicalizeByAt, canonicalizeListByAt]
      unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
      by_cases same : declaration.parallelUnitConstructor =
          declaration.quoteConstructor <;> simp [same]
    rw [unitCanonical] at equality
    cases equality
  · have stable : parallelContents declaration
        [canonicalizeByAt key declaration depth pattern] =
          [canonicalizeByAt key declaration depth pattern] := by
      simpa [declaration] using
        (rhoProc_canonicalizeByAt_parallelLeaf key color typed
          isUnit notParallel depth)
    have membership : canonicalizeByAt key declaration depth pattern ∈
        parallelContents declaration
          [canonicalizeByAt key declaration depth pattern] := by
      rw [stable]
      simp
    have forbidden := keyedParallelFrontier_noParallel key declaration depth
      [pattern] (canonicalizeByAt key declaration depth pattern) (by
        simpa [canonicalizeListByAt] using membership) elements
    exact forbidden equality

private theorem rhoParallel_elements_hasType
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort)) :
    ElementsHaveType rhoCIGSLT.costWholeLanguage free bound elements
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
  rcases hasType_collection_inversion typed with
    ⟨elementType, typeEq, elementsTyped⟩ |
      ⟨rule, parameterName, elementType, membership, parameterShape,
        typeEq, elementsTyped⟩
  · cases typeEq
  · rcases rho_collectionRule_cases membership parameterShape with
      ⟨parallelType, category, element⟩ |
      ⟨parallelType, category, element⟩
    · cases color with
      | base =>
          rw [element] at elementsTyped
          change ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
            elements (.base (costBaseSortName "Proc"))
          exact elementsTyped
      | wrapped =>
          have impossible : costWrappedSortName = costBaseSortName "Proc" :=
            TypeExpr.base.inj (typeEq.trans (congrArg TypeExpr.base category))
          exact (by decide : costWrappedSortName ≠ costBaseSortName "Proc")
            impossible |>.elim
    · cases color with
      | base =>
          have impossible : costBaseSortName "Proc" = costWrappedSortName :=
            TypeExpr.base.inj (typeEq.trans (congrArg TypeExpr.base category))
          exact (by decide : costBaseSortName "Proc" ≠ costWrappedSortName)
            impossible |>.elim
      | wrapped =>
          rw [element] at elementsTyped
          change ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
            elements (.base costWrappedSortName)
          exact elementsTyped

/-- Proof-relevant companion of `rhoParallel_elements_hasType`.  The result
retains the selected static declaration at every nested bare collection. -/
private theorem rhoParallel_elements_hasTypeWithConstructors
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort)) :
    ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound elements
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
  rcases hasTypeWithConstructors_collection_inversion typed with
    ⟨elementType, typeEq, elementsTyped⟩ |
      ⟨rule, parameterName, elementType, _allowedRule, membership,
        parameterShape, typeEq, elementsTyped⟩
  · cases typeEq
  · rcases rho_collectionRule_cases membership parameterShape with
      ⟨parallelType, category, element⟩ |
        ⟨parallelType, category, element⟩
    · cases color with
      | base =>
          rw [element] at elementsTyped
          change ElementsHaveTypeWithConstructors
            rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT .base)
            free bound elements (.base (costBaseSortName "Proc"))
          exact elementsTyped
      | wrapped =>
          have impossible : costWrappedSortName = costBaseSortName "Proc" :=
            TypeExpr.base.inj (typeEq.trans (congrArg TypeExpr.base category))
          exact (by decide : costWrappedSortName ≠ costBaseSortName "Proc")
            impossible |>.elim
    · cases color with
      | base =>
          have impossible : costBaseSortName "Proc" = costWrappedSortName :=
            TypeExpr.base.inj (typeEq.trans (congrArg TypeExpr.base category))
          exact (by decide : costBaseSortName "Proc" ≠ costWrappedSortName)
            impossible |>.elim
      | wrapped =>
          rw [element] at elementsTyped
          change ElementsHaveTypeWithConstructors
            rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT .wrapped)
            free bound elements (.base costWrappedSortName)
          exact elementsTyped

/-- A reachable bare collection carrying the selected-colour hereditary
declaration witness is typed by that colour's PPar, not by the opposite
syntax-invisible collection declaration. -/
private theorem rhoParallel_shapeWithConstructors
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none) type)
    (reachable : rhoReachableType type = true) :
    type = .base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort ∧
      ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound elements
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  rcases hasTypeWithConstructors_collection_inversion typed with
    ⟨elementType, typeEq, _elementsTyped⟩ |
      ⟨rule, parameterName, elementType, allowedRule, membership,
        parameterShape, typeEq, elementsTyped⟩
  · rw [typeEq] at reachable
    simp [rhoReachableType] at reachable
  · obtain ⟨sourceName, wrapped, labelEq⟩ := allowedRule
    have selectedDecode : decodeDeclaredCostStaticConstructor rhoCIGSLT color
        rule.label = some sourceName := by
      rw [labelEq]
      exact decodeDeclaredCostStaticConstructor_symbols_of_wrappedLabel
        rhoCIGSLT color sourceName wrapped
    obtain ⟨constructor, preimage, materializes, sourceNameEq⟩ :=
      exists_costStaticConstructorPreimage_of_decode rhoCIGSLT color rule
        membership selectedDecode
    have decodedConstructor : rhoCIGSLT.decodeDeclaredCostConstructor
        rule.label = some constructor := by
      rw [← materializes,
        rhoCIGSLT.materializeDeclaredCostConstructor_label constructor]
      exact rhoCIGSLT.decodeDeclaredCostConstructor_render constructor
    have selectedRole : rhoCIGSLT.declaredCostConstructorRole constructor =
        .static color := by
      have decodedPair :
          rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
            decodeCostStaticConstructor color rule.label = some sourceName := by
        simpa [decodeDeclaredCostStaticConstructor, decodedConstructor] using
          selectedDecode
      exact decodedPair.1
    have targetBare : UsesBareCollection rule :=
      ⟨parameterName, _, elementType, parameterShape⟩
    have sourceBare : UsesBareCollection preimage.sourceConstructor.1 :=
      preimage.source_usesBareCollection selectedRole
        (materializes ▸ targetBare)
    obtain ⟨sourceParameter, sourceCollection, sourceElement, sourceShape⟩ :=
      sourceBare
    have sourceEq : preimage.sourceConstructor.1 = rhoCalc.terms[3] :=
      CostCanonicalLaws.rho_rule_eq_parallel_of_bare_shape
        preimage.sourceConstructor.2
        sourceShape
    have categorySelected : rule.category = declaration.processSort := by
      have mappedCategory := preimage.categoryMap
      rw [materializes, sourceEq] at mappedCategory
      simpa [declaration, costStaticReflectivePresentationDecl_eq_map,
        ReflectionExtension.mapReflectivePresentation,
        CostStaticColor.reflectiveSymbols_sort,
        rhoReflectivePresentation, rhoCalc,
        TypeExpr.proc, TypeExpr.baseType] using mappedCategory
    rcases rho_collectionRule_cases membership parameterShape with
      ⟨_parallelType, baseCategory, baseElement⟩ |
        ⟨_parallelType, wrappedCategory, wrappedElement⟩
    · cases color with
      | base =>
          refine ⟨typeEq.trans (congrArg TypeExpr.base categorySelected), ?_⟩
          rw [baseElement] at elementsTyped
          exact elementsTyped
      | wrapped =>
          have impossible : costBaseSortName "Proc" = costWrappedSortName :=
            baseCategory.symm.trans categorySelected
          exact (by decide : costBaseSortName "Proc" ≠ costWrappedSortName)
            impossible |>.elim
    · cases color with
      | base =>
          have impossible : costWrappedSortName = costBaseSortName "Proc" :=
            wrappedCategory.symm.trans categorySelected
          exact (by decide : costWrappedSortName ≠ costBaseSortName "Proc")
            impossible |>.elim
      | wrapped =>
          refine ⟨typeEq.trans (congrArg TypeExpr.base categorySelected), ?_⟩
          rw [wrappedElement] at elementsTyped
          exact elementsTyped

mutual
  /-- Recursive parallel flattening preserves the selected-colour hereditary
  typing of every retained occurrence. -/
  private theorem rhoProc_parallelLeaves_typedWithConstructors
      (color : CostStaticColor) (free : FreeTypeContext)
      (bound : List TypeExpr) {pattern : Pattern}
      (typed : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound pattern
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort)) :
      ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound
        (parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern)
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort) := by
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    change HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound pattern (.base declaration.processSort) at typed
    change ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      free bound (parallelLeaves declaration pattern)
      (.base declaration.processSort)
    by_cases isUnit : pattern =
        .apply declaration.parallelUnitConstructor []
    · subst pattern
      simpa [parallelLeaves] using
        (ElementsHaveTypeWithConstructors.nil bound
          (.base declaration.processSort) :
          ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
            free bound [] (.base declaration.processSort))
    · by_cases isParallel : ∃ elements,
          pattern = .collection declaration.parallelCollection elements none
      · obtain ⟨elements, rfl⟩ := isParallel
        simpa [declaration, parallelLeaves] using
          rhoProc_parallelLeavesList_typedWithConstructors color free bound
            (rhoParallel_elements_hasTypeWithConstructors color typed)
      · rw [parallelLeaves_of_not_unit_or_parallel declaration pattern isUnit
          (fun elements equality => isParallel ⟨elements, equality⟩)]
        exact .cons typed (.nil bound (.base declaration.processSort))
  termination_by sizeOf pattern

  private theorem rhoProc_parallelLeavesList_typedWithConstructors
      (color : CostStaticColor) (free : FreeTypeContext)
      (bound : List TypeExpr) {patterns : List Pattern}
      (typed : ElementsHaveTypeWithConstructors
        rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound patterns
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort)) :
      ElementsHaveTypeWithConstructors rhoCIGSLT.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        free bound
        (parallelLeavesList
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) patterns)
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).processSort) := by
    cases typed with
    | nil => exact .nil bound _
    | cons headTyped tailTyped =>
        exact
          (rhoProc_parallelLeaves_typedWithConstructors color free bound
            headTyped).append
          (rhoProc_parallelLeavesList_typedWithConstructors color free bound
            tailTyped)
  termination_by sizeOf patterns

  decreasing_by
    all_goals simp_all
    all_goals omega
end

mutual
  private theorem rhoProc_parallelLeaves_typed
      (color : CostStaticColor) (free : FreeTypeContext)
      (bound : List TypeExpr) {pattern : Pattern}
      (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort)) :
      ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
        (parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern)
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    change HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base declaration.processSort) at typed
    change ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
      (parallelLeaves declaration pattern) (.base declaration.processSort)
    by_cases isUnit : pattern =
        .apply declaration.parallelUnitConstructor []
    · subst pattern
      simpa [parallelLeaves] using
        (ElementsHaveType.nil bound (.base declaration.processSort) :
          ElementsHaveType rhoCIGSLT.costWholeLanguage free bound []
            (.base declaration.processSort))
    · by_cases isParallel : ∃ elements,
          pattern = .collection declaration.parallelCollection elements none
      · obtain ⟨elements, rfl⟩ := isParallel
        simpa [declaration, parallelLeaves] using
          rhoProc_parallelLeavesList_typed color free bound
            (rhoParallel_elements_hasType color typed)
      · rw [parallelLeaves_of_not_unit_or_parallel declaration pattern isUnit
          (fun elements equality => isParallel ⟨elements, equality⟩)]
        exact .cons typed (.nil bound (.base declaration.processSort))
  termination_by sizeOf pattern

  private theorem rhoProc_parallelLeavesList_typed
      (color : CostStaticColor) (free : FreeTypeContext)
      (bound : List TypeExpr) {patterns : List Pattern}
      (typed : ElementsHaveType rhoCIGSLT.costWholeLanguage free bound patterns
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort)) :
      ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
        (parallelLeavesList
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) patterns)
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases typed with
    | nil => exact .nil bound _
    | cons headTyped tailTyped =>
        exact (rhoProc_parallelLeaves_typed color free bound headTyped).append
          (rhoProc_parallelLeavesList_typed color free bound tailTyped)
  termination_by sizeOf patterns

  decreasing_by
    all_goals simp_all
    all_goals omega
end

mutual
  private theorem parallelLeaves_objects
      (declaration : ReflectivePresentationDecl) : ∀ {pattern},
      isObjectPattern pattern = true →
        isObjectPatternList (parallelLeaves declaration pattern) = true
    | pattern, object => by
        by_cases isUnit : pattern =
            .apply declaration.parallelUnitConstructor []
        · subst pattern
          simp [parallelLeaves, isObjectPatternList]
        · by_cases isParallel : ∃ elements,
              pattern = .collection declaration.parallelCollection elements none
          · obtain ⟨elements, rfl⟩ := isParallel
            have elementsObject : isObjectPatternList elements = true := by
              simpa [isObjectPattern] using object
            simpa [parallelLeaves] using
              parallelLeavesList_objects declaration elementsObject
          · rw [parallelLeaves_of_not_unit_or_parallel declaration pattern isUnit
              (fun elements equality => isParallel ⟨elements, equality⟩)]
            simp [isObjectPatternList, object]
  termination_by pattern => sizeOf pattern

  private theorem parallelLeavesList_objects
      (declaration : ReflectivePresentationDecl) : ∀ {patterns},
      isObjectPatternList patterns = true →
        isObjectPatternList (parallelLeavesList declaration patterns) = true
    | [], object => by simp [parallelLeavesList, isObjectPatternList]
    | pattern :: patterns, object => by
        have parts : isObjectPattern pattern = true ∧
            isObjectPatternList patterns = true := by
          simpa [isObjectPatternList] using object
        simpa [parallelLeavesList] using
          AvailableOpenArguments.object_append_true _ _
            (parallelLeaves_objects declaration parts.1)
            (parallelLeavesList_objects declaration parts.2)
  termination_by patterns => sizeOf patterns

  decreasing_by
    all_goals simp_all
    all_goals omega
end

mutual
  private theorem parallelLeaves_supported
      (declaration : ReflectivePresentationDecl) (allowed : String → Prop) :
      ∀ {pattern}, ConstructorsWithin allowed pattern →
        ConstructorListWithin allowed (parallelLeaves declaration pattern)
    | pattern, supported => by
        by_cases isUnit : pattern =
            .apply declaration.parallelUnitConstructor []
        · subst pattern
          simp [parallelLeaves]
        · by_cases isParallel : ∃ elements,
              pattern = .collection declaration.parallelCollection elements none
          · obtain ⟨elements, rfl⟩ := isParallel
            simpa [parallelLeaves] using
              parallelLeavesList_supported declaration allowed supported
          · rw [parallelLeaves_of_not_unit_or_parallel declaration pattern isUnit
              (fun elements equality => isParallel ⟨elements, equality⟩)]
            exact ⟨supported, trivial⟩
  termination_by pattern => sizeOf pattern

  private theorem parallelLeavesList_supported
      (declaration : ReflectivePresentationDecl) (allowed : String → Prop) :
      ∀ {patterns}, ConstructorListWithin allowed patterns →
        ConstructorListWithin allowed (parallelLeavesList declaration patterns)
    | [], supported => trivial
    | pattern :: patterns, supported => by
        exact (parallelLeaves_supported declaration allowed supported.1).append
          (parallelLeavesList_supported declaration allowed supported.2)
  termination_by patterns => sizeOf patterns

  decreasing_by
    all_goals simp_all
    all_goals omega
end

mutual
  private theorem rhoProc_parallelLeaves_frontier_perm
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key) (color : CostStaticColor)
      (free : FreeTypeContext) (bound : List TypeExpr) {pattern : Pattern}
      (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
      (depth : Nat) :
      List.Perm
        (parallelContents
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          [canonicalizeByAt key
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            depth pattern])
        (canonicalizeListByAt key
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          depth
          (parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            pattern)) := by
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    change HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base declaration.processSort) at typed
    change List.Perm
      (parallelContents declaration
        [canonicalizeByAt key declaration depth pattern])
      (canonicalizeListByAt key declaration depth
        (parallelLeaves declaration pattern))
    cases pattern with
    | bvar index => simp [parallelLeaves, canonicalizeByAt,
        canonicalizeListByAt, parallelContents, parallelSplice]
    | fvar name => simp [parallelLeaves, canonicalizeByAt,
        canonicalizeListByAt, parallelContents, parallelSplice]
    | apply constructor arguments =>
        by_cases isUnit : Pattern.apply constructor arguments =
            .apply declaration.parallelUnitConstructor []
        · injection isUnit with constructorEq argumentsEq
          subst constructor
          subst arguments
          have unitCanonical : canonicalizeByAt key declaration depth
              (.apply declaration.parallelUnitConstructor []) =
              .apply declaration.parallelUnitConstructor [] := by
            simp only [canonicalizeByAt, canonicalizeListByAt]
            unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
            by_cases same : declaration.parallelUnitConstructor =
                declaration.quoteConstructor <;> simp [same]
          rw [unitCanonical]
          simp [parallelLeaves, canonicalizeListByAt, parallelContents,
            parallelSplice]
        · have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
            isUnit (by intro elements equality; cases equality) depth
          have leavesEq : parallelLeaves declaration
              (.apply constructor arguments) = [.apply constructor arguments] :=
            parallelLeaves_of_not_unit_or_parallel declaration _ isUnit
              (by intro elements equality; cases equality)
          rw [leavesEq]
          simpa [declaration, canonicalizeListByAt] using
            (List.Perm.of_eq stable)
    | lambda binder body =>
        have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
          (by intro equality; cases equality)
          (by intro elements equality; cases equality) depth
        simpa [declaration, parallelLeaves, canonicalizeListByAt] using
          List.Perm.of_eq stable
    | multiLambda arity binders body =>
        have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
          (by intro equality; cases equality)
          (by intro elements equality; cases equality) depth
        simpa [declaration, parallelLeaves, canonicalizeListByAt] using
          List.Perm.of_eq stable
    | subst body replacement =>
        have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
          (by intro equality; cases equality)
          (by intro elements equality; cases equality) depth
        simpa [declaration, parallelLeaves, canonicalizeListByAt] using
          List.Perm.of_eq stable
    | collection collectionType elements rest =>
        cases rest with
        | some restName =>
            have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
              (by intro equality; cases equality)
              (by intro nested equality; cases equality) depth
            simpa [declaration, parallelLeaves, canonicalizeListByAt] using
              List.Perm.of_eq stable
        | none =>
            by_cases selected : collectionType = declaration.parallelCollection
            · subst collectionType
              have elementsTyped := rhoParallel_elements_hasType color typed
              have exposed :=
                parallelContents_canonicalizeByAt_singleton_perm key declaration
                  depth (.collection declaration.parallelCollection elements none)
              have children := rhoProc_parallelLeavesList_frontier_perm key color
                free bound elementsTyped depth
              have filtered :=
                parallelContents_canonicalizeListByAt_filter_unit key declaration
                  depth elements
              exact exposed.trans (by
                simpa [declaration, parallelContents, parallelSplice,
                  parallelLeaves] using
                    (List.Perm.of_eq filtered).trans children)
            · have stable := rhoProc_canonicalizeByAt_parallelLeaf key color typed
                (by intro equality; cases equality)
                (by intro nested equality
                    injection equality with collectionEq
                    exact selected collectionEq) depth
              have leavesEq : parallelLeaves declaration
                  (.collection collectionType elements none) =
                    [.collection collectionType elements none] :=
                parallelLeaves_of_not_unit_or_parallel declaration _
                  (by intro equality; cases equality)
                  (by intro nested equality
                      injection equality with collectionEq
                      exact selected collectionEq)
              rw [leavesEq]
              simpa [declaration, canonicalizeListByAt] using
                (List.Perm.of_eq stable)
  termination_by sizeOf pattern

  private theorem rhoProc_parallelLeavesList_frontier_perm
      {Key : Type} [LinearOrder Key]
      (key : Nat → Pattern → Key) (color : CostStaticColor)
      (free : FreeTypeContext) (bound : List TypeExpr)
      {patterns : List Pattern}
      (typed : ElementsHaveType rhoCIGSLT.costWholeLanguage free bound patterns
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
      (depth : Nat) :
      List.Perm
        (parallelContents
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (canonicalizeListByAt key
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            depth patterns))
        (canonicalizeListByAt key
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          depth
          (parallelLeavesList
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            patterns)) := by
    cases typed with
    | nil => simp [parallelLeavesList, canonicalizeListByAt, parallelContents]
    | cons headTyped tailTyped =>
        have head := rhoProc_parallelLeaves_frontier_perm key color
          free bound headTyped depth
        have tail := rhoProc_parallelLeavesList_frontier_perm key color
          free bound tailTyped depth
        simp only [canonicalizeListByAt, parallelLeavesList]
        rw [show canonicalizeByAt key
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              depth _ :: canonicalizeListByAt key
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                depth _ =
            [canonicalizeByAt key
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              depth _] ++ canonicalizeListByAt key
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                depth _ by rfl,
          parallelContents_append]
        simpa only [canonicalizeListByAt_eq_map, List.map_append] using
          head.append tail
  termination_by sizeOf patterns

  decreasing_by
    all_goals simp_all
    all_goals omega
end

/-- Equal ordinary canonical classes of two typed process terms induce an
occurrence-preserving permutation of their recursively flattened parallel
leaves.  Singleton parallel wrappers are used only in the ordinary
canonical quotient, where absorption is unconditional; keyed endpoints stay
fully explicit. -/
private theorem rhoProcParallelLeaves_canonical_map_perm
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {left right : Pattern}
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage free bound left
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage free bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) left =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) right)
    (depth : Nat) :
    List.Perm
      ((parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        left).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)))
      ((parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        right).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftFrontier := rhoProc_parallelLeaves_frontier_perm key color
    free bound leftTyped depth
  have rightFrontier := rhoProc_parallelLeaves_frontier_perm key color
    free bound rightTyped depth
  have wrappedCanonical : canonicalize declaration
        (.collection declaration.parallelCollection [left] none) =
      canonicalize declaration
        (.collection declaration.parallelCollection [right] none) := by
    simpa only [canonicalize_parallel_singleton] using canonical
  have outer := canonicalize_parallelContents_keyed_perm_of_equal key
    declaration depth wrappedCanonical
  have leftToLeaves : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth left]).map
          (canonicalize declaration))
      ((parallelLeaves declaration left).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        leftFrontier.map (canonicalize declaration)
  have rightToLeaves : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth right]).map
          (canonicalize declaration))
      ((parallelLeaves declaration right).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        rightFrontier.map (canonicalize declaration)
  have outerSingleton : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth left]).map
          (canonicalize declaration))
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth right]).map
          (canonicalize declaration)) := by
    simpa [canonicalizeListByAt] using outer
  exact leftToLeaves.symm.trans (outerSingleton.trans rightToLeaves)

/-- Flattening a typed process into its raw parallel occurrences and then
ordinary-canonicalizing those occurrences yields the same multiset as the
ordinary canonical parallel frontier of the process itself.  The keyed
frontier is used only as the occurrence-preserving intermediary; no keyed
fixed-point law is assumed. -/
private theorem rhoProcParallelLeaves_canonical_map_perm_plainFrontier
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (depth : Nat) :
    List.Perm
      ((parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        pattern).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)))
      ((parallelContents
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (canonicalizeList
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          [pattern])).map
            (canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leaves := rhoProc_parallelLeaves_frontier_perm key color free bound
    typed depth
  have leavesCanonical : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth pattern]).map
          (canonicalize declaration))
      ((parallelLeaves declaration pattern).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        leaves.map (canonicalize declaration)
  have plain := canonicalize_parallelContents_keyed_plain_perm key declaration
    depth [pattern]
  simpa [declaration, canonicalizeListByAt] using
    leavesCanonical.symm.trans plain

/-- If a typed rho process canonically exposes one Drop, recursive parallel
flattening contains exactly one raw occurrence whose ordinary canonical form
is that Drop.  In particular, a singleton collapse is exposed without
identifying the raw process with its canonical representative. -/
private theorem rhoProc_parallelLeaves_eq_singleton_of_canonical_drop
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern name : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (depth : Nat) :
    ∃ leaf,
      parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          pattern = [leaf] ∧
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leaf =
          .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).dropConstructor [name] := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have fixed : canonicalize declaration
      (.apply declaration.dropConstructor [name]) =
        .apply declaration.dropConstructor [name] := by
    rw [← canonical]
    exact canonicalize_idempotent declaration pattern
  have frontier := rhoProcParallelLeaves_canonical_map_perm_plainFrontier
    key color typed depth
  rw [canonicalizeList_eq_map, List.map_singleton, canonical] at frontier
  have exposed : parallelContents declaration
      [.apply declaration.dropConstructor [name]] =
        [.apply declaration.dropConstructor [name]] := by
    simp [parallelContents, parallelSplice]
  rw [exposed, List.map_singleton, fixed] at frontier
  have singleton : (parallelLeaves declaration pattern).map
      (canonicalize declaration) =
        [.apply declaration.dropConstructor [name]] := by
    exact List.perm_singleton.mp frontier
  obtain ⟨leaf, leaves, leafCanonical⟩ :=
    List.map_eq_singleton_iff.mp singleton
  exact ⟨leaf, leaves, leafCanonical⟩

/-- A typed process whose canonical form is one selected Drop exposes one
raw Drop occurrence through parallel flattening.  Typing, objecthood, and
constructor support of the raw name payload are retained, and its ordinary
canonical form is the exposed canonical name. -/
private theorem rhoProc_canonical_drop_exposure
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern name : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (object : isObjectPattern pattern = true)
    (supported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      pattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (depth : Nat) :
    ∃ rawName,
      parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          pattern =
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [rawName]] ∧
      HasType rhoCIGSLT.costWholeLanguage free bound rawName
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).nameSort) ∧
      isObjectPattern rawName = true ∧
      ConstructorsWithin
        (fun constructor => ∃ sourceConstructor,
          decodeCostStaticConstructor color constructor = some sourceConstructor)
        rawName ∧
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rawName = name := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let allowed := fun constructor => ∃ sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  obtain ⟨leaf, leaves, leafCanonical⟩ :=
    rhoProc_parallelLeaves_eq_singleton_of_canonical_drop key color typed
      canonical depth
  have leafMembership : leaf ∈ parallelLeaves declaration pattern := by
    rw [leaves]
    simp
  have leavesTyped := rhoProc_parallelLeaves_typed color free bound typed
  have leafTyped := elementsHaveType_of_mem leavesTyped leafMembership
  have leavesObject := parallelLeaves_objects declaration object
  have leafObject := isObjectPattern_of_mem leavesObject leafMembership
  have leavesSupported := parallelLeaves_supported declaration allowed supported
  have leafSupported := leavesSupported.of_mem leafMembership
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    simpa [declaration] using rhoCostStatic_quote_ne_drop color
  have dropFixed : canonicalize declaration
      (.apply declaration.dropConstructor [name]) =
        .apply declaration.dropConstructor [name] := by
    rw [← canonical]
    exact canonicalize_idempotent declaration pattern
  have nameFixed : canonicalize declaration name = name := by
    rw [canonicalize_apply_of_ne_quote declaration quoteNeDrop.symm] at dropFixed
    injection dropFixed with headEquality argumentsEquality
    exact (List.cons.inj argumentsEquality).1
  have leafPairCanonical : canonicalize declaration leaf =
      canonicalize declaration (.apply declaration.dropConstructor [name]) :=
    leafCanonical.trans dropFixed.symm
  rcases canonicalize_eq_root_cases declaration leafPairCanonical with
    leafCollapsing | rightCollapsing | aligned
  · obtain ⟨elements, shape⟩ :=
      rhoProc_collapsingRoot_is_parallel color leafTyped leafCollapsing
    exact (parallelLeaves_noParallel declaration pattern leaf leafMembership
      elements shape).elim
  · rcases rightCollapsing with quoted | parallel
    · obtain ⟨arguments, shape⟩ := quoted
      injection shape with headEquality argumentsEquality
      exact (quoteNeDrop headEquality.symm).elim
    · obtain ⟨elements, shape⟩ := parallel
      cases shape
  · cases aligned with
    | apply notQuote children =>
        cases children with
        | @cons rawName rightName leftTail rightTail rawCanonical tail =>
            cases tail
            have rawTyped := rhoCostStatic_drop_inner_hasType color leafTyped
            have rawObject : isObjectPattern rawName = true := by
              simpa [isObjectPattern, isObjectPatternList] using leafObject
            have rawSupported : ConstructorsWithin allowed rawName := by
              simpa [ConstructorsWithin, ConstructorListWithin] using
                leafSupported.2.1
            exact ⟨rawName, by simpa [declaration] using leaves, rawTyped,
              rawObject, rawSupported, rawCanonical.trans nameFixed⟩

/-- Occurrence-indexed form of `rhoProc_canonical_drop_exposure`.

Besides the unique flattened Drop value, this theorem returns the exact
one-hole context selecting that raw occurrence in the original process.  A
static-region plan can therefore replay the same occurrence into its retained
boundary table, including when equal leaves occur elsewhere in the source. -/
private theorem rhoProc_canonical_drop_exposure_with_context
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern name : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (object : isObjectPattern pattern = true)
    (supported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      pattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (depth : Nat) :
    ∃ rawName, ∃ context : OneHoleContext,
      pattern = context.fill
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [rawName]) ∧
      parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          pattern =
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [rawName]] ∧
      HasType rhoCIGSLT.costWholeLanguage free bound rawName
        (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).nameSort) ∧
      isObjectPattern rawName = true ∧
      ConstructorsWithin
        (fun constructor => ∃ sourceConstructor,
          decodeCostStaticConstructor color constructor = some sourceConstructor)
        rawName ∧
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rawName = name := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨rawName, leaves, rawTyped, rawObject, rawSupported, rawCanonical⟩ :=
    rhoProc_canonical_drop_exposure key color typed object supported canonical
      depth
  have leaves' : parallelLeaves declaration pattern =
      [.apply declaration.dropConstructor [rawName]] := by
    simpa [declaration] using leaves
  have membership : .apply declaration.dropConstructor [rawName] ∈
      parallelLeaves declaration pattern := by
    rw [leaves']
    simp
  obtain ⟨context, contextEq⟩ :=
    parallelLeaves_context declaration pattern
      (.apply declaration.dropConstructor [rawName]) membership
  exact ⟨rawName, context, contextEq, leaves, rawTyped, rawObject,
    rawSupported, rawCanonical⟩

/-- A typed process with exactly one recursively flattened parallel
occurrence has the same keyed canonical representative as that occurrence.
The proof handles a genuine nested parallel by exposing its occurrence
frontier; all other terms reduce to the defining singleton leaf equation. -/
private theorem rhoProc_canonicalizeByAt_eq_single_parallelLeaf
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern leaf : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage free bound pattern
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (leaves : parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      [leaf])
    (depth : Nat) :
    canonicalizeByAt key
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        depth pattern =
      canonicalizeByAt key
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        depth leaf := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  change HasType rhoCIGSLT.costWholeLanguage free bound pattern
    (.base declaration.processSort) at typed
  change parallelLeaves declaration pattern = [leaf] at leaves
  change canonicalizeByAt key declaration depth pattern =
    canonicalizeByAt key declaration depth leaf
  by_cases isUnit : pattern =
      .apply declaration.parallelUnitConstructor []
  · subst pattern
    simp [parallelLeaves] at leaves
  · by_cases isParallel : ∃ elements,
        pattern = .collection declaration.parallelCollection elements none
    · obtain ⟨elements, rfl⟩ := isParallel
      have elementsTyped := rhoParallel_elements_hasType color typed
      have leavesList : parallelLeavesList declaration elements = [leaf] := by
        simpa [parallelLeaves] using leaves
      have frontier := rhoProc_parallelLeavesList_frontier_perm key color
        free bound elementsTyped depth
      rw [leavesList] at frontier
      simp only [canonicalizeListByAt] at frontier
      have frontierEq : parallelContents declaration
          (canonicalizeListByAt key declaration depth elements) =
        [canonicalizeByAt key declaration depth leaf] :=
        List.perm_singleton.mp frontier
      have normalizedEq : normalizeParallelElementsBy (key depth) declaration
          (canonicalizeListByAt key declaration depth elements) =
        [canonicalizeByAt key declaration depth leaf] := by
        unfold normalizeParallelElementsBy
        change Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
            (parallelContents declaration
              (canonicalizeListByAt key declaration depth elements)) = _
        rw [frontierEq]
        exact List.perm_singleton.mp
          (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm (key depth)
            [canonicalizeByAt key declaration depth leaf])
      simp only [canonicalizeByAt]
      simp [normalizedEq, collapseParallel]
    · have defining := parallelLeaves_of_not_unit_or_parallel declaration
        pattern isUnit (fun elements equality =>
          isParallel ⟨elements, equality⟩)
      rw [defining] at leaves
      have patternEq : pattern = leaf := (List.cons.inj leaves).1
      subst leaf
      rfl

private theorem rhoParallelLeaves_canonical_map_perm
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {leftElements rightElements : List Pattern}
    (leftTyped : ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
      leftElements
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightTyped : ElementsHaveType rhoCIGSLT.costWholeLanguage free bound
      rightElements
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection leftElements none) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection rightElements none))
    (depth : Nat) :
    List.Perm
      ((parallelLeavesList
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftElements).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)))
      ((parallelLeavesList
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightElements).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftFrontier := rhoProc_parallelLeavesList_frontier_perm key color
    free bound leftTyped depth
  have rightFrontier := rhoProc_parallelLeavesList_frontier_perm key color
    free bound rightTyped depth
  have outer := canonicalize_parallelContents_keyed_perm_of_equal key
    declaration depth canonical
  have leftToLeaves : List.Perm
      ((parallelContents declaration
        (canonicalizeListByAt key declaration depth leftElements)).map
          (canonicalize declaration))
      ((parallelLeavesList declaration leftElements).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        leftFrontier.map (canonicalize declaration)
  have rightToLeaves : List.Perm
      ((parallelContents declaration
        (canonicalizeListByAt key declaration depth rightElements)).map
          (canonicalize declaration))
      ((parallelLeavesList declaration rightElements).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        rightFrontier.map (canonicalize declaration)
  exact leftToLeaves.symm.trans (outer.trans rightToLeaves)

/-- A typed bare rho parallel pair with the same ordinary canonical image
closes through recursively aligned flattened occurrences.  The keyed frontier
may reorder equal semantic classes, but it neither discards duplicate
occurrences nor promotes stable tie order to semantics. -/
theorem rhoBareParallelApex
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {leftElements rightElements : List Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {left right : Pattern},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound left
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound right
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound right
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
          (fun constructor => ∃ sourceConstructor,
            decodeCostStaticConstructor color constructor =
              some sourceConstructor) left →
        ConstructorsWithin
          (fun constructor => ∃ sourceConstructor,
            decodeCostStaticConstructor color constructor =
              some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl) left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl) right →
        sizeOf left + sizeOf right <
          sizeOf
              (Pattern.collection
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).parallelCollection leftElements none) +
            sizeOf
              (Pattern.collection
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).parallelCollection rightElements none) →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth left)
          (canonicalizeByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth right))
    (leftHereditary : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightHereditary : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection rightElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection rightElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (leftObject : isObjectPattern
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none) = true)
    (rightObject : isObjectPattern
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection rightElements none) = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none))
    (rightSupported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection rightElements none))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection leftElements none) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection rightElements none))
    (leftDepth_eq : leftDepth = rootDepth)
    (rightDepth_eq : rightDepth = rootDepth) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection leftElements none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection rightElements none)) := by
  subst leftDepth
  subst rightDepth
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let allowed := fun constructor => ∃ sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  have leftElementsTyped := rhoParallel_elements_hasType color leftTyped
  have rightElementsTyped := rhoParallel_elements_hasType color rightTyped
  have leftElementsHereditary :=
    rhoParallel_elements_hasTypeWithConstructors color leftHereditary
  have rightElementsHereditary :=
    rhoParallel_elements_hasTypeWithConstructors color rightHereditary
  have leftElementsObject : isObjectPatternList leftElements = true := by
    simpa [isObjectPattern] using leftObject
  have rightElementsObject : isObjectPatternList rightElements = true := by
    simpa [isObjectPattern] using rightObject
  have leftLeavesTyped := rhoProc_parallelLeavesList_typed color
    cospan.commonTargetFreeContext bound leftElementsTyped
  have rightLeavesTyped := rhoProc_parallelLeavesList_typed color
    cospan.commonTargetFreeContext bound rightElementsTyped
  have leftLeavesHereditary :=
    rhoProc_parallelLeavesList_typedWithConstructors color
      cospan.commonTargetFreeContext bound leftElementsHereditary
  have rightLeavesHereditary :=
    rhoProc_parallelLeavesList_typedWithConstructors color
      cospan.commonTargetFreeContext bound rightElementsHereditary
  have leftLeavesObject := parallelLeavesList_objects declaration
    leftElementsObject
  have rightLeavesObject := parallelLeavesList_objects declaration
    rightElementsObject
  have leftLeavesSupported := parallelLeavesList_supported declaration allowed
    leftSupported
  have rightLeavesSupported := parallelLeavesList_supported declaration allowed
    rightSupported
  have canonicalLeaves := rhoParallelLeaves_canonical_map_perm key color
    leftElementsTyped rightElementsTyped canonical rootDepth
  let leafAlignment : CommonRestorationApex.Permutation cospan declaration
      rootDepth
      (canonicalizeListByAt key declaration rootDepth
        (parallelLeavesList declaration leftElements))
      (canonicalizeListByAt key declaration rootDepth
        (parallelLeavesList declaration rightElements)) :=
    CommonRestorationApex.Permutation.of_canonical_map_perm cospan declaration
      rootDepth canonicalLeaves (fun leftMembership rightMembership equal =>
        close
          (leftLeavesHereditary.hasType_of_mem leftMembership)
          (rightLeavesHereditary.hasType_of_mem rightMembership)
          (elementsHaveType_of_mem leftLeavesTyped leftMembership)
          (elementsHaveType_of_mem rightLeavesTyped rightMembership)
          (isObjectPattern_of_mem leftLeavesObject leftMembership)
          (isObjectPattern_of_mem rightLeavesObject rightMembership)
          (leftLeavesSupported.of_mem leftMembership)
          (rightLeavesSupported.of_mem rightMembership) equal (by
            have leftSmaller := parallelLeavesList_size_lt declaration
              leftElements _ leftMembership
            have rightSmaller := parallelLeavesList_size_lt declaration
              rightElements _ rightMembership
            simp_wf
            omega))
  have leftFrontier := rhoProc_parallelLeavesList_frontier_perm key color
    cospan.commonTargetFreeContext bound leftElementsTyped rootDepth
  have rightFrontier := rhoProc_parallelLeavesList_frontier_perm key color
    cospan.commonTargetFreeContext bound rightElementsTyped rootDepth
  let frontierAlignment :=
    CommonRestorationApex.Permutation.of_endpoint_perms leafAlignment
      leftFrontier rightFrontier
  exact CommonRestorationApex.parallel_of_permutation cospan declaration
    rootDepth frontierAlignment

/-- A typed bare parallel process closes against an arbitrary typed process
of the same static colour whenever the latter is not itself syntactically a
bare parallel collection.  The parallel side descends strictly through its
flattened occurrences; the other side is bounded by its own size.  Its
temporary singleton wrapper is removed only after the typed frontier theorem
has proved that keyed canonicalization cannot expose a parallel root there. -/
theorem rhoBareParallelLeftApex
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {leftElements : List Pattern} {right : Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {leftLeaf rightLeaf : Pattern},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound leftLeaf
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound rightLeaf
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound leftLeaf
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound rightLeaf
          (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) →
        isObjectPattern leftLeaf = true →
        isObjectPattern rightLeaf = true →
        ConstructorsWithin
          (fun constructor => ∃ sourceConstructor,
            decodeCostStaticConstructor color constructor =
              some sourceConstructor) leftLeaf →
        ConstructorsWithin
          (fun constructor => ∃ sourceConstructor,
            decodeCostStaticConstructor color constructor =
              some sourceConstructor) rightLeaf →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftLeaf =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightLeaf →
        sizeOf leftLeaf + sizeOf rightLeaf <
          sizeOf
              (Pattern.collection
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).parallelCollection leftElements none) +
            sizeOf right →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth leftLeaf)
          (canonicalizeByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth rightLeaf))
    (leftHereditary : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightHereditary : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none)
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (leftObject : isObjectPattern
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none) = true)
    (rightObject : isObjectPattern right = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection leftElements none))
    (rightSupported : ConstructorsWithin
      (fun constructor => ∃ sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      right)
    (rightNotParallel : ∀ elements,
      right ≠ .collection
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelCollection elements none)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection leftElements none) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) right)
    (leftDepth_eq : leftDepth = rootDepth)
    (rightDepth_eq : rightDepth = rootDepth) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.collection
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection leftElements none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right) := by
  subst leftDepth
  subst rightDepth
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let allowed := fun constructor => ∃ sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  have leftElementsTyped := rhoParallel_elements_hasType color leftTyped
  have leftElementsHereditary :=
    rhoParallel_elements_hasTypeWithConstructors color leftHereditary
  have leftElementsObject : isObjectPatternList leftElements = true := by
    simpa [isObjectPattern] using leftObject
  have leftLeavesTyped := rhoProc_parallelLeavesList_typed color
    cospan.commonTargetFreeContext bound leftElementsTyped
  have rightLeavesTyped := rhoProc_parallelLeaves_typed color
    cospan.commonTargetFreeContext bound rightTyped
  have leftLeavesHereditary :=
    rhoProc_parallelLeavesList_typedWithConstructors color
      cospan.commonTargetFreeContext bound leftElementsHereditary
  have rightLeavesHereditary :=
    rhoProc_parallelLeaves_typedWithConstructors color
      cospan.commonTargetFreeContext bound rightHereditary
  have leftLeavesObject := parallelLeavesList_objects declaration
    leftElementsObject
  have rightLeavesObject := parallelLeaves_objects declaration rightObject
  have leftLeavesSupported := parallelLeavesList_supported declaration allowed
    leftSupported
  have rightLeavesSupported := parallelLeaves_supported declaration allowed
    rightSupported
  have canonicalLeaves : List.Perm
      ((parallelLeavesList declaration leftElements).map
        (canonicalize declaration))
      ((parallelLeaves declaration right).map
        (canonicalize declaration)) := by
    simpa [declaration, parallelLeaves] using
      (rhoProcParallelLeaves_canonical_map_perm key color leftTyped rightTyped
        canonical rootDepth)
  let leafAlignment : CommonRestorationApex.Permutation cospan declaration
      rootDepth
      (canonicalizeListByAt key declaration rootDepth
        (parallelLeavesList declaration leftElements))
      (canonicalizeListByAt key declaration rootDepth
        (parallelLeaves declaration right)) :=
    CommonRestorationApex.Permutation.of_canonical_map_perm cospan declaration
      rootDepth canonicalLeaves (fun leftMembership rightMembership equal =>
        close
          (leftLeavesHereditary.hasType_of_mem leftMembership)
          (rightLeavesHereditary.hasType_of_mem rightMembership)
          (elementsHaveType_of_mem leftLeavesTyped leftMembership)
          (elementsHaveType_of_mem rightLeavesTyped rightMembership)
          (isObjectPattern_of_mem leftLeavesObject leftMembership)
          (isObjectPattern_of_mem rightLeavesObject rightMembership)
          (leftLeavesSupported.of_mem leftMembership)
          (rightLeavesSupported.of_mem rightMembership) equal (by
            have leftSmaller := parallelLeavesList_size_lt declaration
              leftElements _ leftMembership
            have rightBounded := parallelLeaves_size_le declaration
              right _ rightMembership
            simp_wf
            omega))
  have leftFrontier := rhoProc_parallelLeavesList_frontier_perm key color
    cospan.commonTargetFreeContext bound leftElementsTyped rootDepth
  have rightFrontier := rhoProc_parallelLeaves_frontier_perm key color
    cospan.commonTargetFreeContext bound rightTyped rootDepth
  let frontierAlignment :=
    CommonRestorationApex.Permutation.of_endpoint_perms leafAlignment
      leftFrontier rightFrontier
  have wrapped : CommonRestorationApex rhoCIGSLT cospan declaration rootDepth
      (canonicalizeByAt key declaration rootDepth
        (.collection declaration.parallelCollection leftElements none))
      (canonicalizeByAt key declaration rootDepth
        (.collection declaration.parallelCollection [right] none)) :=
    CommonRestorationApex.parallel_of_permutation cospan declaration
      rootDepth frontierAlignment
  have rightCanonicalNotParallel :=
    rhoProc_canonicalizeByAt_notParallel key color rightTyped
      rightNotParallel rootDepth
  have absorbRight := canonicalizeByAt_parallel_singleton_of_not_parallel key
    declaration rootDepth right rightCanonicalNotParallel
  simpa only [absorbRight] using wrapped


/-- The endpoint key depths used by the recursive rho apex are synchronized
with its restoration depth except in the generated reflective-name fibre.
Names may be compared at any restoration depth because typed, supported rho
names have depth-independent keyed canonicalization. -/
def RhoApexDepthCompatible (declaration : ReflectivePresentationDecl)
    (type : TypeExpr)
    (leftDepth rightDepth rootDepth : Nat) : Prop :=
  type = .base declaration.nameSort ∨
    (leftDepth = rootDepth ∧ rightDepth = rootDepth)

/-- Lift a typed rho constructor spine through a caller-supplied apex for
strictly smaller canonical pairs.  Parameter reachability is supplied from
the one generated rule, so the recursion never invents a second typing table. -/
theorem rhoArguments
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (typedAllowed rawAllowed : String -> Prop)
    (parentLeft parentRight : Pattern)
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage typedAllowed
          cospan.commonTargetFreeContext bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage typedAllowed
          cospan.commonTargetFreeContext bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin rawAllowed left →
        ConstructorsWithin rawAllowed right →
        canonicalize declaration left = canonicalize declaration right →
        sizeOf left + sizeOf right <
          sizeOf parentLeft + sizeOf parentRight →
        rhoReachableType type = true →
        RhoApexDepthCompatible declaration type leftDepth rightDepth
          rootDepth →
        CommonRestorationApex rhoCIGSLT cospan declaration rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration leftDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration rightDepth right)) :
    ∀ {bound : List TypeExpr} {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam} {leftDepth rightDepth rootDepth : Nat},
      ArgumentsHaveTypesWithConstructors rhoCIGSLT.costWholeLanguage typedAllowed
          cospan.commonTargetFreeContext bound leftArguments parameters →
      ArgumentsHaveTypesWithConstructors rhoCIGSLT.costWholeLanguage typedAllowed
          cospan.commonTargetFreeContext bound rightArguments parameters →
      isObjectPatternList leftArguments = true →
      isObjectPatternList rightArguments = true →
      ConstructorListWithin rawAllowed leftArguments →
      ConstructorListWithin rawAllowed rightArguments →
      (∀ argument ∈ leftArguments, sizeOf argument < sizeOf parentLeft) →
      (∀ argument ∈ rightArguments, sizeOf argument < sizeOf parentRight) →
      (∀ {parameter : TermParam}, parameter ∈ parameters →
        ∀ {expected : TypeExpr}, parameterType? parameter = some expected →
          rhoReachableType expected = true) →
      (∀ {parameter : TermParam}, parameter ∈ parameters →
        ∀ {expected : TypeExpr}, parameterType? parameter = some expected →
          RhoApexDepthCompatible declaration expected leftDepth
            rightDepth rootDepth) →
      List.Forall₂
        (fun left right =>
          canonicalize declaration left = canonicalize declaration right)
        leftArguments rightArguments →
      CommonRestorationApexList rhoCIGSLT cospan declaration rootDepth
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration leftDepth
          leftArguments)
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration rightDepth
          rightArguments) := by
  intro bound leftArguments rightArguments parameters leftDepth rightDepth
    rootDepth leftTyped rightTyped leftObjects rightObjects leftSupported
    rightSupported leftSmaller rightSmaller parametersReachable
    parametersCompatible canonical
  rw [canonicalizeListByAt_eq_map, canonicalizeListByAt_eq_map]
  induction canonical generalizing parameters with
  | nil =>
      cases leftTyped
      cases rightTyped
      exact .nil rootDepth
  | @cons leftHead rightHead leftTail rightTail headCanonical tailCanonical ih =>
      cases leftTyped with
      | @cons _ _ _ leftParameter leftParameters leftExpected
          leftRepresentation leftParameterType leftHeadTyped leftTailTyped =>
          cases rightTyped with
          | @cons _ _ _ rightParameter rightParameters rightExpected
              rightRepresentation rightParameterType rightHeadTyped
              rightTailTyped =>
              have expectedEq : rightExpected = leftExpected :=
                Option.some.inj
                  (rightParameterType.symm.trans leftParameterType)
              subst rightExpected
              have leftObjectParts : isObjectPattern leftHead = true ∧
                  isObjectPatternList leftTail = true := by
                simpa [isObjectPatternList] using leftObjects
              have rightObjectParts : isObjectPattern rightHead = true ∧
                  isObjectPatternList rightTail = true := by
                simpa [isObjectPatternList] using rightObjects
              have headMeasure : sizeOf leftHead + sizeOf rightHead <
                  sizeOf parentLeft + sizeOf parentRight := by
                have leftLt := leftSmaller leftHead (by simp)
                have rightLt := rightSmaller rightHead (by simp)
                omega
              have headReachable : rhoReachableType leftExpected = true :=
                parametersReachable (by simp) leftParameterType
              have head := close (leftDepth := leftDepth)
                (rightDepth := rightDepth) (rootDepth := rootDepth)
                leftHeadTyped rightHeadTyped
                leftObjectParts.1 rightObjectParts.1
                (leftSupported.of_mem (by simp))
                (rightSupported.of_mem (by simp)) headCanonical headMeasure
                headReachable
                (parametersCompatible (by simp) leftParameterType)
              have tail := ih leftTailTyped rightTailTyped leftObjectParts.2
                rightObjectParts.2 leftSupported.2 rightSupported.2
                (fun argument membership =>
                  leftSmaller argument (by simp [membership]))
                (fun argument membership =>
                  rightSmaller argument (by simp [membership]))
                (fun {parameter} membership {expected} parameterType =>
                  parametersReachable (by simp [membership]) parameterType)
                (fun {parameter} membership {expected} parameterType =>
                  parametersCompatible (by simp [membership]) parameterType)
              exact .cons head tail

/-- Two selected Quotes whose typed process arguments do not canonically
expose Drop close by ordinary quoted congruence.  The arguments are compared
at quote-visible depth zero, while the outer apex retains its caller-selected
restoration depth. -/
theorem rhoQuoteNonDropApex
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {leftInner rightInner : Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {childDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) left →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right <
          sizeOf
              (Pattern.apply
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).quoteConstructor [leftInner]) +
            sizeOf
              (Pattern.apply
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).quoteConstructor [rightInner]) →
        rhoReachableType type = true →
        RhoApexDepthCompatible
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          type childDepth childDepth rootDepth →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth right))
    (leftTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [leftInner])
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (rightTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [rightInner])
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (leftObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [leftInner]) = true)
    (rightObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [rightInner]) = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [leftInner]))
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [rightInner]))
    (leftNotDrop : ∀ name, canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) leftInner ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (rightNotDrop : ∀ name, canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) rightInner ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [leftInner]) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [rightInner])) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [leftInner]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [rightInner])) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let allowed := fun constructor => ∃ sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  change (∀ name, canonicalize declaration leftInner ≠
    .apply declaration.dropConstructor [name]) at leftNotDrop
  change (∀ name, canonicalize declaration rightInner ≠
    .apply declaration.dropConstructor [name]) at rightNotDrop
  change canonicalize declaration
      (.apply declaration.quoteConstructor [leftInner]) =
    canonicalize declaration
      (.apply declaration.quoteConstructor [rightInner]) at canonical
  have leftInnerTyped :=
    rhoCostStatic_quote_inner_hasTypeWithConstructors color leftTyped
  have rightInnerTyped :=
    rhoCostStatic_quote_inner_hasTypeWithConstructors color rightTyped
  have leftInnerObject : isObjectPattern leftInner = true := by
    simpa [isObjectPattern, isObjectPatternList] using leftObject
  have rightInnerObject : isObjectPattern rightInner = true := by
    simpa [isObjectPattern, isObjectPatternList] using rightObject
  have leftInnerSupported : ConstructorsWithin allowed leftInner := by
    simpa [ConstructorsWithin, ConstructorListWithin] using
      leftSupported.2.1
  have rightInnerSupported : ConstructorsWithin allowed rightInner := by
    simpa [ConstructorsWithin, ConstructorListWithin] using
      rightSupported.2.1
  have leftOuterForm : canonicalize declaration
      (.apply declaration.quoteConstructor [leftInner]) =
        .apply declaration.quoteConstructor
          [canonicalize declaration leftInner] := by
    rw [canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    exact finishNormalizeReflectiveApply_quote_of_not_drop declaration
      leftNotDrop
  have rightOuterForm : canonicalize declaration
      (.apply declaration.quoteConstructor [rightInner]) =
        .apply declaration.quoteConstructor
          [canonicalize declaration rightInner] := by
    rw [canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    exact finishNormalizeReflectiveApply_quote_of_not_drop declaration
      rightNotDrop
  have innerCanonical : canonicalize declaration leftInner =
      canonicalize declaration rightInner := by
    have outerEquality := leftOuterForm.symm.trans
      (canonical.trans rightOuterForm)
    injection outerEquality with headEquality argumentsEquality
    exact (List.cons.inj argumentsEquality).1
  have recursiveMeasure : sizeOf leftInner + sizeOf rightInner <
      sizeOf (Pattern.apply declaration.quoteConstructor [leftInner]) +
        sizeOf (Pattern.apply declaration.quoteConstructor [rightInner]) := by
    have leftChild : sizeOf leftInner <
        sizeOf (Pattern.apply declaration.quoteConstructor [leftInner]) := by
      simp_wf
      omega
    have rightChild : sizeOf rightInner <
        sizeOf (Pattern.apply declaration.quoteConstructor [rightInner]) := by
      simp_wf
      omega
    omega
  have child := close (childDepth := 0) (rootDepth := 0)
    leftInnerTyped rightInnerTyped leftInnerObject rightInnerObject
    leftInnerSupported rightInnerSupported innerCanonical recursiveMeasure
    (by simp [rhoReachableType]) (Or.inr ⟨rfl, rfl⟩)
  change CommonRestorationApex rhoCIGSLT cospan declaration 0
    (canonicalizeByAt key declaration 0 leftInner)
    (canonicalizeByAt key declaration 0 rightInner) at child
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    simpa [declaration] using rhoCostStatic_quote_ne_drop color
  have leftKeyedNotDrop :=
    canonicalizeByAt_not_drop_of_canonicalize_not_drop key declaration
      quoteNeDrop leftNotDrop 0
  have rightKeyedNotDrop :=
    canonicalizeByAt_not_drop_of_canonicalize_not_drop key declaration
      quoteNeDrop rightNotDrop 0
  have leftKeyedForm : canonicalizeByAt key declaration leftDepth
      (.apply declaration.quoteConstructor [leftInner]) =
        .apply declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 leftInner] := by
    calc
      canonicalizeByAt key declaration leftDepth
          (.apply declaration.quoteConstructor [leftInner]) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 leftInner] := by
            simp [canonicalizeByAt, canonicalizeListByAt]
      _ = _ := finishNormalizeReflectiveApply_quote_of_not_drop declaration
        leftKeyedNotDrop
  have rightKeyedForm : canonicalizeByAt key declaration rightDepth
      (.apply declaration.quoteConstructor [rightInner]) =
        .apply declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 rightInner] := by
    calc
      canonicalizeByAt key declaration rightDepth
          (.apply declaration.quoteConstructor [rightInner]) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 rightInner] := by
            simp [canonicalizeByAt, canonicalizeListByAt]
      _ = _ := finishNormalizeReflectiveApply_quote_of_not_drop declaration
        rightKeyedNotDrop
  have quoteStatus : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor = true := by
    simpa [declaration] using rhoCostStatic_quote_isQuote color
  have arguments : CommonRestorationApexList rhoCIGSLT cospan declaration
      (if ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor
        then 0 else rootDepth)
      [canonicalizeByAt key declaration 0 leftInner]
      [canonicalizeByAt key declaration 0 rightInner] := by
    simpa [quoteStatus] using
      (CommonRestorationApexList.cons child
        (CommonRestorationApexList.nil 0))
  have quoted := CommonRestorationApex.apply declaration.quoteConstructor
    (depth := rootDepth) arguments
  exact CommonRestorationApex.reindex leftKeyedForm.symm
    rightKeyedForm.symm quoted

/-- A selected Quote whose typed process argument canonically exposes one
Drop closes by first recovering the unique raw Drop occurrence and then
recursing on its name payload.  This is the non-syntactic Quote/Drop arm:
parallel units and singleton wrappers may intervene inside the Quote, but
their occurrences are retained until the typed exposure theorem proves that
exactly one Drop remains. -/
theorem rhoQuoteCanonicalDropLeft
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {inner name right : Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {left : Pattern}
      {type : TypeExpr} {childDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) left →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right <
          sizeOf
              (Pattern.apply
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).quoteConstructor [inner]) +
            sizeOf right →
        rhoReachableType type = true →
        RhoApexDepthCompatible
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          type childDepth childDepth rootDepth →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth right))
    (leftTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [inner])
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (rightTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (leftObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [inner]) = true)
    (rightObject : isObjectPattern right = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor [inner]))
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      right)
    (innerCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) inner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).dropConstructor [name])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [inner]) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) right) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor [inner]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let allowed := fun constructor => ∃ sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  change canonicalize declaration inner =
    .apply declaration.dropConstructor [name] at innerCanonical
  change canonicalize declaration
      (.apply declaration.quoteConstructor [inner]) =
    canonicalize declaration right at canonical
  have innerTyped :=
    rhoCostStatic_quote_inner_hasTypeWithConstructors color leftTyped
  have innerObject : isObjectPattern inner = true := by
    simpa [isObjectPattern, isObjectPatternList] using leftObject
  have innerSupported : ConstructorsWithin allowed inner := by
    simpa [ConstructorsWithin, ConstructorListWithin] using
      leftSupported.2.1
  obtain ⟨rawName, leaves, _rawTyped, rawObject, rawSupported, rawCanonical⟩ :=
    rhoProc_canonical_drop_exposure key color innerTyped.toHasType innerObject
      innerSupported innerCanonical 0
  change parallelLeaves declaration inner =
    [.apply declaration.dropConstructor [rawName]] at leaves
  change canonicalize declaration rawName = name at rawCanonical
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    simpa [declaration] using rhoCostStatic_quote_ne_drop color
  have outerCanonical : canonicalize declaration
      (.apply declaration.quoteConstructor [inner]) = name := by
    calc
      canonicalize declaration
          (.apply declaration.quoteConstructor [inner]) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalize declaration inner] := by
            rw [canonicalize_apply_eq_finish]
            rfl
      _ =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) innerCanonical
      _ = name := finishNormalizeReflectiveApply_quote_drop declaration name
  have recursiveCanonical : canonicalize declaration rawName =
      canonicalize declaration right :=
    rawCanonical.trans (outerCanonical.symm.trans canonical)
  have rawMembership : .apply declaration.dropConstructor [rawName] ∈
      parallelLeaves declaration inner := by
    rw [leaves]
    simp
  have rawDropHereditary :=
    (rhoProc_parallelLeaves_typedWithConstructors color
      cospan.commonTargetFreeContext bound innerTyped).hasType_of_mem
      rawMembership
  have rawNameHereditary :=
    rhoCostStatic_drop_inner_hasTypeWithConstructors color rawDropHereditary
  have rawBound := parallelLeaves_size_le declaration inner
    (.apply declaration.dropConstructor [rawName]) rawMembership
  have recursiveMeasure : sizeOf rawName + sizeOf right <
      sizeOf (Pattern.apply declaration.quoteConstructor [inner]) +
        sizeOf right := by
    have rawNameChild : sizeOf rawName <
        sizeOf (Pattern.apply declaration.dropConstructor [rawName]) := by
      simp_wf
      omega
    have innerChild : sizeOf inner <
        sizeOf (Pattern.apply declaration.quoteConstructor [inner]) := by
      simp_wf
      omega
    omega
  have recursive := close (childDepth := 0) (rootDepth := rootDepth)
    rawNameHereditary rightTyped rawObject rightObject rawSupported rightSupported
    recursiveCanonical recursiveMeasure (by simp [rhoReachableType])
    (Or.inl rfl)
  have rightDepthIndependent :=
    canonicalizeByAt_depth_independent_of_typedNameWithin key color
      rightTyped.toHasType
      rfl rightObject rightSupported 0 rightDepth
  have recursiveAtRightDepth := CommonRestorationApex.reindex rfl
    rightDepthIndependent recursive
  have innerKeyed := rhoProc_canonicalizeByAt_eq_single_parallelLeaf key color
    innerTyped.toHasType leaves 0
  have dropKeyed : canonicalizeByAt key declaration 0
      (.apply declaration.dropConstructor [rawName]) =
        .apply declaration.dropConstructor
          [canonicalizeByAt key declaration 0 rawName] := by
    simp [canonicalizeByAt, canonicalizeListByAt, quoteNeDrop.symm]
  have leftKeyedCollapse : canonicalizeByAt key declaration leftDepth
      (.apply declaration.quoteConstructor [inner]) =
        canonicalizeByAt key declaration 0 rawName := by
    calc
      canonicalizeByAt key declaration leftDepth
          (.apply declaration.quoteConstructor [inner]) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 inner] := by
        simp [canonicalizeByAt, canonicalizeListByAt]
      _ =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0
            (.apply declaration.dropConstructor [rawName])] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) innerKeyed
      _ =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor
            [canonicalizeByAt key declaration 0 rawName]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) dropKeyed
      _ = canonicalizeByAt key declaration 0 rawName :=
        finishNormalizeReflectiveApply_quote_drop declaration _
  exact CommonRestorationApex.reindex leftKeyedCollapse.symm rfl
    recursiveAtRightDepth

/-- A selected-colour Quote/Drop shell closes by recursively comparing its
payload at quote-visible depth zero with the opposite endpoint.  Typing,
objecthood, and constructor support of the payload are derived from the
outer shell; the caller supplies only the well-founded closure for the
strictly smaller canonical pair. -/
theorem rhoQuoteDropLeft
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {inner right : Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {childDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) left →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right <
          sizeOf
              (Pattern.apply
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).quoteConstructor
                [Pattern.apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).dropConstructor [inner]]) +
            sizeOf right →
        rhoReachableType type = true →
        RhoApexDepthCompatible
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          type childDepth childDepth rootDepth →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth right))
    (leftTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]])
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (rightTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (leftObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) = true)
    (rightObject : isObjectPattern right = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]))
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      right)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).quoteConstructor
            [.apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).dropConstructor [inner]]) =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          right) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor
          [.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).dropConstructor [inner]]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  have declarationValid :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      rhoCIGSLT.costWholeAdmittedReflection.2 declarationMembership
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor :=
    quoteConstructor_ne_dropConstructor_of_validate
      rhoCIGSLT.costWholeLanguage declaration declarationValid
  have dropTyped :=
    rhoCostStatic_quote_inner_hasTypeWithConstructors color leftTyped
  have innerTyped :=
    rhoCostStatic_drop_inner_hasTypeWithConstructors color dropTyped
  have innerObject : isObjectPattern inner = true := by
    simpa [isObjectPattern, isObjectPatternList] using leftObject
  have innerSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      inner := by
    simpa [ConstructorsWithin, ConstructorListWithin] using
      leftSupported.2.1.2.1
  have innerCanonical : canonicalize declaration inner =
      canonicalize declaration right := by
    exact (canonicalize_quote_drop declaration quoteNeDrop.symm inner).symm.trans
      canonical
  have innerSmaller : sizeOf inner + sizeOf right <
      sizeOf
          (Pattern.apply declaration.quoteConstructor
            [Pattern.apply declaration.dropConstructor [inner]]) +
        sizeOf right := by
    simp_wf
    omega
  have innerApexAtZero := close (childDepth := 0)
    (rootDepth := rootDepth) innerTyped rightTyped innerObject rightObject
    innerSupported rightSupported innerCanonical innerSmaller
    (by simp [rhoReachableType]) (Or.inl rfl)
  have rightDepthIndependent :=
    canonicalizeByAt_depth_independent_of_typedNameWithin
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) color rightTyped.toHasType rfl
        rightObject rightSupported 0 rightDepth
  have innerApex := CommonRestorationApex.reindex rfl
    rightDepthIndependent innerApexAtZero
  exact CommonRestorationApex.of_quoteDrop_left cospan declaration quoteNeDrop
    innerApex

/-- Right-oriented companion of `rhoQuoteDropLeft`. -/
theorem rhoQuoteDropRight
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {left inner : Pattern}
    {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {childDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) left →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right <
          sizeOf left +
            sizeOf
              (Pattern.apply
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  ).quoteConstructor
              [Pattern.apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).dropConstructor [inner]]) →
        rhoReachableType type = true →
        RhoApexDepthCompatible
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          type childDepth childDepth rootDepth →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            childDepth right))
    (leftTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound left
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (rightTyped : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]])
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (leftObject : isObjectPattern left = true)
    (rightObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      left)
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]))
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          (.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).quoteConstructor
            [.apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).dropConstructor [inner]])) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor
          [.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).dropConstructor [inner]])) := by
  exact (rhoQuoteDropLeft cospan color
    (close := fun leftTyped rightTyped leftObject rightObject leftSupported
      rightSupported canonical smaller reachable compatible =>
        (close rightTyped leftTyped rightObject leftObject rightSupported
          leftSupported canonical.symm (by omega) reachable compatible).symm)
    rightTyped leftTyped rightObject leftObject rightSupported leftSupported
    canonical.symm).symm

/-- One non-collapsing typed rho layer lifts to the common restoration apex.
The recursive callback is used only on proper children.  Structural
collection fibres are excluded by `rhoReachableType`; the only base-typed
bare collection rule is PPar, which cannot occur in the nonparallel aligned
arm. -/
theorem rhoCanonicalRootAlignedWithin
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {parentLeft parentRight : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound left type →
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) left →
        ConstructorsWithin
            (fun constructor => exists sourceConstructor,
              decodeCostStaticConstructor color constructor =
                some sourceConstructor) right →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right < sizeOf parentLeft + sizeOf parentRight →
        rhoReachableType type = true →
        RhoApexDepthCompatible
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          type leftDepth rightDepth rootDepth →
        CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightDepth right))
    (leftHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound parentLeft type)
    (rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound parentRight type)
    (leftObject : isObjectPattern parentLeft = true)
    (rightObject : isObjectPattern parentRight = true)
    (admissible : rhoReachableType type = true)
    (compatible : RhoApexDepthCompatible
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      type leftDepth rightDepth rootDepth)
    (aligned : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      parentLeft parentRight) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth parentLeft)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth parentRight) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let leftTyped := leftHereditary.toHasType
  let rightTyped := rightHereditary.toHasType
  let leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      parentLeft :=
    leftHereditary.constructorsWithin.mono fun constructor included =>
      CostStaticColor.hereditaryConstructorImage_decodes rhoCIGSLT color
        constructor included
  let rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor = some sourceConstructor)
      parentRight :=
    rightHereditary.constructorsWithin.mono fun constructor included =>
      CostStaticColor.hereditaryConstructorImage_decodes rhoCIGSLT color
        constructor included
  cases aligned with
  | bvar index =>
      simpa [declaration, canonicalizeByAt] using
        (CommonRestorationApex.refl (source := rhoCIGSLT) cospan declaration rootDepth
          (.bvar index))
  | fvar name =>
      simpa [declaration, canonicalizeByAt] using
        (CommonRestorationApex.refl (source := rhoCIGSLT) cospan declaration rootDepth
          (.fvar name))
  | @apply constructor ne leftArguments rightArguments childrenCanonical =>
      obtain ⟨rule, membership, labelEq, notBare, typeEq, leftArgumentsTyped,
          rightArgumentsTyped⟩ :=
        hasType_apply_pair rho_costWholeLanguage_labelDeterministic leftTyped
          rightTyped
      subst constructor
      subst type
      obtain ⟨leftRule, _leftAllowed, leftMembership, leftLabel,
          _leftNotBare, _leftType, leftArgumentsHereditary⟩ :=
        hasTypeWithConstructors_apply_inversion leftHereditary
      have leftRuleEq : leftRule = rule :=
        rho_costWholeLanguage_labelDeterministic leftMembership membership
          leftLabel.symm
      subst leftRule
      obtain ⟨rightRule, _rightAllowed, rightMembership, rightLabel,
          _rightNotBare, _rightType, rightArgumentsHereditary⟩ :=
        hasTypeWithConstructors_apply_inversion rightHereditary
      have rightRuleEq : rightRule = rule :=
        rho_costWholeLanguage_labelDeterministic rightMembership membership
          rightLabel.symm
      subst rightRule
      have leftObjects : isObjectPatternList leftArguments = true := by
        simpa [isObjectPattern] using leftObject
      have rightObjects : isObjectPatternList rightArguments = true := by
        simpa [isObjectPattern] using rightObject
      have ordinaryDeclarationHead : rule.label ≠
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor := by
        simpa [declaration] using ne
      have ordinaryMappedHead : rule.label ≠
          (ReflectionExtension.mapReflectivePresentation
            (CostStaticColor.reflectiveSymbols rhoCIGSLT color)
            rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor := by
        simpa only [costStaticReflectivePresentationDecl_eq_map] using
          ordinaryDeclarationHead
      have declarationMembership : declaration ∈
          rhoCIGSLT.costWholeReflectionProfile.presentations := by
        simpa [declaration] using
          costStaticReflectivePresentationDecl_mem rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            (by
              change rhoReflectivePresentation.toReflectivePresentationDecl ∈
                ReflectionExtension.rhoReflectionProfile.presentations
              simp [ReflectionExtension.rhoReflectionProfile])
      have notName : (TypeExpr.base rule.category : TypeExpr) ≠
          .base declaration.nameSort := by
        intro equalType
        have categoryEquality : rule.category = declaration.nameSort :=
          TypeExpr.base.inj equalType
        have quoted :=
          CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
            declarationMembership rule membership categoryEquality
        exact ordinaryDeclarationHead
          (quote_eq_selected_of_decodesColor leftSupported.1 quoted.1)
      have synchronized : leftDepth = rootDepth ∧ rightDepth = rootDepth := by
        rcases compatible with sameName | synchronized
        · exact (notName sameName).elim
        · exact synchronized
      have quoteHeadFalse : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile rule.label = false :=
        Bool.eq_false_iff.mpr (fun quoted => ordinaryDeclarationHead
          (quote_eq_selected_of_decodesColor leftSupported.1 quoted))
      have arguments := rhoArguments cospan declaration
        (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
        (fun constructor => exists sourceConstructor,
          decodeCostStaticConstructor color constructor =
            some sourceConstructor)
        (.apply rule.label leftArguments) (.apply rule.label rightArguments)
        close leftArgumentsHereditary rightArgumentsHereditary
        leftObjects rightObjects
        leftSupported.2 rightSupported.2
        (by
          intro argument argumentMembership
          have argumentBound := List.sizeOf_lt_of_mem argumentMembership
          simp_wf
          omega)
        (by
          intro argument argumentMembership
          have argumentBound := List.sizeOf_lt_of_mem argumentMembership
          simp_wf
          omega)
        (by
          intro parameter parameterMembership expected parameterType
          exact rho_generatedParameter_reachable membership notBare
            parameterMembership parameterType)
        (by
          intro parameter parameterMembership expected parameterType
          exact Or.inr synchronized)
        childrenCanonical (leftDepth := leftDepth) (rightDepth := rightDepth)
        (rootDepth := rootDepth)
      have leftCanonical :
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              leftDepth (.apply rule.label leftArguments) =
            .apply rule.label
              (canonicalizeListByAt
                (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                leftDepth leftArguments) := by
        simp [canonicalizeByAt, ordinaryMappedHead]
      have rightCanonical :
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              rightDepth (.apply rule.label rightArguments) =
            .apply rule.label
              (canonicalizeListByAt
                (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                rightDepth rightArguments) := by
        simp [canonicalizeByAt, ordinaryMappedHead]
      rw [leftCanonical, rightCanonical]
      have argumentsAtVisibleDepth : CommonRestorationApexList rhoCIGSLT
          cospan declaration
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.costWholeReflectionProfile rule.label then 0
            else rootDepth)
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
            leftDepth leftArguments)
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
            rightDepth rightArguments) := by
        simpa [quoteHeadFalse] using arguments
      exact CommonRestorationApex.apply rule.label argumentsAtVisibleDepth
  | @lambda binder leftBody rightBody bodyCanonical =>
      obtain ⟨leftDomain, leftCodomain, leftTypeEq, leftBodyHereditary⟩ :=
        hasTypeWithConstructors_lambda_inversion leftHereditary
      obtain ⟨rightDomain, rightCodomain, rightTypeEq,
          rightBodyHereditary⟩ :=
        hasTypeWithConstructors_lambda_inversion rightHereditary
      have typeParts := TypeExpr.arrow.inj
        (leftTypeEq.symm.trans rightTypeEq)
      have domainEq : rightDomain = leftDomain := typeParts.1.symm
      have codomainEq : rightCodomain = leftCodomain := typeParts.2.symm
      subst rightDomain
      subst rightCodomain
      have synchronized : leftDepth = rootDepth ∧
          rightDepth = rootDepth := by
        rcases compatible with sameName | synchronized
        · rw [leftTypeEq] at sameName
          cases sameName
        · exact synchronized
      have childAdmissible : rhoReachableType leftCodomain = true := by
        rw [leftTypeEq] at admissible
        simpa [rhoReachableType] using admissible
      have body := close (leftDepth := leftDepth + 1)
        (rightDepth := rightDepth + 1)
        (rootDepth := rootDepth + 1) leftBodyHereditary
        rightBodyHereditary
        (by simpa [isObjectPattern] using leftObject)
        (by simpa [isObjectPattern] using rightObject)
        (by simpa using leftSupported)
        (by simpa using rightSupported) bodyCanonical (by
          have leftBound : sizeOf leftBody <
              sizeOf (Pattern.lambda binder leftBody) := by simp_wf
          have rightBound : sizeOf rightBody <
              sizeOf (Pattern.lambda binder rightBody) := by simp_wf
          exact Nat.add_lt_add leftBound rightBound)
        childAdmissible
        (Or.inr ⟨congrArg (fun depth => depth + 1) synchronized.1,
          congrArg (fun depth => depth + 1) synchronized.2⟩)
      exact .lambda binder body
  | @multiLambda arity binders leftBody rightBody bodyCanonical =>
      obtain ⟨leftDomain, leftCodomain, leftTypeEq, leftBodyHereditary⟩ :=
        hasTypeWithConstructors_multiLambda_inversion leftHereditary
      obtain ⟨rightDomain, rightCodomain, rightTypeEq,
          rightBodyHereditary⟩ :=
        hasTypeWithConstructors_multiLambda_inversion rightHereditary
      have typeParts := TypeExpr.arrow.inj
        (leftTypeEq.symm.trans rightTypeEq)
      have domainEq : rightDomain = leftDomain :=
        TypeExpr.multiBinder.inj typeParts.1 |>.symm
      have codomainEq : rightCodomain = leftCodomain := typeParts.2.symm
      subst rightDomain
      subst rightCodomain
      have synchronized : leftDepth = rootDepth ∧
          rightDepth = rootDepth := by
        rcases compatible with sameName | synchronized
        · rw [leftTypeEq] at sameName
          cases sameName
        · exact synchronized
      have childAdmissible : rhoReachableType leftCodomain = true := by
        rw [leftTypeEq] at admissible
        simpa [rhoReachableType] using admissible
      have body := close (leftDepth := leftDepth + arity)
        (rightDepth := rightDepth + arity)
        (rootDepth := rootDepth + arity) leftBodyHereditary
        rightBodyHereditary
        (by simpa [isObjectPattern] using leftObject)
        (by simpa [isObjectPattern] using rightObject)
        (by simpa using leftSupported)
        (by simpa using rightSupported) bodyCanonical (by
          have leftBound : sizeOf leftBody <
              sizeOf (Pattern.multiLambda arity binders leftBody) := by
            simp_wf
          have rightBound : sizeOf rightBody <
              sizeOf (Pattern.multiLambda arity binders rightBody) := by
            simp_wf
          exact Nat.add_lt_add leftBound rightBound)
        childAdmissible
        (Or.inr ⟨congrArg (fun depth => depth + arity) synchronized.1,
          congrArg (fun depth => depth + arity) synchronized.2⟩)
      exact .multiLambda binders body
  | subst bodyCanonical replacementCanonical =>
      simp [isObjectPattern] at leftObject
  | @collection collectionType ne leftElements rightElements
      childrenCanonical =>
      rcases hasType_collection_inversion leftTyped with
        ⟨elementType, typeEq, elementsTyped⟩ |
          ⟨rule, parameterName, elementType, membership, parameterShape,
            typeEq, elementsTyped⟩
      · rw [typeEq] at admissible
        exact (rhoCanonicalRecursiveTypeDomain.noCollection admissible).elim
      · rcases rho_collectionRule_cases membership parameterShape with
          ⟨parallelType, category, element⟩ |
          ⟨parallelType, category, element⟩
        all_goals
          have declarationParallel : declaration.parallelCollection =
              rhoReflectivePresentation.parallelCollection := by
            cases color <;> rfl
          exact (ne (parallelType.trans declarationParallel.symm)).elim
  | collectionRest collectionType rest childrenCanonical =>
      simp [isObjectPattern] at leftObject

/-- Every canonically equal, hereditarily typed pair in one generated rho
static colour has a common restoration apex.  The recursion is on the
symmetric raw endpoint size.  Aligned roots recurse through their authored
parameter spines; Quote/Drop and bare parallel roots use their dedicated
typed terminals. -/
theorem rhoCommonRestorationApex_of_canonicalWithin
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {parentLeft parentRight : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (leftHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound parentLeft type)
    (rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound parentRight type)
    (leftObject : isObjectPattern parentLeft = true)
    (rightObject : isObjectPattern parentRight = true)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        parentLeft =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        parentRight)
    (admissible : rhoReachableType type = true)
    (compatible : RhoApexDepthCompatible
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      type leftDepth rightDepth rootDepth) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth parentLeft)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth parentRight) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let allowed := fun constructor => exists sourceConstructor,
    decodeCostStaticConstructor color constructor = some sourceConstructor
  have leftSupported : ConstructorsWithin allowed parentLeft :=
    leftHereditary.constructorsWithin.mono fun constructor included =>
      CostStaticColor.hereditaryConstructorImage_decodes rhoCIGSLT color
        constructor included
  have rightSupported : ConstructorsWithin allowed parentRight :=
    rightHereditary.constructorsWithin.mono fun constructor included =>
      CostStaticColor.hereditaryConstructorImage_decodes rhoCIGSLT color
        constructor included
  have processNeName :
      (TypeExpr.base declaration.processSort : TypeExpr) ≠
        .base declaration.nameSort := by
    have interactingName :
        rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := by
      rfl
    cases color with
    | base =>
        have processSort : declaration.processSort =
            costBaseSortName "Proc" := by
          simp [declaration, costStaticReflectivePresentationDecl_eq_map,
            ReflectionExtension.mapReflectivePresentation,
            rhoReflectivePresentation, CostStaticColor.symbols,
            costBaseStaticSymbols, costBasePresentationSymbols]
        have nameSort : declaration.nameSort =
            costBaseSortName "Name" := by
          simp [declaration, costStaticReflectivePresentationDecl_eq_map,
            ReflectionExtension.mapReflectivePresentation,
            rhoReflectivePresentation, CostStaticColor.symbols,
            costBaseStaticSymbols, costBasePresentationSymbols]
        rw [processSort, nameSort]
        intro equality
        exact (show "Proc" ≠ "Name" by decide)
          (costBaseSortName_injective (TypeExpr.base.inj equality))
    | wrapped =>
        have processSort : declaration.processSort = costWrappedSortName := by
          simp [declaration, costStaticReflectivePresentationDecl_eq_map,
            ReflectionExtension.mapReflectivePresentation,
            rhoReflectivePresentation, CostStaticColor.symbols,
            costWrappedStaticSymbols, interactingName]
        have nameSort : declaration.nameSort =
            costBaseSortName "Name" := by
          simp [declaration, costStaticReflectivePresentationDecl_eq_map,
            ReflectionExtension.mapReflectivePresentation,
            rhoReflectivePresentation, CostStaticColor.symbols,
            costWrappedStaticSymbols, interactingName,
            show "Name" ≠ "Proc" by decide]
        rw [processSort, nameSort]
        intro equality
        exact costBaseSortName_ne_wrapped "Name"
          (TypeExpr.base.inj equality).symm
  let recur : forall {childBound : List TypeExpr}
      {left right : Pattern} {childType : TypeExpr}
      {childLeftDepth childRightDepth childRootDepth : Nat},
      HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext childBound left childType ->
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
          (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
          cospan.commonTargetFreeContext childBound right childType ->
        isObjectPattern left = true ->
        isObjectPattern right = true ->
        ConstructorsWithin allowed left ->
        ConstructorsWithin allowed right ->
        canonicalize declaration left = canonicalize declaration right ->
        sizeOf left + sizeOf right <
          sizeOf parentLeft + sizeOf parentRight ->
        rhoReachableType childType = true ->
        RhoApexDepthCompatible declaration childType childLeftDepth
          childRightDepth childRootDepth ->
        CommonRestorationApex rhoCIGSLT cospan declaration childRootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration childLeftDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration childRightDepth right) :=
    fun leftTyped rightTyped leftObject rightObject _leftSupported
      _rightSupported canonical smaller reachable compatible =>
        rhoCommonRestorationApex_of_canonicalWithin cospan color
          leftTyped rightTyped leftObject rightObject canonical reachable
          compatible
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · rcases leftCollapsing with quoted | parallel
    · obtain ⟨arguments, shape⟩ := quoted
      rw [shape] at leftHereditary leftObject leftSupported canonical ⊢
      obtain ⟨leftInner, argumentsEq, typeEq, _leftInnerTyped⟩ :=
        rhoCostStatic_quote_shapeWithConstructors color leftHereditary
      subst arguments
      subst type
      by_cases leftDrops : exists name,
          canonicalize declaration leftInner =
            .apply declaration.dropConstructor [name]
      · obtain ⟨name, innerCanonical⟩ := leftDrops
        exact rhoQuoteCanonicalDropLeft cospan color
          (close := fun leftTyped rightTyped leftObject rightObject
            _leftSupported _rightSupported canonical smaller reachable
            compatible =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by simp [declaration, shape] at smaller ⊢; omega)
                reachable compatible)
          leftHereditary rightHereditary leftObject rightObject
          leftSupported rightSupported innerCanonical canonical
      · have leftNotDrop : forall name,
            canonicalize declaration leftInner ≠
              .apply declaration.dropConstructor [name] := by
          intro name equality
          exact leftDrops ⟨name, equality⟩
        obtain ⟨rightInner, rightShape⟩ :=
          rhoCostStatic_name_eq_quote_of_canonical_quote_nonDrop color
            rightHereditary rfl rightObject rightSupported leftNotDrop canonical
        rw [rightShape] at rightHereditary rightObject rightSupported canonical ⊢
        by_cases rightDrops : exists name,
            canonicalize declaration rightInner =
              .apply declaration.dropConstructor [name]
        · obtain ⟨name, innerCanonical⟩ := rightDrops
          exact (rhoQuoteCanonicalDropLeft cospan color
            (close := fun leftTyped rightTyped leftObject rightObject
              _leftSupported _rightSupported canonical smaller reachable
              compatible =>
                recur leftTyped rightTyped leftObject rightObject
                  _leftSupported _rightSupported canonical
                  (by
                    simp [declaration, shape, rightShape] at smaller ⊢
                    omega)
                  reachable compatible)
            rightHereditary leftHereditary rightObject leftObject
            rightSupported leftSupported innerCanonical canonical.symm).symm
        · have rightNotDrop : forall name,
              canonicalize declaration rightInner ≠
                .apply declaration.dropConstructor [name] := by
            intro name equality
            exact rightDrops ⟨name, equality⟩
          exact rhoQuoteNonDropApex cospan color
            (close := fun leftTyped rightTyped leftObject rightObject
              _leftSupported _rightSupported canonical smaller reachable
              compatible =>
                recur leftTyped rightTyped leftObject rightObject
                  _leftSupported _rightSupported canonical
                  (by
                    simp [declaration, shape, rightShape] at smaller ⊢
                    omega)
                  reachable
                  compatible)
            leftHereditary rightHereditary leftObject rightObject
            leftSupported rightSupported leftNotDrop rightNotDrop canonical
    · obtain ⟨leftElements, shape⟩ := parallel
      rw [shape] at leftHereditary leftObject leftSupported canonical ⊢
      obtain ⟨typeEq, _leftElementsTyped⟩ :=
        rhoParallel_shapeWithConstructors color leftHereditary admissible
      subst type
      have synchronized : leftDepth = rootDepth ∧ rightDepth = rootDepth := by
        rcases compatible with sameName | synchronized
        · exact (processNeName sameName).elim
        · exact synchronized
      by_cases rightParallel : exists rightElements,
          parentRight = .collection declaration.parallelCollection
            rightElements none
      · obtain ⟨rightElements, rightShape⟩ := rightParallel
        rw [rightShape] at rightHereditary rightObject rightSupported canonical ⊢
        exact rhoBareParallelApex cospan color
          (close := fun leftTyped rightTyped _leftOrdinary _rightOrdinary
            leftObject rightObject _leftSupported _rightSupported canonical
            smaller =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by
                  simp [declaration, shape, rightShape] at smaller ⊢
                  omega)
                (by simp [rhoReachableType]) (Or.inr ⟨rfl, rfl⟩))
          leftHereditary rightHereditary leftHereditary.toHasType
          rightHereditary.toHasType leftObject rightObject leftSupported
          rightSupported canonical synchronized.1 synchronized.2
      · exact rhoBareParallelLeftApex cospan color
          (close := fun leftTyped rightTyped _leftOrdinary _rightOrdinary
            leftObject rightObject _leftSupported _rightSupported canonical
            smaller =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by simp [declaration, shape] at smaller ⊢; omega)
                (by simp [rhoReachableType]) (Or.inr ⟨rfl, rfl⟩))
          leftHereditary rightHereditary leftHereditary.toHasType
          rightHereditary.toHasType leftObject rightObject leftSupported
          rightSupported (fun elements equality =>
            rightParallel ⟨elements, equality⟩) canonical synchronized.1
          synchronized.2
  · rcases rightCollapsing with quoted | parallel
    · obtain ⟨arguments, shape⟩ := quoted
      rw [shape] at rightHereditary rightObject rightSupported canonical ⊢
      obtain ⟨rightInner, argumentsEq, typeEq, _rightInnerTyped⟩ :=
        rhoCostStatic_quote_shapeWithConstructors color rightHereditary
      subst arguments
      subst type
      by_cases rightDrops : exists name,
          canonicalize declaration rightInner =
            .apply declaration.dropConstructor [name]
      · obtain ⟨name, innerCanonical⟩ := rightDrops
        exact (rhoQuoteCanonicalDropLeft cospan color
          (close := fun leftTyped rightTyped leftObject rightObject
            _leftSupported _rightSupported canonical smaller reachable
            compatible =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by simp [declaration, shape] at smaller ⊢; omega)
                reachable
                compatible)
          rightHereditary leftHereditary rightObject leftObject
          rightSupported leftSupported innerCanonical canonical.symm).symm
      · have rightNotDrop : forall name,
            canonicalize declaration rightInner ≠
              .apply declaration.dropConstructor [name] := by
          intro name equality
          exact rightDrops ⟨name, equality⟩
        obtain ⟨leftInner, leftShape⟩ :=
          rhoCostStatic_name_eq_quote_of_canonical_quote_nonDrop color
            leftHereditary rfl leftObject leftSupported rightNotDrop
            canonical.symm
        rw [leftShape] at leftHereditary leftObject leftSupported canonical ⊢
        by_cases leftDrops : exists name,
            canonicalize declaration leftInner =
              .apply declaration.dropConstructor [name]
        · obtain ⟨name, innerCanonical⟩ := leftDrops
          exact rhoQuoteCanonicalDropLeft cospan color
            (close := fun leftTyped rightTyped leftObject rightObject
              _leftSupported _rightSupported canonical smaller reachable
              compatible =>
                recur leftTyped rightTyped leftObject rightObject
                  _leftSupported _rightSupported canonical
                  (by
                    simp [declaration, shape, leftShape] at smaller ⊢
                    omega)
                  reachable
                  compatible)
            leftHereditary rightHereditary leftObject rightObject
            leftSupported rightSupported innerCanonical canonical
        · have leftNotDrop : forall name,
              canonicalize declaration leftInner ≠
                .apply declaration.dropConstructor [name] := by
            intro name equality
            exact leftDrops ⟨name, equality⟩
          exact rhoQuoteNonDropApex cospan color
            (close := fun leftTyped rightTyped leftObject rightObject
              _leftSupported _rightSupported canonical smaller reachable
              compatible =>
                recur leftTyped rightTyped leftObject rightObject
                  _leftSupported _rightSupported canonical
                  (by
                    simp [declaration, shape, leftShape] at smaller ⊢
                    omega)
                  reachable
                  compatible)
            leftHereditary rightHereditary leftObject rightObject
            leftSupported rightSupported leftNotDrop rightNotDrop canonical
    · obtain ⟨rightElements, shape⟩ := parallel
      rw [shape] at rightHereditary rightObject rightSupported canonical ⊢
      obtain ⟨typeEq, _rightElementsTyped⟩ :=
        rhoParallel_shapeWithConstructors color rightHereditary admissible
      subst type
      have synchronized : leftDepth = rootDepth ∧ rightDepth = rootDepth := by
        rcases compatible with sameName | synchronized
        · exact (processNeName sameName).elim
        · exact synchronized
      by_cases leftParallel : exists leftElements,
          parentLeft = .collection declaration.parallelCollection
            leftElements none
      · obtain ⟨leftElements, leftShape⟩ := leftParallel
        rw [leftShape] at leftHereditary leftObject leftSupported canonical ⊢
        exact rhoBareParallelApex cospan color
          (close := fun leftTyped rightTyped _leftOrdinary _rightOrdinary
            leftObject rightObject _leftSupported _rightSupported canonical
            smaller =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by
                  simp [declaration, shape, leftShape] at smaller ⊢
                  omega)
                (by simp [rhoReachableType]) (Or.inr ⟨rfl, rfl⟩))
          leftHereditary rightHereditary leftHereditary.toHasType
          rightHereditary.toHasType leftObject rightObject leftSupported
          rightSupported canonical synchronized.1 synchronized.2
      · exact (rhoBareParallelLeftApex cospan color
          (close := fun leftTyped rightTyped _leftOrdinary _rightOrdinary
            leftObject rightObject _leftSupported _rightSupported canonical
            smaller =>
              recur leftTyped rightTyped leftObject rightObject
                _leftSupported _rightSupported canonical
                (by simp [declaration, shape] at smaller ⊢; omega)
                (by simp [rhoReachableType]) (Or.inr ⟨rfl, rfl⟩))
          rightHereditary leftHereditary rightHereditary.toHasType
          leftHereditary.toHasType rightObject leftObject rightSupported
          leftSupported (fun elements equality =>
            leftParallel ⟨elements, equality⟩) canonical.symm synchronized.2
          synchronized.1).symm
  · exact rhoCanonicalRootAlignedWithin cospan color
      (close := fun leftTyped rightTyped leftObject rightObject
        _leftSupported _rightSupported canonical smaller reachable compatible =>
          recur leftTyped rightTyped leftObject rightObject _leftSupported
            _rightSupported canonical smaller reachable compatible)
      leftHereditary rightHereditary leftObject rightObject admissible
      compatible aligned
termination_by sizeOf parentLeft + sizeOf parentRight
decreasing_by
  assumption

/-- A structurally aligned pair of actual atomized rho target frames lifts to
the recursive common-restoration apex.  Typing, object admissibility, and the
reachable result fibre are derived from the transported frame carriers; the
caller supplies only the well-founded recursive closures for proper
children. -/
theorem commonReifiedTargetFramesApex_of_rootAligned
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftTypeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (leftEnvironment.atomValue slot).key.sourceType =
        (leftEnvironment.atomValue slot).key.targetType)
    (rightTypeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (rightEnvironment.atomValue slot).key.sourceType =
        (rightEnvironment.atomValue slot).key.targetType)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount -> Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount -> Fin cospan.commonKeys.length)
    (leftCommutes : forall slot,
      cospan.commonKeys.get (leftLeg slot) =
        (leftEnvironment.atomValue slot).key)
    (rightCommutes : forall slot,
      cospan.commonKeys.get (rightLeg slot) =
        (rightEnvironment.atomValue slot).key)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : color.mapLangSort rhoCIGSLT leftNode.sourceSort =
      color.mapLangSort rhoCIGSLT rightNode.sourceSort)
    (close :
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan leftLeg leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan rightLeg rightCommutes
      forall {bound : List TypeExpr} {left right : Pattern}
        {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
            cospan.commonTargetFreeContext
            bound left type ->
          HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
            cospan.commonTargetFreeContext
            bound right type ->
          isObjectPattern left = true ->
          isObjectPattern right = true ->
          ConstructorsWithin
              (fun constructor => exists sourceConstructor,
                decodeCostStaticConstructor color constructor =
                  some sourceConstructor) left ->
          ConstructorsWithin
              (fun constructor => exists sourceConstructor,
                decodeCostStaticConstructor color constructor =
                  some sourceConstructor) right ->
          canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              left =
            canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              right ->
          sizeOf left + sizeOf right <
            sizeOf leftCommon.1.1 + sizeOf rightCommon.1.1 ->
          rhoReachableType type = true ->
          RhoApexDepthCompatible
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            type leftDepth rightDepth rootDepth ->
          CommonRestorationApex rhoCIGSLT cospan
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth
            (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              leftDepth left)
            (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              rightDepth right))
    (aligned :
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan leftLeg leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan rightLeg rightCommutes
      CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftCommon.1.1 rightCommon.1.1) :
    let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
      cospan leftLeg leftCommutes
    let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
      cospan rightLeg rightCommutes
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftNode.targetBound.length
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftNode.targetBound.length leftCommon.1.1)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightNode.targetBound.length rightCommon.1.1) := by
  let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
    cospan leftLeg leftCommutes
  let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
    cospan rightLeg rightCommutes
  let leftHereditary := commonReifiedTargetFrame_hereditaryTyped leftNode
    leftEnvironment cospan leftLeg leftCommutes leftTypeMap
  let rightHereditaryRaw := commonReifiedTargetFrame_hereditaryTyped rightNode
    rightEnvironment cospan rightLeg rightCommutes rightTypeMap
  let rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext leftNode.targetBound rightCommon.1.1
      (.base (color.mapLangSort rhoCIGSLT leftNode.sourceSort).1) :=
    rightHereditaryRaw.reindexBoundType sameBound.symm
      (congrArg (fun mapped => (.base mapped.1 : TypeExpr)) sameSort.symm)
  exact rhoCanonicalRootAlignedWithin cospan color close
    leftHereditary rightHereditary
    leftCommon.1.2.1.2.2.1 rightCommon.1.2.1.2.2.1
    rfl
    (Or.inr ⟨rfl, (congrArg List.length sameBound).symm⟩) aligned

/-- Canonically equal actual atomized rho target frames have a total common
restoration apex.  Unlike the older root-aligned interface, this theorem
contains the complete well-founded recursion: callers provide only the two
typed frame environments and their ordinary canonical equality. -/
theorem commonReifiedTargetFramesApex
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftTypeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (leftEnvironment.atomValue slot).key.sourceType =
        (leftEnvironment.atomValue slot).key.targetType)
    (rightTypeMap : forall slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (rightEnvironment.atomValue slot).key.sourceType =
        (rightEnvironment.atomValue slot).key.targetType)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount -> Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount -> Fin cospan.commonKeys.length)
    (leftCommutes : forall slot,
      cospan.commonKeys.get (leftLeg slot) =
        (leftEnvironment.atomValue slot).key)
    (rightCommutes : forall slot,
      cospan.commonKeys.get (rightLeg slot) =
        (rightEnvironment.atomValue slot).key)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : color.mapLangSort rhoCIGSLT leftNode.sourceSort =
      color.mapLangSort rhoCIGSLT rightNode.sourceSort)
    (canonical :
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan leftLeg leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan rightLeg rightCommutes
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftCommon.1.1 =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightCommon.1.1) :
    let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
      cospan leftLeg leftCommutes
    let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
      cospan rightLeg rightCommutes
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftNode.targetBound.length
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftNode.targetBound.length leftCommon.1.1)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightNode.targetBound.length rightCommon.1.1) := by
  let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
    cospan leftLeg leftCommutes
  let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
    cospan rightLeg rightCommutes
  let leftHereditary := commonReifiedTargetFrame_hereditaryTyped leftNode
    leftEnvironment cospan leftLeg leftCommutes leftTypeMap
  let rightHereditaryRaw := commonReifiedTargetFrame_hereditaryTyped rightNode
    rightEnvironment cospan rightLeg rightCommutes rightTypeMap
  let rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext leftNode.targetBound rightCommon.1.1
      (.base (color.mapLangSort rhoCIGSLT leftNode.sourceSort).1) :=
    rightHereditaryRaw.reindexBoundType sameBound.symm
      (congrArg (fun mapped => (.base mapped.1 : TypeExpr)) sameSort.symm)
  exact rhoCommonRestorationApex_of_canonicalWithin cospan color
    leftHereditary rightHereditary leftCommon.1.2.1.2.2.1
    rightCommon.1.2.1.2.2.1 canonical (by simp [rhoReachableType])
    (Or.inr ⟨rfl, (congrArg List.length sameBound).symm⟩)

/-- Transport a common-namespace apex on the raw atomized target frames to
the exact endpoint-canonical frames consumed by hereditary normalization.
The only change of endpoints is the already-proved naturality square for
semantic-key canonicalization; all occurrence identities remain in the two
finite endpoint inventories. -/
noncomputable def rootBridgeOfCommonReifiedTargetApex
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (apex :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      CommonRestorationApex rhoCIGSLT cospan declaration
        leftNode.targetBound.length
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration leftNode.targetBound.length
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.reifyTargetFrame leftEnvironment)))
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration rightNode.targetBound.length
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.reifyTargetFrame rightEnvironment)))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonRestorationApex leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have leftCovered : leftEnvironment.Covers
      (leftNode.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftNode.reifyTargetFrame_atomCovered leftEnvironment name membership
  have rightCovered : rightEnvironment.Covers
      (rightNode.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightNode.reifyTargetFrame_atomCovered rightEnvironment name membership
  have leftNaturality :=
    leftEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.leftSlot cospan.leftCommutes declaration
      leftNode.targetBound.length (leftNode.reifyTargetFrame leftEnvironment)
      leftCovered
  have rightNaturality :=
    rightEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.rightSlot cospan.rightCommutes declaration
      rightNode.targetBound.length (rightNode.reifyTargetFrame rightEnvironment)
      rightCovered
  exact CommonRestorationApex.reindex leftNaturality.symm
    rightNaturality.symm apex

/-- Close an aligned pair of actual same-colour static rho frames, assuming
only recursive apex evidence for strictly smaller typed children.  The
construction composes transported target typing, the rho root recursion, the
semantic-key naturality square, and the established hereditary restoration
eliminator. -/
noncomputable def rootBridgeOfCommonReifiedTargetRootAligned
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : color.mapLangSort rhoCIGSLT leftNode.sourceSort =
      color.mapLangSort rhoCIGSLT rightNode.sourceSort)
    (close :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan cospan.leftSlot cospan.leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan cospan.rightSlot cospan.rightCommutes
      forall {bound : List TypeExpr} {left right : Pattern}
        {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
        HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
            cospan.commonTargetFreeContext
            bound left type ->
          HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
            (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
            cospan.commonTargetFreeContext
            bound right type ->
          isObjectPattern left = true ->
          isObjectPattern right = true ->
          ConstructorsWithin
              (fun constructor => exists sourceConstructor,
                decodeCostStaticConstructor color constructor =
                  some sourceConstructor) left ->
          ConstructorsWithin
              (fun constructor => exists sourceConstructor,
                decodeCostStaticConstructor color constructor =
                  some sourceConstructor) right ->
          canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              left =
            canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              right ->
          sizeOf left + sizeOf right <
            sizeOf leftCommon.1.1 + sizeOf rightCommon.1.1 ->
          rhoReachableType type = true ->
          RhoApexDepthCompatible
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            type leftDepth rightDepth rootDepth ->
          CommonRestorationApex rhoCIGSLT cospan
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rootDepth
            (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              leftDepth left)
            (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              rightDepth right))
    (aligned :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan cospan.leftSlot cospan.leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan cospan.rightSlot cospan.rightCommutes
      CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftCommon.1.1 rightCommon.1.1) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rootBridgeOfCommonReifiedTargetApex leftNode rightNode leftChildren
    rightChildren (congrArg List.length sameBound)
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  exact commonReifiedTargetFramesApex_of_rootAligned leftNode rightNode
    leftEnvironment rightEnvironment
    (leftNode.semanticAtom_typeMap leftValues leftInventory)
    (rightNode.semanticAtom_typeMap rightValues rightInventory)
    cospan cospan.leftSlot
    cospan.rightSlot
    cospan.leftCommutes cospan.rightCommutes sameBound sameSort close aligned

/-- Close two actual same-colour static rho trees from canonical equality of
their atomized target frames.  All recursive Quote/Drop, binder, application,
and parallel cases are supplied by `rhoCommonRestorationApex_of_canonicalWithin`;
no recursive callback remains in this public bridge. -/
noncomputable def rootBridgeOfCommonReifiedTargetCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : color.mapLangSort rhoCIGSLT leftNode.sourceSort =
      color.mapLangSort rhoCIGSLT rightNode.sourceSort)
    (canonical :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let leftCommon := commonReifiedTargetFrame leftNode leftEnvironment
        cospan cospan.leftSlot cospan.leftCommutes
      let rightCommon := commonReifiedTargetFrame rightNode rightEnvironment
        cospan cospan.rightSlot cospan.rightCommutes
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftCommon.1.1 =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightCommon.1.1) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rootBridgeOfCommonReifiedTargetApex leftNode rightNode leftChildren
    rightChildren (congrArg List.length sameBound)
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  exact commonReifiedTargetFramesApex leftNode rightNode leftEnvironment
    rightEnvironment (leftNode.semanticAtom_typeMap leftValues leftInventory)
    (rightNode.semanticAtom_typeMap rightValues rightInventory) cospan
    cospan.leftSlot cospan.rightSlot cospan.leftCommutes cospan.rightCommutes
    sameBound sameSort canonical

/-- Assemble the aligned static/static pair directly from a common
restoration apex on the two actual atomized target frames.

This is the elimination boundary needed by plan-context recursion: recursive
work may construct the apex one retained context at a time, while this theorem
performs only dependent root reindexing and packages the resulting hereditary
tree alignment. -/
noncomputable def pairElaborationOfCommonReifiedTargetApex
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (apex :
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      CommonRestorationApex rhoCIGSLT cospan declaration
        leftView.node.targetBound.length
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration leftView.node.targetBound.length
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.reifyTargetFrame leftEnvironment)))
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration rightView.node.targetBound.length
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.reifyTargetFrame rightEnvironment)))) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  have sameBound : leftView.node.targetBound = rightView.node.targetBound :=
    leftView.targetBound_eq_targetBound rightView
  let bridge := rootBridgeOfCommonReifiedTargetApex
    (leftOuter := outer) (rightOuter := outer) leftView.node rightView.node
      leftView.children rightView.children (congrArg List.length sameBound)
      apex
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex rightView bridge).toTreeAlignment }

/-- The aligned static/static arm in the exact pair-closure shape.

The caller supplies only canonical equality of the two atomized target frames.
Binder and result-sort equality are recovered from the two static-root views,
and the resulting semantic bridge is transported back through their dependent
tree indices.  This is deliberately weaker than closing arbitrary preselected
trees: it constructs precisely the paired elaboration consumed by the
well-founded canonical-pair theorem. -/
noncomputable def pairElaborationOfCommonReifiedTargetCanonical
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (canonical :
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let leftCommon := commonReifiedTargetFrame leftView.node leftEnvironment
        cospan cospan.leftSlot cospan.leftCommutes
      let rightCommon := commonReifiedTargetFrame rightView.node
        rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftCommon.1.1 =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightCommon.1.1) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  have sameBound : leftView.node.targetBound = rightView.node.targetBound :=
    leftView.targetBound_eq_targetBound rightView
  have sameSort :
      color.mapLangSort rhoCIGSLT leftView.node.sourceSort =
        color.mapLangSort rhoCIGSLT rightView.node.sourceSort := by
    apply Subtype.ext
    exact TypeExpr.base.inj (leftView.typeEq.trans rightView.typeEq.symm)
  let bridge := rootBridgeOfCommonReifiedTargetCanonical
    (leftOuter := outer) (rightOuter := outer) leftView.node rightView.node
      leftView.children rightView.children sameBound sameSort canonical
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex rightView bridge).toTreeAlignment }

end RhoCommonRestorationApex

/-! ## Enclosing-frame semantic cuts

A collapsing Quote/Drop or singleton-parallel shell changes the typed fibre
at its hole.  Such a shell is therefore closed at the enclosing static root,
not by pretending that its reached child and the opposite endpoint form a
same-typed recursive pair.  Ordinary congruence remains available in the
non-collapsing arm, where both roots have one intrinsic static colour.
-/

/-- Canonical agreement of two actual same-colour static target frames after
their finite semantic-atom inventories have been embedded into one common
namespace.  This is the semantic datum consumed by the total rho apex
recursion; it is stronger than equality of the compact source endpoints and
weaker than a hereditary tree alignment. -/
def RhoMatchedStaticFramesCanonical
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    leftView.node leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
  let rightCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    rightView.node rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
  canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftCommon.1.1 =
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightCommon.1.1

/-- A parent-level restoration apex between the keyed common-reified target
frames of two same-colour static roots.  Collapsing branches carry this form:
their semantic rule closes at the enclosing root rather than descending into
a differently typed reached child. -/
abbrev RhoMatchedStaticFramesApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let leftCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    leftView.node leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
  let rightCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    rightView.node rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
  CommonRestorationApex rhoCIGSLT cospan declaration
    leftView.node.targetBound.length
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration leftView.node.targetBound.length leftCommon.1.1)
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration rightView.node.targetBound.length rightCommon.1.1)

namespace RhoMatchedStaticFramesApex

/-- Common-frame canonical equality constructs the parent-level apex. -/
noncomputable def ofCanonical
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (canonical : RhoMatchedStaticFramesCanonical leftView rightView) :
    RhoMatchedStaticFramesApex leftView rightView := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  exact RhoCommonRestorationApex.commonReifiedTargetFramesApex
    leftView.node rightView.node leftEnvironment rightEnvironment
    (leftView.node.semanticAtom_typeMap leftValues leftInventory)
    (rightView.node.semanticAtom_typeMap rightValues rightInventory)
    cospan cospan.leftSlot cospan.rightSlot cospan.leftCommutes
      cospan.rightCommutes
    (leftView.targetBound_eq_targetBound rightView)
    (by
      apply Subtype.ext
      exact TypeExpr.base.inj (leftView.typeEq.trans rightView.typeEq.symm))
    canonical

end RhoMatchedStaticFramesApex

/-- A proof-relevant cut between the keyed common-reified target frames of
two same-colour static roots.  Unlike bare canonical equality, this retains
the selected semantic cospan and every contextual restoration step used to
relate non-collapsing frames. -/
abbrev RhoMatchedStaticFramesCut
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color) : Type :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let leftCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    leftView.node leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
  let rightCommon := RhoCommonRestorationApex.commonReifiedTargetFrame
    rightView.node rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
  CommonRestorationCut rhoCIGSLT cospan declaration
    leftView.node.targetBound.length
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration leftView.node.targetBound.length leftCommon.1.1)
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration rightView.node.targetBound.length rightCommon.1.1)

namespace RhoMatchedStaticFramesCut

/-- Compatibility introduction from common-frame canonical equality.

The total rho apex construction performs the semantic recursion.  The cut is
terminal at the selected parent root, so a collapsing Quote/Drop shell is not
misrepresented as contextual descent into a differently typed child. -/
noncomputable def ofCanonical
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (canonical : RhoMatchedStaticFramesCanonical leftView rightView) :
    RhoMatchedStaticFramesCut leftView rightView :=
  .terminal (RhoMatchedStaticFramesApex.ofCanonical leftView rightView canonical)

end RhoMatchedStaticFramesCut

/-- Structural alignment of two possibly different-colour canonical frames,
with every selected semantic leaf required to agree under the common
supported assignment at every binder depth.

This is the direct generic restoration relation specialized to two actual rho
static views.  It is proof-relevant and strictly upstream of evaluator-result
equality: rigid constructors remain visible in `PatternLeafAligned`, while
only chosen leaves may use semantic restoration. -/
abbrev RhoStaticFramesRestorationAligned
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  PatternLeafAligned
    (fun leftLeaf rightLeaf =>
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            leftLeaf)
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            rightLeaf))
    (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
      (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
        rhoReflectivePresentation.toReflectivePresentationDecl))
    (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
      (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
        rhoReflectivePresentation.toReflectivePresentationDecl))

/-- Eliminate direct restoration alignment of two exposed static frames to
the paired hereditary elaboration on the original dependent tree indices. -/
noncomputable def pairElaborationOfRestorationAligned
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (alignment : RhoStaticFramesRestorationAligned leftView rightView) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ReflectiveContextSupport.RestoresTogether
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot leftLeaf)
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          rightLeaf)
  have canonicalFramesAligned : PatternLeafAligned relation
      (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl))
      (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation.toReflectivePresentationDecl)) := by
    exact alignment
  let bridge := rhoStaticRootBridgeOfRestoredPatternLeafAlignedCanonicalFrame
    (leftOuter := outer) (rightOuter := outer)
    leftView.node rightView.node leftView.children rightView.children
    (leftView.targetBound_length_eq_targetBound_length rightView)
    (relation := relation) canonicalFramesAligned (by
      dsimp only
      intro leftLeaf rightLeaf related depth
      exact related depth)
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex rightView bridge).toTreeAlignment }

/-- A proof-relevant semantic cut for one classified static pair.

The leaf-enclosing constructors retain a complete atom-or-rigid exposure at
the parent root.  The static-enclosing constructors cover the other genuine
collapsing shapes.  Same-colour endpoints use the total restoration apex;
different-colour endpoints retain equality only after their independently
canonicalized frames enter one common restored semantic namespace.  The
matched constructor is restricted to the root-aligned case.  Thus no
constructor asks a heterogeneous reached child to satisfy a fictitious
same-fibre recursive premise. -/
inductive RhoCanonicalStaticPairSemanticCut
    (declarationColor : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type) :
    RhoCanonicalStaticPairBridgeCase declarationColor left right → Type where
  | leftEnclosing
      {leftColor : CostStaticColor}
      (leftView : left.StaticRootView leftColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern)
      (exposure : RhoCollapsingLeafExposure leftView.node leftView.children
        right) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.leftCollapsing leftColor leftView collapsing)
  | leftStaticEnclosing
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern)
      (rightView : right.StaticRootView color)
      (apex : RhoMatchedStaticFramesApex leftView rightView) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.leftCollapsing color leftView collapsing)
  | leftCrossColorEnclosing
      {leftColor rightColor : CostStaticColor}
      (leftView : left.StaticRootView leftColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern)
      (rightView : right.StaticRootView rightColor)
      (different : leftColor ≠ rightColor)
      (restorations : RhoStaticFramesRestorationAligned leftView rightView) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.leftCollapsing leftColor leftView collapsing)
  | rightEnclosing
      {rightColor : CostStaticColor}
      (rightView : right.StaticRootView rightColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
      (exposure : RhoCollapsingLeafExposure rightView.node rightView.children
        left) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.rightCollapsing rightColor rightView collapsing)
  | rightStaticEnclosing
      {color : CostStaticColor}
      (rightView : right.StaticRootView color)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
      (leftView : left.StaticRootView color)
      (apex : RhoMatchedStaticFramesApex leftView rightView) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.rightCollapsing color rightView collapsing)
  | rightCrossColorEnclosing
      {leftColor rightColor : CostStaticColor}
      (rightView : right.StaticRootView rightColor)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
      (leftView : left.StaticRootView leftColor)
      (different : leftColor ≠ rightColor)
      (restorations : RhoStaticFramesRestorationAligned leftView rightView) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.rightCollapsing rightColor rightView collapsing)
  | matched
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color)
      (roots : CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern rightPattern)
      (cut : RhoMatchedStaticFramesCut leftView rightView) :
      RhoCanonicalStaticPairSemanticCut declarationColor left right
        (.aligned color leftView rightView roots)

namespace RhoCanonicalStaticPairSemanticCut

/-- Eliminate an enclosing-frame semantic cut to the exact paired
elaboration required by the well-founded static step.

Collapsing cuts either use the semantic-atom/rigid-leaf terminal or compare
two complete same-colour static frames at the enclosing root.  Root-aligned
cuts use that same total common-apex construction without changing the root
classification. -/
noncomputable def toPairElaboration
    {declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {rootCase : RhoCanonicalStaticPairBridgeCase declarationColor left right}
    (cut : RhoCanonicalStaticPairSemanticCut declarationColor left right
      rootCase) :
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  cases cut with
  | leftEnclosing leftView collapsing exposure =>
      exact exposure.toLeftPairElaboration left leftView right
  | leftStaticEnclosing leftView collapsing rightView apex =>
      exact
        RhoCommonRestorationApex.pairElaborationOfCommonReifiedTargetApex
          left right leftView rightView apex
  | leftCrossColorEnclosing leftView collapsing rightView different
      restorations =>
      exact pairElaborationOfRestorationAligned left right leftView rightView
        restorations
  | rightEnclosing rightView collapsing exposure =>
      exact exposure.toRightPairElaboration left right rightView
  | rightStaticEnclosing rightView collapsing leftView apex =>
      exact
        RhoCommonRestorationApex.pairElaborationOfCommonReifiedTargetApex
          left right leftView rightView apex
  | rightCrossColorEnclosing rightView collapsing leftView different
      restorations =>
      exact pairElaborationOfRestorationAligned left right leftView rightView
        restorations
  | matched leftView rightView roots frameCut =>
      exact RhoCommonRestorationApex.pairElaborationOfCommonReifiedTargetApex
        left right leftView rightView frameCut.toApex

end RhoCanonicalStaticPairSemanticCut

/-- Proof-relevant semantic-cut coverage for one rho static step.

Compared with `CostCanonicalStaticPairStepInDomain`, this interface retains
the two constructed trees, their exhaustive root classification, and the
chosen enclosing-or-matched semantic cut.  It is therefore a strictly more
informative construction target for the rho plan analysis: a collapsing
shell cannot be discharged by an opaque recursive child pair. -/
def RhoCanonicalStaticPairSemanticCutsInDomain
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    (CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) →
    (∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType rightChild →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftChild =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (CostCanonicalPairElaboration rhoCIGSLT
        rhoHereditaryNormalizationKernel targetFree childAvailable childOuter
        leftChild rightChild childType)) →
    Nonempty (Σ left : CostRegionTree rhoCIGSLT targetFree available outer
        leftPattern type,
      Σ right : CostRegionTree rhoCIGSLT targetFree available outer
        rightPattern type,
      Σ rootCase : RhoCanonicalStaticPairBridgeCase declarationColor left
        right,
        RhoCanonicalStaticPairSemanticCut declarationColor left right rootCase)

/-- The sole rho-specific producer obligation after generic tree construction
and exhaustive root classification.

This interface starts from the raw typed canonical pair and the strictly
smaller recursion supplied by `CostCanonicalStaticPairStepInDomain`.  The two
trees and their bridge case are already constructed data; the provider need
only choose the appropriate enclosing or matched semantic cut.  In
particular, no `CostStaticPlanEdge` or authored generator occurrence is an
input to this closure theorem. -/
def RhoCanonicalStaticPairSemanticCutProviderInDomain
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    (CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) →
    (∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType rightChild →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftChild =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (CostCanonicalPairElaboration rhoCIGSLT
        rhoHereditaryNormalizationKernel targetFree childAvailable childOuter
        leftChild rightChild childType)) →
    ∀ (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type)
      (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type)
      (rootCase : RhoCanonicalStaticPairBridgeCase declarationColor left
        right),
      Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
        rootCase)

namespace RhoCanonicalStaticPairSemanticCutsInDomain

/-- A classified cut provider covers the raw semantic-cut interface.

The construction of the two endpoint trees is total on well-sorted patterns,
and canonical equality plus one static root shape supplies the exhaustive
rho bridge case.  Hence the only language-specific content is the cut
returned by `provider`; no static-plan edge is synthesized or assumed. -/
theorem of_provider
    {declarationColor : CostStaticColor}
    (provider :
      RhoCanonicalStaticPairSemanticCutProviderInDomain declarationColor) :
    RhoCanonicalStaticPairSemanticCutsInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller
  let leftResult := CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := targetFree) available outer leftPattern type
  have leftSome : leftResult.isSome = true :=
    CostRegionTree.build?_isSome_of_wellSorted leftWellSorted
  let left := leftResult.get leftSome
  let rightResult := CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := targetFree) available outer rightPattern type
  have rightSome : rightResult.isSome = true :=
    CostRegionTree.build?_isSome_of_wellSorted rightWellSorted
  let right := rightResult.get rightSome
  obtain ⟨rootCase⟩ := nonempty_rhoCanonicalStaticPairBridgeCase
    declarationColor left right canonical staticShape
  obtain ⟨cut⟩ := provider admissible leftWellSorted rightWellSorted canonical
    staticShape closeSmaller left right rootCase
  exact ⟨⟨left, right, rootCase, cut⟩⟩

/-- Semantic-cut coverage discharges the generic well-founded static-step
interface while retaining its stronger branch discipline internally.

The conversion performs no semantic search: the provider has already chosen
an enclosing cut for collapsing roots or a matched cut for congruent roots;
`toPairElaboration` merely eliminates that certificate. -/
theorem toStaticPairStepInDomain
    {declarationColor : CostStaticColor}
    (cuts : RhoCanonicalStaticPairSemanticCutsInDomain declarationColor) :
    CostCanonicalStaticPairStepInDomain rhoCanonicalRecursiveTypeDomain
      rhoHereditaryNormalizationKernel
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl) := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller
  obtain ⟨⟨left, right, rootCase, cut⟩⟩ :=
    cuts admissible leftWellSorted rightWellSorted canonical staticShape
      closeSmaller
  exact ⟨cut.toPairElaboration⟩

/-- Direct raw-pair route from the sole rho cut provider to the generic
well-founded static step. -/
theorem toStaticPairStepInDomain_of_provider
    {declarationColor : CostStaticColor}
    (provider :
      RhoCanonicalStaticPairSemanticCutProviderInDomain declarationColor) :
    CostCanonicalStaticPairStepInDomain rhoCanonicalRecursiveTypeDomain
      rhoHereditaryNormalizationKernel
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl) :=
  toStaticPairStepInDomain (of_provider provider)

end RhoCanonicalStaticPairSemanticCutsInDomain

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
