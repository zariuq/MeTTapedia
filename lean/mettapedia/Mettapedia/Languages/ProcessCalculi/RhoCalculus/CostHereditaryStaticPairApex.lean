import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostEquationEndpointShape
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
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
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan

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
      have categoryEq : declaration.processSort = rule.category :=
        TypeExpr.base.inj typeEq
      have notQuote : rule.label ≠ declaration.quoteConstructor := by
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
          (beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2).trans
            selected.symm
        have sameRule : witness.quote = rule :=
          List.inj_on_of_nodup_map
            (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
              rhoCIGSLT.costWholeLanguage
              rhoCIGSLT.costWholeLanguage_validate)
            quoteMembership membership sameLabel
        exact witness.sortsDistinct (by
          calc
            declaration.processSort = rule.category := categoryEq
            _ = witness.quote.category :=
              congrArg GrammarRule.category sameRule.symm
            _ = declaration.nameSort := witness.quoteCategory)
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
  have leftElementsObject : isObjectPatternList leftElements = true := by
    simpa [isObjectPattern] using leftObject
  have rightElementsObject : isObjectPatternList rightElements = true := by
    simpa [isObjectPattern] using rightObject
  have leftLeavesTyped := rhoProc_parallelLeavesList_typed color
    cospan.commonTargetFreeContext bound leftElementsTyped
  have rightLeavesTyped := rhoProc_parallelLeavesList_typed color
    cospan.commonTargetFreeContext bound rightElementsTyped
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
    (allowed : String -> Prop)
    (parentLeft parentRight : Pattern)
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        ConstructorsWithin allowed left →
        ConstructorsWithin allowed right →
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
      ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage
          cospan.commonTargetFreeContext bound leftArguments parameters →
      ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage
          cospan.commonTargetFreeContext bound rightArguments parameters →
      isObjectPatternList leftArguments = true →
      isObjectPatternList rightArguments = true →
      ConstructorListWithin allowed leftArguments →
      ConstructorListWithin allowed rightArguments →
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
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
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
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
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
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
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
  have innerTyped := rho_costStatic_quoteDrop_inner_hasType color leftTyped
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
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) color rightTyped rfl
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
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
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
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound left
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).nameSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
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
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
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
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound parentLeft type)
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound parentRight type)
    (leftObject : isObjectPattern parentLeft = true)
    (rightObject : isObjectPattern parentRight = true)
    (leftSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor =
          some sourceConstructor)
      parentLeft)
    (rightSupported : ConstructorsWithin
      (fun constructor => exists sourceConstructor,
        decodeCostStaticConstructor color constructor =
          some sourceConstructor)
      parentRight)
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
        (fun constructor => exists sourceConstructor,
          decodeCostStaticConstructor color constructor =
            some sourceConstructor)
        (.apply rule.label leftArguments) (.apply rule.label rightArguments)
        close leftArgumentsTyped rightArgumentsTyped leftObjects rightObjects
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
      cases leftTyped with
      | lambda leftBodyTyped =>
          cases rightTyped with
          | lambda rightBodyTyped =>
              have synchronized : leftDepth = rootDepth ∧
                  rightDepth = rootDepth := by
                rcases compatible with sameName | synchronized
                · cases sameName
                · exact synchronized
              have body := close (leftDepth := leftDepth + 1)
                (rightDepth := rightDepth + 1)
                (rootDepth := rootDepth + 1) leftBodyTyped rightBodyTyped
                (by simpa [isObjectPattern] using leftObject)
                (by simpa [isObjectPattern] using rightObject)
                (by simpa using leftSupported)
                (by simpa using rightSupported) bodyCanonical (by
                  have leftBound : sizeOf leftBody <
                      sizeOf (Pattern.lambda binder leftBody) := by simp_wf
                  have rightBound : sizeOf rightBody <
                      sizeOf (Pattern.lambda binder rightBody) := by simp_wf
                  exact Nat.add_lt_add leftBound rightBound)
                (by simpa [rhoReachableType] using admissible)
                (Or.inr ⟨congrArg (fun depth => depth + 1) synchronized.1,
                  congrArg (fun depth => depth + 1) synchronized.2⟩)
              exact .lambda binder body
  | @multiLambda arity binders leftBody rightBody bodyCanonical =>
      cases leftTyped with
      | multiLambda leftBodyTyped =>
          cases rightTyped with
          | multiLambda rightBodyTyped =>
              have synchronized : leftDepth = rootDepth ∧
                  rightDepth = rootDepth := by
                rcases compatible with sameName | synchronized
                · cases sameName
                · exact synchronized
              have body := close (leftDepth := leftDepth + arity)
                (rightDepth := rightDepth + arity)
                (rootDepth := rootDepth + arity) leftBodyTyped rightBodyTyped
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
                (by simpa [rhoReachableType] using admissible)
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
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
            bound left type ->
          HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
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
  let rightReindexed := rightCommon.1.reindex rfl sameBound.symm sameSort.symm
  let rightTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext leftNode.targetBound rightCommon.1.1
      (.base (color.mapLangSort rhoCIGSLT leftNode.sourceSort).1) :=
    WellSorted.HasType.transportPattern
      (ReflectiveWellSorted.OpenTerm.reindex_pattern rfl sameBound.symm
        sameSort.symm rightCommon.1)
      rightReindexed.2.1.1
  exact rhoCanonicalRootAlignedWithin cospan color close
    leftCommon.1.2.1.1 rightTyped
    leftCommon.1.2.1.2.2.1 rightCommon.1.2.1.2.2.1
    (commonReifiedTargetFrame_constructorsWithinColor leftNode
      leftEnvironment cospan leftLeg leftCommutes)
    (commonReifiedTargetFrame_constructorsWithinColor rightNode
      rightEnvironment cospan rightLeg rightCommutes) rfl
    (Or.inr ⟨rfl, (congrArg List.length sameBound).symm⟩) aligned

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
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
            bound left type ->
          HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
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
    leftEnvironment rightEnvironment cospan cospan.leftSlot
    cospan.rightSlot
    cospan.leftCommutes cospan.rightCommutes sameBound sameSort close aligned

end RhoCommonRestorationApex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
