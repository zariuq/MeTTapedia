import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryTreeAvailabilityTransposition

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier

/-- Hereditary normalization preserves closure of an object even when its
tree was constructed with additional ambient availability.  The proof moves
that availability out of the active context, normalizes the resulting closed
tree, and uses availability-suffix invariance to return to the original
tree. -/
theorem CostRegionTree.normalize_pattern_isWellScopedAt_zero
    {targetFree : FreeTypeContext} {available : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available [] pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true)
    (reflective : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile available.length pattern)
    (closed : pattern.isWellScopedAt 0 = true) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern.isWellScopedAt
        0 = true := by
  have closedTyped : HasType rhoCIGSLT.costWholeLanguage targetFree [] pattern
      type := by
    have checkedAtAvailable : checkHasType rhoCIGSLT.costWholeLanguage
        targetFree available pattern type = true := by
      apply checkHasType_complete_of_object
      · simpa only [List.append_nil] using tree.originalTyped
      · exact object
    have contextInvariant := checkHasType_append_outer_eq_of_scoped
      (language := rhoCIGSLT.costWholeLanguage) (free := targetFree)
      (inner := []) (outer := available) (type := type) object closed
    have checkedClosed : checkHasType rhoCIGSLT.costWholeLanguage targetFree []
        pattern type = true := by
      rw [← contextInvariant]
      simpa only [List.nil_append] using checkedAtAvailable
    exact checkHasType_sound checkedClosed
  have closedReflective : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile 0 pattern := by
    intro presentation membership
    exact binderSafeAt_of_isWellScopedAt_of_binderSafeAt
      presentation.quoteConstructor closed
        (reflective presentation membership) (Nat.zero_le _)
  have closedWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] type pattern :=
    ⟨⟨closedTyped, canonical, object, closedTyped.isWellScopedAt⟩,
      closedReflective⟩
  let closedTree : CostRegionTree rhoCIGSLT targetFree [] [] pattern type :=
    (CostRegionTree.build? [] [] pattern type).get
      (CostRegionTree.build?_isSome_of_wellSorted closedWellSorted)
  have normalizedEq :
      (closedTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
      (smallAvailable := []) (largeAvailable := available)
        (ambient := available) (by simp) closedTree tree rfl rfl object
  have closedNormal :=
    (closedTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).typed.isWellScopedAt
  rw [normalizedEq] at closedNormal
  simpa only [List.nil_append, List.length_nil] using closedNormal

/-- A certified rho boundary in the authored name fibre is closed at the
quotation reset depth.  Generated name applications are reflective quotes,
so their typed argument spine is scoped independently of the ambient binder
prefix. -/
theorem rho_boundaryNamePlan_pattern_isWellScopedAt_zero
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (sourceTypeName : sourceType = .base "Name")
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) :
    pattern.isWellScopedAt 0 = true := by
  cases plan with
  | bvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | fvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | application =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | lambda => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | multiLambda =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      rename_i wireName arguments
      have mappedName : mapTypeExpr (color.symbols rhoCIGSLT)
          (.base "Name") = .base (costBaseSortName "Name") := by
        cases color <;> rfl
      have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
          sourceAvailable (.apply wireName arguments)
          (.base (costBaseSortName "Name")) := by
        have contentTyped := certified.typed.contentTyped
        rw [certified.content_eq, certified.targetSupport_eq,
          certified.targetType_eq, sourceTypeName, mappedName] at contentTyped
        exact contentTyped
      obtain ⟨rule, membership, label, _notBare, typeEq,
          argumentsTyped⟩ := hasType_apply_inversion typed
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
      have declarationMembership : declaration ∈
          rhoCIGSLT.costWholeReflectionProfile.presentations := by
        simpa only [declaration] using
          CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile .base
      have categoryEquality : rule.category = declaration.nameSort := by
        have categoryEquality := (TypeExpr.base.inj typeEq).symm
        change rule.category = costBaseSortName "Name"
        exact categoryEquality
      have quoted : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile rule.label = true :=
        (CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
          declarationMembership rule membership categoryEquality).1
      have scopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
          rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
          (.apply rule.label arguments) := by
        simpa only [label, certified.content_eq,
          certified.targetSupport_eq] using
            certified.typed.contentReflectiveScopeSafe
      have argumentsAtZero :=
        WellSorted.isWellScopedListAt_zero_of_typed_quote
          rhoCIGSLT.costWholeLanguage_validate
          rhoCIGSLT.costWholeReflectionProfile_validate membership
          argumentsTyped quoted scopeSafe
      simpa only [Pattern.isWellScopedAt] using argumentsAtZero
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact False.elim
        (rho_boundaryCollection_choices_absurd color targetFree targetBound
          _ _ _ oppositeSelected currentRejected)

/-- A typed rho boundary application in the authored name fibre is closed at
the quotation reset depth.  This entry-level form only assumes the table's
type-map equation, so it applies to a positionally selected boundary child. -/
theorem rho_typedBoundary_nameApplication_content_isWellScopedAt_zero
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
    (typeMap : mapTypeExpr (color.symbols rhoCIGSLT)
      boundary.boundary.type = boundary.boundary.targetType)
    (sourceTypeName : boundary.boundary.type = .base "Name")
    {wireName : String} {arguments : List Pattern}
    (content : boundary.boundary.content = .apply wireName arguments) :
    boundary.boundary.content.isWellScopedAt 0 = true := by
  have mappedName : mapTypeExpr (color.symbols rhoCIGSLT)
      (.base "Name") = .base (costBaseSortName "Name") := by
    cases color <;> rfl
  have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
      boundary.boundary.targetSupport (.apply wireName arguments)
      (.base (costBaseSortName "Name")) := by
    have contentTyped := boundary.contentTyped
    rw [content, ← typeMap, sourceTypeName, mappedName] at contentTyped
    exact contentTyped
  obtain ⟨rule, membership, label, _notBare, typeEq,
      argumentsTyped⟩ := hasType_apply_inversion typed
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa only [declaration] using
      CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile .base
  have categoryEquality : rule.category = declaration.nameSort := by
    have categoryEquality := (TypeExpr.base.inj typeEq).symm
    change rule.category = costBaseSortName "Name"
    exact categoryEquality
  have quoted : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile rule.label = true :=
    (CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
      declarationMembership rule membership categoryEquality).1
  have scopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile
        boundary.boundary.targetSupport.length
        (.apply rule.label arguments) := by
    simpa only [label, content] using boundary.contentReflectiveScopeSafe
  have argumentsAtZero :=
    WellSorted.isWellScopedListAt_zero_of_typed_quote
      rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate membership
      argumentsTyped quoted scopeSafe
  rw [content]
  simpa only [Pattern.isWellScopedAt] using argumentsAtZero

@[simp]
theorem decodeCostBaseSortName_wrapped_eq_none :
    decodeCostBaseSortName costWrappedSortName = none := by
  cases decoded : decodeCostBaseSortName costWrappedSortName with
  | none => rfl
  | some sourceName =>
      have encoded : costWrappedSortName = costBaseSortTag ++ sourceName :=
        (decodeTaggedPayload_eq_some_iff costBaseSortTag costWrappedSortName
          sourceName).mp (by
            simpa only [decodeCostBaseSortName] using decoded)
      exact False.elim
        (costBaseSortName_ne_wrapped sourceName (by
          simpa only [costBaseSortName] using encoded.symm))

@[simp]
theorem decodeCostBaseSortName_apparatus_eq_none (kind : String) :
    decodeCostBaseSortName (costApparatusSortName kind) = none := by
  cases decoded : decodeCostBaseSortName (costApparatusSortName kind) with
  | none => rfl
  | some sourceName =>
      have encoded : costApparatusSortName kind =
          costBaseSortTag ++ sourceName :=
        (decodeTaggedPayload_eq_some_iff costBaseSortTag
          (costApparatusSortName kind) sourceName).mp (by
            simpa only [decodeCostBaseSortName] using decoded)
      exact False.elim
        (costBaseSortName_ne_apparatus sourceName kind (by
          simpa only [costBaseSortName] using encoded.symm))

@[simp]
theorem costApparatusSortName_ne_wrapped (kind : String) :
    costApparatusSortName kind ≠ costWrappedSortName :=
  (costWrappedSortName_ne_apparatus kind).symm

/-- A typed rho boundary application drawn from a coherent static table can
only have one of rho's two authored source result types. -/
theorem rho_typedBoundary_application_sourceType_name_or_proc
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
    (typeMap : mapTypeExpr (color.symbols rhoCIGSLT)
      boundary.boundary.type = boundary.boundary.targetType)
    {wireName : String} {arguments : List Pattern}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (content : boundary.boundary.content = .apply wireName arguments) :
    boundary.boundary.type = .base "Name" ∨
      boundary.boundary.type = .base "Proc" := by
  have interactingSort :
      rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := rfl
  have contentTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      boundary.boundary.targetSupport (.apply wireName arguments)
        (mapTypeExpr (color.symbols rhoCIGSLT) boundary.boundary.type) := by
    have typed := boundary.contentTyped
    rw [content, ← typeMap] at typed
    exact typed
  obtain ⟨rule, membership, label, _notBare, typeEq, _argumentsTyped⟩ :=
    hasType_apply_inversion contentTyped
  have coreMembership : rule ∈ rhoCIGSLT.costCoreLanguage.terms := by
    simpa only [rhoCIGSLT.costWholeLanguage_terms] using membership
  obtain ⟨typedConstructor, materializes⟩ :=
    rhoCIGSLT.exists_declaredCostConstructor_of_mem rule coreMembership
  have renderedRule :
      rhoCIGSLT.renderDeclaredCostConstructor typedConstructor = wireName := by
    calc
      rhoCIGSLT.renderDeclaredCostConstructor typedConstructor =
          (rhoCIGSLT.materializeDeclaredCostConstructor typedConstructor).label :=
        (rhoCIGSLT.materializeDeclaredCostConstructor_label
          typedConstructor).symm
      _ = rule.label := congrArg GrammarRule.label materializes
      _ = wireName := label.symm
  have constructorEq : typedConstructor = constructor :=
    rhoCIGSLT.renderDeclaredCostConstructor_injective
      (renderedRule.trans rendered.symm)
  subst typedConstructor
  have mappedTypeEq : mapTypeExpr (color.symbols rhoCIGSLT)
      boundary.boundary.type =
        .base (rhoCIGSLT.materializeDeclaredCostConstructor constructor).category := by
    exact typeEq.trans
      (congrArg (fun materialized => TypeExpr.base materialized.category)
        materializes.symm)
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor =>
      rcases rho_rule_category_name_or_proc sourceConstructor.2 with
          category | category
      · left
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costBaseConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
      · right
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costBaseConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
  | wrapped sourceConstructor =>
      rcases rho_rule_category_name_or_proc sourceConstructor.2 with
          category | category
      · left
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
      · right
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, category, decodeCostStaticTypeExpr,
            interactingSort] at decoded
        all_goals exact decoded
  | apparatus kind =>
      have decoded := congrArg
        (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
      rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
      right
      cases color <;> cases kind <;>
        simp [CIGSLT.materializeDeclaredCostConstructor,
          CostApparatusConstructor.grammarRule, decodeCostStaticTypeExpr,
          costSignatureSortName,
          costTokenStackSortName, costSignatureUnitConstructor,
          costSignatureProductConstructor, costSignedConstructor,
          costTokenStackEmptyConstructor, costTokenStackConsConstructor,
          costFundingConstructor, costContactConstructor,
          interactingSort] at decoded
      all_goals exact decoded

/-- The normalized value of a positionally selected rho name boundary is
closed at depth zero.  Application entries use quotation sealing; collection
entries are excluded by rho's cross-colour collection gate. -/
theorem rho_boundaryTreeEntry_name_normal_isWellScopedAt_zero
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (index : Fin node.finiteBoundaryTable.entries.length)
    (sourceTypeName : (trees.getEntry index).boundary.boundary.type =
      .base "Name") :
    ((trees.getEntry index).tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern.isWellScopedAt
        0 = true := by
  let entry := trees.getEntry index
  have membership : entry.boundary ∈ node.plan.boundaryTable.entries := by
    exact trees.getEntry_mem index
  have typeMap := node.plan.boundaryTable_fiberCoherent.typeMap
    entry.boundary membership
  have kind := node.plan.boundaryKind_of_mem_entries entry.boundary membership
  cases kind with
  | application constructor rendered outsideCurrent content =>
      apply CostRegionTree.normalize_pattern_isWellScopedAt_zero
        entry.tree entry.boundary.contentCanonicalBinderMetadata
          entry.boundary.contentObjectPattern
            entry.boundary.contentReflectiveScopeSafe
      exact rho_typedBoundary_nameApplication_content_isWellScopedAt_zero
        entry.boundary typeMap sourceTypeName content
  | collection currentRejected oppositeChoice oppositeSelected content =>
      exact False.elim
        (rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          oppositeSelected currentRejected)

/-- The normalized value of a positionally selected rho process boundary
retains the rendered head of its outside-current declared constructor. -/
theorem rho_boundaryTreeEntry_proc_normal_application
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (index : Fin node.finiteBoundaryTable.entries.length)
    (sourceTypeProc : (trees.getEntry index).boundary.boundary.type =
      .base "Proc") :
    ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    ∃ wire normalizedArguments,
      rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color ∧
      ((trees.getEntry index).tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .apply wire normalizedArguments := by
  let entry := trees.getEntry index
  have membership : entry.boundary ∈ node.plan.boundaryTable.entries := by
    exact trees.getEntry_mem index
  have typeMap := node.plan.boundaryTable_fiberCoherent.typeMap
    entry.boundary membership
  have kind := node.plan.boundaryKind_of_mem_entries entry.boundary membership
  cases kind with
  | application constructor rendered outsideCurrent content =>
      rename_i wire arguments
      have targetTypeEq : entry.boundary.boundary.targetType =
          mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") := by
        exact typeMap.symm.trans
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeProc)
      let processTree :=
        (entry.tree.reindexPattern content).reindexType targetTypeEq
      have structural : processTree.rootIsStatic = false := by
        by_contra notStructural
        have static : processTree.rootIsStatic = true :=
          Bool.eq_true_of_not_eq_false notStructural
        obtain ⟨treeColor, view⟩ :=
          processTree.staticRootView_of_rootIsStatic static
        have colorEq : treeColor = color := by
          by_contra different
          have flipEq : treeColor = color.flip :=
            CostStaticColor.eq_flip_of_ne (Ne.symm different)
          subst treeColor
          apply mapTypeExpr_flipProc_ne color.flip
            (.base view.node.sourceSort.1)
          simpa [CostStaticColor.mapLangSort_name, mapTypeExpr] using
            view.typeEq.symm
        subst treeColor
        obtain ⟨currentConstructor, decoded, current⟩ :=
          view.node.plan.application_dispatch_of_isStaticRoot
            view.node.rootStatic view.patternEq
        have currentRendered :
            rhoCIGSLT.renderDeclaredCostConstructor currentConstructor =
              wire :=
          rhoCIGSLT.renderDeclaredCostConstructor_eq_of_decode wire
            currentConstructor decoded
        have constructorEq : constructor = currentConstructor :=
          rhoCIGSLT.renderDeclaredCostConstructor_injective
            (rendered.trans currentRendered.symm)
        subst currentConstructor
        exact outsideCurrent current
      obtain ⟨normalizedArguments, processNormal⟩ :=
        ParallelFrontier.CostRegionTree.exists_normalize_pattern_eq_apply_of_structural
          processTree structural
      have normalUnchanged :
          (processTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (entry.tree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
        simp [processTree, CostRegionTree.reindexType_normalize,
          CostRegionTree.reindexPattern_normalize]
      exact ⟨constructor, wire, normalizedArguments, rendered,
        outsideCurrent, normalUnchanged.symm.trans processNormal⟩
  | collection currentRejected oppositeChoice oppositeSelected content =>
      exact False.elim
        (rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          oppositeSelected currentRejected)

/-- Hereditary normalization of a certified rho name boundary cannot expose
an ambient bound variable: the boundary is closed at its quotation reset and
normalization preserves that closure. -/
theorem rho_boundaryNamePlan_normalize_pattern_isWellScopedAt_zero
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType targetType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (sourceTypeName : sourceType = .base "Name")
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (tree : CostRegionTree rhoCIGSLT targetFree sourceAvailable [] pattern
      targetType)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true)
    (reflective : ReflectiveWellSorted.ReflectiveScopeSafeAt
      rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length pattern) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern.isWellScopedAt
        0 = true := by
  apply CostRegionTree.normalize_pattern_isWellScopedAt_zero tree canonical
    object reflective
  exact rho_boundaryNamePlan_pattern_isWellScopedAt_zero plan sourceTypeName
    boundaryClass

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
