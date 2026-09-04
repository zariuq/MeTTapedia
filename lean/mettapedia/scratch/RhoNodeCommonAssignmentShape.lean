import scratch.RhoSemanticAtomClassification
import scratch.SemanticFrameRestorationInversion
import scratch.ExactNonBoundaryCrossTieCanary
import scratch.CommonCospanAtomRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.GSLT.LanguageDef.CostStaticPlanProvenancedReification

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- A wire name belongs to the selected colour's declared static image. -/
def RhoCurrentStaticHead (color : CostStaticColor) (wire : String) : Prop :=
  ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor = .static color

/-- Every authored constructor retained by rho's continuation fragment maps
to a declared constructor in the selected static colour. -/
theorem rho_currentStaticHead_symbols_of_mem_wrappedLabels
    (color : CostStaticColor) {label : String}
    (membership : label ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) :
    RhoCurrentStaticHead color
      ((color.symbols rhoCIGSLT).constructor label) := by
  change label ∈
      rhoCIGSLT.continuationRetyping.wrappedConstructors.map
        (fun constructor => constructor.1.label) at membership
  obtain ⟨authored, wrapped, labelEq⟩ := List.mem_map.mp membership
  cases color with
  | base =>
      let constructor : rhoCIGSLT.DeclaredCostConstructor :=
        ⟨.base authored, True.intro⟩
      refine ⟨constructor, ?_, ?_⟩
      · change costBaseConstructorName authored.1.label =
          costBaseConstructorName label
        exact congrArg costBaseConstructorName labelEq
      · rcases (rhoCIGSLT.continuationRetyping.mem_wrappedConstructors_iff
          authored).mp wrapped with ⟨notProgram, notEnvironment⟩
        exact rhoCIGSLT.declaredCostConstructorRole_base_of_nonprincipal
          authored notProgram notEnvironment
  | wrapped =>
      let constructor : rhoCIGSLT.DeclaredCostConstructor :=
        ⟨.wrapped authored, wrapped⟩
      refine ⟨constructor, ?_, ?_⟩
      · change costWrappedConstructorName authored.1.label =
          costWrappedConstructorName label
        exact congrArg costWrappedConstructorName labelEq
      · exact rhoCIGSLT.declaredCostConstructorRole_wrapped authored wrapped

/-- The constructors which reflective canonicalization may erase or insert
all belong to the selected rho static image. -/
theorem rho_currentStaticHead_reflectiveConstructorsAllowed
    (color : CostStaticColor) :
    ReflectiveConstructorsAllowed (RhoCurrentStaticHead color)
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl) := by
  have sourceMembership :
      rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoCIGSLT.reflection.1.presentations := by
    change rhoReflectivePresentation.toReflectivePresentationDecl ∈
      ReflectionExtension.rhoReflectionProfile.presentations
    simp [ReflectionExtension.rhoReflectionProfile]
  have labels :=
    (rhoCIGSLT.reflectivePresentationsRetypable rhoReflectivePresentation
      sourceMembership).constructorLabels_mem_wrapped
  constructor
  · simpa [costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation] using
        rho_currentStaticHead_symbols_of_mem_wrappedLabels color labels.1
  · simpa [costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation] using
        rho_currentStaticHead_symbols_of_mem_wrappedLabels color labels.2.1
  · simpa [costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation] using
        rho_currentStaticHead_symbols_of_mem_wrappedLabels color labels.2.2

/-- A reached subplan's common-reified, mapped, thickened, and keyed-canonical
frame stays inside the selected rho static constructor fragment. -/
theorem rho_plan_commonFrame_constructorsWithin
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.finiteBoundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.finiteBoundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries node.finiteBoundaryTable.entries)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    ConstructorsWithin (RhoCurrentStaticHead color)
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith environment.lookupAtom? leg
          (frameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify plan.abstractPattern))))) := by
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let sourceFrame := environment.reify plan.abstractPattern
  let mappedFrame := mapPattern (color.symbols rhoCIGSLT) sourceFrame
  let thickenedFrame :=
    frameThinning.thickenAmbientBVars scopeDepth mappedFrame
  let commonFrame :=
    cospan.reifyWith environment.lookupAtom? leg thickenedFrame
  obtain ⟨supported, _safe⟩ :=
    plan.abstractPattern_supportedSafe node.finiteBoundaryTable embedding.subset
  have sourceSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) sourceFrame := by
    dsimp only [sourceFrame]
    rw [environment.reify_eq_renameFVars]
    exact supported.constructorsWithin.renameFVars environment.reifyName
  have mappedSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      mappedFrame := by
    apply constructorsWithin_mapPattern (color.symbols rhoCIGSLT)
    · intro constructor membership
      exact rho_currentStaticHead_symbols_of_mem_wrappedLabels color membership
    · exact sourceSupported
  have thickenedSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      thickenedFrame :=
    frameThinning.constructorsWithin_thickenAmbientBVars mappedSupported
      scopeDepth
  have commonSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      commonFrame := by
    dsimp only [commonFrame]
    rw [cospan.reifyWith_eq_renameFVars]
    exact thickenedSupported.renameFVars _
  change ConstructorsWithin (RhoCurrentStaticHead color)
    (canonicalizeByAt key targetDeclaration keyDepth commonFrame)
  rw [← canonicalizeByDepths_ignoreScope key targetDeclaration keyDepth 0
    commonFrame]
  exact
    (Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.constructorsWithin_canonicalizeByDepths_iff
      (fun availableDepth _ pattern => key availableDepth pattern)
      targetDeclaration
      (rho_currentStaticHead_reflectiveConstructorsAllowed color)
      keyDepth 0 commonFrame).mpr commonSupported

/-- Mapping, thickening, and common-cospan reification preserve the selected
rho constructor fragment for every source argument spine accepted by the
authored continuation fragment. -/
theorem rho_argumentFrames_constructorsWithin
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.finiteBoundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.finiteBoundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (patterns : List Pattern)
    (sourceSupported : ConstructorListWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) patterns)
    (availableDepth scopeDepth : Nat) :
    ConstructorListWithin (RhoCurrentStaticHead color)
      ((canonicalizeListByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          availableDepth scopeDepth (patterns.map environment.reify)).map
        (fun pattern => cospan.reifyWith environment.lookupAtom? leg
          (frameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT) pattern)))) := by
  let sourceDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  have sourceMembership : sourceDeclaration ∈
      rhoCIGSLT.reflection.1.presentations := by
    change rhoReflectivePresentation.toReflectivePresentationDecl ∈
      ReflectionExtension.rhoReflectionProfile.presentations
    simp [ReflectionExtension.rhoReflectionProfile]
  have sourceLabels :=
    (rhoCIGSLT.reflectivePresentationsRetypable
      rhoReflectivePresentation sourceMembership).constructorLabels_mem_wrapped
  have sourceReflectiveAllowed : ReflectiveConstructorsAllowed
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
      sourceDeclaration := ⟨sourceLabels.1, sourceLabels.2.1,
        sourceLabels.2.2⟩
  rw [constructorListWithin_iff_forall]
  intro commonFrame commonMembership
  rw [List.mem_map] at commonMembership
  obtain ⟨canonicalSource, canonicalMembership, rfl⟩ := commonMembership
  rw [canonicalizeListByDepths_eq_map, List.mem_map] at canonicalMembership
  obtain ⟨reifiedSource, reifiedMembership, rfl⟩ := canonicalMembership
  rw [List.mem_map] at reifiedMembership
  obtain ⟨sourcePattern, sourceMembershipInList, rfl⟩ := reifiedMembership
  have sourcePatternSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) sourcePattern :=
    (constructorListWithin_iff_forall patterns).mp sourceSupported
      sourcePattern sourceMembershipInList
  have reifiedSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
      (environment.reify sourcePattern) :=
    by
      rw [environment.reify_eq_renameFVars]
      exact sourcePatternSupported.renameFVars environment.reifyName
  have canonicalSupported : ConstructorsWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
        sourceDeclaration availableDepth scopeDepth
        (environment.reify sourcePattern)) :=
    (Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.constructorsWithin_canonicalizeByDepths_iff
      (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
      sourceDeclaration sourceReflectiveAllowed availableDepth scopeDepth
      (environment.reify sourcePattern)).mpr reifiedSupported
  have mappedSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
          sourceDeclaration availableDepth scopeDepth
          (environment.reify sourcePattern))) := by
    apply constructorsWithin_mapPattern (color.symbols rhoCIGSLT)
    · intro constructor membership
      exact rho_currentStaticHead_symbols_of_mem_wrappedLabels color membership
    · exact canonicalSupported
  have thickenedSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
            sourceDeclaration availableDepth scopeDepth
            (environment.reify sourcePattern)))) :=
    frameThinning.constructorsWithin_thickenAmbientBVars mappedSupported
      scopeDepth
  rw [cospan.reifyWith_eq_renameFVars]
  exact thickenedSupported.renameFVars _

/-- The normalized value of an exact rho boundary-table entry is either a
free variable, an application outside the selected static image, or a closed
application of the selected colour's quote constructor. -/
theorem rho_boundaryTreeEntry_normal_shape
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (index : Fin node.finiteBoundaryTable.entries.length) :
    let normal := ((trees.getEntry index).tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern
    (∃ name, normal = .fvar name) ∨
      (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
        normal = .apply wire arguments) ∨
      (normal.isWellScopedAt 0 = true ∧
        ∃ arguments, normal = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor arguments) := by
  dsimp only
  let entry := trees.getEntry index
  have membership : entry.boundary ∈ node.plan.boundaryTable.entries :=
    trees.getEntry_mem index
  have typeMap := node.plan.boundaryTable_fiberCoherent.typeMap
    entry.boundary membership
  have kind := node.plan.boundaryKind_of_mem_entries entry.boundary membership
  cases kind with
  | application constructor rendered outsideCurrent content =>
      rename_i wire arguments
      rcases rho_typedBoundary_application_sourceType_name_or_proc
          entry.boundary typeMap constructor rendered content with
        sourceTypeName | sourceTypeProc
      · have closed := rho_boundaryTreeEntry_name_normal_isWellScopedAt_zero
          node trees index sourceTypeName
        let atom := TypedCostStaticAtom.ofBoundaryValue entry.boundary
          (entry.tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel)
        have atomNormal : atom.key.normal =
            (entry.tree.normalize
              (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := rfl
        have typedName : HasType rhoCIGSLT.costWholeLanguage targetFree
            entry.boundary.boundary.targetSupport atom.key.normal
              (.base (costBaseSortName "Name")) := by
          have typed := atom.normalTyped
          change HasType rhoCIGSLT.costWholeLanguage targetFree
            entry.boundary.boundary.targetSupport atom.key.normal
              entry.boundary.boundary.targetType at typed
          rw [← typeMap, sourceTypeName] at typed
          cases color <;> exact typed
        have object : isObjectPattern atom.key.normal = true := atom.normalObject
        rcases rho_costName_pattern_cases typedName object with
          ⟨boundIndex, normalEq⟩ | ⟨name, normalEq⟩ |
            ⟨quoteColor, quoteArguments, normalEq⟩
        · have impossible : (Pattern.bvar boundIndex).isWellScopedAt 0 = true := by
            rw [← atomNormal, normalEq] at closed
            exact closed
          change decide (boundIndex < 0) = true at impossible
          exact (Nat.not_lt_zero boundIndex (of_decide_eq_true impossible)).elim
        · left
          refine ⟨name, ?_⟩
          exact atomNormal.symm.trans normalEq
        · by_cases sameColor : quoteColor = color
          · subst quoteColor
            right; right
            refine ⟨closed, quoteArguments, ?_⟩
            have quoteHeadEq :
                (color.symbols rhoCIGSLT).constructor "NQuote" =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).quoteConstructor := by
              cases color <;> rfl
            rw [quoteHeadEq] at normalEq
            exact atomNormal.symm.trans normalEq
          · right; left
            refine ⟨(quoteColor.symbols rhoCIGSLT).constructor "NQuote",
              quoteArguments, ?_, ?_⟩
            · rintro ⟨currentConstructor, currentRendered, currentRole⟩
              have quoteRole :=
                CostHereditaryLeafDichotomyProbe.rhoRole_static_of_render_eq_quote
                (color := quoteColor) currentConstructor (by
                  exact currentRendered.trans (by
                    cases quoteColor <;> rfl))
              have roleEq :
                  CIGSLT.GeneratedCostConstructorRole.static color =
                    .static quoteColor := currentRole.symm.trans quoteRole
              cases roleEq
              exact sameColor rfl
            · exact atomNormal.symm.trans normalEq
      · obtain ⟨foreignConstructor, foreignWire, normalizedArguments,
            foreignRendered, foreignRole, normalEq⟩ :=
          rho_boundaryTreeEntry_proc_normal_application node trees index
            sourceTypeProc
        right; left
        refine ⟨foreignWire, normalizedArguments, ?_, normalEq⟩
        rintro ⟨currentConstructor, currentRendered, currentRole⟩
        have constructorEq : foreignConstructor = currentConstructor :=
          rhoCIGSLT.renderDeclaredCostConstructor_injective
            (foreignRendered.trans currentRendered.symm)
        subst currentConstructor
        exact foreignRole currentRole
  | collection currentRejected oppositeChoice oppositeSelected content =>
      exact False.elim
        (rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          oppositeSelected currentRejected)

/-- Every semantic atom in the executable environment of one rho node has
the boundary/source shape forced by its exact positional occurrence. -/
theorem rhoNode_atomValue_normal_shape
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.finiteBoundaryTable
      (trees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    let normal :=
      ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.normal
    (∃ name, normal = .fvar name) ∨
      (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
        normal = .apply wire arguments) ∨
      (normal.isWellScopedAt 0 = true ∧
        ∃ arguments, normal = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor arguments) := by
  dsimp only
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  obtain ⟨position, rfl⟩ :=
    CostStaticAtomEnvironment.ofInventory_occurrenceSlot_surjective inventory
      slot
  rw [environment.occurrenceValue]
  change
    (∃ name, (inventory.occurrenceAt position).atom.key.normal = .fvar name) ∨
      (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
        (inventory.occurrenceAt position).atom.key.normal =
          .apply wire arguments) ∨
      ((inventory.occurrenceAt position).atom.key.normal.isWellScopedAt 0 =
          true ∧
        ∃ arguments, (inventory.occurrenceAt position).atom.key.normal =
          .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).quoteConstructor arguments)
  generalize parameterEq : inventory.occurrenceAt position = parameter
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      left
      exact ⟨_, rfl⟩
  | boundary occurrence notSource resolved resolution =>
      have tableResolution :
          node.finiteBoundaryTable.resolve occurrence.name = some resolved.1 := by
        have agrees :=
          (trees.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer)
            ).resolve_boundary node.finiteBoundaryTable occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      have boundaryMembership :
          resolved.1 ∈ node.finiteBoundaryTable.entries :=
        node.finiteBoundaryTable.mem_entries_of_resolve_eq_some tableResolution
      obtain ⟨index, indexEq⟩ := List.get_of_mem boundaryMembership
      have entryBoundaryEq : (trees.getEntry index).boundary = resolved.1 :=
        (trees.getEntry_boundary index).trans indexEq
      obtain ⟨selected, selectedResolution, _selectedBoundary,
          selectedNormal⟩ :=
        trees.exists_resolve_normalizedValue_eq_getEntry
          (kernel := rhoHereditaryNormalizationKernel)
          CostCanonicalLaws.rho_unambiguousStaticDecomposition index
      have nameEq : occurrence.name =
          costRegionBoundaryVariableName resolved.1.boundary :=
        node.finiteBoundaryTable.name_eq_boundaryVariable_of_resolve_eq_some
          tableResolution
      have selectedResolutionAtName :
          (trees.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer)
            ).resolve node.finiteBoundaryTable occurrence.name = some selected := by
        rw [nameEq, ← entryBoundaryEq]
        exact selectedResolution
      have selectedEq : resolved = selected :=
        Option.some.inj (resolution.symm.trans selectedResolutionAtName)
      subst selected
      have resolvedNormal : resolved.2.1 =
          ((trees.getEntry index).tree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
        exact selectedNormal
      change
        (∃ name, resolved.2.1 = .fvar name) ∨
          (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
            resolved.2.1 = .apply wire arguments) ∨
          (resolved.2.1.isWellScopedAt 0 = true ∧
            ∃ arguments, resolved.2.1 = .apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor arguments)
      rw [resolvedNormal]
      exact rho_boundaryTreeEntry_normal_shape node trees index

/-- Every resolvable assignment in the common semantic namespace inherits
its shape from an exact atom occurrence in one endpoint node. -/
theorem rhoNode_commonAssignment_shape
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1)
    (name : String)
    (resolvable :
      (((CostStaticAtomEnvironment.ofInventory leftInventory).semanticKeyCospan
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        ).lookupCommon? name).isSome = true) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    (∃ restoredName, cospan.commonAssignment name = .fvar restoredName) ∨
      (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
        cospan.commonAssignment name = .apply wire arguments) ∨
      ((cospan.commonAssignment name).isWellScopedAt 0 = true ∧
        ∃ arguments, cospan.commonAssignment name = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor arguments) := by
  dsimp only
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  change (cospan.lookupCommon? name).isSome = true at resolvable
  rw [Option.isSome_iff_exists] at resolvable
  obtain ⟨slot, selected⟩ := resolvable
  change
    (∃ restoredName, cospan.commonAssignment name = .fvar restoredName) ∨
      (∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
        cospan.commonAssignment name = .apply wire arguments) ∨
      ((cospan.commonAssignment name).isWellScopedAt 0 = true ∧
        ∃ arguments, cospan.commonAssignment name = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor arguments)
  rw [show cospan.commonAssignment name =
      (cospan.commonKeys.get slot).normal by
    simp [CostStaticAtomKeyCospan.commonAssignment, selected]]
  rcases leftEnvironment.semanticKeyCospan_has_endpoint_origin
      rightEnvironment slot with
    ⟨leftSlot, origin⟩ | ⟨rightSlot, origin⟩
  · rw [origin]
    exact rhoNode_atomValue_normal_shape leftNode leftTrees leftInventory
      leftSlot
  · rw [origin]
    exact rhoNode_atomValue_normal_shape rightNode rightTrees rightInventory
      rightSlot

/-- The common support of two rho node environments is inherited from one
endpoint and is therefore either the shared ambient target context or empty. -/
theorem rhoNode_commonAtom_targetSupport_eq_targetBound_or_nil
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.finiteBoundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.finiteBoundaryTable}
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable leftValues leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable rightValues rightNode.skeleton.1)
    (slot : Fin
      ((CostStaticAtomEnvironment.ofInventory leftInventory).semanticKeyCospan
        (CostStaticAtomEnvironment.ofInventory rightInventory)
        ).commonKeys.length) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    (cospan.commonKeys.get slot).targetSupport = leftNode.targetBound ∨
      (cospan.commonKeys.get slot).targetSupport = [] := by
  dsimp only
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  rcases leftEnvironment.semanticKeyCospan_has_endpoint_origin
      rightEnvironment slot with
    ⟨leftSlot, origin⟩ | ⟨rightSlot, origin⟩
  · rw [origin]
    exact CostStaticRegionNode.ofInventory_atomValue_targetSupport_eq_targetBound_or_nil
      leftNode leftInventory leftSlot
  · rw [origin]
    rcases CostStaticRegionNode.ofInventory_atomValue_targetSupport_eq_targetBound_or_nil
        rightNode rightInventory rightSlot with exposed | sealed
    · exact Or.inl (exposed.trans sameTargetBound.symm)
    · exact Or.inr sealed

/-- Every common assignment name has the exact rigid-or-fixed-quote behavior
consumed by the semantic-frame inversion. Names outside the finite quotient
remain rigid free variables. -/
theorem rhoNode_commonAssignment_rigidOrFixedQuote
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1)
    (name : String) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ((∀ depth,
      (∃ restoredName,
        ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment depth (.fvar name) =
          .fvar restoredName) ∨
        ∃ wire arguments, ¬ RhoCurrentStaticHead color wire ∧
          ReflectiveContextSupport.substituteAt
              rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
            .apply wire arguments) ∨
      ∃ arguments, ∀ depth,
        ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment depth (.fvar name) =
          .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).quoteConstructor arguments) := by
  dsimp only
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  by_cases resolvable : (cospan.lookupCommon? name).isSome = true
  · exact NonBoundaryCrossTie.atom_rigidOrFixedQuote_of_assignment_shape
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment (RhoCurrentStaticHead color)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor name
      (rhoNode_commonAssignment_shape leftNode rightNode leftTrees rightTrees
        leftInventory rightInventory name resolvable)
  · have selected : cospan.lookupCommon? name = none := by
      cases lookup : cospan.lookupCommon? name with
      | none => exact rfl
      | some slot => exact False.elim (resolvable (by simp [lookup]))
    apply NonBoundaryCrossTie.atom_rigidOrFixedQuote_of_assignment_shape
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment (RhoCurrentStaticHead color)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor name
    left
    exact ⟨name, by simp [CostStaticAtomKeyCospan.commonAssignment, selected]⟩

/-- Equality between any two common-assignment names at one depth is uniform
at all depths. Resolvable names use the proof-relevant common-atom theorem;
unresolvable names remain literal free variables. -/
theorem rhoNode_commonAssignments_restoreTogether
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    {leftName rightName : String} {depth : Nat}
    (equalAt :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment depth (.fvar leftName) =
        ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment depth (.fvar rightName)) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.RestoresTogether
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment (.fvar leftName) (.fvar rightName) := by
  dsimp only at equalAt ⊢
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  change ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment depth (.fvar leftName) =
    ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment depth (.fvar rightName) at equalAt
  change ReflectiveContextSupport.RestoresTogether
    rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment (.fvar leftName) (.fvar rightName)
  cases leftLookup : cospan.lookupCommon? leftName with
  | none =>
      cases rightLookup : cospan.lookupCommon? rightName with
      | none =>
          have namesEqual : leftName = rightName := by
            simpa [ReflectiveContextSupport.substituteAt,
              CostStaticAtomKeyCospan.commonSupport,
              CostStaticAtomKeyCospan.commonAssignment, leftLookup,
              rightLookup,
              Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using equalAt
          subst rightName
          exact ReflectiveContextSupport.RestoresTogether.refl
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment (.fvar leftName)
      | some rightSlot =>
          have rightShape := rhoNode_commonAssignment_shape leftNode rightNode
            leftTrees rightTrees leftInventory rightInventory rightName
              (by
                change (cospan.lookupCommon? rightName).isSome = true
                simp [rightLookup])
          rcases rightShape with ⟨restoredName, rightValue⟩ |
              ⟨wire, arguments, outside, rightValue⟩ |
              ⟨closed, arguments, rightValue⟩
          · have rightValue' : (cospan.commonKeys.get rightSlot).normal =
                .fvar restoredName := by
              change cospan.commonAssignment rightName =
                .fvar restoredName at rightValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, rightLookup]
                using rightValue
            have namesEqual : leftName = restoredName := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [rightValue'] at equalAt
              simpa [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
                equalAt
            intro currentDepth
            simp only [ReflectiveContextSupport.substituteAt,
              CostStaticAtomKeyCospan.commonSupport,
              CostStaticAtomKeyCospan.commonAssignment, leftLookup,
              rightLookup]
            rw [rightValue']
            simpa [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
              congrArg Pattern.fvar namesEqual
          · have rightValue' : (cospan.commonKeys.get rightSlot).normal =
                .apply wire arguments := by
              change cospan.commonAssignment rightName =
                .apply wire arguments at rightValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, rightLookup]
                using rightValue
            have impossible : False := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [rightValue'] at equalAt
              simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at equalAt
              cases equalAt
            exact impossible.elim
          · have rightValue' : (cospan.commonKeys.get rightSlot).normal =
                .apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).quoteConstructor arguments := by
              change cospan.commonAssignment rightName =
                .apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).quoteConstructor arguments at rightValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, rightLookup]
                using rightValue
            have impossible : False := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [rightValue'] at equalAt
              simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at equalAt
              cases equalAt
            exact impossible.elim
  | some leftSlot =>
      cases rightLookup : cospan.lookupCommon? rightName with
      | none =>
          have leftShape := rhoNode_commonAssignment_shape leftNode rightNode
            leftTrees rightTrees leftInventory rightInventory leftName
              (by
                change (cospan.lookupCommon? leftName).isSome = true
                simp [leftLookup])
          rcases leftShape with ⟨restoredName, leftValue⟩ |
              ⟨wire, arguments, outside, leftValue⟩ |
              ⟨closed, arguments, leftValue⟩
          · have leftValue' : (cospan.commonKeys.get leftSlot).normal =
                .fvar restoredName := by
              change cospan.commonAssignment leftName =
                .fvar restoredName at leftValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, leftLookup]
                using leftValue
            have namesEqual : restoredName = rightName := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [leftValue'] at equalAt
              simpa [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
                equalAt
            intro currentDepth
            simp only [ReflectiveContextSupport.substituteAt,
              CostStaticAtomKeyCospan.commonSupport,
              CostStaticAtomKeyCospan.commonAssignment, leftLookup,
              rightLookup]
            rw [leftValue']
            simpa [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] using
              congrArg Pattern.fvar namesEqual
          · have leftValue' : (cospan.commonKeys.get leftSlot).normal =
                .apply wire arguments := by
              change cospan.commonAssignment leftName =
                .apply wire arguments at leftValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, leftLookup]
                using leftValue
            have impossible : False := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [leftValue'] at equalAt
              simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at equalAt
              cases equalAt
            exact impossible.elim
          · have leftValue' : (cospan.commonKeys.get leftSlot).normal =
                .apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).quoteConstructor arguments := by
              change cospan.commonAssignment leftName =
                .apply
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).quoteConstructor arguments at leftValue
              simpa [CostStaticAtomKeyCospan.commonAssignment, leftLookup]
                using leftValue
            have impossible : False := by
              simp only [ReflectiveContextSupport.substituteAt,
                CostStaticAtomKeyCospan.commonSupport,
                CostStaticAtomKeyCospan.commonAssignment, leftLookup,
                rightLookup] at equalAt
              rw [leftValue'] at equalAt
              simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at equalAt
              cases equalAt
            exact impossible.elim
      | some rightSlot =>
          have canonicalEqual :
              ReflectiveContextSupport.substituteAt
                  rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
                    cospan.commonAssignment depth
                    (.fvar (cospan.commonAtomName leftSlot)) =
                ReflectiveContextSupport.substituteAt
                  rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
                    cospan.commonAssignment depth
                    (.fvar (cospan.commonAtomName rightSlot)) := by
            simpa [ReflectiveContextSupport.substituteAt,
              CostStaticAtomKeyCospan.commonSupport,
              CostStaticAtomKeyCospan.commonAssignment, leftLookup,
              rightLookup] using equalAt
          have canonicalRestores :=
            RhoMatchedStaticFramesApex.restoresTogether_commonAtoms_of_substituteAt_eq_of_support_eq_or_nil
              leftEnvironment rightEnvironment leftSlot rightSlot
              (rhoNode_commonAtom_targetSupport_eq_targetBound_or_nil
                leftNode rightNode sameTargetBound leftInventory rightInventory
                  leftSlot)
              (rhoNode_commonAtom_targetSupport_eq_targetBound_or_nil
                leftNode rightNode sameTargetBound leftInventory rightInventory
                  rightSlot)
              canonicalEqual
          intro currentDepth
          have restored := canonicalRestores currentDepth
          simpa [ReflectiveContextSupport.substituteAt,
            CostStaticAtomKeyCospan.commonSupport,
            CostStaticAtomKeyCospan.commonAssignment, leftLookup,
            rightLookup] using restored

/-- Two exact subplan frames that tie under the common semantic key admit a
restoration apex at every requested depth. The proof uses only their retained
entry embeddings, selected-colour constructor support, and the semantic shape
of the actual parent environments. -/
theorem rho_planFrames_commonRestorationApex_of_keyEq
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {leftPayload rightPayload : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      leftSourceType)
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload rightSourceType)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftPlan.boundaryTable.entries leftNode.finiteBoundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightPlan.boundaryTable.entries rightNode.finiteBoundaryTable.entries)
    (scopeDepth keyDepth restorationDepth : Nat)
    (keyEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
        color rhoReflectivePresentation.toReflectivePresentationDecl
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftPlan.abstractPattern))))) =
        key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightPlan.abstractPattern)))))) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration restorationDepth
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (leftEnvironment.reify leftPlan.abstractPattern)))))
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify rightPlan.abstractPattern))))) := by
  dsimp only at keyEq ⊢
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify leftPlan.abstractPattern))))
  let rightFrame := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightPlan.abstractPattern))))
  change key keyDepth leftFrame = key keyDepth rightFrame at keyEq
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    targetDeclaration restorationDepth leftFrame rightFrame
  have leftSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      leftFrame := by
    dsimp only [leftFrame]
    exact rho_plan_commonFrame_constructorsWithin leftNode leftEnvironment
      leftFrameThinning cospan cospan.leftSlot leftPlan leftEmbedding scopeDepth
        keyDepth
  have rightSupported : ConstructorsWithin (RhoCurrentStaticHead color)
      rightFrame := by
    dsimp only [rightFrame]
    exact rho_plan_commonFrame_constructorsWithin rightNode rightEnvironment
      rightFrameThinning cospan cospan.rightSlot rightPlan rightEmbedding
        scopeDepth keyDepth
  have equalAt :=
    (cospan.commonSemanticPatternKeyAt_eq_iff rhoCIGSLT keyDepth leftFrame
      rightFrame).mp keyEq
  have restores :=
    ReflectiveContextSupport.restoresTogether_of_substituteAt_eq_of_rigidAtoms
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment (RhoCurrentStaticHead color) (fun _ => True)
      targetDeclaration.quoteConstructor
      (isQuoteConstructor_costStaticReflectivePresentationDecl color _ (by
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile]))
      (fun name _ =>
        rhoNode_commonAssignment_rigidOrFixedQuote leftNode rightNode leftTrees
          rightTrees leftInventory rightInventory name)
      (fun {_leftName _rightName _depth} _ _ equality =>
        rhoNode_commonAssignments_restoreTogether leftNode rightNode leftTrees
          rightTrees leftInventory rightInventory sameTargetBound equality)
      leftSupported rightSupported (fun _ _ => True.intro)
      (fun _ _ => True.intro) equalAt
  exact .leafAligned (.leaf restores)

/-- Equal-key members of two exact process-plan frontiers admit restoration
apices at every depth. Frontier membership is first inverted to the retained
subplan witnesses; their entry embeddings are then composed into the two
parent node inventories before applying the exact-frame theorem. -/
theorem rho_processPlan_frontier_crossTies
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1)
    (rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.finiteBoundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1)
    (sameTargetBound : leftNode.targetBound = rightNode.targetBound)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (leftParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftPlan.boundaryTable.entries
        leftNode.finiteBoundaryTable.entries)
    (rightParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightPlan.boundaryTable.entries
        rightNode.finiteBoundaryTable.entries)
    (scopeDepth keyDepth : Nat) :
    let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
    let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftFrame := fun pattern =>
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify pattern)))
    let rightFrame := fun pattern =>
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify pattern)))
    ∀ {leftEndpoint rightEndpoint},
      leftEndpoint ∈ parallelContents targetDeclaration
        (canonicalizeListByAt key targetDeclaration keyDepth
          [leftFrame leftPlan.abstractPattern]) →
      rightEndpoint ∈ parallelContents targetDeclaration
        (canonicalizeListByAt key targetDeclaration keyDepth
          [rightFrame rightPlan.abstractPattern]) →
      key keyDepth leftEndpoint = key keyDepth rightEndpoint →
      ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
        cospan targetDeclaration depth leftEndpoint rightEndpoint := by
  dsimp only
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := fun pattern =>
    cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify pattern)))
  let rightFrame := fun pattern =>
    cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify pattern)))
  intro leftEndpoint rightEndpoint leftMembership rightMembership keyEq depth
  obtain ⟨leftRaw, leftAbstract, _leftRawMembership, leftWitness,
      leftEndpointEq⟩ :=
    ParallelFrontier.exists_leafWitness_of_mem_commonReifiedMappedThickened_frontier
      leftEnvironment leftFrameThinning cospan cospan.leftSlot leftPlan
        leftAdmission scopeDepth keyDepth (by
          simpa only [canonicalizeListByAt] using leftMembership)
  obtain ⟨rightRaw, rightAbstract, _rightRawMembership, rightWitness,
      rightEndpointEq⟩ :=
    ParallelFrontier.exists_leafWitness_of_mem_commonReifiedMappedThickened_frontier
      rightEnvironment rightFrameThinning cospan cospan.rightSlot rightPlan
        rightAdmission scopeDepth keyDepth (by
          simpa only [canonicalizeListByAt] using rightMembership)
  rcases leftWitness with
    ⟨_leftOuter, leftSubplan, _leftContext, _leftRootEq,
      leftAbstractEq, _leftSubAdmission, ⟨leftSubEmbedding⟩⟩
  rcases rightWitness with
    ⟨_rightOuter, rightSubplan, _rightContext, _rightRootEq,
      rightAbstractEq, _rightSubAdmission, ⟨rightSubEmbedding⟩⟩
  subst leftAbstract
  subst rightAbstract
  have subplanKeyEq :
      key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (leftFrame leftSubplan.abstractPattern)) =
        key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (rightFrame rightSubplan.abstractPattern)) := by
    rw [leftEndpointEq, rightEndpointEq]
    exact keyEq
  have subplanApex := rho_planFrames_commonRestorationApex_of_keyEq
    leftNode rightNode leftTrees rightTrees leftInventory rightInventory
      sameTargetBound leftFrameThinning rightFrameThinning leftSubplan
      rightSubplan (leftSubEmbedding.comp leftParentEmbedding)
      (rightSubEmbedding.comp rightParentEmbedding) scopeDepth keyDepth depth
      subplanKeyEq
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex leftEndpointEq
    rightEndpointEq subplanApex

/-- A paired authored quotation reached under a foreign declaration has a
common restoration apex once every strictly smaller argument stop has one.
The proof coordinates the only root-changing Quote/Drop case through the
argument-spine apex itself. -/
noncomputable def rho_quotePlanStops_commonRestorationApex_of_below
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    {parentMeasure : Nat}
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload rightPayload)
    (mapBelow :
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment rightValues).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
        color rhoReflectivePresentation
      ∀ availableDepth scopeDepth rootDepth {leftArgument rightArgument},
        CostStaticPlanCanonicalStopBelow leftReached.plan rightReached.plan
          rhoReflectivePresentation
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (RhoCanonicalRawStop declarationColor parentMeasure)
          (sizeOf leftPayload + sizeOf rightPayload)
          leftArgument rightArgument →
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          targetDeclaration rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    leftView.node leftEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (leftEnvironment.reify leftArgument)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (rightEnvironment.reify rightArgument)))))) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
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
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  obtain ⟨leftArguments, rightArguments, leftShape, rightShape,
      argumentsAligned⟩ :=
    RhoCanonicalRawStop.foreign_sourceQuoteArguments_alignedBelow leftReached
      rightReached foreign leftAdmission rightAdmission sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftQuote
      rightQuote aligned
  have leftArgumentsInRoot : ∀ name,
      name ∈ leftArguments.flatMap Pattern.freeFvarNames →
        name ∈ leftView.node.skeleton.1.freeFvarNames := by
    intro name membership
    rw [leftView.node.skeleton_pattern, leftReached.abstract_eq]
    apply Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
    rw [leftShape]
    simpa [Pattern.freeFvarNames] using membership
  have rightArgumentsInRoot : ∀ name,
      name ∈ rightArguments.flatMap Pattern.freeFvarNames →
        name ∈ rightView.node.skeleton.1.freeFvarNames := by
    intro name membership
    rw [rightView.node.skeleton_pattern, rightReached.abstract_eq]
    apply Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
    rw [rightShape]
    simpa [Pattern.freeFvarNames] using membership
  have routed := CanonicalStopAlignedList.routeFVars argumentsAligned
    (leftRootFree := leftView.node.skeleton.1.freeFvarNames)
    (rightRootFree := rightView.node.skeleton.1.freeFvarNames)
    leftArgumentsInRoot rightArgumentsInRoot
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  have argumentsApexWithLeftThinning :=
    CanonicalStopRoutedList.environmentMapThickenCanonicalizeCommonApexByDepths
      leftEnvironment rightEnvironment leftView.node.thinning
      (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
        leftEnvironment)
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
        rightEnvironment)
      rhoReflectivePresentation.toReflectivePresentationDecl
      (sourceStop := fun leftArgument rightArgument =>
        CostStaticPlanCanonicalStopBelow leftReached.plan rightReached.plan
          rhoReflectivePresentation
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (RhoCanonicalRawStop declarationColor parentMeasure)
          (sizeOf leftPayload + sizeOf rightPayload)
          leftArgument rightArgument ∨
        MemberFVarPair leftView.node.skeleton.1.freeFvarNames
          rightView.node.skeleton.1.freeFvarNames leftArgument rightArgument)
      (fun availableDepth scopeDepth rootDepth {leftArgument rightArgument}
          stopped => by
        rcases stopped with stopped | ⟨name, leftEq, rightEq, leftMembership,
          rightMembership⟩
        · have endpointApex :=
            mapBelow availableDepth scopeDepth rootDepth stopped
          apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
            endpointApex
          exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
            (thickenEq scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (rightEnvironment.reify rightArgument)))).symm
        · subst leftEq
          subst rightEq
          have memberApex := memberFVar_commonRestorationApex leftView.node
            rightView.node leftView.children rightView.children leftEnvironment
            rightEnvironment name leftMembership rightMembership
            targetDeclaration rootDepth
          simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
            canonicalizeByDepths, mapPattern,
            CostStaticBinderThinning.thickenAmbientBVars,
            CostStaticAtomKeyCospan.reifyLeft,
            CostStaticAtomKeyCospan.reifyRight, targetDeclaration,
            costStaticReflectivePresentationDecl_eq_map] using memberApex)
      routed 0 callbackScope 0
  let leftArgumentFrames :=
    ((canonicalizeListByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
          leftEnvironment)
        rhoReflectivePresentation.toReflectivePresentationDecl
        0 callbackScope
        (leftArguments.map leftEnvironment.reify)).map
      (fun pattern => cospan.reifyLeft leftEnvironment.lookupAtom?
        (leftView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT) pattern))))
  let rightArgumentFrames :=
    ((canonicalizeListByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
          rightEnvironment)
        rhoReflectivePresentation.toReflectivePresentationDecl
        0 callbackScope
        (rightArguments.map rightEnvironment.reify)).map
      (fun pattern => cospan.reifyRight rightEnvironment.lookupAtom?
        (rightView.node.thinning.thickenAmbientBVars callbackScope
          (mapPattern (color.symbols rhoCIGSLT) pattern))))
  have rightFramesEq :
      ((canonicalizeListByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          0 callbackScope
          (rightArguments.map rightEnvironment.reify)).map
        (fun pattern => cospan.reifyRight rightEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars callbackScope
            (mapPattern (color.symbols rhoCIGSLT) pattern)))) =
        rightArgumentFrames := by
    dsimp only [rightArgumentFrames]
    apply List.map_congr_left
    intro pattern _membership
    exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
      (thickenEq callbackScope
        (mapPattern (color.symbols rhoCIGSLT) pattern))
  have argumentsApex :
      CostStaticAtomKeyCospan.CommonRestorationApexList rhoCIGSLT cospan
        targetDeclaration 0 leftArgumentFrames rightArgumentFrames := by
    dsimp only [leftArgumentFrames]
    rw [← rightFramesEq]
    simpa only [CostStaticAtomKeyCospan.reifyLeft,
      CostStaticAtomKeyCospan.reifyRight] using
        argumentsApexWithLeftThinning
  obtain ⟨leftTyped, _leftSafe⟩ :=
    leftReached.plan.abstractPattern_supportedSafe
      leftReached.plan.boundaryTable (fun _ membership => membership)
  obtain ⟨rightTyped, _rightSafe⟩ :=
    rightReached.plan.abstractPattern_supportedSafe
      rightReached.plan.boundaryTable (fun _ membership => membership)
  have leftSourceSupported : ConstructorListWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) leftArguments := by
    rw [leftShape] at leftTyped
    exact leftTyped.constructorsWithin.2
  have rightSourceSupported : ConstructorListWithin
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) rightArguments := by
    rw [rightShape] at rightTyped
    exact rightTyped.constructorsWithin.2
  have leftSupported : ConstructorListWithin (RhoCurrentStaticHead color)
      leftArgumentFrames := by
    dsimp only [leftArgumentFrames]
    exact rho_argumentFrames_constructorsWithin leftView.node leftEnvironment
      leftView.node.thinning cospan cospan.leftSlot leftArguments
      leftSourceSupported 0 callbackScope
  have rightSupported : ConstructorListWithin (RhoCurrentStaticHead color)
      rightArgumentFrames := by
    dsimp only [rightArgumentFrames]
    exact rho_argumentFrames_constructorsWithin rightView.node rightEnvironment
      rightView.node.thinning cospan cospan.rightSlot rightArguments
      rightSourceSupported 0 callbackScope
  have finishesRestore :=
    ReflectiveContextSupport.restoresTogether_finishNormalizeReflectiveApply_quote_of_argumentsApex
      cospan targetDeclaration (RhoCurrentStaticHead color) (fun _ => True)
      (isQuoteConstructor_costStaticReflectivePresentationDecl color _ (by
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile]))
      (rho_currentStaticHead_reflectiveConstructorsAllowed color).drop
      (declC_dropNeQuote color)
      (CostCanonicalLaws.rho_costStatic_drop_isOrdinary color)
      (fun name _ => rhoNode_commonAssignment_rigidOrFixedQuote leftView.node
        rightView.node leftView.children rightView.children leftInventory
        rightInventory name)
      (fun {_leftName _rightName _depth} _ _ equality =>
        rhoNode_commonAssignments_restoreTogether leftView.node rightView.node
          leftView.children rightView.children leftInventory rightInventory
          (leftView.targetBound_eq_targetBound rightView) equality)
      argumentsApex leftSupported rightSupported (fun _ _ => True.intro)
      (fun _ _ => True.intro)
  have finishApex : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      cospan targetDeclaration callbackRoot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        targetDeclaration targetDeclaration.quoteConstructor
        leftArgumentFrames)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        targetDeclaration targetDeclaration.quoteConstructor
        rightArgumentFrames) :=
    .leafAligned (.leaf finishesRestore)
  have leftReifyListEq :
      leftArguments.map leftEnvironment.reify =
        leftArguments.map
          (Pattern.renameFVars leftEnvironment.reifyName) :=
    List.map_congr_left (fun pattern _membership =>
      leftEnvironment.reify_eq_renameFVars pattern)
  have rightReifyListEq :
      rightArguments.map rightEnvironment.reify =
        rightArguments.map
          (Pattern.renameFVars rightEnvironment.reifyName) :=
    List.map_congr_left (fun pattern _membership =>
      rightEnvironment.reify_eq_renameFVars pattern)
  dsimp only [leftArgumentFrames, rightArgumentFrames] at finishApex
  rw [leftReifyListEq, rightReifyListEq] at finishApex
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    targetDeclaration callbackRoot _ _
  rw [leftShape, rightShape]
  simpa [leftValues, rightValues, leftInventory, rightInventory,
    leftEnvironment, rightEnvironment, cospan, targetDeclaration,
    leftArgumentFrames, rightArgumentFrames, canonicalizeByDepths,
    CostStaticAtomEnvironment.reify,
    leftEnvironment.reify_eq_renameFVars,
    rightEnvironment.reify_eq_renameFVars,
    Pattern.renameFVars, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
    CostStaticAtomKeyCospan.reifyWith, mapPatternList_eq_map, List.map_map,
    Function.comp_def, costStaticReflectivePresentationDecl_eq_map,
    ReflectionExtension.mapReflectivePresentation,
    Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapPattern_finishNormalizeReflectiveApply,
    Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.thickenAmbientBVars_finishNormalizeReflectiveApply,
    ReflectiveContextSupport.renameFVars_finishNormalizeReflectiveApply] using
      finishApex

/-- Reconstruct a reached process-plan pair in its parent semantic cospan
while keeping available, structural, and restoration depths independent.
The paired frontier callback handles corresponding raw leaves; all remaining
equal-key ties are discharged from their exact retained subplans. -/
noncomputable def
    rho_reachedPlanPairCommonApex_of_foreignCanonical
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftProcess : leftReached.sourceType = .base "Proc")
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (close :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
        leftRaw ∈ RhoCommonRestorationApex.parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPayload ∧
        ParallelFrontier.LeafWitness leftReached.sourceBound
          leftReached.targetBound leftReached.thinning
          leftReached.sourceAvailable leftReached.plan.abstractPattern
          leftReached.plan.boundaryTable.entries leftRaw leftAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
        rightRaw ∈ RhoCommonRestorationApex.parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPayload ∧
        ParallelFrontier.LeafWitness rightReached.sourceBound
          rightReached.targetBound rightReached.thinning
          rightReached.sourceAvailable rightReached.plan.abstractPattern
          rightReached.plan.boundaryTable.entries rightRaw rightAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) rightRaw →
      ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
        cospan
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        depth leftEndpoint rightEndpoint) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
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
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify leftView.node
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes leftReached
        callbackAvailable callbackScope
  have rightNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify rightView.node
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
        rightReached callbackAvailable callbackScope
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  cases sourceBoundEq
  cases targetBoundEq
  cases sourceAvailableEq
  cases thinningEq
  have rightProcess : rst = .base "Proc" := sourceTypeEq.symm.trans leftProcess
  subst leftProcess
  subst rightProcess
  have sameParentTargetBound : leftView.node.targetBound =
      rightView.node.targetBound :=
    leftView.targetBound_eq_targetBound rightView
  have apex :=
    ParallelFrontier.processPlans_commonRestorationApex_at_independentDepths_of_foreignCanonical
      leftEnvironment rightEnvironment leftView.node.thinning
      rightView.node.thinning cospan cospan.leftSlot cospan.rightSlot lp rp
      leftAdmission rightAdmission foreign canonical targetDeclaration rfl
      callbackScope callbackAvailable callbackRoot (by
        intro leftRaw leftEndpoint rightRaw rightEndpoint leftWitness
          rightWitness rawCanonical depth
        simpa only [leftEnvironment, rightEnvironment, cospan,
          targetDeclaration, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using
            (close (leftRaw := leftRaw) (leftEndpoint := leftEndpoint)
              (rightRaw := rightRaw) (rightEndpoint := rightEndpoint)
              leftWitness rightWitness rawCanonical depth))
      (by
        dsimp only
        intro leftEndpoint rightEndpoint leftMembership rightMembership keyEq
          depth
        exact rho_processPlan_frontier_crossTies leftView.node rightView.node
          leftView.children rightView.children leftInventory rightInventory
          sameParentTargetBound leftView.node.thinning
          rightView.node.thinning lp rp leftAdmission rightAdmission
          leftParentEmbedding rightParentEmbedding callbackScope
          callbackAvailable leftMembership rightMembership keyEq depth)
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftNaturality.symm rightNaturality.symm apex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
