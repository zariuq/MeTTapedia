import Mettapedia.GSLT.LanguageDef.CostElaborationTransport

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace CostStaticRegionNode

namespace CostStaticSourceTerm

/-- Proof-only transport of a static source term between equal fibers. -/
def reindex
    {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {firstSourceBound secondSourceBound firstTargetBound secondTargetBound :
      List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support secondSourceBound
      secondTargetBound secondSort)
    (sourceBoundEq : firstSourceBound = secondSourceBound)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort) :
    CostStaticSourceTerm source color free support firstSourceBound
      firstTargetBound firstSort := by
  cases sourceBoundEq
  cases targetBoundEq
  cases sortEq
  exact term

@[simp]
theorem reindex_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {firstSourceBound secondSourceBound firstTargetBound secondTargetBound :
      List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support secondSourceBound
      secondTargetBound secondSort)
    (sourceBoundEq : firstSourceBound = secondSourceBound)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort) :
    (term.reindex sourceBoundEq targetBoundEq sortEq).term.1 = term.term.1 := by
  cases sourceBoundEq
  cases targetBoundEq
  cases sortEq
  rfl

/-- Reindexing along the target context and then using the canonical target
thinning does not alter the acted raw pattern. -/
theorem reindex_act_ofTarget
    {source : CIGSLT} {color : CostStaticColor}
    {free assignmentFree targetFree : WellSorted.FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {firstTargetBound secondTargetBound : List TypeExpr}
    {firstSort secondSort :
      LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support
      (CostStaticBinderThinning.sourceContextOfTarget source color
        secondTargetBound) secondTargetBound secondSort)
    (targetBoundEq : firstTargetBound = secondTargetBound)
    (sortEq : firstSort = secondSort)
    (assignment : WellSorted.SupportedOpenAssignment source.costWholeLanguage
      assignmentFree targetFree assignmentSupport) :
    (term.reindex
        (congrArg
          (CostStaticBinderThinning.sourceContextOfTarget source color)
          targetBoundEq)
        targetBoundEq sortEq).act
          (CostStaticBinderThinning.ofTargetThinning source color
            firstTargetBound) assignment =
      term.act
        (CostStaticBinderThinning.ofTargetThinning source color
          secondTargetBound) assignment := by
  cases targetBoundEq
  cases sortEq
  rfl

end CostStaticSourceTerm

def sourceActionTermIn
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    CostStaticSourceTerm source color globalTable.sourceFreeContext
      globalTable.sourceSupport node.sourceBound node.targetBound
        node.sourceSort := by
  let supportedSafe :=
    node.plan.abstractPattern_supportedSafe globalTable entriesSubset
  let supported := Classical.choose supportedSafe
  let safe := Classical.choose_spec supportedSafe
  exact
    { term :=
        ⟨node.plan.abstractPattern, supported.toHasType,
          node.plan.abstractPattern_canonicalBinderMetadata node.term.2.2.1,
          node.plan.abstractPattern_object node.term.2.2.2.1,
          node.plan.abstractPattern_reflectiveScopeSafeAt⟩
      supported := supported
      safe := safe }

@[simp]
theorem sourceActionTermIn_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    (node.sourceActionTermIn globalTable entriesSubset).term.1 =
      node.plan.abstractPattern := by
  rfl

/-- Restoring a node through any containing finite table recovers its exact
compact term; enlarging the table changes only proof support. -/
theorem restoreMappedAbstractPatternIn_eq_term
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree
      globalOccurrences)
    (entriesSubset : node.boundaryTable.entries ⊆ globalTable.entries) :
    ReflectiveContextSupport.substituteAt source.costWholeLanguage
        globalTable.restorationSupport globalTable.restorationAssignment
        node.targetBound.length
        (node.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source) node.plan.abstractPattern)) =
      node.term.1 := by
  change ReflectiveContextSupport.substituteAt source.costWholeLanguage
      globalTable.restorationSupport globalTable.restorationAssignment
      node.targetBound.length
      ((CostStaticBinderThinning.ofTargetThinning source color
        node.targetBound).thickenAmbientBVars 0
          (mapPattern (color.symbols source) node.plan.abstractPattern)) =
    node.term.1
  exact (node.plan.restoreMappedAbstractPattern globalTable entriesSubset
    node.term.2.2.2.1).trans node.plan.recomposePattern_eq

end CostStaticRegionNode

theorem testStatic
    (source : CIGSLT) (staticLift : CostStaticPlanLift source)
    (stable : CostStaticMappedGeneratorFiberAction source) :
    source.CostStaticRegionTransportSound staticLift := by
  intro targetFree color outer leftNode rightNode leftChildren rightChildren
    sourceSortEq planStep children childrenSound
  intro leftCanonical leftObject leftScope rightCanonical rightObject rightScope
  let globalTable := TypedCostRegionBoundaryTable.append
    leftNode.boundaryTable rightNode.boundaryTable
  have leftSubset : leftNode.boundaryTable.entries ⊆ globalTable.entries := by
    intro boundary membership
    simpa only [globalTable, TypedCostRegionBoundaryTable.entries_append] using
      List.mem_append_left rightNode.boundaryTable.entries membership
  have rightSubset : rightNode.boundaryTable.entries ⊆ globalTable.entries := by
    intro boundary membership
    simpa only [globalTable, TypedCostRegionBoundaryTable.entries_append] using
      List.mem_append_right leftNode.boundaryTable.entries membership
  have globalCoherent : globalTable.FiberCoherent := by
    exact (TypedCostRegionBoundaryTable.fiberCoherent_append_iff
      leftNode.boundaryTable rightNode.boundaryTable).2
        ⟨leftNode.plan.boundaryTable_fiberCoherent,
          rightNode.plan.boundaryTable_fiberCoherent⟩
  let globalTransport := globalTable.transport_of_fiberCoherent globalCoherent
  let assignment := globalTable.supportedOpenAssignment
  have targetBoundEq : leftNode.targetBound = rightNode.targetBound :=
    leftNode.plan.decoration_targetBound.symm.trans
      ((staticLift.preservesFiber planStep).targetBound_eq.trans
        rightNode.plan.decoration_targetBound)
  let sourceBoundEq : leftNode.sourceBound = rightNode.sourceBound :=
    congrArg (CostStaticBinderThinning.sourceContextOfTarget source color)
      targetBoundEq
  have targetTypeEq :
      TypeExpr.base
          (CostStaticColor.mapLangSort source color leftNode.sourceSort).1 =
        TypeExpr.base
          (CostStaticColor.mapLangSort source color rightNode.sourceSort).1 := by
    simp only [CostStaticColor.mapLangSort_name]
    exact congrArg
      (fun name => TypeExpr.base ((color.symbols source).sort name))
      (congrArg Subtype.val sourceSortEq)
  let leftSource := leftNode.sourceActionTermIn globalTable leftSubset
  let rightSourceRaw := rightNode.sourceActionTermIn globalTable rightSubset
  let rightSource : CostStaticRegionNode.CostStaticSourceTerm source color
      globalTable.sourceFreeContext globalTable.sourceSupport
      leftNode.sourceBound leftNode.targetBound leftNode.sourceSort :=
    rightSourceRaw.reindex sourceBoundEq targetBoundEq sourceSortEq
  have sourceGenerator :
      CostStaticRegionNode.CostStaticSourceTerm.generator leftSource
        rightSource := by
    unfold CostStaticRegionNode.CostStaticSourceTerm.generator
      openEquationGenerator
    simpa only [leftSource, rightSource, rightSourceRaw,
      CostStaticRegionNode.CostStaticSourceTerm.reindex_pattern,
      CostStaticRegionNode.sourceActionTermIn_pattern,
      leftNode.plan.decoration_abstractPattern,
      rightNode.plan.decoration_abstractPattern] using
      (staticLift.generatorWitness planStep).erase
  have localPath := stable leftNode.thinning assignment
    globalTransport.freeContext globalTransport.reflectiveSupport sourceGenerator
  have openPathRaw :=
    WellSorted.AvailableOpenPattern.equationSetoid_to_openPatternEquationSetoid
      localPath
  have openPath := WellSorted.openPatternEquationSetoid_reindexBound
    (List.append_nil leftNode.targetBound) openPathRaw
  have lifted :=
    WellSorted.AvailableOpenPattern.openPatternEquationSetoid_to_availableWithOuter
      outer openPath
  have leftEndpoint :
      WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
          ((leftSource.actAvailable leftNode.thinning assignment
            globalTransport.freeContext globalTransport.reflectiveSupport
            ).toOpenPattern.reindexBound
              (List.append_nil leftNode.targetBound)) outer =
        (CostRegionTree.static leftNode leftChildren
          ).originalAvailableOpenPattern leftCanonical leftObject leftScope := by
    apply WellSorted.AvailableOpenPattern.ext
    simp only [WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
      WellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern]
    simpa [leftSource, CostStaticRegionNode.CostStaticSourceTerm.act,
      assignment, TypedCostRegionBoundaryTable.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.supportedAssignment,
      ReflectiveContextSupport.substitute, globalTransport] using
      leftNode.restoreMappedAbstractPatternIn_eq_term globalTable leftSubset
  have rightEndpoint :
      WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter
          ((rightSource.actAvailable leftNode.thinning assignment
            globalTransport.freeContext globalTransport.reflectiveSupport
            ).toOpenPattern.reindexBound
              (List.append_nil leftNode.targetBound)) outer =
        ((CostRegionTree.static rightNode rightChildren
          ).originalAvailableOpenPattern rightCanonical rightObject rightScope
          ).reindexFiber targetBoundEq.symm rfl targetTypeEq.symm := by
    apply WellSorted.AvailableOpenPattern.ext
    simp only [WellSorted.AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
      WellSorted.OpenPattern.reindexBound_pattern,
      WellSorted.AvailableOpenPattern.toOpenPattern_pattern,
      CostStaticRegionNode.CostStaticSourceTerm.actAvailable_pattern,
      WellSorted.AvailableOpenPattern.reindexFiber_pattern,
      CostRegionTree.originalAvailableOpenPattern_pattern]
    rw [CostStaticRegionNode.CostStaticSourceTerm.reindex_act_ofTarget
      rightSourceRaw targetBoundEq sourceSortEq assignment]
    simpa [rightSourceRaw,
      CostStaticRegionNode.CostStaticSourceTerm.act,
      assignment, TypedCostRegionBoundaryTable.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.supportedAssignment,
      ReflectiveContextSupport.substitute, globalTransport] using
      rightNode.restoreMappedAbstractPatternIn_eq_term globalTable rightSubset
  rw [leftEndpoint, rightEndpoint] at lifted
  exact lifted

end Mettapedia.GSLT.LanguageDef
