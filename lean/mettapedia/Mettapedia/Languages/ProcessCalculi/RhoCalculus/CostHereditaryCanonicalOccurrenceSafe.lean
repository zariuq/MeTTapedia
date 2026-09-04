import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceAvailability

/-!
# Exact reflective safety at canonical rho occurrences

The static-plan proof retains the authored occurrence that supplied each
semantic atom.  This module first recovers its exact quote-local availability,
then transports that evidence along the typed canonical occurrence trace.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

/-- Application-occurrence inversion retains the complete local zipper, not
only the selected child plan. -/
theorem planOccurrence_application_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {sourceLabel : String}
    {constructor : source.DeclaredCostConstructor}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.application sourceLabel constructor children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .apply sourceLabel
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | application nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

/-- Collection counterpart to application-occurrence zipper inversion. -/
theorem planOccurrence_collection_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {collectionType : CollType}
    {sourceRest : Option String} {choice : CostCollectionTypingChoice}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.collection collectionType sourceRest choice children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .collection collectionType
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) sourceRest ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | collection nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- A semantic atom at an exact static-plan occurrence is safe at the
  quote-local availability determined by that occurrence's zipper. -/
  theorem CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
        plan.abstractPattern = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {targetTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage targetFree
        targetBound pattern (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (targetSafe : targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      {name : String} {context : OneHoleContext}
      {planAvailable : List TypeExpr}
      (planOccurrence : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        plan.decoration context planAvailable)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoCanonicalOccurrenceAvailable reflectiveAvailable context)
          binderImage parameter := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        cases planOccurrence
    | @fvar sourceBound targetBound sourceAvailable thinning outer sourceName
        sourceType targetLookup =>
        cases planOccurrence with
        | sourceFVar =>
            simpa [rhoCanonicalOccurrenceAvailable] using
              sourceLeafSemanticSafeAt targetLookup targetSafe parameter
                nameEquality
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        cases planOccurrence with
        | boundaryApplication =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            simpa [rhoCanonicalOccurrenceAvailable] using
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality
    | application constructor rendered current preimage notBare children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_application_split_context planOccurrence
        obtain ⟨argumentsTyped, argumentsSafe⟩ :=
          applicationArgumentsSafe constructor rendered preimage targetSafe
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have leafSafe :=
          CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree collectionDeterministic globalTable values
              entriesSubset argumentsSafe decomposition nested parameter
                nameEquality childrenPreserve
        rw [contextEquality]
        simpa [rhoCanonicalOccurrenceAvailable] using leafSafe
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern] at frameFree
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | collection choice selected children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_collection_split_context planOccurrence
        obtain ⟨elementsTyped, elementsSafe⟩ :=
          collectionElementsSafe collectionDeterministic choice selected
            targetSafe
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have leafSafe :=
          CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree collectionDeterministic globalTable values
              entriesSubset elementsSafe decomposition nested parameter
                nameEquality childrenPreserve
        rw [contextEquality]
        simpa [rhoCanonicalOccurrenceAvailable] using leafSafe
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        cases planOccurrence with
        | boundaryCollection =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            simpa [rhoCanonicalOccurrenceAvailable] using
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to exact quote-local leaf safety. -/
  theorem CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {argumentsTyped : WellSorted.ArgumentsHaveTypes
        rhoCIGSLT.costWholeLanguage targetFree targetBound arguments
          (parameters.map (mapTermParam (color.symbols rhoCIGSLT)))}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoCanonicalOccurrenceAvailable reflectiveAvailable inner)
          binderImage parameter := by
    cases plan with
    | nil => simp [CostStaticArgumentPlan.decorations] at decomposition
    | cons representation parameterType head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          argumentsSafeAt_cons_map (source := rhoCIGSLT) (color := color)
            parameterType argumentsSafe
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree
                head.abstractPattern = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticArgumentPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticArgumentPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            exact CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              head freeParts.1 collectionDeterministic globalTable values
                headSubset headSafe parameter headOccurrence nameEquality
                  childrenPreserve
        | cons skipped selectedBefore =>
            simp only [CostStaticArgumentPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticArgumentPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              tail freeParts.2 collectionDeterministic globalTable values
                tailSubset tailSafe decomposition.2 nested parameter
                  nameEquality childrenPreserve
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-collection companion to exact quote-local leaf safety. -/
  theorem CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic rhoCIGSLT.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {elementsTyped : WellSorted.ElementsHaveType
        rhoCIGSLT.costWholeLanguage targetFree targetBound elements
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceElementType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (elementsSafe : elementsTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support reflectiveAvailable
          binderImage)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence rhoCIGSLT color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticSemanticLeafSafeAt support
        (rhoCanonicalOccurrenceAvailable reflectiveAvailable inner)
          binderImage parameter := by
    cases plan with
    | nil => simp [CostStaticElementPlan.decorations] at decomposition
    | cons head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          elementsSafeAt_cons (source := rhoCIGSLT) elementsSafe
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree
                head.abstractPattern = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticElementPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticElementPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            exact CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              head freeParts.1 collectionDeterministic globalTable values
                headSubset headSafe parameter headOccurrence nameEquality
                  childrenPreserve
        | cons skipped selectedBefore =>
            simp only [CostStaticElementPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticElementPlan.semanticLeafSafeAt_quoteLocal
              (name := name) (planAvailable := planAvailable)
              tail freeParts.2 collectionDeterministic globalTable values
                tailSubset tailSafe decomposition.2 nested parameter
                  nameEquality childrenPreserve
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- Every selected semantic atom is safe at the quote-local availability of
its exact authored plan occurrence. -/
theorem occurrenceAtomSafeAt_quoteLocal
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (position : inventory.Occurrence) :
    (inventory.occurrenceAtom position).normalTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support
        (rhoCanonicalOccurrenceAvailable available
          (planDecorationOccurrenceAt node inventory position).context)
        binderImage := by
  let positional := planDecorationOccurrenceAt node inventory position
  obtain ⟨packed⟩ := nonempty_planOccurrenceAt node inventory position
  rcases packed with ⟨planAvailable, planOccurrence⟩
  let parameter := inventory.occurrenceAt position
  have nameEquality : parameter.fvarOccurrence.name = positional.name :=
    (planDecorationOccurrenceAt_name node inventory position).symm
  have planFree : WellSorted.ReflectiveSubstitutionBinderFree
      node.plan.abstractPattern = true :=
    CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
      ⟨node.sourceSort.1, rfl⟩
  have semanticSafe :=
    CostStaticRegionPlan.semanticLeafSafeAt_quoteLocal node.plan planFree
      rho_costWholeLanguage_collectionChoiceDeterministic node.boundaryTable
        values (fun _ membership => membership) inputSafe parameter
          planOccurrence.1 nameEquality childrenPreserve
  exact semanticSafe.atomSafe

/-- A semantic atom selected by a final canonical occurrence is safe at the
final occurrence's quote-local availability.  Equal-availability ancestry
uses the exact authored certificate; a Quote/Drop exposure is Name-sorted and
therefore transports from the sealed regime by rho's name-result law. -/
theorem rhoCanonicalOccurrence_atomSafeAt_targetAvailable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt node
          (CostStaticAtomEnvironment.ofInventory inventory))
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame
          (CostStaticAtomEnvironment.ofInventory inventory)).1)) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
      targetOccurrence
    (inventory.occurrenceAtom
      ancestry.sourcePosition).normalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support
          (rhoCanonicalOccurrenceAvailable available
            targetOccurrence.context) binderImage := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  have sourceSafe := occurrenceAtomSafeAt_quoteLocal node values inventory
    support available binderImage childrenPreserve inputSafe
      ancestry.sourcePosition
  have occurrenceAncestry :=
    rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
      node environment targetOccurrence available
  rcases occurrenceAncestry with sameAvailable | exposure
  · rw [sameAvailable] at sourceSafe
    exact sourceSafe
  · have safeAtNil :
        (inventory.occurrenceAtom
          ancestry.sourcePosition).normalTyped.ReflectiveSupportSafeAt
            rhoCIGSLT.costWholeReflectionProfile support [] binderImage := by
      rw [exposure.1] at sourceSafe
      exact sourceSafe
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    have sourceMembership :
        rhoReflectivePresentation.toReflectivePresentationDecl ∈
          rhoCIGSLT.reflection.1.presentations := by
      change rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoReflectionProfile.presentations
      simp [rhoReflectionProfile]
    have declarationMembership : declaration ∈
        rhoCIGSLT.costWholeReflectionProfile.presentations := by
      simpa [declaration] using
        costStaticReflectivePresentationDecl_mem rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
            sourceMembership
    have mappedType := node.semanticAtom_typeMap values inventory
      (environment.occurrenceSlot ancestry.sourcePosition)
    rw [environment.occurrenceValue] at mappedType
    have sourceTypeName :
        (inventory.occurrenceAtom
          ancestry.sourcePosition).key.sourceType = TypeExpr.name := by
      rw [← environment.occurrenceValue]
      exact exposure.2
    have targetTypeName :
        (inventory.occurrenceAtom
          ancestry.sourcePosition).key.targetType =
            .base declaration.nameSort := by
      calc
        (inventory.occurrenceAtom
            ancestry.sourcePosition).key.targetType =
            mapTypeExpr (color.symbols rhoCIGSLT)
              (inventory.occurrenceAtom
                ancestry.sourcePosition).key.sourceType :=
          mappedType.symm
        _ = mapTypeExpr (color.symbols rhoCIGSLT) TypeExpr.name := by
          rw [sourceTypeName]
        _ = .base declaration.nameSort := by
          have interactingName :
              rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := by
            rfl
          cases color <;>
            simp [declaration, costStaticReflectivePresentationDecl_eq_map,
              mapReflectivePresentation, CostStaticColor.symbols,
              costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
              costWrappedStaticSymbols, rhoReflectivePresentation,
              mapTypeExpr, TypeExpr.name, TypeExpr.baseType,
              interactingName, show "Name" ≠ "Proc" by decide]
    exact
      WellSorted.HasType.ReflectiveSupportSafeAt.nameResult_of_nil
        rho_costReflectiveNameResultsQuoted declaration declarationMembership
          (inventory.occurrenceAtom
            ancestry.sourcePosition).normalTyped targetTypeName
              safeAtNil
                (inventory.occurrenceAtom
                  ancestry.sourcePosition).normalObject
                    (rhoCanonicalOccurrenceAvailable available
                      targetOccurrence.context)

/-! ## Reconstructing a frame certificate from exact occurrences -/

/-- Every free-variable occurrence of a static frame has enough quote-local
availability for the support assigned to its spelling. -/
def RhoCanonicalOccurrenceSupportBounded (support : ContextSupport.Support)
    (available : List TypeExpr) (pattern : Pattern) : Prop :=
  ∀ occurrence : CostStaticFVarOccurrence pattern,
    support occurrence.name <:+
      rhoCanonicalOccurrenceAvailable available occurrence.context

/-- List-indexed companion to canonical occurrence support bounds. -/
def RhoCanonicalListOccurrenceSupportBounded (support : ContextSupport.Support)
    (available : List TypeExpr) (patterns : List Pattern) : Prop :=
  ∀ occurrence : CostStaticFVarListOccurrence patterns,
    support occurrence.occurrence.name <:+
      rhoCanonicalOccurrenceAvailable available occurrence.occurrence.context

private theorem rhoCIGSLT_reflection_eq_rhoReflectionProfile :
    rhoCIGSLT.reflection.1 = rhoReflectionProfile := rfl

theorem rhoCanonicalListOccurrenceSupportBounded_of_apply
    (support : ContextSupport.Support) (available : List TypeExpr)
    (constructor : String) (arguments : List Pattern)
    (bounded : RhoCanonicalOccurrenceSupportBounded support available
      (.apply constructor arguments)) :
    RhoCanonicalListOccurrenceSupportBounded support
      (if ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
          constructor then [] else available) arguments := by
  intro occurrence
  have selected := bounded (occurrence.inApply constructor)
  change support occurrence.occurrence.name <:+
    rhoCanonicalOccurrenceAvailable
      (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
        constructor then [] else available) occurrence.occurrence.context at selected
  rw [rhoCIGSLT_reflection_eq_rhoReflectionProfile] at selected
  exact selected

theorem rhoCanonicalListOccurrenceSupportBounded_of_collection
    (support : ContextSupport.Support) (available : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern)
    (rest : Option String)
    (bounded : RhoCanonicalOccurrenceSupportBounded support available
      (.collection collectionType elements rest)) :
    RhoCanonicalListOccurrenceSupportBounded support available elements := by
  intro occurrence
  have selected := bounded (occurrence.inCollection collectionType rest)
  simpa [RhoCanonicalOccurrenceSupportBounded,
    RhoCanonicalListOccurrenceSupportBounded,
    CostStaticFVarListOccurrence.inCollection,
    rhoCanonicalOccurrenceAvailable] using selected

theorem rhoCanonicalOccurrenceSupportBounded_head
    (support : ContextSupport.Support) (available : List TypeExpr)
    (head : Pattern) (tail : List Pattern)
    (bounded : RhoCanonicalListOccurrenceSupportBounded support available
      (head :: tail)) :
    RhoCanonicalOccurrenceSupportBounded support available head := by
  intro occurrence
  let selected : CostStaticFVarListOccurrence (head :: tail) :=
    { position := ⟨0, by simp⟩
      occurrence := occurrence }
  exact bounded selected

theorem rhoCanonicalListOccurrenceSupportBounded_tail
    (support : ContextSupport.Support) (available : List TypeExpr)
    (head : Pattern) (tail : List Pattern)
    (bounded : RhoCanonicalListOccurrenceSupportBounded support available
      (head :: tail)) :
    RhoCanonicalListOccurrenceSupportBounded support available tail := by
  intro occurrence
  let selected : CostStaticFVarListOccurrence (head :: tail) :=
    { position := Fin.succ occurrence.position
      occurrence := occurrence.occurrence }
  exact bounded selected

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- A binder-free rho frame is support-safe if each exact occurrence has the
  suffix required at its own quote-local zipper. -/
  theorem WellSorted.HasType.rhoCanonicalFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType rhoCalc free bound pattern type)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFree pattern = true)
      (bounded : RhoCanonicalOccurrenceSupportBounded support available pattern) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | bvar lookup => exact .bvar lookup available
    | @fvar bound name type lookup =>
        have suffix := bounded
          ({ name := name
             context := .hole
             selected := Selects.here } : CostStaticFVarOccurrence (.fvar name))
        exact .fvar lookup available (by
          exact List.suffix_iff_exists_eq_append.mp
            (by simpa [rhoCanonicalOccurrenceAvailable] using suffix))
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        have argumentsFree : WellSorted.ReflectiveSubstitutionBinderFreeList
            arguments = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
            rhoReflectionProfile rule.label = true
        · have argumentsBounded :=
            rhoCanonicalListOccurrenceSupportBounded_of_apply support available
              rule.label arguments bounded
          have argumentsSafe :=
            WellSorted.ArgumentsHaveTypes.rhoCanonicalFrame_supportSafe_of_occurrences
              (binderImage := binderImage) argumentsTyped argumentsFree
                (by simpa [quoted] using argumentsBounded)
          exact .constructorQuote (membership := membership)
            (notBare := notBare) quoted argumentsSafe
        · have ordinary : ReflectiveContextSupport.isQuoteConstructor
              rhoReflectionProfile rule.label = false :=
            Bool.eq_false_of_not_eq_true quoted
          have argumentsBounded :=
            rhoCanonicalListOccurrenceSupportBounded_of_apply support available
              rule.label arguments bounded
          have argumentsSafe :=
            WellSorted.ArgumentsHaveTypes.rhoCanonicalFrame_supportSafe_of_occurrences
              (binderImage := binderImage) argumentsTyped argumentsFree
                (by simpa [ordinary] using argumentsBounded)
          exact .constructorOrdinary (membership := membership)
            (notBare := notBare) ordinary argumentsSafe
    | lambda bodyTyped =>
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | multiLambda bodyTyped =>
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | subst bodyTyped replacementTyped =>
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have elementsFree : WellSorted.ReflectiveSubstitutionBinderFreeList
            elements = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have elementsBounded :=
          rhoCanonicalListOccurrenceSupportBounded_of_collection support available
            collectionType elements rest bounded
        exact .collection
          (WellSorted.ElementsHaveType.rhoCanonicalFrame_supportSafe_of_occurrences
            elementsTyped elementsFree elementsBounded)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        have elementsFree : WellSorted.ReflectiveSubstitutionBinderFreeList
            elements = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have elementsBounded :=
          rhoCanonicalListOccurrenceSupportBounded_of_collection support available
            collectionType elements rest bounded
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (WellSorted.ElementsHaveType.rhoCanonicalFrame_supportSafe_of_occurrences
            elementsTyped elementsFree elementsBounded)
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion to canonical occurrence reconstruction. -/
  theorem WellSorted.ArgumentsHaveTypes.rhoCanonicalFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
        parameters)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        arguments = true)
      (bounded : RhoCanonicalListOccurrenceSupportBounded support available
        arguments) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | nil => exact .nil bound available
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree argument = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                arguments = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (WellSorted.HasType.rhoCanonicalFrame_supportSafe_of_occurrences
            argumentTyped freeParts.1
              (rhoCanonicalOccurrenceSupportBounded_head support available
                argument arguments bounded))
          (WellSorted.ArgumentsHaveTypes.rhoCanonicalFrame_supportSafe_of_occurrences
            argumentsTyped freeParts.2
              (rhoCanonicalListOccurrenceSupportBounded_tail support available
                argument arguments bounded))
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-element companion to canonical occurrence reconstruction. -/
  theorem WellSorted.ElementsHaveType.rhoCanonicalFrame_supportSafe_of_occurrences
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveType rhoCalc free bound elements
        elementType)
      {support : ContextSupport.Support} {available : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        elements = true)
      (bounded : RhoCanonicalListOccurrenceSupportBounded support available
        elements) :
      typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
        binderImage := by
    cases typed with
    | nil => exact .nil bound elementType available
    | @cons bound element elements elementType elementTyped elementsTyped =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree element = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                elements = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        exact .cons
          (WellSorted.HasType.rhoCanonicalFrame_supportSafe_of_occurrences
            elementTyped freeParts.1
              (rhoCanonicalOccurrenceSupportBounded_head support available
                element elements bounded))
          (WellSorted.ElementsHaveType.rhoCanonicalFrame_supportSafe_of_occurrences
            elementsTyped freeParts.2
              (rhoCanonicalListOccurrenceSupportBounded_tail support available
                element elements bounded))
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-! ## Exact occurrence support quotient -/

/-- The finite support quotient whose positional availability is exactly the
quote-local availability of the authored zipper. -/
noncomputable def quoteLocalOccurrenceSupportProfile
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    CostStaticOccurrenceSupportProfile
      (CostStaticAtomEnvironment.ofInventory inventory) support binderImage := by
  let occurrenceAvailable : inventory.Occurrence → List TypeExpr :=
    fun position => rhoCanonicalOccurrenceAvailable available
      (planDecorationOccurrenceAt node inventory position).context
  let classSupport : OccurrenceClassSupport
      (CostStaticAtomEnvironment.ofInventory inventory).occurrenceSlot :=
    OccurrenceClassSupport.ofSurjective occurrenceAvailable
      (CostStaticAtomEnvironment.ofInventory_occurrenceSlot_surjective
        inventory)
  exact
    { classSupport := classSupport
      occurrenceSafe := by
        intro position
        exact occurrenceAtomSafeAt_quoteLocal node values inventory support
          available binderImage childrenPreserve inputSafe position }

@[simp]
theorem quoteLocalOccurrenceSupportProfile_occurrenceAvailable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (position : inventory.Occurrence) :
    (quoteLocalOccurrenceSupportProfile node values inventory support available
      binderImage childrenPreserve inputSafe).classSupport.occurrenceAvailable
        position =
      rhoCanonicalOccurrenceAvailable available
        (planDecorationOccurrenceAt node inventory position).context := rfl

/-- The GCS support selected from exact authored positions is sufficient at
every free-variable occurrence of the canonical source frame. -/
theorem semanticCanonicalizedSourcePattern_supportBounded
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    RhoCanonicalOccurrenceSupportBounded profile.semanticInputSupport available
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  change RhoCanonicalOccurrenceSupportBounded profile.semanticInputSupport
    available
    (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
      rhoReflectivePresentation node.targetBound.length 0
      (node.reifiedSourceFrame environment).1)
  intro targetOccurrence
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  have classToAuthored := profile.atomAvailable_suffix_occurrenceAvailable
    ancestry.sourcePosition
  have occurrenceAvailable :
      profile.classSupport.occurrenceAvailable ancestry.sourcePosition =
        rhoCanonicalOccurrenceAvailable available
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context := by
    exact quoteLocalOccurrenceSupportProfile_occurrenceAvailable node values
      inventory support available binderImage childrenPreserve inputSafe
        ancestry.sourcePosition
  have occurrenceAncestry :=
    rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
      node environment targetOccurrence available
  have classToTarget : profile.classSupport.classAvailable
      (environment.occurrenceSlot ancestry.sourcePosition) <:+
        rhoCanonicalOccurrenceAvailable available targetOccurrence.context := by
    rcases occurrenceAncestry with sameAvailable | exposure
    · rw [occurrenceAvailable, sameAvailable] at classToAuthored
      exact classToAuthored
    · rw [occurrenceAvailable, exposure.1] at classToAuthored
      have classEmpty : profile.classSupport.classAvailable
          (environment.occurrenceSlot ancestry.sourcePosition) = [] := by
        obtain ⟨prefixPart, prefixEquality⟩ := classToAuthored
        exact (List.append_eq_nil_iff.mp prefixEquality).2
      rw [classEmpty]
      exact List.nil_suffix
  rw [ancestry.target_name_eq_atomName]
  rw [profile.semanticInputSupport_atomName]
  exact classToTarget

/-- The canonical source frame is safe for the GCS support derived from its
exact authored occurrences at the caller's availability. -/
theorem semanticCanonicalizedSourceFrame_supportSafeAt_quoteLocalGCS
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    ∃ sourceNormalized : WellSorted.HasTypeWithConstructors rhoCalc
        (· ∈ rhoContinuationRetyping.wrappedLabels)
        environment.sourceAtomFreeContext node.sourceBound
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1)
        (.base node.sourceSort.1),
      sourceNormalized.toHasType.ReflectiveSupportSafeAt rhoReflectionProfile
        profile.semanticInputSupport available
          (mapTypeExpr (color.symbols rhoCIGSLT)) := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  change ∃ sourceNormalized : WellSorted.HasTypeWithConstructors rhoCalc
      (· ∈ rhoContinuationRetyping.wrappedLabels)
      environment.sourceAtomFreeContext node.sourceBound
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)
      (.base node.sourceSort.1),
    sourceNormalized.toHasType.ReflectiveSupportSafeAt rhoReflectionProfile
      profile.semanticInputSupport available
        (mapTypeExpr (color.symbols rhoCIGSLT))
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have sourceSafe : sourceSupported.toHasType.ReflectiveSupportSafeAt
      rhoReflectionProfile environment.sourceAtomSupport node.targetBound
      (mapTypeExpr (color.symbols rhoCIGSLT)) :=
    (node.reifiedSourceFrame_supportSafe environment).castTyping
  obtain ⟨sourceNormalized, _sourceNormalizedSafe⟩ :=
    rhoCanonicalizeByDepths_hasTypeWithConstructors
      (sourceSemanticPatternKeyAt node environment) 0 sourceSupported
        sourceSafe (by trivial)
          (node.reifiedSourceFrame environment).2.1.2.2.1
  have bounded : RhoCanonicalOccurrenceSupportBounded
      profile.semanticInputSupport available
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1) :=
    semanticCanonicalizedSourcePattern_supportBounded node values inventory
      support available binderImage childrenPreserve inputSafe
  have safe :=
    WellSorted.HasType.rhoCanonicalFrame_supportSafe_of_occurrences
      sourceNormalized.toHasType
      (rhoReflectiveSubstitutionBinderFree_canonicalizeByDepths
        (sourceSemanticPatternKeyAt node environment)
          node.targetBound.length 0 (node.reifiedSourceFrame environment).1
            (reifiedSourceFrame_binderFree node environment)) bounded
      (binderImage := mapTypeExpr (color.symbols rhoCIGSLT))
  exact ⟨sourceNormalized, safe⟩

/-! ## Generated target-frame transport -/

mutual
  /-- Static symbol mapping changes labels and sorts but never introduces a
  binder or an explicit substitution node. -/
  theorem rhoReflectiveSubstitutionBinderFree_mapPattern
      (symbols : LanguageDefSymbolMap) : ∀ pattern,
      WellSorted.ReflectiveSubstitutionBinderFree (mapPattern symbols pattern) =
        WellSorted.ReflectiveSubstitutionBinderFree pattern
    | .bvar _ => rfl
    | .fvar _ => by
        simp [mapPattern, WellSorted.ReflectiveSubstitutionBinderFree]
    | .apply constructor arguments => by
        simp only [mapPattern, WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_mapPattern symbols
          arguments
    | .lambda _ _ => rfl
    | .multiLambda _ _ _ => rfl
    | .subst _ _ => by
        simp [mapPattern, WellSorted.ReflectiveSubstitutionBinderFree]
    | .collection collectionType elements rest => by
        simp only [mapPattern, WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_mapPattern symbols
          elements
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- List companion to binder-freedom under static symbol mapping. -/
  theorem rhoReflectiveSubstitutionBinderFreeList_mapPattern
      (symbols : LanguageDefSymbolMap) : ∀ patterns,
      WellSorted.ReflectiveSubstitutionBinderFreeList
          (mapPatternList symbols patterns) =
        WellSorted.ReflectiveSubstitutionBinderFreeList patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [mapPatternList,
          WellSorted.ReflectiveSubstitutionBinderFreeList,
          rhoReflectiveSubstitutionBinderFree_mapPattern symbols pattern,
          rhoReflectiveSubstitutionBinderFreeList_mapPattern symbols patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

mutual
  /-- Certified ambient-binder reinsertion changes indices but cannot add
  binder syntax to a binder-free frame. -/
  theorem rhoReflectiveSubstitutionBinderFree_thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) (depth : Nat) : ∀ pattern,
      WellSorted.ReflectiveSubstitutionBinderFree
          (thinning.thickenAmbientBVars depth pattern) =
        WellSorted.ReflectiveSubstitutionBinderFree pattern
    | .bvar _ => by
        simp [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | .fvar _ => by
        simp [CostStaticBinderThinning.thickenAmbientBVars]
    | .apply constructor arguments => by
        simp only [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_thickenAmbientBVars
          thinning depth arguments
    | .lambda _ _ => by
        simp [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | .multiLambda _ _ _ => by
        simp [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | .subst _ _ => by
        simp [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | .collection collectionType elements rest => by
        simp only [CostStaticBinderThinning.thickenAmbientBVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_thickenAmbientBVars
          thinning depth elements
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- List companion to binder-freedom under ambient-binder reinsertion. -/
  theorem rhoReflectiveSubstitutionBinderFreeList_thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) (depth : Nat) : ∀ patterns,
      WellSorted.ReflectiveSubstitutionBinderFreeList
          (patterns.map (thinning.thickenAmbientBVars depth)) =
        WellSorted.ReflectiveSubstitutionBinderFreeList patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map,
          WellSorted.ReflectiveSubstitutionBinderFreeList,
          rhoReflectiveSubstitutionBinderFree_thickenAmbientBVars
            thinning depth pattern,
          rhoReflectiveSubstitutionBinderFreeList_thickenAmbientBVars
            thinning depth patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- The mapped and ambient-thickened target canonical frame retains the
caller-side GCS certificate derived from exact source occurrences. -/
theorem canonicalizeReifiedTargetFrame_supportSafeAt_quoteLocalGCS
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let environment := CostStaticAtomEnvironment.ofInventory inventory
    let profile := quoteLocalOccurrenceSupportProfile node values inventory
      support available binderImage childrenPreserve inputSafe
    ∃ targetTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage
        environment.atomFreeContext node.targetBound
        (node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation))
        (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
      targetTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile profile.semanticInputSupport
          available binderImage := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  let profile := quoteLocalOccurrenceSupportProfile node values inventory
    support available binderImage childrenPreserve inputSafe
  change ∃ targetTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage
      environment.atomFreeContext node.targetBound
      (node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1),
    targetTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile profile.semanticInputSupport
        available binderImage
  obtain ⟨sourceNormalized, sourceSafe⟩ :=
    semanticCanonicalizedSourceFrame_supportSafeAt_quoteLocalGCS node values
      inventory support available binderImage childrenPreserve inputSafe
  obtain ⟨mappedTypedRaw, mappedSafeRaw⟩ :=
    sourceSafe.mapCostStatic rhoCIGSLT color
      sourceNormalized.constructorsWithin
  have contextEquality :
      environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT) =
        environment.atomFreeContext :=
    environment.sourceAtomFreeContext_map_eq_atomFreeContext
      (node.semanticAtom_typeMap values inventory)
  rw [← contextEquality]
  let thickenedTypedRaw := mappedTypedRaw.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedSafeRaw := mappedSafeRaw.thickenAmbientBVars
    (inner := []) node.thinning
  have thickenedTyped : WellSorted.HasType rhoCIGSLT.costWholeLanguage
      (environment.sourceAtomFreeContext.map (color.symbols rhoCIGSLT))
      node.targetBound
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1)))
      (.base (color.mapLangSort rhoCIGSLT node.sourceSort).1) := by
    simpa only [List.nil_append, List.length_nil, mapTypeExpr,
      CostStaticColor.mapLangSort_name] using thickenedTypedRaw
  have thickenedSafeId : thickenedTyped.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile profile.semanticInputSupport
      available id :=
    thickenedSafeRaw.castTyping
  have sourceFrameFree :=
    rhoReflectiveSubstitutionBinderFree_canonicalizeByDepths
      (sourceSemanticPatternKeyAt node environment)
        node.targetBound.length 0 (node.reifiedSourceFrame environment).1
          (reifiedSourceFrame_binderFree node environment)
  have mappedFrameFree : WellSorted.ReflectiveSubstitutionBinderFree
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation node.targetBound.length 0
          (node.reifiedSourceFrame environment).1)) = true := by
    rw [rhoReflectiveSubstitutionBinderFree_mapPattern]
    exact sourceFrameFree
  have thickenedFrameFree : WellSorted.ReflectiveSubstitutionBinderFree
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame environment).1))) = true := by
    rw [rhoReflectiveSubstitutionBinderFree_thickenAmbientBVars]
    exact mappedFrameFree
  have thickenedSafe :=
    thickenedSafeId.changeBinderImage_of_binderFree thickenedFrameFree
      binderImage
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize node
    environment]
  exact ⟨thickenedTyped, thickenedSafe⟩

/-! ## Positional transport into the generated target frame -/

/-- Quote-local availability in the generated rho Cost frame. -/
def rhoCostCanonicalOccurrenceAvailable (ambient : List TypeExpr) :
    OneHoleContext → List TypeExpr
  | .hole => ambient
  | .apply constructor _ inner _ =>
      rhoCostCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile constructor then [] else ambient)
          inner
  | .lambda _ inner => rhoCostCanonicalOccurrenceAvailable ambient inner
  | .multiLambda _ _ inner =>
      rhoCostCanonicalOccurrenceAvailable ambient inner
  | .substBody inner _ => rhoCostCanonicalOccurrenceAvailable ambient inner
  | .substReplacement _ inner =>
      rhoCostCanonicalOccurrenceAvailable ambient inner
  | .collection _ _ inner _ _ =>
      rhoCostCanonicalOccurrenceAvailable ambient inner

/-- Static symbol mapping preserves every quote boundary crossed by a source
occurrence zipper. -/
theorem rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext
    (color : CostStaticColor) (ambient : List TypeExpr) :
    ∀ context : OneHoleContext,
      rhoCostCanonicalOccurrenceAvailable ambient
          (CIGSLT.mapOneHoleContext (color.symbols rhoCIGSLT) context) =
        rhoCanonicalOccurrenceAvailable ambient context
  | .hole => rfl
  | .apply constructor before inner after => by
      simp only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable,
        reflectiveIsQuoteConstructor_mapCostStatic]
      exact rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color
        (if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 constructor then [] else ambient) inner
  | .lambda binder inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
          inner
  | .multiLambda arity binders inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
          inner
  | .substBody inner replacement => by
      simpa only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
          inner
  | .substReplacement body inner => by
      simpa only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
          inner
  | .collection collectionType before inner after rest => by
      simpa only [CIGSLT.mapOneHoleContext,
        rhoCostCanonicalOccurrenceAvailable,
        rhoCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
          inner

/-- Ambient de Bruijn renaming changes indices and hole depth, but cannot
change a quote boundary crossed by a selected occurrence. -/
theorem rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt
    (rename : Nat → Nat) : ∀ (depth : Nat) (ambient : List TypeExpr)
      (context : OneHoleContext),
      rhoCostCanonicalOccurrenceAvailable ambient
          (ContextSubstitution.renameAmbientContextAt rename depth context).1 =
        rhoCostCanonicalOccurrenceAvailable ambient context
  | _, _, .hole => rfl
  | depth, ambient, .apply constructor before inner after => by
      simp only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable]
      exact rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
        depth
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.costWholeReflectionProfile constructor then [] else ambient)
            inner
  | depth, ambient, .lambda binder inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
          (depth + 1) ambient inner
  | depth, ambient, .multiLambda arity binders inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
          (depth + arity) ambient inner
  | depth, ambient, .substBody inner replacement => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
          (depth + 1) ambient inner
  | depth, ambient, .substReplacement body inner => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
          depth ambient inner
  | depth, ambient, .collection collectionType before inner after rest => by
      simpa only [ContextSubstitution.renameAmbientContextAt,
        rhoCostCanonicalOccurrenceAvailable] using
        rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt rename
          depth ambient inner

/-- An exact generated target occurrence reflects to a source canonical
occurrence with the same name and the same quote-local availability. -/
theorem exists_sourceOccurrence_of_mappedThickenedOccurrence
    {color : CostStaticColor} {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound) (sourceRoot : Pattern) (ambient : List TypeExpr)
    (targetOccurrence : CostStaticFVarOccurrence
      (thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT) sourceRoot))) :
    ∃ sourceOccurrence : CostStaticFVarOccurrence sourceRoot,
      sourceOccurrence.name = targetOccurrence.name ∧
        rhoCanonicalOccurrenceAvailable ambient sourceOccurrence.context =
          rhoCostCanonicalOccurrenceAvailable ambient
            targetOccurrence.context := by
  obtain ⟨mappedPayload, mappedContext, holeDepth, mappedSelected,
      mappedContextEquality, mappedPayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_thickenAmbientBVars
      thinning 0 targetOccurrence.selected
  have mappedPayloadShape : mappedPayload = .fvar targetOccurrence.name := by
    cases mappedPayload <;>
      simp_all [CostStaticBinderThinning.thickenAmbientBVars]
  subst mappedPayload
  obtain ⟨sourcePayload, sourceContext, sourceSelected,
      sourceContextEquality, sourcePayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_mapPattern
      (color.symbols rhoCIGSLT) mappedSelected
  cases sourcePayload with
  | bvar index => simp [mapPattern] at sourcePayloadEquality
  | fvar sourceName =>
      simp only [mapPattern, Pattern.fvar.injEq] at sourcePayloadEquality
      let sourceOccurrence : CostStaticFVarOccurrence sourceRoot :=
        { name := sourceName
          context := sourceContext
          selected := sourceSelected }
      refine ⟨sourceOccurrence, sourcePayloadEquality, ?_⟩
      have mappedContextTarget :
          (ContextSubstitution.renameAmbientContextAt thinning.toTargetIndex 0
            mappedContext).1 = targetOccurrence.context :=
        congrArg Prod.fst mappedContextEquality
      calc
        rhoCanonicalOccurrenceAvailable ambient sourceOccurrence.context =
            rhoCostCanonicalOccurrenceAvailable ambient
              (CIGSLT.mapOneHoleContext (color.symbols rhoCIGSLT)
                sourceContext) :=
          (rhoCostCanonicalOccurrenceAvailable_mapOneHoleContext color ambient
            sourceContext).symm
        _ = rhoCostCanonicalOccurrenceAvailable ambient mappedContext := by
          rw [sourceContextEquality]
        _ = rhoCostCanonicalOccurrenceAvailable ambient
              (ContextSubstitution.renameAmbientContextAt
                thinning.toTargetIndex 0 mappedContext).1 :=
          (rhoCostCanonicalOccurrenceAvailable_renameAmbientContextAt
            thinning.toTargetIndex 0 ambient mappedContext).symm
        _ = rhoCostCanonicalOccurrenceAvailable ambient
              targetOccurrence.context := by
          rw [mappedContextTarget]
  | apply constructor arguments => simp [mapPattern] at sourcePayloadEquality
  | lambda binder body => simp [mapPattern] at sourcePayloadEquality
  | multiLambda arity binders body =>
      simp [mapPattern] at sourcePayloadEquality
  | subst body replacement => simp [mapPattern] at sourcePayloadEquality
  | collection collectionType elements rest =>
      simp [mapPattern] at sourcePayloadEquality

/-- The restoration value selected for a generated target occurrence is safe
at that occurrence's exact generated quote-local availability. -/
theorem mappedThickenedCanonicalOccurrence_assignmentSafeAt
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    {type : TypeExpr}
    (targetOccurrence : CostStaticFVarOccurrence
      (node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (sourceSemanticPatternKeyAt node
              (CostStaticAtomEnvironment.ofInventory inventory))
            rhoReflectivePresentation node.targetBound.length 0
            (node.reifiedSourceFrame
              (CostStaticAtomEnvironment.ofInventory inventory)).1))))
    (lookup : (CostStaticAtomEnvironment.ofInventory inventory).atomFreeContext
      targetOccurrence.name = some type) :
    ((CostStaticAtomEnvironment.ofInventory
        inventory).restorationSupportedOpenAssignment.typed
      lookup).ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support
          (rhoCostCanonicalOccurrenceAvailable available
            targetOccurrence.context) binderImage := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  obtain ⟨sourceOccurrence, nameEquality, availabilityEquality⟩ :=
    exists_sourceOccurrence_of_mappedThickenedOccurrence node.thinning
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1) available targetOccurrence
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    sourceOccurrence
  have sourceSafe := rhoCanonicalOccurrence_atomSafeAt_targetAvailable node
    values inventory support available binderImage childrenPreserve inputSafe
      sourceOccurrence
  have targetName : targetOccurrence.name =
      environment.atomName
        (environment.occurrenceSlot ancestry.sourcePosition) :=
    nameEquality.symm.trans ancestry.target_name_eq_atomName
  rw [targetName, environment.atomFreeContext_atomName] at lookup
  have typeEquality :
      (environment.atomValue
        (environment.occurrenceSlot ancestry.sourcePosition)).key.targetType =
          type := Option.some.inj lookup
  subst type
  have valueEquality : environment.atomValue
      (environment.occurrenceSlot ancestry.sourcePosition) =
        inventory.occurrenceAtom ancestry.sourcePosition :=
    environment.occurrenceValue ancestry.sourcePosition
  rw [← availabilityEquality]
  simp only [CostStaticAtomEnvironment.restorationSupportedOpenAssignment,
    CostStaticAtomEnvironment.restorationAssignment]
  convert sourceSafe using 2 <;>
    simp [environment, ancestry, targetName, valueEquality,
      CostStaticAtomEnvironment.restorationSupport,
      CostStaticAtomEnvironment.lookupAtom?_atomName]

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
