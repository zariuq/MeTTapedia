import Mettapedia.GSLT.LanguageDef.CostAvailabilityTransposedPlanReification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryPlanOccurrenceAvailability

/-!
# Availability transposition for hereditary rho normalization

The hereditary planner may move an ambient binder suffix from inert outer
context into active availability.  This module transports the resulting
endpoint-local restoration alignment through the selected-color keyed
canonicalizer.  The theorem is restricted to the selected static constructor
fragment: the generated reflection profile contains both Cost colors, while
an atomized static frame contains constructors from exactly one color.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

/-- Inside one selected static color, the generated reflection profile marks
exactly the mapped authored rho quotation constructor as a quote boundary. -/
private theorem rhoCostStatic_quoteIff_of_decodes
    (color : CostStaticColor) (constructor sourceConstructor : String)
    (decoded : decodeCostStaticConstructor color constructor =
      some sourceConstructor) :
    ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile constructor = true ↔
      constructor =
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).quoteConstructor := by
  have constructorEq :
      constructor = (color.symbols rhoCIGSLT).constructor sourceConstructor := by
    rw [CostStaticColor.symbols_constructor]
    exact (decodeCostStaticConstructor_eq_some_iff color constructor
      sourceConstructor).mp decoded
  subst constructor
  rw [reflectiveIsQuoteConstructor_mapCostStatic]
  rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
  rw [costStaticReflectivePresentationDecl_eq_map]
  simp only [mapReflectivePresentation,
    CostStaticColor.reflectiveSymbols_toPresentationSymbols]
  change
    ReflectiveContextSupport.isQuoteConstructor rhoReflectionProfile
        sourceConstructor = true ↔
      (color.symbols rhoCIGSLT).constructor sourceConstructor =
        (color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor
  constructor
  · intro recognized
    apply congrArg (color.symbols rhoCIGSLT).constructor
    have reversed : rhoReflectivePresentation.quoteConstructor =
        sourceConstructor := by
      simpa [ReflectiveContextSupport.isQuoteConstructor,
        rhoReflectionProfile] using recognized
    exact reversed.symm
  · intro equality
    have sourceEq : sourceConstructor =
        rhoReflectivePresentation.quoteConstructor :=
      (CostStaticColor.symbols_constructor_injective rhoCIGSLT color) equality
    subst sourceConstructor
    simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]

/-- The selected-color target frame uses no quotation boundary other than the
declaration that its keyed canonicalizer is about to normalize. -/
private theorem reifyTargetFrame_selectedQuoteFragment
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    ConstructorsWithin
      (fun constructor =>
        ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile constructor = true ↔
          constructor =
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor)
      (node.reifyTargetFrame environment) := by
  apply (node.reifiedTargetFrame_constructorsWithinColor environment).mono
  intro constructor decoded
  rcases decoded with ⟨sourceConstructor, sourceDecoded⟩
  exact rhoCostStatic_quoteIff_of_decodes color constructor sourceConstructor
    sourceDecoded

/-- Endpoint-local keyed canonicalization preserves the exact positional
availability alignment of two atomized static frames. -/
theorem canonicalizeReifiedTargetFrame_availabilityTransposedAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {smallValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree smallNode.boundaryTable}
    {largeValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree largeNode.boundaryTable}
    {smallInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      smallNode.boundaryTable smallValues smallNode.skeleton.1}
    {largeInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      largeNode.boundaryTable largeValues largeNode.skeleton.1}
    (smallEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      largeInventory)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (sourceAligned :
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        rhoCIGSLT.reflection.1
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient .exposed
        (smallNode.reifiedSourceFrame smallEnvironment).1
        (largeNode.reifiedSourceFrame largeEnvironment).1) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.costWholeReflectionProfile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient .exposed
      (smallNode.canonicalizeReifiedTargetFrame smallEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))
      (largeNode.canonicalizeReifiedTargetFrame largeEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have targetAligned :=
    Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.reifyTargetFrame_availabilityTransposedAligned
      smallNode largeNode smallEnvironment largeEnvironment targetBoundEq
        sourceAligned
  have quoteRecognized :
      ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor =
        true := by
    unfold declaration
    rw [costStaticReflectivePresentationDecl_eq_map]
    simp only [mapReflectivePresentation,
      CostStaticColor.reflectiveSymbols_toPresentationSymbols]
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
    simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]
  have normalized :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.canonicalizeByAt
      targetAligned declaration quoteRecognized
        (reifyTargetFrame_selectedQuoteFragment smallNode smallEnvironment)
          smallNode.targetBound.length
  change
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.costWholeReflectionProfile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient .exposed
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (fun current pattern =>
          Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
            (ReflectiveContextSupport.substituteAt
              rhoCIGSLT.costWholeReflectionProfile
              smallEnvironment.restorationSupport
              smallEnvironment.restorationAssignment current pattern))
        declaration smallNode.targetBound.length
          (smallNode.reifyTargetFrame smallEnvironment))
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (fun current pattern =>
          Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
            (ReflectiveContextSupport.substituteAt
              rhoCIGSLT.costWholeReflectionProfile
              largeEnvironment.restorationSupport
              largeEnvironment.restorationAssignment current pattern))
        declaration largeNode.targetBound.length
          (largeNode.reifyTargetFrame largeEnvironment))
  simpa [CostStaticAvailabilityRegime.largeDepth, targetBoundEq,
    List.length_append] using normalized

/-- Restoring the two canonical frames at their actual endpoint binder depths
produces the same compact hereditary static result. -/
theorem normalizeHereditaryWithInventory_availabilityTransposed_eq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree smallNode.boundaryTable)
    (largeValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree largeNode.boundaryTable)
    (smallInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      smallNode.boundaryTable smallValues smallNode.skeleton.1)
    (largeInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      largeNode.boundaryTable largeValues largeNode.skeleton.1)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (sourceAligned :
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        rhoCIGSLT.reflection.1
        (CostStaticAtomEnvironment.ofInventory
          smallInventory).restorationSupport
        (CostStaticAtomEnvironment.ofInventory
          smallInventory).restorationAssignment
        (CostStaticAtomEnvironment.ofInventory
          largeInventory).restorationSupport
        (CostStaticAtomEnvironment.ofInventory
          largeInventory).restorationAssignment ambient .exposed
        (smallNode.reifiedSourceFrame
          (CostStaticAtomEnvironment.ofInventory smallInventory)).1
        (largeNode.reifiedSourceFrame
          (CostStaticAtomEnvironment.ofInventory largeInventory)).1) :
    (normalizeHereditaryWithInventory smallNode smallValues
        smallInventory).1 =
      (normalizeHereditaryWithInventory largeNode largeValues
        largeInventory).1 := by
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have canonicalAligned :=
    canonicalizeReifiedTargetFrame_availabilityTransposedAligned smallNode
      largeNode smallEnvironment largeEnvironment targetBoundEq sourceAligned
  have restored := canonicalAligned.toRestoresTogether
    smallNode.targetBound.length
  simpa [normalizeHereditaryWithInventory,
    WellSorted.ReflectiveWellSorted.OpenTerm.substituteReflectiveSupported,
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_openTerm,
    CostStaticAtomEnvironment.restorationSupportedOpenAssignment,
    ReflectiveContextSupport.substitute,
    CostStaticAvailabilityRegime.largeDepth, targetBoundEq,
    List.length_append, smallEnvironment, largeEnvironment] using restored

/-- Interpret a rho planner alignment from exact occurrence zippers.  At a
sealed boundary leaf, the plan says both that the stored support is the
boundary support and that it is the quote-local availability.  Exact regime
tracking therefore forces that support to be empty, closing the leaf without
an external re-exposure callback. -/
theorem reifyAlignedAtOccurrences_of_normalizedBoundaryTrees
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {smallInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      smallNode.boundaryTable
        (smallTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))
      smallNode.skeleton.1}
    {largeInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      largeNode.boundaryTable
        (largeTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))
      largeNode.skeleton.1}
    (smallEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      largeInventory)
    {ambient : List TypeExpr}
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallNode.boundaryTable
        largeNode.boundaryTable smallTrees largeTrees)
    (alignment : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.reflection.1
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient .exposed
      (smallEnvironment.reify smallNode.skeleton.1)
      (largeEnvironment.reify largeNode.skeleton.1) := by
  refine CostStaticAbstractPatternAlignment.reifyAlignedAtOccurrences
      (rootRegime := .exposed) smallEnvironment largeEnvironment ?_ ?_
        alignment ?_ ?_ ?_ ?_
  · intro current name smallOccurrence largeOccurrence smallName largeName
      _smallPath _largePath
    apply CostStaticAbstractPatternAlignment.sourceFVar_reifyAligned
      smallEnvironment largeEnvironment current name
    · simpa only [smallName] using smallOccurrence.name_mem_freeFvarNames
    · simpa only [largeName] using largeOccurrence.name_mem_freeFvarNames
    · exact smallNode.skeleton.2.1.2.2.1
    · exact largeNode.skeleton.2.1.2.2.1
  · intro current smallPosition largePosition positionEq supportAt
      smallOccurrence largeOccurrence smallName largeName smallPath _largePath
    refine CostStaticAbstractPatternAlignment.boundary_reifyAligned
      (kernel := rhoHereditaryNormalizationKernel)
      (smallInventory := smallInventory) (largeInventory := largeInventory)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      smallTrees largeTrees smallEnvironment largeEnvironment
      smallPosition largePosition positionEq supportAt ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [smallName] using smallOccurrence.name_mem_freeFvarNames
    · simpa only [largeName] using largeOccurrence.name_mem_freeFvarNames
    · exact smallNode.skeleton.2.1.2.2.1
    · exact largeNode.skeleton.2.1.2.2.1
    · exact forests.getEntry_normal_eq smallPosition largePosition positionEq
    · intro sealed nonemptySupport
      let planOccurrence := castCostStaticFVarOccurrenceRoot
        (smallNode.skeleton_pattern.trans
          smallNode.plan.decoration_abstractPattern.symm) smallOccurrence
      obtain ⟨packed⟩ :=
        CostStaticPlanDecoration.nonempty_abstractOccurrence
          smallNode.plan.decoration planOccurrence
      rcases packed with ⟨planAvailable, selectedOccurrence⟩
      have planFree : WellSorted.ReflectiveSubstitutionBinderFree
          smallNode.plan.abstractPattern = true :=
        CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
          smallNode.plan ⟨smallNode.sourceSort.1, rfl⟩
      have planName : planOccurrence.name = costRegionBoundaryVariableName
          (smallNode.boundaryTable.entries.get smallPosition).boundary := by
        simpa [planOccurrence] using smallName
      have availableEqQuote :=
        CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
          smallNode.plan planFree selectedOccurrence
      have availableEqSupport :=
        CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
          smallNode.plan selectedOccurrence
            (smallNode.boundaryTable.entries.get smallPosition).boundary planName
      have occurrenceSealed :
          CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
              .exposed planOccurrence.context = .sealed := by
        simpa [planOccurrence, sealed] using smallPath
      have quoteLocalNil :=
        rhoCanonicalOccurrenceAvailable_eq_nil_of_atContext_sealed
          smallNode.targetBound planOccurrence.context occurrenceSealed
      have supportNil :
          (smallNode.boundaryTable.entries.get
            smallPosition).boundary.targetSupport = [] := by
        rw [← availableEqSupport, availableEqQuote, quoteLocalNil]
      exact (nonemptySupport supportNil).elim
  · intro occurrence
    exact Subtype.mk occurrence rfl
  · intro occurrence
    exact Subtype.mk occurrence rfl
  · intro occurrence
    rfl
  · intro occurrence
    rfl

/-- Callback-free rho static-node availability transposition. -/
theorem normalizeHereditary_availabilityTransposed_eq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallNode.boundaryTable
        largeNode.boundaryTable smallTrees largeTrees)
    (sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  let smallValues := smallTrees.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let largeValues := largeTrees.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let smallPacked := smallNode.semanticAtomEnvironment smallValues
  let largePacked := largeNode.semanticAtomEnvironment largeValues
  let smallInventory := smallPacked.1
  let largeInventory := largePacked.1
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have sourceAligned :=
    reifyAlignedAtOccurrences_of_normalizedBoundaryTrees smallNode largeNode
      smallTrees largeTrees smallEnvironment largeEnvironment forests
        sourcePlanAligned
  have normalized :=
    normalizeHereditaryWithInventory_availabilityTransposed_eq smallNode
      largeNode smallValues largeValues smallInventory largeInventory
        targetBoundEq sourceAligned
  change
    (normalizeHereditaryWithInventory smallNode smallValues smallInventory).1 =
      (normalizeHereditaryWithInventory largeNode largeValues largeInventory).1
  simpa [normalizeHereditary, smallValues, largeValues, smallPacked,
    largePacked, smallInventory, largeInventory] using normalized

/-- Static-node consequence of a positional planner suffix certificate.  The
caller supplies equality of recursively normalized children at matching
finite positions; this theorem assembles the forest certificate and invokes
the callback-free canonicalization/restoration bridge. -/
theorem normalizeHereditary_static_eq_of_positionalSuffix
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (occurrencesEq : smallNode.plan.occurrences = largeNode.plan.occurrences)
    (tables : TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
      (TypedCostRegionBoundaryTable.cast occurrencesEq
        smallNode.boundaryTable) largeNode.boundaryTable)
    (sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1)
    (childNormalEq : ∀
      (smallPosition : Fin smallNode.boundaryTable.entries.length)
      (largePosition : Fin largeNode.boundaryTable.entries.length),
      smallPosition.1 = largePosition.1 →
      ((smallTrees.getEntry smallPosition).tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        ((largeTrees.getEntry largePosition).tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  let forests :=
    CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross.of_getEntry_normal_eq
      occurrencesEq tables childNormalEq
  exact normalizeHereditary_availabilityTransposed_eq smallNode largeNode
    smallTrees largeTrees targetBoundEq forests sourcePlanAligned

/-- Planner-derived static-node transposition.  Propositional equality of
the two independently typed node indices is discharged by the generic
planner wrapper; recursive child equality is the sole semantic input. -/
theorem normalizeHereditary_static_eq_of_availabilitySuffix
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (sourceSortEq : smallNode.sourceSort = largeNode.sourceSort)
    (termEq : smallNode.term.1 = largeNode.term.1)
    (childNormalEq : ∀
      (smallPosition : Fin smallNode.boundaryTable.entries.length)
      (largePosition : Fin largeNode.boundaryTable.entries.length),
      smallPosition.1 = largePosition.1 →
      ((smallTrees.getEntry smallPosition).tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        ((largeTrees.getEntry largePosition).tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  have sourceTypeEq : TypeExpr.base smallNode.sourceSort.1 =
      TypeExpr.base largeNode.sourceSort.1 :=
    congrArg (fun sort => TypeExpr.base sort.1) sourceSortEq
  obtain ⟨occurrencesEq, tables, abstractAligned⟩ :=
    CostStaticRegionPlan.boundaryTablesAndAbstractAvailabilitySuffix_of_scoped
      CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
      (show CostStaticAvailabilityAt ambient .exposed smallNode.targetBound
          largeNode.targetBound from targetBoundEq)
      targetBoundEq termEq sourceTypeEq smallNode.term.2.2.2.1
      smallNode.term.2.1.isWellScopedAt smallNode.plan largeNode.plan
  have sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1 := by
    rw [smallNode.skeleton_pattern, largeNode.skeleton_pattern]
    exact abstractAligned
  exact normalizeHereditary_static_eq_of_positionalSuffix smallNode largeNode
    smallTrees largeTrees targetBoundEq occurrencesEq tables sourcePlanAligned
      childNormalEq

/-- The complete static-node transposition step.  A positional planner
alignment and recursively related boundary forests determine the semantic
source-frame alignment; endpoint-local canonicalization and restoration then
produce the same hereditary normal form.  The remaining callback is exactly
the recursive fact needed when a quotation shell disappears and a sealed
boundary becomes exposed. -/
theorem normalizeHereditary_availabilityTransposed_eq_of_forests
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallNode.boundaryTable
        largeNode.boundaryTable smallTrees largeTrees)
    (sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1)
    (boundaryReexposes :
      let smallValues := smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let largeValues := largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let smallInventory := (smallNode.semanticAtomEnvironment smallValues).1
      let largeInventory := (largeNode.semanticAtomEnvironment largeValues).1
      let smallEnvironment := CostStaticAtomEnvironment.ofInventory
        smallInventory
      let largeEnvironment := CostStaticAtomEnvironment.ofInventory
        largeInventory
      ∀ (current : CostStaticAvailabilityRegime)
        (smallPosition : Fin smallNode.boundaryTable.entries.length)
        (largePosition : Fin largeNode.boundaryTable.entries.length),
        smallPosition.1 = largePosition.1 →
        current = CostStaticAvailabilityRegime.sealed →
        (smallNode.boundaryTable.entries.get
          smallPosition).boundary.targetSupport ≠ [] →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
          rhoCIGSLT.reflection.1 smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient .exposed
          (.fvar (smallEnvironment.reifyName
            (costRegionBoundaryVariableName
              (smallNode.boundaryTable.entries.get smallPosition).boundary)))
          (.fvar (largeEnvironment.reifyName
            (costRegionBoundaryVariableName
              (largeNode.boundaryTable.entries.get largePosition).boundary)))) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  let smallValues := smallTrees.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let largeValues := largeTrees.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let smallPacked := smallNode.semanticAtomEnvironment smallValues
  let largePacked := largeNode.semanticAtomEnvironment largeValues
  let smallInventory := smallPacked.1
  let largeInventory := largePacked.1
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have sourceAligned :=
    CostStaticAbstractPatternAlignment.reifyAligned_of_normalizedBoundaryTrees
      (kernel := rhoHereditaryNormalizationKernel)
      (smallRoot := smallNode.skeleton.1)
      (largeRoot := largeNode.skeleton.1)
      (smallInventory := smallInventory)
      (largeInventory := largeInventory)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition smallTrees largeTrees
        smallEnvironment largeEnvironment forests sourcePlanAligned
        smallNode.skeleton.2.1.2.2.1 largeNode.skeleton.2.1.2.2.1
        (by
          intro current smallPosition largePosition positionEq sealed
            nonemptySupport
          exact boundaryReexposes current smallPosition largePosition positionEq
            sealed nonemptySupport)
  have normalized :=
    normalizeHereditaryWithInventory_availabilityTransposed_eq smallNode
      largeNode smallValues largeValues smallInventory largeInventory
        targetBoundEq sourceAligned
  change
    (normalizeHereditaryWithInventory smallNode smallValues smallInventory).1 =
      (normalizeHereditaryWithInventory largeNode largeValues largeInventory).1
  simpa [normalizeHereditary, smallValues, largeValues, smallPacked,
    largePacked, smallInventory, largeInventory] using normalized

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
