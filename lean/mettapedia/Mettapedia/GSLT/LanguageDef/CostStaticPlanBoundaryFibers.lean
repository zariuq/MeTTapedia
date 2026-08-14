import Mettapedia.GSLT.LanguageDef.CostRegionBoundaryFiberSuffix

/-!
# Boundary fibres projected from the authoritative static plan

The executable static plan is the decomposition authority used by region
trees.  This module projects its retained target fibres in occurrence order
and proves that certifying the projection recovers the plan's finite table
exactly.  Thus syntax-level fibre conservation can be connected to the
proof-relevant table without introducing a second boundary authority.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Expose one certification step without leaving a dependent match over the
occurrence-list index in downstream plan proofs. -/
theorem TypedCostRegionBoundaryTable.certify?_cons
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    (targetSupport : List TypeExpr) (targetType : TypeExpr)
    (tail : CostRegionBoundaryFibers occurrences) :
    TypedCostRegionBoundaryTable.certify? (source := source) (color := color)
        (targetFree := targetFree)
        (.cons (occurrence := occurrence) targetSupport targetType tail) =
      match certifyCostRegionBoundary? source color targetFree targetSupport
          targetType occurrence.content with
      | none => none
      | some boundary =>
          (TypedCostRegionBoundaryTable.certify? tail).map
            (TypedCostRegionBoundaryTable.cons boundary.typed
              boundary.content_eq) := by
  cases headResult : certifyCostRegionBoundary? source color targetFree
      targetSupport targetType occurrence.content with
  | none => simp [TypedCostRegionBoundaryTable.certify?, headResult]
  | some boundary =>
      cases tailResult : TypedCostRegionBoundaryTable.certify? tail <;>
        simp [TypedCostRegionBoundaryTable.certify?, headResult, tailResult]

mutual
  /-- Target support and type of every boundary retained by one static plan. -/
  def CostStaticRegionPlan.boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      CostRegionBoundaryFibers plan.occurrences :=
    match plan with
    | .bvar _ _ _ _ | .fvar _ => .nil
    | .boundaryApplication _ _ _ certified _ =>
        .cons sourceAvailable
          (mapTypeExpr (color.symbols source) sourceType) .nil
    | .application _ _ _ _ _ children => children.boundaryFibers
    | .lambda bodyPlan => bodyPlan.boundaryFibers
    | .multiLambda bodyPlan => bodyPlan.boundaryFibers
    | .collection _ _ children => children.boundaryFibers
    | .boundaryCollection _ _ _ certified _ =>
        .cons sourceAvailable
          (mapTypeExpr (color.symbols source) sourceType) .nil

  /-- Boundary-fibre projection for a constructor-argument spine. -/
  def CostStaticArgumentPlan.boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters) : CostRegionBoundaryFibers plan.occurrences :=
    match plan with
    | .nil => .nil
    | .cons _ _ head tail =>
        head.boundaryFibers.append tail.boundaryFibers

  /-- Boundary-fibre projection for a homogeneous collection spine. -/
  def CostStaticElementPlan.boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType) :
      CostRegionBoundaryFibers plan.occurrences :=
    match plan with
    | .nil => .nil
    | .cons head tail => head.boundaryFibers.append tail.boundaryFibers
end

mutual
  /-- Re-certifying the fibres projected from a region plan returns exactly
  its authoritative table. -/
  theorem CostStaticRegionPlan.certify_boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      TypedCostRegionBoundaryTable.certify? plan.boundaryFibers =
        some plan.boundaryTable := by
    cases plan with
    | bvar | fvar => rfl
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        simp only [CostStaticRegionPlan.boundaryFibers,
          CostStaticRegionPlan.boundaryTable, CostStaticRegionPlan.occurrences]
        rw [TypedCostRegionBoundaryTable.certify?_cons, certifies]
        rfl
    | application constructor rendered current preimage notBare children =>
        exact children.certify_boundaryFibers
    | lambda bodyPlan => exact bodyPlan.certify_boundaryFibers
    | multiLambda bodyPlan => exact bodyPlan.certify_boundaryFibers
    | collection choice selected children =>
        exact children.certify_boundaryFibers
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        simp only [CostStaticRegionPlan.boundaryFibers,
          CostStaticRegionPlan.boundaryTable, CostStaticRegionPlan.occurrences]
        rw [TypedCostRegionBoundaryTable.certify?_cons, certifies]
        rfl

  /-- Re-certification commutes with an argument spine's ordered append. -/
  theorem CostStaticArgumentPlan.certify_boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters) :
      TypedCostRegionBoundaryTable.certify? plan.boundaryFibers =
        some plan.boundaryTable := by
    cases plan with
    | nil => rfl
    | cons representation parameterType head tail =>
        simp only [CostStaticArgumentPlan.boundaryFibers,
          CostStaticArgumentPlan.boundaryTable,
          CostStaticArgumentPlan.occurrences]
        rw [TypedCostRegionBoundaryTable.certify?_append,
          CostStaticRegionPlan.certify_boundaryFibers head,
          CostStaticArgumentPlan.certify_boundaryFibers tail]

  /-- Re-certification commutes with a collection spine's ordered append. -/
  theorem CostStaticElementPlan.certify_boundaryFibers
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType) :
      TypedCostRegionBoundaryTable.certify? plan.boundaryFibers =
        some plan.boundaryTable := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        simp only [CostStaticElementPlan.boundaryFibers,
          CostStaticElementPlan.boundaryTable,
          CostStaticElementPlan.occurrences]
        rw [TypedCostRegionBoundaryTable.certify?_append,
          CostStaticRegionPlan.certify_boundaryFibers head,
          CostStaticElementPlan.certify_boundaryFibers tail]
end

/-- Two certified boundaries occupy the same positional event, retain the
same source/target type and content, and differ in active target support only
by the exposed-or-sealed suffix dichotomy. -/
structure TypedCostRegionBoundary.AvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (ambient : List TypeExpr)
    (small large : TypedCostRegionBoundary source color targetFree) : Prop where
  sourceType_eq : small.boundary.type = large.boundary.type
  targetType_eq : small.boundary.targetType = large.boundary.targetType
  targetSupport : CostStaticAvailabilitySuffix ambient
    small.boundary.targetSupport large.boundary.targetSupport
  content_eq : small.boundary.content = large.boundary.content

namespace TypedCostRegionBoundary.AvailabilitySuffix

/-- A boundary is related to itself through the sealed regime. -/
theorem refl {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} (ambient : List TypeExpr)
    (boundary : TypedCostRegionBoundary source color targetFree) :
    TypedCostRegionBoundary.AvailabilitySuffix ambient boundary boundary :=
  ⟨rfl, rfl, CostStaticAvailabilitySuffix.unchanged _ _, rfl⟩

end TypedCostRegionBoundary.AvailabilitySuffix

/-- Positional table relation induced by the target-support suffix
dichotomy.  Duplicate contents remain separate constructors. -/
inductive TypedCostRegionBoundaryTable.AvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} (ambient : List TypeExpr) :
    {occurrences : List CostRegionOccurrence} →
      TypedCostRegionBoundaryTable source color targetFree occurrences →
      TypedCostRegionBoundaryTable source color targetFree occurrences → Prop where
  | nil : AvailabilitySuffix ambient .nil .nil
  | cons {occurrence : CostRegionOccurrence}
      {occurrences : List CostRegionOccurrence}
      {smallBoundary largeBoundary :
        TypedCostRegionBoundary source color targetFree}
      {smallContent : smallBoundary.boundary.content = occurrence.content}
      {largeContent : largeBoundary.boundary.content = occurrence.content}
      {smallTail largeTail : TypedCostRegionBoundaryTable source color
        targetFree occurrences}
      (head : TypedCostRegionBoundary.AvailabilitySuffix ambient
        smallBoundary largeBoundary)
      (tail : AvailabilitySuffix ambient smallTail largeTail) :
      AvailabilitySuffix ambient
        (.cons smallBoundary smallContent smallTail)
        (.cons largeBoundary largeContent largeTail)

namespace TypedCostRegionBoundaryTable.AvailabilitySuffix

/-- Certifying two positionally suffix-related fibre plans yields tables
related by the same dichotomy. -/
theorem of_certify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallFibers largeFibers : CostRegionBoundaryFibers occurrences}
    (suffix : CostRegionBoundaryFibers.AvailabilitySuffix ambient
      smallFibers largeFibers)
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    (smallCertified : TypedCostRegionBoundaryTable.certify? smallFibers =
      some smallTable)
    (largeCertified : TypedCostRegionBoundaryTable.certify? largeFibers =
      some largeTable) :
    TypedCostRegionBoundaryTable.AvailabilitySuffix ambient smallTable
      largeTable := by
  induction suffix with
  | nil =>
      simp [TypedCostRegionBoundaryTable.certify?] at smallCertified
      simp [TypedCostRegionBoundaryTable.certify?] at largeCertified
      subst smallTable
      subst largeTable
      exact .nil
  | @cons occurrence occurrences smallSupport largeSupport targetType
      smallTail largeTail support tail inductionHypothesis =>
      cases smallHeadResult : certifyCostRegionBoundary? source color
          targetFree smallSupport targetType occurrence.content with
      | none =>
          rw [TypedCostRegionBoundaryTable.certify?_cons,
            smallHeadResult] at smallCertified
          contradiction
      | some smallBoundary =>
          cases smallTailResult : TypedCostRegionBoundaryTable.certify?
              smallTail with
          | none =>
              rw [TypedCostRegionBoundaryTable.certify?_cons,
                smallHeadResult, smallTailResult] at smallCertified
              contradiction
          | some smallCertifiedTail =>
              cases largeHeadResult : certifyCostRegionBoundary? source color
                  targetFree largeSupport targetType occurrence.content with
              | none =>
                  rw [TypedCostRegionBoundaryTable.certify?_cons,
                    largeHeadResult] at largeCertified
                  contradiction
              | some largeBoundary =>
                  cases largeTailResult :
                      TypedCostRegionBoundaryTable.certify? largeTail with
                  | none =>
                      rw [TypedCostRegionBoundaryTable.certify?_cons,
                        largeHeadResult, largeTailResult] at largeCertified
                      contradiction
                  | some largeCertifiedTail =>
                      rw [TypedCostRegionBoundaryTable.certify?_cons,
                        smallHeadResult, smallTailResult] at smallCertified
                      rw [TypedCostRegionBoundaryTable.certify?_cons,
                        largeHeadResult, largeTailResult] at largeCertified
                      simp at smallCertified
                      simp at largeCertified
                      subst smallTable
                      subst largeTable
                      have sourceTypeEquality :
                          smallBoundary.typed.boundary.type =
                            largeBoundary.typed.boundary.type := by
                        apply mapTypeExpr_costStatic_injective source color
                        exact (certifyCostRegionBoundary?_typeMap
                          smallHeadResult).trans
                            (certifyCostRegionBoundary?_typeMap
                              largeHeadResult).symm
                      have targetTypeEquality :
                          smallBoundary.typed.boundary.targetType =
                            largeBoundary.typed.boundary.targetType :=
                        smallBoundary.targetType_eq.trans
                          largeBoundary.targetType_eq.symm
                      have targetSupportSuffix : CostStaticAvailabilitySuffix
                          ambient smallBoundary.typed.boundary.targetSupport
                            largeBoundary.typed.boundary.targetSupport := by
                        simpa [smallBoundary.targetSupport_eq,
                          largeBoundary.targetSupport_eq] using support
                      have contentEquality :
                          smallBoundary.typed.boundary.content =
                            largeBoundary.typed.boundary.content :=
                        smallBoundary.content_eq.trans
                          largeBoundary.content_eq.symm
                      exact .cons
                        ⟨sourceTypeEquality, targetTypeEquality,
                          targetSupportSuffix, contentEquality⟩
                        (inductionHypothesis smallTailResult largeTailResult)

/-- Positionally related tables have the same finite length. -/
theorem entries_length_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    (_related : AvailabilitySuffix ambient smallTable largeTable) :
    smallTable.entries.length = largeTable.entries.length := by
  rw [TypedCostRegionBoundaryTable.entries_length,
    TypedCostRegionBoundaryTable.entries_length]

/-- An exact position in two suffix-related tables selects suffix-related
boundaries.  Equal boundary values at other positions are irrelevant. -/
theorem getEntry
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    (related : AvailabilitySuffix ambient smallTable largeTable)
    (index : Fin smallTable.entries.length) :
    let largeIndex : Fin largeTable.entries.length :=
      Fin.cast (entries_length_eq related) index
    TypedCostRegionBoundary.AvailabilitySuffix ambient
      (smallTable.entries.get index) (largeTable.entries.get largeIndex) := by
  induction related with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      induction index using Fin.cases with
      | zero => exact head
      | succ previous => exact inductionHypothesis previous

end TypedCostRegionBoundaryTable.AvailabilitySuffix

/-! ## Positional alignment of availability-related abstract skeletons -/

/- Two abstract static-plan skeletons have the same constructors and retain
the same authored source variables.  Boundary leaves are paired by exact
finite positions in their endpoint-local tables.  The positions, rather than
boundary-name equality, are the identity of a boundary occurrence. -/
mutual
  inductive CostStaticAbstractPatternAlignment
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      (smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree))
      (ambient : List TypeExpr) :
      CostStaticAvailabilityRegime → Pattern → Pattern → Prop where
    | bvar (regime : CostStaticAvailabilityRegime) (index : Nat) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.bvar index) (.bvar index)
    | sourceFVar (regime : CostStaticAvailabilityRegime) (name : String) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.fvar (costRegionSourceVariableName name))
          (.fvar (costRegionSourceVariableName name))
    | boundary
        (regime : CostStaticAvailabilityRegime)
        (smallPosition : Fin smallEntries.length)
        (largePosition : Fin largeEntries.length)
        (position_eq : smallPosition.1 = largePosition.1)
        (support : CostStaticAvailabilityAt ambient regime
          (smallEntries.get smallPosition).boundary.targetSupport
          (largeEntries.get largePosition).boundary.targetSupport) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.fvar (costRegionBoundaryVariableName
            (smallEntries.get smallPosition).boundary))
          (.fvar (costRegionBoundaryVariableName
            (largeEntries.get largePosition).boundary))
    | apply (regime : CostStaticAvailabilityRegime) (constructor : String)
        {smallArguments largeArguments : List Pattern}
        (arguments : CostStaticAbstractPatternListAlignment smallEntries
          largeEntries ambient
          (if ReflectiveContextSupport.isQuoteConstructor
              source.reflection.1 constructor then .sealed
            else regime)
          smallArguments largeArguments) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.apply constructor smallArguments) (.apply constructor largeArguments)
    | lambda (regime : CostStaticAvailabilityRegime) (binder : Option String)
        {smallBody largeBody : Pattern}
        (body : CostStaticAbstractPatternAlignment smallEntries largeEntries
          ambient regime smallBody largeBody) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.lambda binder smallBody) (.lambda binder largeBody)
    | multiLambda (regime : CostStaticAvailabilityRegime)
        (arity : Nat) (binders : List String)
        {smallBody largeBody : Pattern}
        (body : CostStaticAbstractPatternAlignment smallEntries largeEntries
          ambient regime smallBody largeBody) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.multiLambda arity binders smallBody)
          (.multiLambda arity binders largeBody)
    | collection (regime : CostStaticAvailabilityRegime)
        (collectionType : CollType) {smallElements largeElements : List Pattern}
        (rest : Option String)
        (elements : CostStaticAbstractPatternListAlignment smallEntries
          largeEntries ambient regime smallElements largeElements) :
        CostStaticAbstractPatternAlignment smallEntries largeEntries ambient regime
          (.collection collectionType smallElements
            (rest.map costRegionSourceVariableName))
          (.collection collectionType largeElements
            (rest.map costRegionSourceVariableName))

  /-- Ordered-list companion of `CostStaticAbstractPatternAlignment`. -/
  inductive CostStaticAbstractPatternListAlignment
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      (smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree))
      (ambient : List TypeExpr) :
      CostStaticAvailabilityRegime → List Pattern → List Pattern → Prop where
    | nil (regime : CostStaticAvailabilityRegime) :
        CostStaticAbstractPatternListAlignment smallEntries largeEntries
        ambient regime
        [] []
    | cons (regime : CostStaticAvailabilityRegime)
        {smallHead largeHead : Pattern}
        {smallTail largeTail : List Pattern}
        (head : CostStaticAbstractPatternAlignment smallEntries largeEntries
          ambient regime smallHead largeHead)
        (tail : CostStaticAbstractPatternListAlignment smallEntries largeEntries
          ambient regime smallTail largeTail) :
        CostStaticAbstractPatternListAlignment smallEntries largeEntries
          ambient regime
          (smallHead :: smallTail) (largeHead :: largeTail)
end

namespace CostStaticAbstractPatternAlignment

/- Appending unrelated table suffixes preserves every exact position in an
aligned skeleton. -/
mutual
  def appendEntries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree)}
      (smallSuffix largeSuffix :
        List (TypedCostRegionBoundary source color targetFree))
      {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
      {smallPattern largePattern : Pattern} :
      CostStaticAbstractPatternAlignment smallEntries largeEntries
          ambient regime smallPattern largePattern →
        CostStaticAbstractPatternAlignment
          (smallEntries ++ smallSuffix) (largeEntries ++ largeSuffix)
          ambient regime smallPattern largePattern
    | .bvar regime index => .bvar regime index
    | .sourceFVar regime name => .sourceFVar regime name
    | .boundary regime smallPosition largePosition position_eq support => by
        simpa [List.get_eq_getElem] using
          (CostStaticAbstractPatternAlignment.boundary
            (smallEntries := smallEntries ++ smallSuffix)
            (largeEntries := largeEntries ++ largeSuffix)
            regime
            (Fin.cast (by simp)
              (Fin.castAdd smallSuffix.length smallPosition))
            (Fin.cast (by simp)
              (Fin.castAdd largeSuffix.length largePosition))
            (by simpa using position_eq)
            (by simpa [List.get_eq_getElem] using support))
    | .apply regime constructor arguments =>
        .apply regime constructor
          (CostStaticAbstractPatternListAlignment.appendEntries
            smallSuffix largeSuffix arguments)
    | .lambda regime binder body => .lambda regime binder
        (appendEntries smallSuffix largeSuffix body)
    | .multiLambda regime arity binders body => .multiLambda regime arity binders
        (appendEntries smallSuffix largeSuffix body)
    | .collection regime collectionType rest elements =>
        .collection regime collectionType rest
          (CostStaticAbstractPatternListAlignment.appendEntries
            smallSuffix largeSuffix elements)

  /-- Ordered-list companion of `appendEntries`. -/
  def CostStaticAbstractPatternListAlignment.appendEntries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree)}
      (smallSuffix largeSuffix :
        List (TypedCostRegionBoundary source color targetFree))
      {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
      {smallPatterns largePatterns : List Pattern} :
      CostStaticAbstractPatternListAlignment smallEntries largeEntries
          ambient regime smallPatterns largePatterns →
        CostStaticAbstractPatternListAlignment
          (smallEntries ++ smallSuffix) (largeEntries ++ largeSuffix)
          ambient regime smallPatterns largePatterns
    | .nil _ => .nil regime
    | .cons _ head tail => .cons regime
        (appendEntries smallSuffix largeSuffix head)
        (CostStaticAbstractPatternListAlignment.appendEntries
          smallSuffix largeSuffix tail)
end

/- Prepending unrelated table prefixes shifts every boundary position while
preserving the selected endpoint entry. -/
mutual
  def prependEntries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      (smallPrefix largePrefix :
        List (TypedCostRegionBoundary source color targetFree))
      (prefixLength_eq : smallPrefix.length = largePrefix.length)
      {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
      {smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree)}
      {smallPattern largePattern : Pattern} :
      CostStaticAbstractPatternAlignment smallEntries largeEntries
          ambient regime smallPattern largePattern →
        CostStaticAbstractPatternAlignment
          (smallPrefix ++ smallEntries) (largePrefix ++ largeEntries)
          ambient regime smallPattern largePattern
    | .bvar regime index => .bvar regime index
    | .sourceFVar regime name => .sourceFVar regime name
    | .boundary regime smallPosition largePosition position_eq support => by
        simpa [List.get_eq_getElem] using
          (CostStaticAbstractPatternAlignment.boundary
            (smallEntries := smallPrefix ++ smallEntries)
            (largeEntries := largePrefix ++ largeEntries)
            regime
            (Fin.cast (by simp)
              (Fin.natAdd smallPrefix.length smallPosition))
            (Fin.cast (by simp)
              (Fin.natAdd largePrefix.length largePosition))
            (by
              change smallPrefix.length + smallPosition.1 =
                largePrefix.length + largePosition.1
              omega)
            (by simpa [List.get_eq_getElem] using support))
    | .apply regime constructor arguments =>
        .apply regime constructor
          (CostStaticAbstractPatternListAlignment.prependEntries
            smallPrefix largePrefix prefixLength_eq arguments)
    | .lambda regime binder body => .lambda regime binder
        (prependEntries smallPrefix largePrefix prefixLength_eq body)
    | .multiLambda regime arity binders body => .multiLambda regime arity binders
        (prependEntries smallPrefix largePrefix prefixLength_eq body)
    | .collection regime collectionType rest elements =>
        .collection regime collectionType rest
          (CostStaticAbstractPatternListAlignment.prependEntries
            smallPrefix largePrefix prefixLength_eq elements)

  /-- Ordered-list companion of `prependEntries`. -/
  def CostStaticAbstractPatternListAlignment.prependEntries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      (smallPrefix largePrefix :
        List (TypedCostRegionBoundary source color targetFree))
      (prefixLength_eq : smallPrefix.length = largePrefix.length)
      {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
      {smallEntries largeEntries :
        List (TypedCostRegionBoundary source color targetFree)}
      {smallPatterns largePatterns : List Pattern} :
      CostStaticAbstractPatternListAlignment smallEntries largeEntries
          ambient regime smallPatterns largePatterns →
        CostStaticAbstractPatternListAlignment
          (smallPrefix ++ smallEntries) (largePrefix ++ largeEntries)
          ambient regime smallPatterns largePatterns
    | .nil _ => .nil regime
    | .cons _ head tail => .cons regime
        (prependEntries smallPrefix largePrefix prefixLength_eq head)
        (CostStaticAbstractPatternListAlignment.prependEntries
          smallPrefix largePrefix prefixLength_eq tail)
end

end CostStaticAbstractPatternAlignment

/-- Proof-relevant plan certificate: the two plans retain the same ordered
boundary occurrences and their authoritative fibre projections satisfy the
availability suffix dichotomy. -/
structure CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern}
    {smallSourceType largeSourceType : TypeExpr}
    (ambient : List TypeExpr)
    (regime : CostStaticAvailabilityRegime)
    (small : CostStaticRegionPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer pattern
      smallSourceType)
    (large : CostStaticRegionPlan source color targetFree largeSourceBound
      largeTargetBound largeThinning largeAvailable outer pattern
      largeSourceType) :
    Prop where
  sourceType_eq : smallSourceType = largeSourceType
  occurrences_eq : small.occurrences = large.occurrences
  fibers : CostRegionBoundaryFibers.AvailabilitySuffix ambient
    (CostRegionBoundaryFibers.cast occurrences_eq small.boundaryFibers)
    large.boundaryFibers
  abstractPattern : CostStaticAbstractPatternAlignment
    small.boundaryTable.entries large.boundaryTable.entries
    ambient regime small.abstractPattern large.abstractPattern

/-- Argument-spine companion of
`CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix`. -/
structure CostStaticArgumentPlan.BoundaryFibersAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {wireName : String}
    {before arguments : List Pattern}
    {smallParameters largeParameters : List TermParam}
    (ambient : List TypeExpr)
    (regime : CostStaticAvailabilityRegime)
    (small : CostStaticArgumentPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer wireName before
      arguments smallParameters)
    (large : CostStaticArgumentPlan source color targetFree largeSourceBound
      largeTargetBound largeThinning largeAvailable outer wireName before
      arguments largeParameters) : Prop where
  parameters_eq : smallParameters = largeParameters
  occurrences_eq : small.occurrences = large.occurrences
  fibers : CostRegionBoundaryFibers.AvailabilitySuffix ambient
    (CostRegionBoundaryFibers.cast occurrences_eq small.boundaryFibers)
    large.boundaryFibers
  abstractPatterns : CostStaticAbstractPatternListAlignment
    small.boundaryTable.entries large.boundaryTable.entries
    ambient regime small.abstractPatterns large.abstractPatterns

/-- Homogeneous-element companion of
`CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix`. -/
structure CostStaticElementPlan.BoundaryFibersAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String}
    {smallSourceElementType largeSourceElementType : TypeExpr}
    (ambient : List TypeExpr)
    (regime : CostStaticAvailabilityRegime)
    (small : CostStaticElementPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer collectionType before
      elements rest smallSourceElementType)
    (large : CostStaticElementPlan source color targetFree largeSourceBound
      largeTargetBound largeThinning largeAvailable outer collectionType before
      elements rest largeSourceElementType) : Prop where
  sourceElementType_eq : smallSourceElementType = largeSourceElementType
  occurrences_eq : small.occurrences = large.occurrences
  fibers : CostRegionBoundaryFibers.AvailabilitySuffix ambient
    (CostRegionBoundaryFibers.cast occurrences_eq small.boundaryFibers)
    large.boundaryFibers
  abstractPatterns : CostStaticAbstractPatternListAlignment
    small.boundaryTable.entries large.boundaryTable.entries
    ambient regime small.abstractPatterns large.abstractPatterns

/-- Positional suffix relations compose over two independently reindexed
spines.  The composite occurrence equality is exactly list append
congruence, so duplicate occurrences remain distinct. -/
theorem CostRegionBoundaryFibers.AvailabilitySuffix.append_cast
    {ambient : List TypeExpr}
    {smallLeftOccurrences largeLeftOccurrences smallRightOccurrences
      largeRightOccurrences : List CostRegionOccurrence}
    {smallLeft : CostRegionBoundaryFibers smallLeftOccurrences}
    {largeLeft : CostRegionBoundaryFibers largeLeftOccurrences}
    {smallRight : CostRegionBoundaryFibers smallRightOccurrences}
    {largeRight : CostRegionBoundaryFibers largeRightOccurrences}
    (leftOccurrences : smallLeftOccurrences = largeLeftOccurrences)
    (rightOccurrences : smallRightOccurrences = largeRightOccurrences)
    (left : CostRegionBoundaryFibers.AvailabilitySuffix ambient
      (CostRegionBoundaryFibers.cast leftOccurrences smallLeft) largeLeft)
    (right : CostRegionBoundaryFibers.AvailabilitySuffix ambient
      (CostRegionBoundaryFibers.cast rightOccurrences smallRight) largeRight) :
    CostRegionBoundaryFibers.AvailabilitySuffix ambient
      (CostRegionBoundaryFibers.cast
        (congrArg₂ List.append leftOccurrences rightOccurrences)
        (smallLeft.append smallRight))
      (largeLeft.append largeRight) := by
  cases leftOccurrences
  cases rightOccurrences
  exact left.append right

/-- Contracting a target index in the retained prefix is independent of an
appended target suffix. -/
theorem CostStaticBinderThinning.targetToSourceIndex?_append_of_lt
    (source : CIGSLT) (color : CostStaticColor)
    (retained suffix : List TypeExpr) (index : Nat)
    (inside : index < retained.length) :
    CostStaticBinderThinning.targetToSourceIndex? source color
        (retained ++ suffix) index =
      CostStaticBinderThinning.targetToSourceIndex? source color retained
        index := by
  induction retained generalizing index with
  | nil => simp at inside
  | cons targetType retained inductionHypothesis =>
      cases index with
      | zero => simp [CostStaticBinderThinning.targetToSourceIndex?]
      | succ index =>
          have tailInside : index < retained.length := by
            simpa using inside
          cases decoded : decodeCostStaticTypeExpr source color targetType <;>
            simp [CostStaticBinderThinning.targetToSourceIndex?, decoded,
              inductionHypothesis index tailInside]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
mutual
  /-- Appending an unused target-binder suffix preserves the authoritative
  plan inventory positionally.  A boundary either sees the suffix or lies
  below a quote reset and retains its local support. -/
  theorem CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallSourceBound largeSourceBound smallTargetBound largeTargetBound
        ambient :
        List TypeExpr}
      {regime : CostStaticAvailabilityRegime}
      {smallThinning : CostStaticBinderThinning source color smallSourceBound
        smallTargetBound}
      {largeThinning : CostStaticBinderThinning source color largeSourceBound
        largeTargetBound}
      {smallAvailable largeAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern}
      {smallSourceType largeSourceType : TypeExpr}
      (unique : CostStaticCollectionGloballyUnambiguous source)
      (availableSuffix : CostStaticAvailabilityAt ambient regime smallAvailable
        largeAvailable)
      (targetBoundEq : largeTargetBound = smallTargetBound ++ ambient)
      (sourceTypeEq : smallSourceType = largeSourceType)
      (object : WellSorted.isObjectPattern pattern = true)
      (scope : pattern.isWellScopedAt smallTargetBound.length = true)
      (small : CostStaticRegionPlan source color targetFree smallSourceBound
        smallTargetBound smallThinning smallAvailable outer pattern
        smallSourceType)
      (large : CostStaticRegionPlan source color targetFree largeSourceBound
        largeTargetBound largeThinning largeAvailable outer pattern
        largeSourceType) :
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix ambient regime small
        large := by
    let rootExpected := mapTypeExpr (color.symbols source) smallSourceType
    let binderFront : List TypeExpr :=
      match pattern, smallSourceType with
      | .lambda _ _, .arrow domain _ =>
          [mapTypeExpr (color.symbols source) domain]
      | .multiLambda arity _ _, .arrow (.multiBinder domain) _ =>
          List.replicate arity (mapTypeExpr (color.symbols source) domain)
      | _, _ => []
    subst largeTargetBound
    cases small with
    | @bvar _ _ _ _ _ targetIndex _ sourceIndex lookup correspondence
        availableScope =>
        cases large with
        | bvar largeSourceIndex largeLookup largeCorrespondence
            largeAvailableScope =>
            have targetInside : targetIndex < smallTargetBound.length := by
              simpa [Pattern.isWellScopedAt] using scope
            rw [CostStaticBinderThinning.toSourceIndex?_eq_targetToSourceIndex?]
              at correspondence largeCorrespondence
            rw [CostStaticBinderThinning.targetToSourceIndex?_append_of_lt
              source color smallTargetBound ambient targetIndex targetInside]
              at largeCorrespondence
            have sourceIndexEq : sourceIndex = largeSourceIndex :=
              Option.some.inj (correspondence.symm.trans largeCorrespondence)
            subst largeSourceIndex
            exact ⟨sourceTypeEq, rfl, .nil, .bvar regime sourceIndex⟩
    | fvar lookup =>
        cases large
        exact ⟨sourceTypeEq, rfl, .nil, .sourceFVar regime _⟩
    | boundaryApplication smallConstructor smallRendered smallOutside
        smallCertified smallCertifies =>
        cases large with
        | boundaryApplication largeConstructor largeRendered largeOutside
            largeCertified largeCertifies =>
            cases sourceTypeEq
            refine ⟨rfl, rfl, .cons availableSuffix.toSuffix .nil, ?_⟩
            change CostStaticAbstractPatternAlignment
              [smallCertified.typed] [largeCertified.typed]
              ambient regime
              (.fvar (costRegionBoundaryVariableName
                smallCertified.typed.boundary))
              (.fvar (costRegionBoundaryVariableName
                largeCertified.typed.boundary))
            exact CostStaticAbstractPatternAlignment.boundary
              (smallEntries := [smallCertified.typed])
              (largeEntries := [largeCertified.typed])
              regime (0 : Fin 1) (0 : Fin 1) rfl
              (by simpa [smallCertified.targetSupport_eq,
                largeCertified.targetSupport_eq] using availableSuffix)
        | application largeConstructor largeRendered largeCurrent
            largePreimage largeNotBare largeChildren =>
            have constructorEq : smallConstructor = largeConstructor :=
              source.renderDeclaredCostConstructor_injective
                (smallRendered.trans largeRendered.symm)
            subst largeConstructor
            exact (smallOutside largeCurrent).elim
    | @application _ _ _ _ _ wireName arguments smallConstructor
        smallRendered smallCurrent smallPreimage smallNotBare smallChildren =>
        cases large with
        | boundaryApplication largeConstructor largeRendered largeOutside
            largeCertified largeCertifies =>
            have constructorEq : smallConstructor = largeConstructor :=
              source.renderDeclaredCostConstructor_injective
                (smallRendered.trans largeRendered.symm)
            subst largeConstructor
            exact (largeOutside smallCurrent).elim
        | application largeConstructor largeRendered largeCurrent
            largePreimage largeNotBare largeChildren =>
            have constructorEq : smallConstructor = largeConstructor :=
              source.renderDeclaredCostConstructor_injective
                (smallRendered.trans largeRendered.symm)
            subst largeConstructor
            have preimageEq : smallPreimage = largePreimage :=
              CostStaticConstructorPreimage.eq _ _
            have childSuffix : CostStaticAvailabilityAt ambient
                (if ReflectiveContextSupport.isQuoteConstructor
                    source.reflection.1
                    smallPreimage.sourceConstructor.1.label then .sealed
                  else regime)
                (if ReflectiveContextSupport.isQuoteConstructor
                    source.reflection.1
                    smallPreimage.sourceConstructor.1.label then []
                  else smallAvailable)
                (if ReflectiveContextSupport.isQuoteConstructor
                    source.reflection.1
                    largePreimage.sourceConstructor.1.label then []
                  else largeAvailable) := by
              have labelEq : smallPreimage.sourceConstructor.1.label =
                  largePreimage.sourceConstructor.1.label :=
                congrArg (fun preimage => preimage.sourceConstructor.1.label)
                  preimageEq
              by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
                  source.reflection.1
                    smallPreimage.sourceConstructor.1.label = true
              · have largeQuoted : ReflectiveContextSupport.isQuoteConstructor
                    source.reflection.1
                      largePreimage.sourceConstructor.1.label = true := by
                  simpa [← labelEq] using quoted
                simp [quoted, largeQuoted, CostStaticAvailabilityAt]
              · have largeOrdinary :
                    ReflectiveContextSupport.isQuoteConstructor
                      source.reflection.1
                        largePreimage.sourceConstructor.1.label ≠ true := by
                  simpa [← labelEq] using quoted
                simpa [quoted, largeOrdinary] using availableSuffix
            have childObject :
                WellSorted.isObjectPatternList arguments = true := by
              simpa [WellSorted.isObjectPattern] using object
            have childScope : Pattern.isWellScopedListAt
                smallTargetBound.length arguments = true := by
              simpa [Pattern.isWellScopedAt] using scope
            have parametersEq :
                smallPreimage.sourceConstructor.1.params =
                  largePreimage.sourceConstructor.1.params :=
              congrArg (fun preimage => preimage.sourceConstructor.1.params)
                preimageEq
            have childrenSuffix :=
              CostStaticArgumentPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique childSuffix rfl parametersEq childObject
                  childScope smallChildren largeChildren
            exact ⟨sourceTypeEq, childrenSuffix.occurrences_eq,
              childrenSuffix.fibers,
              by
                change CostStaticAbstractPatternAlignment
                  smallChildren.boundaryTable.entries
                  largeChildren.boundaryTable.entries
                  ambient regime
                  (.apply smallPreimage.sourceConstructor.1.label
                    smallChildren.abstractPatterns)
                  (.apply largePreimage.sourceConstructor.1.label
                    largeChildren.abstractPatterns)
                simpa [preimageEq] using
                  (CostStaticAbstractPatternAlignment.apply regime
                    smallPreimage.sourceConstructor.1.label
                    childrenSuffix.abstractPatterns)⟩
    | @lambda _ _ _ _ _ binder body domain codomain smallBody =>
        cases large with
        | @lambda _ _ _ _ _ _ _ largeDomain largeCodomain largeBody =>
            injection sourceTypeEq with domainEq codomainEq
            subst_vars
            have childResult :=
              CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
              unique
              (by simpa [binderFront] using
                (CostStaticAvailabilityAt.prepend binderFront
                  availableSuffix))
              rfl rfl
              (by simpa [WellSorted.isObjectPattern] using object)
              (by simpa [binderFront, Pattern.isWellScopedAt, Nat.add_comm]
                using scope)
              smallBody largeBody
            exact ⟨rfl, childResult.occurrences_eq, childResult.fibers,
              by
                change CostStaticAbstractPatternAlignment
                  smallBody.boundaryTable.entries
                  largeBody.boundaryTable.entries
                  ambient regime
                  (.lambda binder smallBody.abstractPattern)
                  (.lambda binder largeBody.abstractPattern)
                exact .lambda regime binder childResult.abstractPattern⟩
    | @multiLambda _ _ _ _ _ arity binders body domain codomain smallBody =>
        cases large with
        | @multiLambda _ _ _ _ _ _ _ _ largeDomain largeCodomain largeBody =>
            injection sourceTypeEq with multiDomainEq codomainEq
            injection multiDomainEq with domainEq
            subst_vars
            have childTargetBoundEq :
                List.replicate arity
                    (mapTypeExpr (color.symbols source) largeDomain) ++
                    (smallTargetBound ++ ambient) =
                  (List.replicate arity
                      (mapTypeExpr (color.symbols source) largeDomain) ++
                    smallTargetBound) ++ ambient := by
              rw [List.append_assoc]
            have childResult :=
              CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
              unique
              (by simpa [binderFront] using
                (CostStaticAvailabilityAt.prepend binderFront
                  availableSuffix))
              childTargetBoundEq rfl
              (by simpa [WellSorted.isObjectPattern] using object)
              (by simpa [binderFront, Pattern.isWellScopedAt,
                  List.length_append, List.length_replicate, Nat.add_comm]
                using scope)
              smallBody largeBody
            exact ⟨rfl, childResult.occurrences_eq, childResult.fibers,
              by
                change CostStaticAbstractPatternAlignment
                  smallBody.boundaryTable.entries
                  largeBody.boundaryTable.entries
                  ambient regime
                  (.multiLambda arity binders smallBody.abstractPattern)
                  (.multiLambda arity binders largeBody.abstractPattern)
                exact .multiLambda regime arity binders
                  childResult.abstractPattern⟩
    | @collection _ _ _ _ _ collectionType elements rest smallType
        smallChoice smallSelected smallChildren =>
        cases sourceTypeEq
        cases large with
        | @collection _ _ _ _ _ _ _ _ _ largeChoice largeSelected
            largeChildren =>
            have objectParts : rest.isNone = true ∧
                WellSorted.isObjectPatternList elements = true := by
              simpa [WellSorted.isObjectPattern] using object
            have objects : WellSorted.isObjectPatternList elements = true :=
              objectParts.2
            have elementsScope : Pattern.isWellScopedListAt
                smallTargetBound.length elements = true := by
              simpa [Pattern.isWellScopedAt] using scope
            have choicesEq :=
              costStaticCollectionTypingChoices_append_outer_eq_of_scoped
                source color targetFree smallTargetBound ambient collectionType
                  elements rootExpected objects elementsScope
            have largeSelectedSmall : largeChoice ∈
                costStaticCollectionTypingChoices source color targetFree
                  smallTargetBound collectionType elements
                    rootExpected := by
              rw [← choicesEq]
              simpa [rootExpected] using largeSelected
            have choiceEq : smallChoice = largeChoice :=
              (unique color targetFree smallTargetBound collectionType elements
                rootExpected).choice_eq
                  (by simpa [rootExpected] using smallSelected)
                  largeSelectedSmall
            subst largeChoice
            have childrenSuffix :=
              CostStaticElementPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique availableSuffix rfl rfl objects elementsScope
                  smallChildren largeChildren
            exact ⟨rfl, childrenSuffix.occurrences_eq,
              childrenSuffix.fibers,
              by
                change CostStaticAbstractPatternAlignment
                  smallChildren.boundaryTable.entries
                  largeChildren.boundaryTable.entries
                  ambient regime
                  (.collection collectionType smallChildren.abstractPatterns
                    (rest.map costRegionSourceVariableName))
                  (.collection collectionType largeChildren.abstractPatterns
                    (rest.map costRegionSourceVariableName))
                exact .collection regime collectionType rest
                  childrenSuffix.abstractPatterns⟩
        | @boundaryCollection _ _ _ _ _ _ _ _ _ largeRejected
            largeOpposite largeOppositeSelected largeCertified largeCertifies =>
            have objectParts : rest.isNone = true ∧
                WellSorted.isObjectPatternList elements = true := by
              simpa [WellSorted.isObjectPattern] using object
            have objects : WellSorted.isObjectPatternList elements = true :=
              objectParts.2
            have elementsScope : Pattern.isWellScopedListAt
                smallTargetBound.length elements = true := by
              simpa [Pattern.isWellScopedAt] using scope
            have choicesEq :=
              costStaticCollectionTypingChoices_append_outer_eq_of_scoped
                source color targetFree smallTargetBound ambient collectionType
                  elements rootExpected objects elementsScope
            have largeRejectedSmall :
                costStaticCollectionTypingChoices source color targetFree
                  (smallTargetBound ++ ambient) collectionType elements
                    rootExpected = [] := by
              simpa [rootExpected] using largeRejected
            rw [choicesEq] at largeRejectedSmall
            have smallSelected' : smallChoice ∈
                costStaticCollectionTypingChoices source color targetFree
                  smallTargetBound collectionType elements rootExpected := by
              simpa [rootExpected] using smallSelected
            rw [largeRejectedSmall] at smallSelected'
            simp at smallSelected'
    | @boundaryCollection _ _ _ _ _ collectionType elements rest smallType
        smallRejected smallOpposite smallOppositeSelected smallCertified
          smallCertifies =>
        cases sourceTypeEq
        cases large with
        | @collection _ _ _ _ _ _ _ _ _ largeChoice largeSelected
            largeChildren =>
            have objectParts : rest.isNone = true ∧
                WellSorted.isObjectPatternList elements = true := by
              simpa [WellSorted.isObjectPattern] using object
            have objects : WellSorted.isObjectPatternList elements = true :=
              objectParts.2
            have elementsScope : Pattern.isWellScopedListAt
                smallTargetBound.length elements = true := by
              simpa [Pattern.isWellScopedAt] using scope
            have choicesEq :=
              costStaticCollectionTypingChoices_append_outer_eq_of_scoped
                source color targetFree smallTargetBound ambient collectionType
                  elements rootExpected objects elementsScope
            have largeSelectedSmall : largeChoice ∈
                costStaticCollectionTypingChoices source color targetFree
                  smallTargetBound collectionType elements
                    rootExpected := by
              rw [← choicesEq]
              simpa [rootExpected] using largeSelected
            have smallRejected' :
                costStaticCollectionTypingChoices source color targetFree
                  smallTargetBound collectionType elements rootExpected = [] := by
              simpa [rootExpected] using smallRejected
            rw [smallRejected'] at largeSelectedSmall
            simp at largeSelectedSmall
        | @boundaryCollection _ _ _ _ _ _ _ _ _ largeRejected
            largeOpposite largeOppositeSelected largeCertified largeCertifies =>
            refine ⟨rfl, rfl, .cons availableSuffix.toSuffix .nil, ?_⟩
            change CostStaticAbstractPatternAlignment
              [smallCertified.typed] [largeCertified.typed]
              ambient regime
              (.fvar (costRegionBoundaryVariableName
                smallCertified.typed.boundary))
              (.fvar (costRegionBoundaryVariableName
                largeCertified.typed.boundary))
            exact CostStaticAbstractPatternAlignment.boundary
              (smallEntries := [smallCertified.typed])
              (largeEntries := [largeCertified.typed])
              regime (0 : Fin 1) (0 : Fin 1) rfl
              (by simpa [smallCertified.targetSupport_eq,
                largeCertified.targetSupport_eq] using availableSuffix)
  termination_by 3 * sizeOf pattern + 2
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Argument-spine companion of the plan-level suffix theorem. -/
  theorem CostStaticArgumentPlan.boundaryFibersAvailabilitySuffix_of_scoped
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallSourceBound largeSourceBound smallTargetBound largeTargetBound
        ambient :
        List TypeExpr}
      {regime : CostStaticAvailabilityRegime}
      {smallThinning : CostStaticBinderThinning source color smallSourceBound
        smallTargetBound}
      {largeThinning : CostStaticBinderThinning source color largeSourceBound
        largeTargetBound}
      {smallAvailable largeAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern}
      {smallParameters largeParameters : List TermParam}
      (unique : CostStaticCollectionGloballyUnambiguous source)
      (availableSuffix : CostStaticAvailabilityAt ambient regime smallAvailable
        largeAvailable)
      (targetBoundEq : largeTargetBound = smallTargetBound ++ ambient)
      (parametersEq : smallParameters = largeParameters)
      (objects : WellSorted.isObjectPatternList arguments = true)
      (scope : Pattern.isWellScopedListAt smallTargetBound.length arguments =
        true)
      (small : CostStaticArgumentPlan source color targetFree smallSourceBound
        smallTargetBound smallThinning smallAvailable outer wireName before
        arguments smallParameters)
      (large : CostStaticArgumentPlan source color targetFree largeSourceBound
        largeTargetBound largeThinning largeAvailable outer wireName before
        arguments largeParameters) :
      CostStaticArgumentPlan.BoundaryFibersAvailabilitySuffix ambient regime small
        large := by
    subst largeTargetBound
    cases parametersEq
    cases small with
    | nil =>
        cases large
        exact ⟨rfl, rfl, .nil, .nil regime⟩
    | @cons _ _ _ _ _ _ _ argument arguments parameter parameters
        smallExpected smallRepresentation smallParameterType smallHead
          smallTail =>
        cases large with
        | @cons _ _ _ _ _ _ _ _ _ _ _ largeExpected largeRepresentation
            largeParameterType largeHead largeTail =>
            have expectedEq : smallExpected = largeExpected :=
              Option.some.inj (smallParameterType.symm.trans
                largeParameterType)
            simp only [WellSorted.isObjectPatternList, Bool.and_eq_true]
              at objects
            simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scope
            have headSuffix :=
              CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique availableSuffix rfl expectedEq objects.1
                  scope.1 smallHead largeHead
            have tailSuffix :=
              CostStaticArgumentPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique availableSuffix rfl rfl objects.2 scope.2
                  smallTail largeTail
            refine ⟨rfl, congrArg₂ List.append headSuffix.occurrences_eq
              tailSuffix.occurrences_eq, ?_, ?_⟩
            · exact CostRegionBoundaryFibers.AvailabilitySuffix.append_cast
                headSuffix.occurrences_eq tailSuffix.occurrences_eq
                  headSuffix.fibers tailSuffix.fibers
            · have headAbstract :=
                CostStaticAbstractPatternAlignment.appendEntries
                  smallTail.boundaryTable.entries
                  largeTail.boundaryTable.entries headSuffix.abstractPattern
              have tailAbstract :=
                CostStaticAbstractPatternAlignment.CostStaticAbstractPatternListAlignment.prependEntries
                  smallHead.boundaryTable.entries
                  largeHead.boundaryTable.entries
                  (by
                    simpa only [TypedCostRegionBoundaryTable.entries_length]
                      using congrArg List.length headSuffix.occurrences_eq)
                  tailSuffix.abstractPatterns
              simp only [CostStaticArgumentPlan.boundaryTable,
                CostStaticArgumentPlan.abstractPatterns,
                CostStaticArgumentPlan.occurrences]
              rw [TypedCostRegionBoundaryTable.entries_append
                smallHead.boundaryTable smallTail.boundaryTable,
                TypedCostRegionBoundaryTable.entries_append
                  largeHead.boundaryTable largeTail.boundaryTable]
              exact .cons regime headAbstract tailAbstract
  termination_by 3 * sizeOf arguments + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Homogeneous-element companion of the plan-level suffix theorem. -/
  theorem CostStaticElementPlan.boundaryFibersAvailabilitySuffix_of_scoped
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallSourceBound largeSourceBound smallTargetBound largeTargetBound
        ambient :
        List TypeExpr}
      {regime : CostStaticAvailabilityRegime}
      {smallThinning : CostStaticBinderThinning source color smallSourceBound
        smallTargetBound}
      {largeThinning : CostStaticBinderThinning source color largeSourceBound
        largeTargetBound}
      {smallAvailable largeAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {smallSourceElementType largeSourceElementType : TypeExpr}
      (unique : CostStaticCollectionGloballyUnambiguous source)
      (availableSuffix : CostStaticAvailabilityAt ambient regime smallAvailable
        largeAvailable)
      (targetBoundEq : largeTargetBound = smallTargetBound ++ ambient)
      (sourceElementTypeEq : smallSourceElementType = largeSourceElementType)
      (objects : WellSorted.isObjectPatternList elements = true)
      (scope : Pattern.isWellScopedListAt smallTargetBound.length elements =
        true)
      (small : CostStaticElementPlan source color targetFree smallSourceBound
        smallTargetBound smallThinning smallAvailable outer collectionType
        before elements rest smallSourceElementType)
      (large : CostStaticElementPlan source color targetFree largeSourceBound
        largeTargetBound largeThinning largeAvailable outer collectionType
        before elements rest largeSourceElementType) :
      CostStaticElementPlan.BoundaryFibersAvailabilitySuffix ambient regime small
        large := by
    subst largeTargetBound
    cases sourceElementTypeEq
    cases small with
    | nil =>
        cases large
        exact ⟨rfl, rfl, .nil, .nil regime⟩
    | @cons _ _ _ _ _ _ _ element elements _ _ smallHead smallTail =>
        cases large with
        | cons largeHead largeTail =>
            simp only [WellSorted.isObjectPatternList, Bool.and_eq_true]
              at objects
            simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scope
            have headSuffix :=
              CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique availableSuffix rfl rfl objects.1 scope.1
                  smallHead largeHead
            have tailSuffix :=
              CostStaticElementPlan.boundaryFibersAvailabilitySuffix_of_scoped
                unique availableSuffix rfl rfl objects.2 scope.2
                  smallTail largeTail
            refine ⟨rfl, congrArg₂ List.append headSuffix.occurrences_eq
              tailSuffix.occurrences_eq, ?_, ?_⟩
            · exact CostRegionBoundaryFibers.AvailabilitySuffix.append_cast
                headSuffix.occurrences_eq tailSuffix.occurrences_eq
                  headSuffix.fibers tailSuffix.fibers
            · have headAbstract :=
                CostStaticAbstractPatternAlignment.appendEntries
                  smallTail.boundaryTable.entries
                  largeTail.boundaryTable.entries headSuffix.abstractPattern
              have tailAbstract :=
                CostStaticAbstractPatternAlignment.CostStaticAbstractPatternListAlignment.prependEntries
                  smallHead.boundaryTable.entries
                  largeHead.boundaryTable.entries
                  (by
                    simpa only [TypedCostRegionBoundaryTable.entries_length]
                      using congrArg List.length headSuffix.occurrences_eq)
                  tailSuffix.abstractPatterns
              simp only [CostStaticElementPlan.boundaryTable,
                CostStaticElementPlan.abstractPatterns,
                CostStaticElementPlan.occurrences]
              rw [TypedCostRegionBoundaryTable.entries_append
                smallHead.boundaryTable smallTail.boundaryTable,
                TypedCostRegionBoundaryTable.entries_append
                  largeHead.boundaryTable largeTail.boundaryTable]
              exact .cons regime headAbstract tailAbstract
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

end

namespace CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix

/-- A plan-level fibre certificate induces the corresponding relation on the
exact finite tables consumed by normalization. -/
theorem boundaryTables
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    {small : CostStaticRegionPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer pattern sourceType}
    {large : CostStaticRegionPlan source color targetFree largeSourceBound
      largeTargetBound largeThinning largeAvailable outer pattern sourceType}
    (aligned : BoundaryFibersAvailabilitySuffix ambient regime small large) :
    TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
      (TypedCostRegionBoundaryTable.cast aligned.occurrences_eq
        small.boundaryTable)
      large.boundaryTable := by
  apply TypedCostRegionBoundaryTable.AvailabilitySuffix.of_certify
    aligned.fibers
  · rw [TypedCostRegionBoundaryTable.certify?_cast,
      small.certify_boundaryFibers]
    rfl
  · exact large.certify_boundaryFibers

end CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix

/-- Consumer-facing planner suffix law.  It returns the exact occurrence
transport together with the certified table relation used by static
normalization. -/
theorem CostStaticRegionPlan.boundaryTablesAvailabilitySuffix_of_scoped
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound largeSourceBound smallTargetBound ambient :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      (smallTargetBound ++ ambient)}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (unique : CostStaticCollectionGloballyUnambiguous source)
    (availableSuffix : CostStaticAvailabilityAt ambient .exposed smallAvailable
      largeAvailable)
    (object : WellSorted.isObjectPattern pattern = true)
    (scope : pattern.isWellScopedAt smallTargetBound.length = true)
    (small : CostStaticRegionPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer pattern sourceType)
    (large : CostStaticRegionPlan source color targetFree largeSourceBound
      (smallTargetBound ++ ambient) largeThinning largeAvailable outer pattern
      sourceType) :
    ∃ occurrencesEq : small.occurrences = large.occurrences,
      TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
        (TypedCostRegionBoundaryTable.cast occurrencesEq small.boundaryTable)
        large.boundaryTable := by
  let aligned :=
    CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped unique
      availableSuffix rfl rfl object scope small large
  exact ⟨aligned.occurrences_eq, aligned.boundaryTables⟩

/-- Equality-tolerant consumer interface for independently indexed plans.
The raw pattern and source type may arrive as propositionally equal node
projections; eliminating those equalities here keeps all dependent table
transport inside the planner layer. -/
theorem CostStaticRegionPlan.boundaryTablesAndAbstractAvailabilitySuffix_of_scoped
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound largeSourceBound smallTargetBound largeTargetBound
      ambient : List TypeExpr}
    {smallThinning : CostStaticBinderThinning source color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning source color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : OneHoleContext} {smallPattern largePattern : Pattern}
    {smallSourceType largeSourceType : TypeExpr}
    (unique : CostStaticCollectionGloballyUnambiguous source)
    (availableSuffix : CostStaticAvailabilityAt ambient .exposed
      smallAvailable largeAvailable)
    (targetBoundEq : largeTargetBound = smallTargetBound ++ ambient)
    (patternEq : smallPattern = largePattern)
    (sourceTypeEq : smallSourceType = largeSourceType)
    (object : WellSorted.isObjectPattern smallPattern = true)
    (scope : smallPattern.isWellScopedAt smallTargetBound.length = true)
    (small : CostStaticRegionPlan source color targetFree smallSourceBound
      smallTargetBound smallThinning smallAvailable outer smallPattern
      smallSourceType)
    (large : CostStaticRegionPlan source color targetFree largeSourceBound
      largeTargetBound largeThinning largeAvailable outer largePattern
      largeSourceType) :
    ∃ occurrencesEq : small.occurrences = large.occurrences,
      TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
          (TypedCostRegionBoundaryTable.cast occurrencesEq
            small.boundaryTable) large.boundaryTable ∧
        CostStaticAbstractPatternAlignment small.boundaryTable.entries
          large.boundaryTable.entries ambient .exposed
            small.abstractPattern large.abstractPattern := by
  subst largePattern
  subst largeSourceType
  let aligned :=
    CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped unique
      availableSuffix targetBoundEq rfl object scope small large
  exact ⟨aligned.occurrences_eq, aligned.boundaryTables,
    aligned.abstractPattern⟩

end Mettapedia.GSLT.LanguageDef
