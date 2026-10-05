import Mettapedia.GSLT.LanguageDef.Cost.RegionPlanAbstraction

/-!
# Source typing for occurrence-parametric retained region abstraction

The existing retained plan supplies constructor membership, binder thinning,
quote resets and certified boundaries. The naming interface requires only the
source type and target support stored at each actual finite occurrence. It
therefore admits distinct names for repeated immutable keys.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Read the boundary at the exact occurrence index, using the proved table length. -/
def boundaryAt {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Fin occurrences.length) : CostRegionBoundary :=
  (table.entries.get (slot.cast (TypedCostRegionBoundaryTable.entries_length table).symm)).boundary

@[simp] theorem boundaryAt_append_left {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right) (slot : Fin left.length) :
    boundaryAt (TypedCostRegionBoundaryTable.append first second) (leftSlot left right slot) =
      boundaryAt first slot := by
  unfold boundaryAt
  simp only [TypedCostRegionBoundaryTable.entries_append, List.get_eq_getElem,
    Fin.val_cast, leftSlot_val]
  rw [List.getElem_append_left (by simpa only [TypedCostRegionBoundaryTable.entries_length] using slot.isLt)]

@[simp] theorem boundaryAt_append_right {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right) (slot : Fin right.length) :
    boundaryAt (TypedCostRegionBoundaryTable.append first second) (rightSlot left right slot) =
      boundaryAt second slot := by
  unfold boundaryAt
  simp only [TypedCostRegionBoundaryTable.entries_append, List.get_eq_getElem,
    Fin.val_cast, rightSlot_val]
  rw [List.getElem_append_right (by simp)]
  simp only [TypedCostRegionBoundaryTable.entries_length, Nat.add_sub_cancel_left]

/-- Names expose exactly the existing per-position source type and target support. -/
def NamesValid {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (free : WellSorted.FreeTypeContext) (support : ContextSupport.Support)
    (names : Fin occurrences.length → String) : Prop :=
  ∀ slot, free (names slot) = some (boundaryAt table slot).type ∧
    support (names slot) = (boundaryAt table slot).targetSupport

theorem namesValid_left {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right)
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {names : Fin (left ++ right).length → String}
    (valid : NamesValid (TypedCostRegionBoundaryTable.append first second) free support names) :
    NamesValid first free support (fun slot => names (leftSlot left right slot)) := by
  intro slot
  simpa only [boundaryAt_append_left] using valid (leftSlot left right slot)

theorem namesValid_right {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right)
    {free : WellSorted.FreeTypeContext} {support : ContextSupport.Support}
    {names : Fin (left ++ right).length → String}
    (valid : NamesValid (TypedCostRegionBoundaryTable.append first second) free support names) :
    NamesValid second free support (fun slot => names (rightSlot left right slot)) := by
  intro slot
  simpa only [boundaryAt_append_right] using valid (rightSlot left right slot)

theorem matchesParameterRepresentation
    {source : CIGSLT} {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType)
    (names : Fin plan.occurrences.length → String) (parameter : TermParam)
    (representation : WellSorted.MatchesParameterRepresentation parameter term) :
    WellSorted.MatchesParameterRepresentation parameter (pattern plan names) := by
  cases plan with
  | @lambda _ _ _ _ _ binder _ _ _ body =>
      cases parameter <;> cases binder <;>
        simp_all [WellSorted.MatchesParameterRepresentation, pattern]
  | @multiLambda _ _ _ _ _ arity binders _ _ _ body =>
      cases parameter <;> cases binders <;>
        simp_all [WellSorted.MatchesParameterRepresentation, pattern]
  | _ => cases parameter <;> simp_all [WellSorted.MatchesParameterRepresentation]

mutual
  /-- The source skeleton projected from a typed region plan is accepted by
  the authored constructor fragment under any position-indexed naming that
  preserves each certified source sort and exact target binder support. -/
  theorem pattern_supportedSafe
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer term sourceType)
      (free : WellSorted.FreeTypeContext) (support : ContextSupport.Support)
      (sourceLookup : ∀ {name type}, targetFree name = some (mapTypeExpr (color.symbols source) type) →
        free (costRegionSourceVariableName name) = some type)
      (sourceSupport : ∀ name, support (costRegionSourceVariableName name) = [])
      (names : Fin plan.occurrences.length → String)
      (named : NamesValid plan.boundaryTable free support names) :
      ∃ typed : WellSorted.HasTypeWithConstructors
          source.theory.presentation.presentation.language
          (· ∈ source.continuationRetyping.wrappedLabels)
          free sourceBound (pattern plan names)
          sourceType,
        typed.toHasType.ReflectiveSupportSafeAt source.reflection.1
          support
          sourceAvailable (mapTypeExpr (color.symbols source)) := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound (.bvar _) _ :=
          .bvar lookup
        refine ⟨typed, ?_⟩
        exact .bvar lookup sourceAvailable
    | @fvar _ _ _ _ _ name _ lookup =>
        have variableLookup := sourceLookup lookup
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (.fvar (costRegionSourceVariableName name)) sourceType :=
          .fvar variableLookup
        refine ⟨typed, ?_⟩
        exact .fvar variableLookup sourceAvailable
          ⟨sourceAvailable, by
            rw [sourceSupport]
            simp⟩
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        have slot := named ⟨0, by change 0 < 1; decide⟩
        have sourceTypeEquality := certifyCostRegionBoundary?_sourceType_eq certifies
        have variableLookup : free (names ⟨0, by change 0 < 1; decide⟩) = some sourceType :=
          slot.1.trans (congrArg some sourceTypeEquality)
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels) free sourceBound
            (.fvar (names ⟨0, by change 0 < 1; decide⟩)) sourceType := .fvar variableLookup
        refine ⟨typed, ?_⟩
        exact .fvar variableLookup sourceAvailable ⟨[], by
          rw [slot.2]
          change sourceAvailable = certified.typed.boundary.targetSupport
          exact certified.targetSupport_eq.symm⟩
    | application constructor rendered current preimage notBare children =>
        obtain ⟨argumentsTyped, argumentsSafe⟩ :=
          arguments_supportedSafe children free support sourceLookup sourceSupport names named
        have allowed : preimage.sourceConstructor.1.label ∈
            source.continuationRetyping.wrappedLabels :=
          (source.continuationRetyping.mem_wrappedLabels_iff
            preimage.sourceConstructor).2 preimage.wrapped
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (.apply preimage.sourceConstructor.1.label
              (CostRegionPlanAbstraction.arguments children names))
            (.base preimage.sourceConstructor.1.category) :=
          .constructor allowed preimage.sourceConstructor.2 notBare
            argumentsTyped
        refine ⟨typed, ?_⟩
        by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
            source.reflection.1
            preimage.sourceConstructor.1.label = true
        · have safeAtQuote :
              argumentsTyped.toArgumentsHaveTypes.ReflectiveSupportSafeAt
                source.reflection.1 support []
                  (mapTypeExpr (color.symbols source)) := by
            simpa [quoted] using argumentsSafe
          change typed.toHasType.ReflectiveSupportSafeAt
            source.reflection.1 support sourceAvailable
              (mapTypeExpr (color.symbols source))
          simpa [typed, pattern] using
            (WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
              (membership := preimage.sourceConstructor.2)
              (notBare := notBare) quoted safeAtQuote)
        · have ordinary : ReflectiveContextSupport.isQuoteConstructor
              source.reflection.1
              preimage.sourceConstructor.1.label = false :=
            Bool.eq_false_of_not_eq_true quoted
          have safeOrdinary :
              argumentsTyped.toArgumentsHaveTypes.ReflectiveSupportSafeAt
                source.reflection.1 support sourceAvailable
                  (mapTypeExpr (color.symbols source)) := by
            simpa [ordinary] using argumentsSafe
          change typed.toHasType.ReflectiveSupportSafeAt
            source.reflection.1 support sourceAvailable
              (mapTypeExpr (color.symbols source))
          simpa [typed, pattern] using
            (WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
              (membership := preimage.sourceConstructor.2)
              (notBare := notBare) ordinary safeOrdinary)
    | @lambda _ _ _ _ _ binder _ _ _ bodyPlan =>
        obtain ⟨bodyTyped, bodySafe⟩ :=
          pattern_supportedSafe bodyPlan free support sourceLookup sourceSupport names named
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (.lambda binder (pattern bodyPlan names)) _ :=
          .lambda (binder := binder) bodyTyped
        refine ⟨typed, ?_⟩
        change typed.toHasType.ReflectiveSupportSafeAt
          source.reflection.1 support sourceAvailable
            (mapTypeExpr (color.symbols source))
        simpa [typed, pattern] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.lambda bodySafe)
    | @multiLambda _ _ _ _ _ arity binders _ _ _ bodyPlan =>
        obtain ⟨bodyTyped, bodySafe⟩ :=
          pattern_supportedSafe bodyPlan free support sourceLookup sourceSupport names named
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (.multiLambda arity binders (pattern bodyPlan names)) _ :=
          .multiLambda (binders := binders) bodyTyped
        refine ⟨typed, ?_⟩
        change typed.toHasType.ReflectiveSupportSafeAt
          source.reflection.1 support sourceAvailable
            (mapTypeExpr (color.symbols source))
        simpa [typed, pattern] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.multiLambda bodySafe)
    | @collection _ _ _ _ _ collectionType elements rest sourceType choice
        selected children =>
        obtain ⟨elementsTyped, elementsSafe⟩ :=
          elements_supportedSafe
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            children free support sourceLookup sourceSupport names named
        rcases mem_costStaticCollectionTypingChoices_sound source color
            targetFree targetBound collectionType elements
            (mapTypeExpr (color.symbols source) sourceType) choice selected with
          direct | bare
        · rcases direct with
            ⟨sourceElementType, choiceEquality, expectedEquality,
              elementsChecked⟩
          subst choice
          have sourceTypeEquality : sourceType =
              .collection collectionType sourceElementType :=
            mapTypeExpr_costStatic_injective source color expectedEquality
          subst sourceType
          let typed : WellSorted.HasTypeWithConstructors
              source.theory.presentation.presentation.language
              (· ∈ source.continuationRetyping.wrappedLabels)
              free sourceBound
              (.collection collectionType (CostRegionPlanAbstraction.elements children names)
                (rest.map costRegionSourceVariableName))
              (.collection collectionType sourceElementType) :=
            .collection elementsTyped
          refine ⟨typed, ?_⟩
          change typed.toHasType.ReflectiveSupportSafeAt
            source.reflection.1 support sourceAvailable
              (mapTypeExpr (color.symbols source))
          simpa [typed, pattern,
            CostCollectionTypingChoice.sourceElementType] using
            (WellSorted.HasType.ReflectiveSupportSafeAt.collection elementsSafe)
        · rcases bare with
            ⟨rule, sourceElementType, choiceEquality, membership,
              allowed, expectedEquality, parameterName, parameterShape,
              elementsChecked⟩
          subst choice
          have sourceTypeEquality : sourceType = .base rule.category :=
            mapTypeExpr_costStatic_injective source color expectedEquality
          subst sourceType
          let typed : WellSorted.HasTypeWithConstructors
              source.theory.presentation.presentation.language
              (· ∈ source.continuationRetyping.wrappedLabels)
              free sourceBound
              (.collection collectionType (CostRegionPlanAbstraction.elements children names)
                (rest.map costRegionSourceVariableName))
              (.base rule.category) :=
            .collectionConstructor allowed membership parameterShape
              elementsTyped
          refine ⟨typed, ?_⟩
          change typed.toHasType.ReflectiveSupportSafeAt
            source.reflection.1 support sourceAvailable
              (mapTypeExpr (color.symbols source))
          simpa [typed, pattern] using
            (WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
              (membership := membership) (parameterShape := parameterShape)
              elementsSafe)
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        have slot := named ⟨0, by change 0 < 1; decide⟩
        have sourceTypeEquality := certifyCostRegionBoundary?_sourceType_eq certifies
        have variableLookup : free (names ⟨0, by change 0 < 1; decide⟩) = some sourceType :=
          slot.1.trans (congrArg some sourceTypeEquality)
        let typed : WellSorted.HasTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels) free sourceBound
            (.fvar (names ⟨0, by change 0 < 1; decide⟩)) sourceType := .fvar variableLookup
        refine ⟨typed, ?_⟩
        exact .fvar variableLookup sourceAvailable ⟨[], by
          rw [slot.2]
          change sourceAvailable = certified.typed.boundary.targetSupport
          exact certified.targetSupport_eq.symm⟩

  /-- Constructor-argument companion to source-skeleton typing and support
  safety. Ordered table append restricts naming to exact finite positions. -/
  theorem arguments_supportedSafe
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (free : WellSorted.FreeTypeContext) (support : ContextSupport.Support)
      (sourceLookup : ∀ {name type}, targetFree name = some (mapTypeExpr (color.symbols source) type) →
        free (costRegionSourceVariableName name) = some type)
      (sourceSupport : ∀ name, support (costRegionSourceVariableName name) = [])
      (names : Fin plan.occurrences.length → String)
      (named : NamesValid plan.boundaryTable free support names) :
      ∃ typed : WellSorted.ArgumentsHaveTypesWithConstructors
          source.theory.presentation.presentation.language
          (· ∈ source.continuationRetyping.wrappedLabels)
          free sourceBound (CostRegionPlanAbstraction.arguments plan names)
          parameters,
        typed.toArgumentsHaveTypes.ReflectiveSupportSafeAt source.reflection.1
          support sourceAvailable
            (mapTypeExpr (color.symbols source)) := by
    cases plan with
    | nil =>
        let typed : WellSorted.ArgumentsHaveTypesWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound [] [] := .nil
        refine ⟨typed, ?_⟩
        exact .nil sourceBound sourceAvailable
    | cons representation parameterType head tail =>
        let headNames := fun slot => names (leftSlot head.occurrences tail.occurrences slot)
        let tailNames := fun slot => names (rightSlot head.occurrences tail.occurrences slot)
        have headNamed := namesValid_left head.boundaryTable tail.boundaryTable named
        have tailNamed := namesValid_right head.boundaryTable tail.boundaryTable named
        obtain ⟨headTyped, headSafe⟩ :=
          pattern_supportedSafe
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            head free support sourceLookup sourceSupport headNames headNamed
        obtain ⟨tailTyped, tailSafe⟩ :=
          arguments_supportedSafe
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            tail free support sourceLookup sourceSupport tailNames tailNamed
        have abstractRepresentation :=
          matchesParameterRepresentation head headNames _ representation
        let typed : WellSorted.ArgumentsHaveTypesWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (pattern head headNames :: arguments tail tailNames) _ :=
          .cons abstractRepresentation parameterType headTyped tailTyped
        refine ⟨typed, ?_⟩
        change typed.toArgumentsHaveTypes.ReflectiveSupportSafeAt
          source.reflection.1 support sourceAvailable
            (mapTypeExpr (color.symbols source))
        simpa [typed, arguments] using
          (WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := abstractRepresentation)
            (parameterType := parameterType) headSafe tailSafe)

  /-- Homogeneous-collection companion to source-skeleton typing and support
  safety. -/
  theorem elements_supportedSafe
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before elements rest
        sourceElementType)
      (free : WellSorted.FreeTypeContext) (support : ContextSupport.Support)
      (sourceLookup : ∀ {name type}, targetFree name = some (mapTypeExpr (color.symbols source) type) →
        free (costRegionSourceVariableName name) = some type)
      (sourceSupport : ∀ name, support (costRegionSourceVariableName name) = [])
      (names : Fin plan.occurrences.length → String)
      (named : NamesValid plan.boundaryTable free support names) :
      ∃ typed : WellSorted.ElementsHaveTypeWithConstructors
          source.theory.presentation.presentation.language
          (· ∈ source.continuationRetyping.wrappedLabels)
          free sourceBound (CostRegionPlanAbstraction.elements plan names)
          sourceElementType,
        typed.toElementsHaveType.ReflectiveSupportSafeAt source.reflection.1
          support sourceAvailable
            (mapTypeExpr (color.symbols source)) := by
    cases plan with
    | nil =>
        let typed : WellSorted.ElementsHaveTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound [] sourceElementType :=
          .nil sourceBound sourceElementType
        refine ⟨typed, ?_⟩
        exact .nil sourceBound sourceElementType sourceAvailable
    | cons head tail =>
        let headNames := fun slot => names (leftSlot head.occurrences tail.occurrences slot)
        let tailNames := fun slot => names (rightSlot head.occurrences tail.occurrences slot)
        have headNamed := namesValid_left head.boundaryTable tail.boundaryTable named
        have tailNamed := namesValid_right head.boundaryTable tail.boundaryTable named
        obtain ⟨headTyped, headSafe⟩ :=
          pattern_supportedSafe
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            head free support sourceLookup sourceSupport headNames headNamed
        obtain ⟨tailTyped, tailSafe⟩ :=
          elements_supportedSafe
            (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable)
            tail free support sourceLookup sourceSupport tailNames tailNamed
        let typed : WellSorted.ElementsHaveTypeWithConstructors
            source.theory.presentation.presentation.language
            (· ∈ source.continuationRetyping.wrappedLabels)
            free sourceBound
            (pattern head headNames :: elements tail tailNames)
            sourceElementType := .cons headTyped tailTyped
        refine ⟨typed, ?_⟩
        change typed.toElementsHaveType.ReflectiveSupportSafeAt
          source.reflection.1 support sourceAvailable
            (mapTypeExpr (color.symbols source))
        simpa [typed, elements] using
          (WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.cons
            headSafe tailSafe)
end

/-- The historical key naming satisfies the common local lookup interface. -/
theorem namesValid_keyNames {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences) :
    NamesValid table table.sourceFreeContext table.sourceSupport (keyNames table) := by
  intro slot
  let entry := table.entries.get (slot.cast (TypedCostRegionBoundaryTable.entries_length table).symm)
  have member : entry ∈ table.entries := List.get_mem _ _
  exact ⟨table.sourceFreeContext_boundaryVariable entry member,
    table.sourceSupport_boundaryVariable entry member⟩

/-- The previous whole-key typing/support theorem, including an arbitrary
containing table, follows from the common positional proof with the same
source typing and support interface. -/
theorem keyNames_supportedSafe {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType)
    {globalOccurrences : List CostRegionOccurrence}
    (globalTable : TypedCostRegionBoundaryTable source color targetFree globalOccurrences)
    (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries) :
    ∃ typed : WellSorted.HasTypeWithConstructors source.theory.presentation.presentation.language
        (· ∈ source.continuationRetyping.wrappedLabels)
        globalTable.sourceFreeContext sourceBound plan.abstractPattern sourceType,
      typed.toHasType.ReflectiveSupportSafeAt source.reflection.1 globalTable.sourceSupport
        sourceAvailable (mapTypeExpr (color.symbols source)) := by
  have lookups : ∀ {name type}, targetFree name = some (mapTypeExpr (color.symbols source) type) →
      globalTable.sourceFreeContext (costRegionSourceVariableName name) = some type := by
    intro name type lookup
    rw [globalTable.sourceFreeContext_sourceVariable, lookup]
    exact CostStaticTypeImage.decode_mapTypeExpr source.theory color type
  have named : NamesValid plan.boundaryTable globalTable.sourceFreeContext globalTable.sourceSupport
      (keyNames plan.boundaryTable) := by
    intro slot
    let entry := plan.boundaryTable.entries.get
      (slot.cast (TypedCostRegionBoundaryTable.entries_length plan.boundaryTable).symm)
    have member : entry ∈ globalTable.entries := entriesSubset (List.get_mem _ _)
    exact ⟨globalTable.sourceFreeContext_boundaryVariable entry member,
      globalTable.sourceSupport_boundaryVariable entry member⟩
  have result := pattern_supportedSafe plan globalTable.sourceFreeContext
    globalTable.sourceSupport lookups globalTable.sourceSupport_sourceVariable
    (keyNames plan.boundaryTable) named
  simpa only [pattern_keyNames] using result

end Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction
