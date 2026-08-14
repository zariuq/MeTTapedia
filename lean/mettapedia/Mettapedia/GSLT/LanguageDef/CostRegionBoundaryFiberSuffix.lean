import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# Binder-suffix transport for Cost boundary fibres

Appending an ambient binder suffix has two possible effects at a maximal
foreign boundary.  Outside quotation the suffix is retained; below a quote
the locally available context is rebuilt independently and is unchanged.
This module records that dichotomy positionally over the exact occurrence
list used by the static-region planner.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- One local availability either retains the new ambient suffix or is
unchanged because an enclosing quote reset the ambient context. -/
def CostStaticAvailabilitySuffix (ambient small large : List TypeExpr) : Prop :=
  large = small ++ ambient ∨ large = small

namespace CostStaticAvailabilitySuffix

theorem exposed (ambient small : List TypeExpr) :
    CostStaticAvailabilitySuffix ambient small (small ++ ambient) :=
  Or.inl rfl

theorem unchanged (ambient current : List TypeExpr) :
    CostStaticAvailabilitySuffix ambient current current :=
  Or.inr rfl

/-- A pair that is neither the exposed extension nor unchanged is rejected. -/
theorem not_of_ne_append_of_ne
    {ambient small large : List TypeExpr}
    (notExposed : large ≠ small ++ ambient)
    (notLocal : large ≠ small) :
    ¬ CostStaticAvailabilitySuffix ambient small large := by
  intro suffix
  exact suffix.elim notExposed notLocal

/-- Prepending the same binder prefix preserves either availability regime. -/
theorem prepend (front : List TypeExpr)
    {ambient small large : List TypeExpr}
    (suffix : CostStaticAvailabilitySuffix ambient small large) :
    CostStaticAvailabilitySuffix ambient (front ++ small)
      (front ++ large) := by
  rcases suffix with exposed | unchanged
  · left
    simpa only [List.append_assoc] using congrArg (front ++ ·) exposed
  · right
    exact congrArg (front ++ ·) unchanged

end CostStaticAvailabilitySuffix

/-- Whether one occurrence remains exposed to an appended ambient suffix or
has crossed a quote that seals the local availability.  This index lives at
the fibre layer because planner evidence must retain the chosen branch. -/
inductive CostStaticAvailabilityRegime where
  | exposed
  | sealed
deriving DecidableEq

/-- The exact availability equation selected by one structural regime. -/
def CostStaticAvailabilityAt (ambient : List TypeExpr) :
    CostStaticAvailabilityRegime → List TypeExpr → List TypeExpr → Prop
  | .exposed, small, large => large = small ++ ambient
  | .sealed, small, large => large = small

namespace CostStaticAvailabilityAt

/-- A regime-indexed equation implies the older disjunctive suffix view. -/
theorem toSuffix {ambient small large : List TypeExpr}
    {regime : CostStaticAvailabilityRegime}
    (related : CostStaticAvailabilityAt ambient regime small large) :
    CostStaticAvailabilitySuffix ambient small large := by
  cases regime with
  | exposed => exact Or.inl related
  | sealed => exact Or.inr related

/-- Prepending the same binder prefix preserves the selected regime. -/
theorem prepend (front : List TypeExpr) {ambient small large : List TypeExpr}
    {regime : CostStaticAvailabilityRegime}
    (related : CostStaticAvailabilityAt ambient regime small large) :
    CostStaticAvailabilityAt ambient regime (front ++ small)
      (front ++ large) := by
  cases regime with
  | exposed =>
      simpa only [CostStaticAvailabilityAt, List.append_assoc] using
        congrArg (front ++ ·) related
  | sealed =>
      simpa only [CostStaticAvailabilityAt] using congrArg (front ++ ·) related

end CostStaticAvailabilityAt

namespace CostRegionBoundaryFibers

/-- Pointwise binder-suffix transport over the exact finite occurrence list.
Target types and positions are retained literally; only target support may
choose independently between the exposed and quote-local regimes. -/
inductive AvailabilitySuffix (ambient : List TypeExpr) :
    {occurrences : List CostRegionOccurrence} →
      CostRegionBoundaryFibers occurrences →
      CostRegionBoundaryFibers occurrences → Prop where
  | nil : AvailabilitySuffix ambient .nil .nil
  | cons {occurrence : CostRegionOccurrence}
      {occurrences : List CostRegionOccurrence}
      {smallSupport largeSupport : List TypeExpr} {targetType : TypeExpr}
      {smallTail largeTail : CostRegionBoundaryFibers occurrences}
      (support : CostStaticAvailabilitySuffix ambient smallSupport largeSupport)
      (tail : AvailabilitySuffix ambient smallTail largeTail) :
      AvailabilitySuffix ambient
        (.cons (occurrence := occurrence) smallSupport targetType smallTail)
        (.cons (occurrence := occurrence) largeSupport targetType largeTail)

namespace AvailabilitySuffix

/-- The empty boundary inventory is suffix-stable. -/
theorem empty (ambient : List TypeExpr) :
    AvailabilitySuffix ambient (.nil : CostRegionBoundaryFibers []) .nil :=
  .nil

/-- Every fibre plan is related to itself through the quote-local regime. -/
theorem refl (ambient : List TypeExpr) :
    {occurrences : List CostRegionOccurrence} →
      (fibers : CostRegionBoundaryFibers occurrences) →
      AvailabilitySuffix ambient fibers fibers
  | [], .nil => .nil
  | _ :: _, .cons support _targetType tail =>
      .cons (CostStaticAvailabilitySuffix.unchanged ambient support)
        (refl ambient tail)

/-- Positional suffix transport composes over the collector's chronological
concatenation. -/
theorem append {ambient : List TypeExpr}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {smallLeft largeLeft : CostRegionBoundaryFibers leftOccurrences}
    {smallRight largeRight : CostRegionBoundaryFibers rightOccurrences}
    (left : AvailabilitySuffix ambient smallLeft largeLeft)
    (right : AvailabilitySuffix ambient smallRight largeRight) :
    AvailabilitySuffix ambient (smallLeft.append smallRight)
      (largeLeft.append largeRight) := by
  induction left with
  | nil => exact right
  | cons support tail inductionHypothesis =>
      exact .cons support inductionHypothesis

/-- Reindexing both fibre plans along the same occurrence equality preserves
their positional suffix relation. -/
theorem cast {ambient : List TypeExpr}
    {source target : List CostRegionOccurrence}
    {small large : CostRegionBoundaryFibers source}
    (occurrences : source = target)
    (suffix : AvailabilitySuffix ambient small large) :
    AvailabilitySuffix ambient
      (CostRegionBoundaryFibers.cast occurrences small)
      (CostRegionBoundaryFibers.cast occurrences large) := by
  cases occurrences
  exact suffix

/-- Equality of the two retained fibre plans transports a positional suffix
certificate without changing its occurrence index. -/
theorem congr {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {small small' large large' : CostRegionBoundaryFibers occurrences}
    (smallEq : small = small') (largeEq : large = large')
    (suffix : AvailabilitySuffix ambient small large) :
    AvailabilitySuffix ambient small' large' := by
  cases smallEq
  cases largeEq
  exact suffix

/-- Inverting a nonempty positional relation exposes the exact support
dichotomy at its head. -/
theorem head {ambient : List TypeExpr}
    {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    {smallSupport largeSupport : List TypeExpr} {targetType : TypeExpr}
    {smallTail largeTail : CostRegionBoundaryFibers occurrences}
    (suffix : AvailabilitySuffix ambient
      (.cons (occurrence := occurrence) smallSupport targetType smallTail)
      (.cons (occurrence := occurrence) largeSupport targetType largeTail)) :
    CostStaticAvailabilitySuffix ambient smallSupport largeSupport := by
  cases suffix with
  | cons support _ => exact support

/-- Positive exposed canary: one positional boundary retains the suffix. -/
theorem singleton_exposed (ambient support : List TypeExpr)
    (targetType : TypeExpr) (occurrence : CostRegionOccurrence) :
    AvailabilitySuffix ambient
      (.cons (occurrence := occurrence) support targetType .nil)
      (.cons (occurrence := occurrence) (support ++ ambient) targetType .nil) :=
  .cons (CostStaticAvailabilitySuffix.exposed ambient support) .nil

/-- Positive quote-local canary: one positional boundary remains unchanged. -/
theorem singleton_local (ambient support : List TypeExpr)
    (targetType : TypeExpr) (occurrence : CostRegionOccurrence) :
    AvailabilitySuffix ambient
      (.cons (occurrence := occurrence) support targetType .nil)
      (.cons (occurrence := occurrence) support targetType .nil) :=
  .cons (CostStaticAvailabilitySuffix.unchanged ambient support) .nil

/-- Negative canary: a singleton support change outside both regimes cannot
be disguised by the dependent occurrence index. -/
theorem not_singleton_of_support_ne_append_of_ne
    {ambient smallSupport largeSupport : List TypeExpr}
    {targetType : TypeExpr} {occurrence : CostRegionOccurrence}
    (notExposed : largeSupport ≠ smallSupport ++ ambient)
    (notLocal : largeSupport ≠ smallSupport) :
    ¬ AvailabilitySuffix ambient
      (.cons (occurrence := occurrence) smallSupport targetType .nil)
      (.cons (occurrence := occurrence) largeSupport targetType .nil) := by
  intro suffix
  exact CostStaticAvailabilitySuffix.not_of_ne_append_of_ne
    notExposed notLocal suffix.head

end AvailabilitySuffix
end CostRegionBoundaryFibers

/-! ### Positional collector conservation -/

private theorem collectCostStaticApplyBoundaryFibers_availabilitySuffix_of
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (inner ambient : List TypeExpr) (outerContext : OneHoleContext)
    (constructor : String) :
    ∀ (before arguments : List Pattern) (parameters : List TermParam),
      WellSorted.isObjectPatternList arguments = true →
      Pattern.isWellScopedListAt inner.length arguments = true →
      (∀ (argument : Pattern), argument ∈ arguments →
        WellSorted.isObjectPattern argument = true →
        argument.isWellScopedAt inner.length = true →
        ∀ (localOuter : OneHoleContext) (expected : TypeExpr)
          {small large : CostRegionBoundaryFibers
            (collectDeclaredCostStaticBoundaryOccurrencesAt source color
              localOuter argument)},
          collectCostStaticBoundaryFibersAt source color targetFree inner
              localOuter argument expected = some small →
          collectCostStaticBoundaryFibersAt source color targetFree
              (inner ++ ambient) localOuter argument expected = some large →
          CostRegionBoundaryFibers.AvailabilitySuffix ambient small large) →
      ∀ {small large : CostRegionBoundaryFibers
        (collectDeclaredCostStaticApplyBoundaryOccurrences source color
          outerContext constructor before arguments)},
        collectCostStaticApplyBoundaryFibers source color targetFree inner
            outerContext constructor before arguments parameters = some small →
        collectCostStaticApplyBoundaryFibers source color targetFree
            (inner ++ ambient) outerContext constructor before arguments
              parameters = some large →
        CostRegionBoundaryFibers.AvailabilitySuffix ambient small large := by
  intro before arguments
  induction arguments generalizing before with
  | nil =>
      intro parameters _objects _scope _children small large smallCollected
        largeCollected
      cases parameters with
      | nil =>
          simp [collectCostStaticApplyBoundaryFibers] at smallCollected largeCollected
          cases smallCollected
          cases largeCollected
          exact .nil
      | cons parameter parameters =>
          simp [collectCostStaticApplyBoundaryFibers] at smallCollected
  | cons argument arguments inductionHypothesis =>
      intro parameters objects scope children small large smallCollected
        largeCollected
      cases parameters with
      | nil =>
          simp [collectCostStaticApplyBoundaryFibers] at smallCollected
      | cons parameter parameters =>
          simp only [WellSorted.isObjectPatternList, Bool.and_eq_true]
            at objects
          simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scope
          cases parameterTypeEquation : WellSorted.parameterType? parameter with
          | none =>
              simp [collectCostStaticApplyBoundaryFibers,
                parameterTypeEquation] at smallCollected
          | some expected =>
              cases representationEquation :
                  WellSorted.matchesParameterRepresentation? parameter argument
              with
              | false =>
                  simp [collectCostStaticApplyBoundaryFibers,
                    parameterTypeEquation, representationEquation]
                    at smallCollected
              | true =>
                  let localOuter := outerContext.comp
                    (.apply constructor before .hole arguments)
                  cases headSmallEquation : collectCostStaticBoundaryFibersAt
                      source color targetFree inner localOuter argument expected
                    with
                  | none =>
                      simp [collectCostStaticApplyBoundaryFibers,
                        parameterTypeEquation, representationEquation,
                        localOuter, headSmallEquation] at smallCollected
                  | some headSmall =>
                      cases headLargeEquation :
                          collectCostStaticBoundaryFibersAt source color
                            targetFree (inner ++ ambient) localOuter argument
                              expected with
                      | none =>
                          simp [collectCostStaticApplyBoundaryFibers,
                            parameterTypeEquation, representationEquation,
                            localOuter, headLargeEquation]
                            at largeCollected
                      | some headLarge =>
                          cases tailSmallEquation :
                              collectCostStaticApplyBoundaryFibers source color
                                targetFree inner outerContext constructor
                                  (before ++ [argument]) arguments parameters
                            with
                          | none =>
                              simp [collectCostStaticApplyBoundaryFibers,
                                parameterTypeEquation, representationEquation,
                                localOuter, headSmallEquation,
                                tailSmallEquation] at smallCollected
                          | some tailSmall =>
                              cases tailLargeEquation :
                                  collectCostStaticApplyBoundaryFibers source
                                    color targetFree (inner ++ ambient)
                                      outerContext constructor
                                        (before ++ [argument]) arguments
                                          parameters with
                              | none =>
                                  simp [collectCostStaticApplyBoundaryFibers,
                                    parameterTypeEquation,
                                    representationEquation, localOuter,
                                    headLargeEquation, tailLargeEquation]
                                    at largeCollected
                              | some tailLarge =>
                                  have headSuffix := children argument (by simp)
                                    objects.1 scope.1 localOuter expected
                                      headSmallEquation headLargeEquation
                                  have tailSuffix := inductionHypothesis
                                    (before ++ [argument]) parameters objects.2
                                      scope.2
                                      (fun member membership memberObject
                                          memberScope =>
                                        children member (by simp [membership])
                                          memberObject memberScope)
                                      tailSmallEquation tailLargeEquation
                                  simp [collectCostStaticApplyBoundaryFibers,
                                    parameterTypeEquation,
                                    representationEquation, localOuter,
                                    headSmallEquation, headLargeEquation,
                                    tailSmallEquation, tailLargeEquation]
                                    at smallCollected largeCollected
                                  subst small
                                  subst large
                                  exact headSuffix.append tailSuffix

private theorem collectCostStaticCollectionBoundaryFibers_availabilitySuffix_of
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (inner ambient : List TypeExpr) (outerContext : OneHoleContext)
    (collectionType : CollType) (rest : Option String)
    (elementType : TypeExpr) :
    ∀ (before elements : List Pattern),
      WellSorted.isObjectPatternList elements = true →
      Pattern.isWellScopedListAt inner.length elements = true →
      (∀ (element : Pattern), element ∈ elements →
        WellSorted.isObjectPattern element = true →
        element.isWellScopedAt inner.length = true →
        ∀ (localOuter : OneHoleContext)
          {small large : CostRegionBoundaryFibers
            (collectDeclaredCostStaticBoundaryOccurrencesAt source color
              localOuter element)},
          collectCostStaticBoundaryFibersAt source color targetFree inner
              localOuter element elementType = some small →
          collectCostStaticBoundaryFibersAt source color targetFree
              (inner ++ ambient) localOuter element elementType = some large →
          CostRegionBoundaryFibers.AvailabilitySuffix ambient small large) →
      ∀ {small large : CostRegionBoundaryFibers
        (collectDeclaredCostStaticCollectionBoundaryOccurrences source color
          outerContext collectionType before elements rest)},
        collectCostStaticCollectionBoundaryFibers source color targetFree inner
            outerContext collectionType before elements rest elementType =
              some small →
        collectCostStaticCollectionBoundaryFibers source color targetFree
            (inner ++ ambient) outerContext collectionType before elements rest
              elementType = some large →
        CostRegionBoundaryFibers.AvailabilitySuffix ambient small large := by
  intro before elements
  induction elements generalizing before with
  | nil =>
      intro _objects _scope _children small large smallCollected largeCollected
      simp [collectCostStaticCollectionBoundaryFibers] at smallCollected largeCollected
      cases smallCollected
      cases largeCollected
      exact .nil
  | cons element elements inductionHypothesis =>
      intro objects scope children small large smallCollected largeCollected
      simp only [WellSorted.isObjectPatternList, Bool.and_eq_true] at objects
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scope
      let localOuter := outerContext.comp
        (.collection collectionType before .hole elements rest)
      cases headSmallEquation : collectCostStaticBoundaryFibersAt source color
          targetFree inner localOuter element elementType with
      | none =>
          simp [collectCostStaticCollectionBoundaryFibers, localOuter,
            headSmallEquation] at smallCollected
      | some headSmall =>
          cases headLargeEquation : collectCostStaticBoundaryFibersAt source
              color targetFree (inner ++ ambient) localOuter element elementType
            with
          | none =>
              simp [collectCostStaticCollectionBoundaryFibers, localOuter,
                headLargeEquation] at largeCollected
          | some headLarge =>
              cases tailSmallEquation :
                  collectCostStaticCollectionBoundaryFibers source color
                    targetFree inner outerContext collectionType
                      (before ++ [element]) elements rest elementType with
              | none =>
                  simp [collectCostStaticCollectionBoundaryFibers, localOuter,
                    headSmallEquation, tailSmallEquation] at smallCollected
              | some tailSmall =>
                  cases tailLargeEquation :
                      collectCostStaticCollectionBoundaryFibers source color
                        targetFree (inner ++ ambient) outerContext collectionType
                          (before ++ [element]) elements rest elementType with
                  | none =>
                      simp [collectCostStaticCollectionBoundaryFibers,
                        localOuter, headLargeEquation, tailLargeEquation]
                        at largeCollected
                  | some tailLarge =>
                      have headSuffix := children element (by simp) objects.1
                        scope.1 localOuter headSmallEquation headLargeEquation
                      have tailSuffix := inductionHypothesis
                        (before ++ [element]) objects.2 scope.2
                          (fun member membership memberObject memberScope =>
                            children member (by simp [membership]) memberObject
                              memberScope)
                          tailSmallEquation tailLargeEquation
                      simp [collectCostStaticCollectionBoundaryFibers,
                        localOuter, headSmallEquation, headLargeEquation,
                        tailSmallEquation, tailLargeEquation]
                        at smallCollected largeCollected
                      subst small
                      subst large
                      exact headSuffix.append tailSuffix

/-- The application collector's foreign-boundary branch, exposed without a
dependent match over the decoder proof. -/
theorem collectCostStaticBoundaryFibersAt_apply_of_decode_none
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (available : List TypeExpr)
    (outerContext : OneHoleContext) (constructor : String)
    (arguments : List Pattern) (expected : TypeExpr)
    (decoded : decodeDeclaredCostStaticConstructor source color constructor =
      none) :
    collectCostStaticBoundaryFibersAt source color targetFree available
        outerContext (.apply constructor arguments) expected =
      some (CostRegionBoundaryFibers.cast (by
        simp [collectDeclaredCostStaticBoundaryOccurrencesAt, decoded])
        (.cons (occurrence :=
          { context := outerContext
            content := .apply constructor arguments })
          available expected .nil)) := by
  unfold collectCostStaticBoundaryFibersAt
  split
  · rfl
  · rename_i sourceConstructor decodedSome
    cases decoded.symm.trans decodedSome

/-- The application collector's selected-static branch, exposed without a
dependent match over either decoder proof. -/
theorem collectCostStaticBoundaryFibersAt_apply_of_decode_some
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (available : List TypeExpr)
    (outerContext : OneHoleContext) (constructor : String)
    (arguments : List Pattern) (expected : TypeExpr)
    (sourceConstructor : String)
    (decoded : decodeDeclaredCostStaticConstructor source color constructor =
      some sourceConstructor)
    (intrinsic : source.DeclaredCostConstructor)
    (intrinsicDecoded : source.decodeDeclaredCostConstructor constructor =
      some intrinsic) :
    collectCostStaticBoundaryFibersAt source color targetFree available
        outerContext (.apply constructor arguments) expected =
      (collectCostStaticApplyBoundaryFibers source color targetFree
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then [] else available)
        outerContext constructor [] arguments
          (source.materializeDeclaredCostConstructor intrinsic).params).map
        (CostRegionBoundaryFibers.cast (by
          simp [collectDeclaredCostStaticBoundaryOccurrencesAt, decoded])) := by
  unfold collectCostStaticBoundaryFibersAt
  split
  · rename_i decodedNone
    cases decoded.symm.trans decodedNone
  · rename_i selected decodedSome
    have selectedEq : selected = sourceConstructor :=
      Option.some.inj (decodedSome.symm.trans decoded)
    subst selected
    split
    · rename_i intrinsicNone
      cases intrinsicDecoded.symm.trans intrinsicNone
    · rename_i selectedIntrinsic intrinsicSome
      have selectedIntrinsicEq : selectedIntrinsic = intrinsic :=
        Option.some.inj (intrinsicSome.symm.trans intrinsicDecoded)
      subst selectedIntrinsic
      rfl

/-- The lambda branch, with its occurrence-index transport made explicit. -/
theorem collectCostStaticBoundaryFibersAt_lambda_arrow
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (available : List TypeExpr)
    (outerContext : OneHoleContext) (binder : Option String) (body : Pattern)
    (domain codomain : TypeExpr) :
    collectCostStaticBoundaryFibersAt source color targetFree available
        outerContext (.lambda binder body) (.arrow domain codomain) =
      collectCostStaticBoundaryFibersAt source color targetFree
        (domain :: available) (outerContext.comp (.lambda binder .hole)) body
          codomain := by
  simp [collectCostStaticBoundaryFibersAt]

/-- The multi-lambda branch, with its occurrence-index transport made
explicit. -/
theorem collectCostStaticBoundaryFibersAt_multiLambda_arrow
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (available : List TypeExpr)
    (outerContext : OneHoleContext) (arity : Nat) (binders : List String)
    (body : Pattern) (domain codomain : TypeExpr) :
    collectCostStaticBoundaryFibersAt source color targetFree available
        outerContext (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain) =
      collectCostStaticBoundaryFibersAt source color targetFree
        (List.replicate arity domain ++ available)
          (outerContext.comp (.multiLambda arity binders .hole)) body
            codomain := by
  simp [collectCostStaticBoundaryFibersAt]

/-- The syntax-derived boundary-fibre collector is positionally stable under
an unused outer binder suffix.  Every retained occurrence either receives
that suffix or lies below a quote and keeps its local support unchanged. -/
theorem collectCostStaticBoundaryFibersAt_availabilitySuffix_of_scoped
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (inner ambient : List TypeExpr) (outerContext : OneHoleContext) :
    ∀ (pattern : Pattern) (expected : TypeExpr),
      WellSorted.isObjectPattern pattern = true →
      pattern.isWellScopedAt inner.length = true →
      ∀ {small large : CostRegionBoundaryFibers
        (collectDeclaredCostStaticBoundaryOccurrencesAt source color
          outerContext pattern)},
        collectCostStaticBoundaryFibersAt source color targetFree inner
            outerContext pattern expected = some small →
        collectCostStaticBoundaryFibersAt source color targetFree
            (inner ++ ambient) outerContext pattern expected = some large →
        CostRegionBoundaryFibers.AvailabilitySuffix ambient small large := by
  intro pattern
  induction pattern using Pattern.inductionOn generalizing inner outerContext
    with
  | hbvar index =>
      intro expected _object _scope small large smallCollected largeCollected
      simp [collectCostStaticBoundaryFibersAt] at smallCollected largeCollected
      subst small
      subst large
      exact .nil
  | hfvar name =>
      intro expected _object _scope small large smallCollected largeCollected
      simp [collectCostStaticBoundaryFibersAt] at smallCollected largeCollected
      subst small
      subst large
      exact .nil
  | happly constructor arguments inductionHypothesis =>
      intro expected object scope small large smallCollected largeCollected
      simp only [WellSorted.isObjectPattern] at object
      simp only [Pattern.isWellScopedAt] at scope
      cases decoded : decodeDeclaredCostStaticConstructor source color
          constructor with
      | none =>
          let occurrence : CostRegionOccurrence :=
            { context := outerContext
              content := .apply constructor arguments }
          have occurrenceEquality : [occurrence] =
              collectDeclaredCostStaticBoundaryOccurrencesAt source color
                outerContext (.apply constructor arguments) := by
            simp [occurrence, collectDeclaredCostStaticBoundaryOccurrencesAt,
              decoded]
          let smallExpected := CostRegionBoundaryFibers.cast
            occurrenceEquality
              (.cons (occurrence := occurrence) inner expected .nil)
          let largeExpected := CostRegionBoundaryFibers.cast
            occurrenceEquality
              (.cons (occurrence := occurrence) (inner ++ ambient) expected
                .nil)
          have smallProduced : collectCostStaticBoundaryFibersAt source color
              targetFree inner outerContext (.apply constructor arguments)
                expected = some smallExpected := by
            simpa [smallExpected, occurrence] using
              collectCostStaticBoundaryFibersAt_apply_of_decode_none source
                color targetFree inner outerContext constructor arguments
                  expected decoded
          have largeProduced : collectCostStaticBoundaryFibersAt source color
              targetFree (inner ++ ambient) outerContext
                (.apply constructor arguments) expected = some largeExpected := by
            simpa [largeExpected, occurrence] using
              collectCostStaticBoundaryFibersAt_apply_of_decode_none source
                color targetFree (inner ++ ambient) outerContext constructor
                  arguments expected decoded
          have smallEq : smallExpected = small :=
            Option.some.inj (smallProduced.symm.trans smallCollected)
          have largeEq : largeExpected = large :=
            Option.some.inj (largeProduced.symm.trans largeCollected)
          apply CostRegionBoundaryFibers.AvailabilitySuffix.congr smallEq largeEq
          exact CostRegionBoundaryFibers.AvailabilitySuffix.cast
            occurrenceEquality
              (CostRegionBoundaryFibers.AvailabilitySuffix.singleton_exposed
                ambient inner expected occurrence)
      | some sourceConstructor =>
          cases intrinsicEquation : source.decodeDeclaredCostConstructor
              constructor with
          | none =>
              unfold decodeDeclaredCostStaticConstructor at decoded
              rw [intrinsicEquation] at decoded
              contradiction
          | some intrinsic =>
              have occurrenceEquality :
                  collectDeclaredCostStaticApplyBoundaryOccurrences source color
                      outerContext constructor [] arguments =
                    collectDeclaredCostStaticBoundaryOccurrencesAt source color
                      outerContext (.apply constructor arguments) := by
                simp [collectDeclaredCostStaticBoundaryOccurrencesAt, decoded]
              by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
                  source.costWholeReflectionProfile constructor = true
              · cases commonEquation : collectCostStaticApplyBoundaryFibers
                    source color targetFree [] outerContext constructor []
                      arguments
                        (source.materializeDeclaredCostConstructor intrinsic).params
                  with
                | none =>
                    have branch :=
                      collectCostStaticBoundaryFibersAt_apply_of_decode_some
                        source color targetFree inner outerContext constructor
                          arguments expected sourceConstructor decoded intrinsic
                            intrinsicEquation
                    rw [if_pos quoted, commonEquation] at branch
                    rw [branch] at smallCollected
                    contradiction
                | some common =>
                    let expectedFibers := CostRegionBoundaryFibers.cast
                      occurrenceEquality common
                    have smallProduced : collectCostStaticBoundaryFibersAt
                        source color targetFree inner outerContext
                          (.apply constructor arguments) expected =
                        some expectedFibers := by
                      have branch :=
                        collectCostStaticBoundaryFibersAt_apply_of_decode_some
                          source color targetFree inner outerContext constructor
                            arguments expected sourceConstructor decoded intrinsic
                              intrinsicEquation
                      rw [if_pos quoted, commonEquation] at branch
                      simpa [expectedFibers] using branch
                    have largeProduced : collectCostStaticBoundaryFibersAt
                        source color targetFree (inner ++ ambient) outerContext
                          (.apply constructor arguments) expected =
                        some expectedFibers := by
                      have branch :=
                        collectCostStaticBoundaryFibersAt_apply_of_decode_some
                          source color targetFree (inner ++ ambient) outerContext
                            constructor arguments expected sourceConstructor
                              decoded intrinsic intrinsicEquation
                      rw [if_pos quoted, commonEquation] at branch
                      simpa [expectedFibers] using branch
                    apply CostRegionBoundaryFibers.AvailabilitySuffix.congr
                      (Option.some.inj (smallProduced.symm.trans smallCollected))
                      (Option.some.inj (largeProduced.symm.trans largeCollected))
                    exact CostRegionBoundaryFibers.AvailabilitySuffix.refl
                      ambient expectedFibers
              · have ordinary : ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile constructor = false :=
                  Bool.eq_false_of_not_eq_true quoted
                cases smallRawEquation : collectCostStaticApplyBoundaryFibers
                    source color targetFree inner outerContext constructor []
                      arguments
                        (source.materializeDeclaredCostConstructor intrinsic).params
                  with
                | none =>
                    have branch :=
                      collectCostStaticBoundaryFibersAt_apply_of_decode_some
                        source color targetFree inner outerContext constructor
                          arguments expected sourceConstructor decoded intrinsic
                            intrinsicEquation
                    rw [if_neg quoted, smallRawEquation] at branch
                    rw [branch] at smallCollected
                    contradiction
                | some smallRaw =>
                    cases largeRawEquation :
                        collectCostStaticApplyBoundaryFibers source color
                          targetFree (inner ++ ambient) outerContext constructor
                            [] arguments
                              (source.materializeDeclaredCostConstructor
                                intrinsic).params with
                    | none =>
                        have branch :=
                          collectCostStaticBoundaryFibersAt_apply_of_decode_some
                            source color targetFree (inner ++ ambient)
                              outerContext constructor arguments expected
                                sourceConstructor decoded intrinsic
                                  intrinsicEquation
                        rw [if_neg quoted, largeRawEquation] at branch
                        rw [branch] at largeCollected
                        contradiction
                    | some largeRaw =>
                        have rawSuffix :=
                          collectCostStaticApplyBoundaryFibers_availabilitySuffix_of
                            source color targetFree inner ambient outerContext
                              constructor [] arguments
                                (source.materializeDeclaredCostConstructor
                                  intrinsic).params object scope
                              (fun argument membership argumentObject
                                  argumentScope localOuter argumentExpected
                                    {small} {large} headSmall headLarge =>
                                inductionHypothesis argument membership
                                  (inner := inner) (outerContext := localOuter)
                                    argumentExpected argumentObject argumentScope
                                      headSmall headLarge)
                              smallRawEquation largeRawEquation
                        let smallExpected := CostRegionBoundaryFibers.cast
                          occurrenceEquality smallRaw
                        let largeExpected := CostRegionBoundaryFibers.cast
                          occurrenceEquality largeRaw
                        have smallProduced :
                            collectCostStaticBoundaryFibersAt source color
                              targetFree inner outerContext
                                (.apply constructor arguments) expected =
                              some smallExpected := by
                          have branch :=
                            collectCostStaticBoundaryFibersAt_apply_of_decode_some
                              source color targetFree inner outerContext
                                constructor arguments expected sourceConstructor
                                  decoded intrinsic intrinsicEquation
                          rw [if_neg quoted, smallRawEquation] at branch
                          simpa [smallExpected] using branch
                        have largeProduced :
                            collectCostStaticBoundaryFibersAt source color
                              targetFree (inner ++ ambient) outerContext
                                (.apply constructor arguments) expected =
                              some largeExpected := by
                          have branch :=
                            collectCostStaticBoundaryFibersAt_apply_of_decode_some
                              source color targetFree (inner ++ ambient)
                                outerContext constructor arguments expected
                                  sourceConstructor decoded intrinsic
                                    intrinsicEquation
                          rw [if_neg quoted, largeRawEquation] at branch
                          simpa [largeExpected] using branch
                        apply
                          CostRegionBoundaryFibers.AvailabilitySuffix.congr
                            (Option.some.inj
                              (smallProduced.symm.trans smallCollected))
                            (Option.some.inj
                              (largeProduced.symm.trans largeCollected))
                        exact rawSuffix.cast occurrenceEquality
  | hlambda binder body inductionHypothesis =>
      intro expected object scope small large smallCollected largeCollected
      cases expected with
      | arrow domain codomain =>
          let childOuter := outerContext.comp (.lambda binder .hole)
          rw [collectCostStaticBoundaryFibersAt_lambda_arrow] at smallCollected
          rw [collectCostStaticBoundaryFibersAt_lambda_arrow] at largeCollected
          have availabilityEquality : domain :: (inner ++ ambient) =
              (domain :: inner) ++ ambient := rfl
          rw [availabilityEquality] at largeCollected
          exact inductionHypothesis (inner := domain :: inner)
            (outerContext := childOuter) codomain object
              (by simpa [Pattern.isWellScopedAt, Nat.add_comm] using scope)
              smallCollected largeCollected
      | base category =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
      | collection collectionType elementType =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
      | multiBinder domain =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
  | hmultiLambda arity binders body inductionHypothesis =>
      intro expected object scope small large smallCollected largeCollected
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder binderType =>
              let childOuter := outerContext.comp
                (.multiLambda arity binders .hole)
              rw [collectCostStaticBoundaryFibersAt_multiLambda_arrow] at smallCollected
              rw [collectCostStaticBoundaryFibersAt_multiLambda_arrow] at largeCollected
              have availabilityEquality :
                  List.replicate arity binderType ++ (inner ++ ambient) =
                    (List.replicate arity binderType ++ inner) ++ ambient :=
                (List.append_assoc _ _ _).symm
              rw [availabilityEquality] at largeCollected
              exact inductionHypothesis
                (inner := List.replicate arity binderType ++ inner)
                (outerContext := childOuter) codomain object
                (by simpa [Pattern.isWellScopedAt, List.length_append,
                  List.length_replicate, Nat.add_comm] using scope)
                smallCollected largeCollected
          | base category =>
              simp [collectCostStaticBoundaryFibersAt] at smallCollected
          | collection collectionType elementType =>
              simp [collectCostStaticBoundaryFibersAt] at smallCollected
          | arrow first second =>
              simp [collectCostStaticBoundaryFibersAt] at smallCollected
      | base category =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
      | collection collectionType elementType =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
      | multiBinder domain =>
          simp [collectCostStaticBoundaryFibersAt] at smallCollected
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro expected object scope small large smallCollected largeCollected
      simp [WellSorted.isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      intro expected object scope small large smallCollected largeCollected
      simp only [WellSorted.isObjectPattern, Bool.and_eq_true] at object
      simp only [Pattern.isWellScopedAt] at scope
      have choiceEquality :=
        costStaticCollectionTypingChoice?_append_outer_eq_of_scoped source color
          targetFree inner ambient collectionType elements expected object.2
            scope
      cases choiceSmallEquation : costStaticCollectionTypingChoice? source color
          targetFree inner collectionType elements expected with
      | none =>
          simp [collectCostStaticBoundaryFibersAt, choiceSmallEquation]
            at smallCollected
      | some choice =>
          have choiceLargeEquation : costStaticCollectionTypingChoice? source
              color targetFree (inner ++ ambient) collectionType elements
                expected = some choice := by
            rw [choiceEquality]
            exact choiceSmallEquation
          simp [collectCostStaticBoundaryFibersAt, choiceSmallEquation,
            choiceLargeEquation] at smallCollected largeCollected
          exact
            collectCostStaticCollectionBoundaryFibers_availabilitySuffix_of
              source color targetFree inner ambient outerContext collectionType
                rest (choice.targetElementType source color) [] elements
                object.2 scope
                (fun element membership elementObject elementScope localOuter
                    {small} {large} headSmall headLarge =>
                  inductionHypothesis element membership (inner := inner)
                    (outerContext := localOuter)
                      (choice.targetElementType source color) elementObject
                        elementScope headSmall headLarge)
                smallCollected largeCollected

end Mettapedia.GSLT.LanguageDef
