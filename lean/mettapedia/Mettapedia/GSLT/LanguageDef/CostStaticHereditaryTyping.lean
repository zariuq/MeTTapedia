import Mettapedia.GSLT.LanguageDef.CostRegionTree
import Mettapedia.GSLT.LanguageDef.CostHereditaryTreeNormalization

/-!
# Proof-relevant typing of hereditary Cost images

Ordinary static transport proves target typing but forgets which declaration
typed a bare collection, because that label is not present in raw `Pattern`.
This module retains the exact cut-derived source-constructor witness through
the static map.  Recursive canonical arguments can therefore distinguish the
two Cost colours without inspecting reserved wire prefixes.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open StructuralMorphism

mutual
  /-- Static transport retaining the exact hereditary constructor image,
  including the syntax-invisible declaration of a bare collection. -/
  theorem WellSorted.HasTypeWithConstructors.mapCostStaticHereditary
      (source : CIGSLT) (color : CostStaticColor)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasTypeWithConstructors
        source.theory.presentation.presentation.language
        (· ∈ source.continuationRetyping.wrappedLabels)
        free bound pattern type) :
      WellSorted.HasTypeWithConstructors source.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage source color)
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (mapPattern (color.symbols source) pattern)
        (mapTypeExpr (color.symbols source) type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr (color.symbols source)))[index]? =
              some (mapTypeExpr (color.symbols source) type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr (color.symbols source))) lookup
        simpa [mapPattern] using
          (WellSorted.HasTypeWithConstructors.bvar
            (free := free.map (color.symbols source)) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map (color.symbols source)) name =
              some (mapTypeExpr (color.symbols source) type) := by
          simp [WellSorted.FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (WellSorted.HasTypeWithConstructors.fvar
            (bound := bound.map (mapTypeExpr (color.symbols source)))
            mappedLookup)
    | @constructor bound rule arguments labelSupported membership notBare
        argumentsTyped =>
        let authored : AuthoredConstructor
            source.theory.presentation.presentation := ⟨rule, membership⟩
        have wrappedConstructor : authored ∈
            source.continuationRetyping.wrappedConstructors :=
          (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
            labelSupported
        cases color with
        | base =>
            have mappedArguments :=
              argumentsTyped.mapCostStaticHereditary source .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetArguments :
                WellSorted.ArgumentsHaveTypesWithConstructors
                  source.costWholeLanguage
                  (CostStaticColor.hereditaryConstructorImage source .base)
                  (free.map (CostStaticColor.base.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.base.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.base.symbols source)))
                  (costBaseConstructor source.cut rule).params := by
              simpa only [parameterEquality, CostStaticColor.symbols] using
                mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costBaseConstructor source.cut rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costBaseConstructor_iff source.cut rule).mp
                  targetBare)
            have targetAllowed :
                CostStaticColor.hereditaryConstructorImage source .base
                  (costBaseConstructor source.cut rule).label :=
              ⟨rule.label, labelSupported, rfl⟩
            simpa [mapPattern, CostStaticColor.symbols, costBaseConstructor,
              costBaseStaticSymbols, costBasePresentationSymbols,
              mapTypeExpr] using
              (WellSorted.HasTypeWithConstructors.constructor targetAllowed
                (source.costBaseConstructor_mem_costWhole rule membership)
                targetNotBare targetArguments)
        | wrapped =>
            have mappedArguments :=
              argumentsTyped.mapCostStaticHereditary source .wrapped
            have parameterMapEquality :
                rule.params.map
                    (mapTermParam (costWrappedStaticSymbols source.theory)) =
                  rule.params.map
                    (mapParameterType
                      (costWrappedTypeExpr
                        source.theory.presentation.interactingSort.1.name)) := by
              apply List.map_congr_left
              intro parameter _membership
              exact mapTermParam_costWrappedStaticSymbols source parameter
            have targetArguments :
                WellSorted.ArgumentsHaveTypesWithConstructors
                  source.costWholeLanguage
                  (CostStaticColor.hereditaryConstructorImage source .wrapped)
                  (free.map (CostStaticColor.wrapped.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.wrapped.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.wrapped.symbols source)))
                  (costWrappedConstructor
                    (theory := source.theory) rule).params := by
              simpa only [costWrappedConstructor, CostStaticColor.symbols,
                parameterMapEquality] using mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costWrappedConstructor (theory := source.theory) rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costWrappedConstructor_iff
                  (theory := source.theory) rule).mp targetBare)
            have targetAllowed :
                CostStaticColor.hereditaryConstructorImage source .wrapped
                  (costWrappedConstructor
                    (theory := source.theory) rule).label :=
              ⟨rule.label, labelSupported, rfl⟩
            simpa [mapPattern, CostStaticColor.symbols,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasTypeWithConstructors.constructor targetAllowed
                (source.costWrappedConstructor_mem_costWhole authored
                  wrappedConstructor)
                targetNotBare targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStaticHereditary source color
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasTypeWithConstructors.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStaticHereditary source color
        have mappedBody' :
            WellSorted.HasTypeWithConstructors source.costWholeLanguage
              (CostStaticColor.hereditaryConstructorImage source color)
              (free.map (color.symbols source))
              (List.replicate arity
                  (mapTypeExpr (color.symbols source) domain) ++
                bound.map (mapTypeExpr (color.symbols source)))
              (mapPattern (color.symbols source) body)
              (mapTypeExpr (color.symbols source) codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasTypeWithConstructors.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody := bodyTyped.mapCostStaticHereditary source color
        have mappedReplacement :=
          replacementTyped.mapCostStaticHereditary source color
        simpa [mapPattern] using
          WellSorted.HasTypeWithConstructors.subst mappedBody mappedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have mappedElements :=
          elementsTyped.mapCostStaticHereditary source color
        simpa [mapPattern, mapTypeExpr] using
          (WellSorted.HasTypeWithConstructors.collection
            (rest := rest) mappedElements)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType labelSupported membership parameterShape
        elementsTyped =>
        let authored : AuthoredConstructor
            source.theory.presentation.presentation := ⟨rule, membership⟩
        have wrappedConstructor : authored ∈
            source.continuationRetyping.wrappedConstructors :=
          (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
            labelSupported
        cases color with
        | base =>
            have mappedElements :=
              elementsTyped.mapCostStaticHereditary source .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetShape :
                (costBaseConstructor source.cut rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr
                        (CostStaticColor.base.symbols source) elementType))] := by
              simp [parameterEquality, parameterShape,
                mapTermParam_costBaseStaticSymbols,
                CostStaticColor.symbols, mapParameterType,
                costBaseTypeExpr]
            have targetAllowed :
                CostStaticColor.hereditaryConstructorImage source .base
                  (costBaseConstructor source.cut rule).label :=
              ⟨rule.label, labelSupported, rfl⟩
            simpa [mapPattern, CostStaticColor.symbols, costBaseConstructor,
              costBaseStaticSymbols, costBasePresentationSymbols,
              mapTypeExpr] using
              (WellSorted.HasTypeWithConstructors.collectionConstructor
                targetAllowed
                (source.costBaseConstructor_mem_costWhole rule membership)
                targetShape mappedElements)
        | wrapped =>
            have mappedElements :=
              elementsTyped.mapCostStaticHereditary source .wrapped
            have targetShape :
                (costWrappedConstructor (theory := source.theory) rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr
                        (CostStaticColor.wrapped.symbols source)
                        elementType))] := by
              simp [costWrappedConstructor, parameterShape,
                CostStaticColor.symbols, mapParameterType,
                costWrappedTypeExpr]
            have targetAllowed :
                CostStaticColor.hereditaryConstructorImage source .wrapped
                  (costWrappedConstructor
                    (theory := source.theory) rule).label :=
              ⟨rule.label, labelSupported, rfl⟩
            simpa [mapPattern, CostStaticColor.symbols,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasTypeWithConstructors.collectionConstructor
                targetAllowed
                (source.costWrappedConstructor_mem_costWhole authored
                  wrappedConstructor)
                targetShape mappedElements)

  theorem WellSorted.ArgumentsHaveTypesWithConstructors.mapCostStaticHereditary
      (source : CIGSLT) (color : CostStaticColor)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypesWithConstructors
        source.theory.presentation.presentation.language
        (· ∈ source.continuationRetyping.wrappedLabels)
        free bound arguments parameters) :
      WellSorted.ArgumentsHaveTypesWithConstructors source.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage source color)
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (arguments.map (mapPattern (color.symbols source)))
        (parameters.map (mapTermParam (color.symbols source))) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            WellSorted.parameterType?
                (mapTermParam (color.symbols source) parameter) =
              some (mapTypeExpr (color.symbols source) expected) := by
          rw [WellSorted.parameterType?_mapTermParam, parameterType]
          rfl
        exact .cons
          ((WellSorted.matchesParameterRepresentation_map_iff
            (color.symbols source) parameter argument).2 representation)
          mappedParameterType
          (argumentTyped.mapCostStaticHereditary source color)
          (argumentsTyped.mapCostStaticHereditary source color)

  theorem WellSorted.ElementsHaveTypeWithConstructors.mapCostStaticHereditary
      (source : CIGSLT) (color : CostStaticColor)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveTypeWithConstructors
        source.theory.presentation.presentation.language
        (· ∈ source.continuationRetyping.wrappedLabels)
        free bound elements elementType) :
      WellSorted.ElementsHaveTypeWithConstructors source.costWholeLanguage
        (CostStaticColor.hereditaryConstructorImage source color)
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (elements.map (mapPattern (color.symbols source)))
        (mapTypeExpr (color.symbols source) elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.mapCostStaticHereditary source color)
          (elementsTyped.mapCostStaticHereditary source color)
end

private theorem matchesParameterRepresentation_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (parameter : TermParam) (pattern : Pattern) :
    WellSorted.MatchesParameterRepresentation parameter pattern →
      WellSorted.MatchesParameterRepresentation parameter
        (thinning.thickenAmbientBVars depth pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [WellSorted.MatchesParameterRepresentation,
          CostStaticBinderThinning.thickenAmbientBVars]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [WellSorted.MatchesParameterRepresentation,
          CostStaticBinderThinning.thickenAmbientBVars]
      case multiLambda arity binders body => cases binders <;> simp

mutual
  /-- Binder reinsertion preserves the proof-relevant hereditary declaration
  witness as well as ordinary typing. -/
  theorem WellSorted.HasTypeWithConstructors.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {language : LanguageDef} {allowed : String → Prop}
      {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasTypeWithConstructors language allowed free
        (inner ++ sourceBound.map (mapTypeExpr (color.symbols source)))
        pattern type)
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) :
      WellSorted.HasTypeWithConstructors language allowed free
        (inner ++ targetBound)
        (thinning.thickenAmbientBVars inner.length pattern) type := by
    cases typed with
    | bvar lookup =>
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.bvar
            (thinning.lookup_embedIndexAt inner lookup))
    | fvar lookup =>
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.fvar
            (bound := inner ++ targetBound) lookup)
    | constructor allowed membership notBare argumentsTyped =>
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.constructor allowed membership
            notBare
            (WellSorted.ArgumentsHaveTypesWithConstructors.thickenAmbientBVars
              (inner := inner) argumentsTyped thinning))
    | @lambda _ binder body domain codomain bodyTyped =>
        have thickenedBody :=
          WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := domain :: inner) bodyTyped thinning
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.lambda (binder := binder)
            thickenedBody)
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have bodyTyped' : WellSorted.HasTypeWithConstructors language allowed
            free ((List.replicate arity domain ++ inner) ++
              sourceBound.map (mapTypeExpr (color.symbols source)))
            body codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have thickenedBody :=
          WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := List.replicate arity domain ++ inner) bodyTyped' thinning
        have thickenedBody' :
            WellSorted.HasTypeWithConstructors language allowed free
              (List.replicate arity domain ++ (inner ++ targetBound))
              (thinning.thickenAmbientBVars (inner.length + arity) body)
              codomain := by
          simpa [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using thickenedBody
        simpa [CostStaticBinderThinning.thickenAmbientBVars,
          List.append_assoc, List.length_append, List.length_replicate,
          Nat.add_comm] using
            (WellSorted.HasTypeWithConstructors.multiLambda
              (binders := binders) thickenedBody')
    | @subst _ body replacement domain codomain bodyTyped replacementTyped =>
        have thickenedBody :=
          WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := domain :: inner) bodyTyped thinning
        have thickenedReplacement :=
          WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := inner) replacementTyped thinning
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.subst thickenedBody
            thickenedReplacement)
    | collection elementsTyped =>
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.collection
            (WellSorted.ElementsHaveTypeWithConstructors.thickenAmbientBVars
              (inner := inner) elementsTyped thinning))
    | collectionConstructor allowed membership parameterShape elementsTyped =>
        simpa [CostStaticBinderThinning.thickenAmbientBVars] using
          (WellSorted.HasTypeWithConstructors.collectionConstructor allowed
            membership parameterShape
            (WellSorted.ElementsHaveTypeWithConstructors.thickenAmbientBVars
              (inner := inner) elementsTyped thinning))

  theorem WellSorted.ArgumentsHaveTypesWithConstructors.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {language : LanguageDef} {allowed : String → Prop}
      {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypesWithConstructors language allowed
        free (inner ++ sourceBound.map (mapTypeExpr (color.symbols source)))
        arguments parameters)
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) :
      WellSorted.ArgumentsHaveTypesWithConstructors language allowed free
        (inner ++ targetBound)
        (arguments.map (thinning.thickenAmbientBVars inner.length))
        parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          (matchesParameterRepresentation_thickenAmbientBVars thinning
            inner.length _ _ representation)
          parameterType
          (WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := inner) argumentTyped thinning)
          (WellSorted.ArgumentsHaveTypesWithConstructors.thickenAmbientBVars
            (inner := inner) argumentsTyped thinning)

  theorem WellSorted.ElementsHaveTypeWithConstructors.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {language : LanguageDef} {allowed : String → Prop}
      {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveTypeWithConstructors language allowed
        free (inner ++ sourceBound.map (mapTypeExpr (color.symbols source)))
        elements elementType)
      (thinning : CostStaticBinderThinning source color sourceBound
        targetBound) :
      WellSorted.ElementsHaveTypeWithConstructors language allowed free
        (inner ++ targetBound)
        (elements.map (thinning.thickenAmbientBVars inner.length))
        elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (WellSorted.HasTypeWithConstructors.thickenAmbientBVars
            (inner := inner) elementTyped thinning)
          (WellSorted.ElementsHaveTypeWithConstructors.thickenAmbientBVars
            (inner := inner) elementsTyped thinning)
end

/-! ## Constructor support through hereditary restoration

The hereditary executor restores recursively normalized boundary values into
one canonical static skeleton.  The typing layer already proves that the
restoration is well sorted.  The following support layer records the
independent fact that neither reflective substitution nor the finite value
vector can introduce an unadmitted constructor label.
-/

/-- Reflective supported substitution preserves a constructor alphabet when
the skeleton and every possible assignment value use that alphabet.  Quote
boundaries affect only the weakening depth, so the proof is independent of
the selected reflection profile and support function. -/
theorem constructorsWithin_reflectiveSubstituteAt
    {allowed : String → Prop}
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (assignmentSupported : ∀ name,
      ConstructorsWithin allowed (assignment name)) :
    ∀ availableDepth pattern,
      ConstructorsWithin allowed pattern →
        ConstructorsWithin allowed
          (ReflectiveContextSupport.substituteAt profile support assignment
            availableDepth pattern) := by
  intro availableDepth pattern patternSupported
  induction pattern using Pattern.inductionOn generalizing availableDepth with
  | hbvar index =>
      simp [ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      simpa [ReflectiveContextSupport.substituteAt] using
        constructorsWithin_liftBVars (assignmentSupported name) 0
          (availableDepth - (support name).length)
  | happly constructor arguments inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        constructorsWithin_apply]
      exact ⟨patternSupported.1,
        patternSupported.2.map fun argument membership =>
          inductionHypothesis argument membership _
            (patternSupported.2.of_mem membership)⟩
  | hlambda binder body inductionHypothesis =>
      simpa only [ReflectiveContextSupport.substituteAt,
        constructorsWithin_lambda] using
          inductionHypothesis (availableDepth + 1) patternSupported
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [ReflectiveContextSupport.substituteAt,
        constructorsWithin_multiLambda] using
          inductionHypothesis (availableDepth + arity) patternSupported
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [ReflectiveContextSupport.substituteAt,
        constructorsWithin_subst] using
          And.intro
            (bodyInduction (availableDepth + 1) patternSupported.1)
            (replacementInduction availableDepth patternSupported.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [ReflectiveContextSupport.substituteAt,
        constructorsWithin_collection]
      exact patternSupported.map fun element membership =>
        inductionHypothesis element membership availableDepth
          (patternSupported.of_mem membership)

/-- Top-level companion to
`constructorsWithin_reflectiveSubstituteAt`. -/
theorem constructorsWithin_reflectiveSubstitute
    {allowed : String → Prop}
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (assignmentSupported : ∀ name,
      ConstructorsWithin allowed (assignment name))
    (bound : List TypeExpr) {pattern : Pattern}
    (patternSupported : ConstructorsWithin allowed pattern) :
    ConstructorsWithin allowed
      (ReflectiveContextSupport.substitute profile support assignment bound
        pattern) := by
  exact constructorsWithin_reflectiveSubstituteAt profile support assignment
    assignmentSupported bound.length pattern patternSupported

namespace CostStaticRegionNode.CostStaticSourceTerm

/-- The action of a statically typed source frame preserves any target
constructor alphabet that contains the selected static image and every
restoration value.  This is the local modular seam used by hereditary rho;
it does not commit the generic executor to the alphabet of a second Cost
layer. -/
theorem act_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {free assignmentFree targetFree : WellSorted.FreeTypeContext}
    {support assignmentSupport : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : CostStaticSourceTerm source color free support sourceBound
      targetBound sort)
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (assignment : WellSorted.SupportedOpenAssignment
      source.costWholeReflectionProfile source.costWholeLanguage
      assignmentFree targetFree assignmentSupport)
    {allowed : String → Prop}
    (imageAllowed : ∀ label,
      CostStaticColor.hereditaryConstructorImage source color label →
        allowed label)
    (assignmentSupported : ∀ name,
      ConstructorsWithin allowed (assignment.assignment name)) :
    ConstructorsWithin allowed (term.act thinning assignment) := by
  unfold CostStaticSourceTerm.act
  apply constructorsWithin_reflectiveSubstitute
      source.costWholeReflectionProfile assignmentSupport
      assignment.assignment assignmentSupported targetBound
  have mapped := term.supported.mapCostStaticHereditary source color
  have thickened := mapped.thickenAmbientBVars (inner := []) thinning
  exact thickened.constructorsWithin.mono imageAllowed

end CostStaticRegionNode.CostStaticSourceTerm

namespace TypedCostRegionBoundaryTable.Values

/-- Every proof-relevant value in a finite boundary vector stays inside one
constructor alphabet.  The predicate follows the table and value indices, so
duplicate boundary occurrences retain distinct evidence. -/
def ConstructorSupported {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (allowed : String → Prop) :
    {occurrences : List CostRegionOccurrence} →
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences} →
    TypedCostRegionBoundaryTable.Values source color targetFree table → Prop
  | _, _, .nil => True
  | _, _, .cons value values =>
      ConstructorsWithin allowed value.1 ∧ ConstructorSupported allowed values

/-- Successful lookup in an occurrence-indexed value vector returns one of
its constructor-supported values.  The proof follows the dependent table and
value lists in lockstep, so it cannot confuse equal duplicate payloads. -/
theorem constructorSupported_of_resolve
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {allowed : String → Prop}
    (supported : ConstructorSupported allowed values)
    {name : String}
    {resolved : TypedCostRegionBoundaryTable.Values.Resolved source color
      targetFree}
    (resolution : values.resolve table name = some resolved) :
    ConstructorsWithin allowed resolved.2.1 := by
  induction values generalizing name resolved with
  | nil =>
      simp [TypedCostRegionBoundaryTable.Values.resolve] at resolution
  | @cons occurrence occurrences boundary content tail value values
      inductionHypothesis =>
      simp only [TypedCostRegionBoundaryTable.Values.resolve] at resolution
      split at resolution
      · cases Option.some.inj resolution
        exact supported.1
      · exact inductionHypothesis supported.2 resolution

end TypedCostRegionBoundaryTable.Values

namespace CostStaticParameterOccurrence

/-- Evaluating a classified parameter occurrence preserves support of the
current boundary-value vector.  Authored source variables contribute no
constructor; foreign boundaries contribute exactly the resolved value. -/
theorem atom_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {allowed : String → Prop}
    (valuesSupported :
      TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed values)
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root) :
    ConstructorsWithin allowed parameter.atom.key.normal := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      simp [CostStaticParameterOccurrence.atom,
        TypedCostStaticAtom.ofSourceFVar]
  | boundary occurrence notSource resolved resolution =>
      change ConstructorsWithin allowed resolved.2.1
      exact
        TypedCostRegionBoundaryTable.Values.constructorSupported_of_resolve
          valuesSupported resolution

end CostStaticParameterOccurrence

namespace CostStaticParameterInventory

/-- Every semantic representative is backed by a constructor-supported
positional occurrence.  Deduplication may merge equal meanings but cannot
introduce a new value. -/
theorem semanticAtoms_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {allowed : String → Prop}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root)
    (valuesSupported :
      TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed values)
    (atom : TypedCostStaticAtom source color targetFree)
    (membership : atom ∈ inventory.semanticAtoms) :
    ConstructorsWithin allowed atom.key.normal := by
  rw [CostStaticParameterInventory.semanticAtoms, List.mem_dedup] at membership
  rcases List.mem_map.mp membership with ⟨parameter, _, equality⟩
  subst atom
  exact parameter.atom_constructorSupported valuesSupported

end CostStaticParameterInventory

namespace CostStaticAtomEnvironment

/-- Every atom selected by the executable finite semantic quotient remains
constructor-supported when its positional value vector was supported. -/
theorem ofInventory_atomValue_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {allowed : String → Prop}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root)
    (valuesSupported :
      TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed values)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    ConstructorsWithin allowed
      ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot
        ).key.normal := by
  apply inventory.semanticAtoms_constructorSupported valuesSupported
  exact List.get_mem inventory.semanticAtoms slot

/-- A semantic-atom environment whose finite values are supported yields a
supported restoration assignment.  Unknown names remain inert free
variables, matching the fail-closed lookup discipline. -/
theorem restorationAssignment_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {allowed : String → Prop}
    (atomSupported : ∀ slot,
      ConstructorsWithin allowed (environment.atomValue slot).key.normal)
    (name : String) :
    ConstructorsWithin allowed (environment.restorationAssignment name) := by
  unfold CostStaticAtomEnvironment.restorationAssignment
  split
  · exact atomSupported _
  · trivial

/-- The executable environment built from a supported occurrence vector has
a constructor-supported restoration assignment. -/
theorem ofInventory_restorationAssignment_constructorSupported
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {allowed : String → Prop}
    (inventory : CostStaticParameterInventory source color targetFree table
      values root)
    (valuesSupported :
      TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed values)
    (name : String) :
    ConstructorsWithin allowed
      ((CostStaticAtomEnvironment.ofInventory inventory
        ).restorationAssignment name) :=
  restorationAssignment_constructorSupported _
    (ofInventory_atomValue_constructorSupported inventory valuesSupported) name

end CostStaticAtomEnvironment

/-- Local constructor law for a static normalization kernel.  It is
deliberately parameterized by the alphabet: the generic tree traversal does
not decide which constructors a client wants to preserve. -/
def CostStaticRegionNormalizerPreservesConstructorSupport
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    (allowed : String → Prop) : Prop :=
  ∀ {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable),
    ConstructorsWithin allowed node.term.1 →
    TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed values →
    ConstructorsWithin allowed (normalizeStatic node values).1

mutual
  /-- Every maximal foreign boundary emitted by a static plan is an actual
  constructor-supported subterm of that plan's input.  This is the structural
  bridge from support of a compact parent to support of each recursive child;
  occurrence positions and duplicate entries remain explicit in the table. -/
  theorem CostStaticRegionPlan.boundaryContents_constructorSupported
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      {allowed : String → Prop}
      (supported : ConstructorsWithin allowed pattern) :
      ∀ boundary, boundary ∈ plan.boundaryTable.entries →
        ConstructorsWithin allowed boundary.boundary.content := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        intro boundary membership
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary source color targetFree)) at membership
        simp at membership
    | fvar lookup =>
        intro boundary membership
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary source color targetFree)) at membership
        simp at membership
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        intro boundary membership
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        simpa only [certified.content_eq] using supported
    | application constructor rendered current preimage notBare children =>
        exact children.boundaryContents_constructorSupported supported.2
    | lambda bodyPlan =>
        exact bodyPlan.boundaryContents_constructorSupported supported
    | multiLambda bodyPlan =>
        exact bodyPlan.boundaryContents_constructorSupported supported
    | collection choice selected children =>
        exact children.boundaryContents_constructorSupported supported
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        intro boundary membership
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        simpa only [certified.content_eq] using supported

  /-- Argument-spine companion to
  `CostStaticRegionPlan.boundaryContents_constructorSupported`. -/
  theorem CostStaticArgumentPlan.boundaryContents_constructorSupported
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      {allowed : String → Prop}
      (supported : ConstructorListWithin allowed arguments) :
      ∀ boundary, boundary ∈ plan.boundaryTable.entries →
        ConstructorsWithin allowed boundary.boundary.content := by
    cases plan with
    | nil =>
        intro boundary membership
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary source color targetFree)) at membership
        simp at membership
    | cons representation parameterType head tail =>
        intro boundary membership
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact head.boundaryContents_constructorSupported supported.1
            boundary headMembership
        · exact tail.boundaryContents_constructorSupported supported.2
            boundary tailMembership

  /-- Collection-spine companion to
  `CostStaticRegionPlan.boundaryContents_constructorSupported`. -/
  theorem CostStaticElementPlan.boundaryContents_constructorSupported
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      {allowed : String → Prop}
      (supported : ConstructorListWithin allowed elements) :
      ∀ boundary, boundary ∈ plan.boundaryTable.entries →
        ConstructorsWithin allowed boundary.boundary.content := by
    cases plan with
    | nil =>
        intro boundary membership
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary source color targetFree)) at membership
        simp at membership
    | cons head tail =>
        intro boundary membership
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact head.boundaryContents_constructorSupported supported.1
            boundary headMembership
        · exact tail.boundaryContents_constructorSupported supported.2
            boundary tailMembership
end

/-! ## Constructor support through the complete alternating tree

The local static-kernel law above composes through the proof-relevant region
tree.  The boundary case is deliberately indexed by the exact finite table:
each duplicate occurrence receives its own recursive support proof before the
value vector is passed back to the enclosing static node.
-/

mutual
  /-- A constructor-preserving static kernel induces constructor preservation
  for every complete alternating region tree. -/
  theorem CostRegionTree.normalize_constructorSupported
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type)
      (normalizeStatic : CostStaticRegionNormalizer source)
      {allowed : String → Prop}
      (localLaw :
        CostStaticRegionNormalizerPreservesConstructorSupport source
          normalizeStatic allowed)
      (supported : ConstructorsWithin allowed pattern) :
      ConstructorsWithin allowed
        (tree.normalize (normalizeStatic := normalizeStatic)).pattern :=
    match tree with
    | .bvar lookup => by
        simp [CostRegionTree.normalize]
    | .fvar lookup => by
        simp [CostRegionTree.normalize]
    | .static node children => by
        simpa only [CostRegionTree.normalize] using
          localLaw node _ supported
            (children.normalizeValues_constructorSupported normalizeStatic
              localLaw fun boundary membership =>
                node.plan.boundaryContents_constructorSupported supported
                  boundary membership)
    | .neutralApplicationOrdinary membership notBareCollection constructor
        materializes neutral ordinary children => by
        simpa only [CostRegionTree.normalize, constructorsWithin_apply] using
          And.intro supported.1
            (children.normalize_constructorSupported normalizeStatic localLaw
              supported.2)
    | .neutralApplicationQuote membership notBareCollection constructor
        materializes neutral quoted children => by
        simpa only [CostRegionTree.normalize, constructorsWithin_apply] using
          And.intro supported.1
            (children.normalize_constructorSupported normalizeStatic localLaw
              supported.2)
    | .lambda bodyTree => by
        simpa only [CostRegionTree.normalize, constructorsWithin_lambda] using
          bodyTree.normalize_constructorSupported normalizeStatic localLaw
            supported
    | .multiLambda bodyTree => by
        simpa only [CostRegionTree.normalize,
          constructorsWithin_multiLambda] using
            bodyTree.normalize_constructorSupported normalizeStatic localLaw
              supported
    | .subst bodyTree replacementTree => by
        simpa only [CostRegionTree.normalize, constructorsWithin_subst] using
          And.intro
            (bodyTree.normalize_constructorSupported normalizeStatic localLaw
              supported.1)
            (replacementTree.normalize_constructorSupported normalizeStatic
              localLaw supported.2)
    | .collection children => by
        simpa only [CostRegionTree.normalize,
          constructorsWithin_collection] using
            children.normalize_constructorSupported normalizeStatic localLaw
              supported
  termination_by tree.weight
  decreasing_by
    all_goals simp [CostRegionTree.weight]
    all_goals omega

  /-- Constructor-support companion for an authored argument spine. -/
  theorem CostRegionArgumentTrees.normalize_constructorSupported
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters)
      (normalizeStatic : CostStaticRegionNormalizer source)
      {allowed : String → Prop}
      (localLaw :
        CostStaticRegionNormalizerPreservesConstructorSupport source
          normalizeStatic allowed)
      (supported : ConstructorListWithin allowed arguments) :
      ConstructorListWithin allowed
        (trees.normalize (normalizeStatic := normalizeStatic)).patterns :=
    match trees with
    | .nil => by
        simp [CostRegionArgumentTrees.normalize]
    | .cons representation parameterType head tail => by
        simpa only [CostRegionArgumentTrees.normalize,
          constructorListWithin_cons] using
            And.intro
              (head.normalize_constructorSupported normalizeStatic localLaw
                supported.1)
              (tail.normalize_constructorSupported normalizeStatic localLaw
                supported.2)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionArgumentTrees.weight]
    all_goals omega

  /-- Constructor-support companion for a homogeneous collection spine. -/
  theorem CostRegionElementTrees.normalize_constructorSupported
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer
        elements elementType)
      (normalizeStatic : CostStaticRegionNormalizer source)
      {allowed : String → Prop}
      (localLaw :
        CostStaticRegionNormalizerPreservesConstructorSupport source
          normalizeStatic allowed)
      (supported : ConstructorListWithin allowed elements) :
      ConstructorListWithin allowed
        (trees.normalize (normalizeStatic := normalizeStatic)).patterns :=
    match trees with
    | .nil _ _ _ => by
        simp [CostRegionElementTrees.normalize]
    | .cons head tail => by
        simpa only [CostRegionElementTrees.normalize,
          constructorListWithin_cons] using
            And.intro
              (head.normalize_constructorSupported normalizeStatic localLaw
                supported.1)
              (tail.normalize_constructorSupported normalizeStatic localLaw
                supported.2)
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionElementTrees.weight]
    all_goals omega

  /-- Normalizing an exact boundary forest yields a constructor-supported
  value at every occurrence whenever each authored boundary payload is
  supported. -/
  theorem CostRegionBoundaryTrees.normalizeValues_constructorSupported
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table)
      (normalizeStatic : CostStaticRegionNormalizer source)
      {allowed : String → Prop}
      (localLaw :
        CostStaticRegionNormalizerPreservesConstructorSupport source
          normalizeStatic allowed)
      (entriesSupported : ∀ boundary, boundary ∈ table.entries →
        ConstructorsWithin allowed boundary.boundary.content) :
      TypedCostRegionBoundaryTable.Values.ConstructorSupported allowed
        (trees.normalizeValues (normalizeStatic := normalizeStatic)) :=
    match trees with
    | .nil => by
        simp [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.ConstructorSupported]
    | @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences boundary
        content tail head children => by
        simp only [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.ConstructorSupported]
        constructor
        · apply head.normalize_constructorSupported normalizeStatic localLaw
          apply entriesSupported boundary
          simp [TypedCostRegionBoundaryTable.entries]
        · apply children.normalizeValues_constructorSupported normalizeStatic
            localLaw
          intro child membership
          apply entriesSupported child
          simp only [TypedCostRegionBoundaryTable.entries, List.mem_cons]
          exact Or.inr membership
  termination_by trees.weight
  decreasing_by
    all_goals simp [CostRegionBoundaryTrees.weight]
    all_goals omega
end

/-- Constructor support and the intrinsic normalized typing reconstruct the
proof-relevant typed-constructor judgment for a complete region tree.  Bare
collection declarations remain an explicit property of the chosen alphabet,
because their labels are intentionally absent from raw collection syntax. -/
theorem CostRegionTree.normalize_hasTypeWithConstructors
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (normalizeStatic : CostStaticRegionNormalizer source)
    {allowed : String → Prop}
    (localLaw : CostStaticRegionNormalizerPreservesConstructorSupport source
      normalizeStatic allowed)
    (typed : WellSorted.HasTypeWithConstructors source.costWholeLanguage
      allowed targetFree (available ++ outer) pattern type)
    (bareAllowed : ∀ rule ∈ source.costWholeLanguage.terms,
      WellSorted.UsesBareCollection rule → allowed rule.label) :
    WellSorted.HasTypeWithConstructors source.costWholeLanguage allowed
      targetFree (available ++ outer)
      (tree.normalize (normalizeStatic := normalizeStatic)).pattern type := by
  apply (tree.normalize (normalizeStatic := normalizeStatic)).typed.withConstructors
  · exact tree.normalize_constructorSupported normalizeStatic localLaw
      typed.constructorsWithin
  · exact bareAllowed

/-- Whole-executor constructor preservation follows from a local static-frame
law and the declaration-level bare-collection condition.  The theorem is
generic in the constructor alphabet and static kernel; repeated Cost chooses
its next wrapped alphabet only at the eventual object instance. -/
theorem CIGSLT.costNormalizeOpenWithStatic_preservesConstructorTyping
    (source : CIGSLT) (normalizeStatic : CostStaticRegionNormalizer source)
    {allowed : String → Prop}
    (localLaw : CostStaticRegionNormalizerPreservesConstructorSupport source
      normalizeStatic allowed)
    (bareAllowed : ∀ rule ∈ source.costWholeLanguage.terms,
      WellSorted.UsesBareCollection rule → allowed rule.label)
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort)
    (typed : WellSorted.HasTypeWithConstructors source.costWholeLanguage
      allowed targetFree targetBound term.1 (.base targetSort.1)) :
    WellSorted.HasTypeWithConstructors source.costWholeLanguage allowed
      targetFree targetBound
      (source.costNormalizeOpenWithStatic normalizeStatic term).1
      (.base targetSort.1) := by
  rw [source.costNormalizeOpenWithStatic_pattern]
  simpa only [List.append_nil] using
    (CostOpenElaboration.compile source term).tree
      |>.normalize_hasTypeWithConstructors normalizeStatic localLaw
        (by simpa only [List.append_nil] using typed) bareAllowed

end Mettapedia.GSLT.LanguageDef
