import Mettapedia.GSLT.LanguageDef.CostOneCategory

/-!
# Reindexing proof-relevant Cost elaborations

The compact Cost functor maps checked syntax.  Its proof-relevant lift must
also map the retained declaration, colour, occurrence, and decomposition data
without erasing and recompiling it.  This file constructs that action from
the declaration map carried by an admissible Cost₁ arrow.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Prefix decoding is natural for the matching prefix-preserving name map. -/
theorem decodeTaggedPayload_mapTaggedName (tag : String)
    (mapPayload : String → String) (name : String) :
    decodeTaggedPayload tag (mapTaggedName tag mapPayload name) =
      (decodeTaggedPayload tag name).map mapPayload := by
  unfold mapTaggedName decodeTaggedPayload
  split
  next suffix decoded =>
    rw [decoded]
    simp [String.toList_append]
  next rejected =>
    rw [rejected]
    rfl

namespace CIGSLT.Morphism

/-- The generated Cost structural map exposes exactly the reserved Cost
symbol action. -/
@[simp]
theorem costWholeStructural_symbols {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.costWholeStructural.symbols =
      costPresentationSymbols
        morphism.underlying.structural.structural.symbols :=
  rfl

/-- Map one intrinsic constructor of the generated Cost signature.  The
three generated summands are preserved literally; only the attached authored
constructor is transported. -/
def mapDeclaredCostConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.DeclaredCostConstructor → target.DeclaredCostConstructor
  | ⟨.base constructor, _⟩ =>
      ⟨.base
        (morphism.underlying.structural.structural.mapConstructor constructor),
        True.intro⟩
  | ⟨.wrapped constructor, membership⟩ =>
      ⟨.wrapped
        (morphism.underlying.structural.structural.mapConstructor constructor),
        morphism.mapsWrappedConstructors constructor membership⟩
  | ⟨.apparatus kind, _⟩ => ⟨.apparatus kind, True.intro⟩

/-- Materialization commutes with intrinsic generated-constructor
reindexing. -/
theorem materialize_mapDeclaredCostConstructor
    {source target : CIGSLT} (morphism : source.Morphism target)
    (constructor : source.DeclaredCostConstructor) :
    target.materializeDeclaredCostConstructor
        (morphism.mapDeclaredCostConstructor constructor) =
      mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (source.materializeDeclaredCostConstructor constructor) := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base constructor =>
      change costBaseConstructor target.cut
          (mapGrammarRule
            morphism.underlying.structural.structural.symbols constructor.1) = _
      exact (morphism.mapGrammarRule_costBaseConstructor constructor.1).symm
  | wrapped constructor =>
      change costWrappedConstructor
          (mapGrammarRule
            morphism.underlying.structural.structural.symbols constructor.1) = _
      exact (morphism.mapGrammarRule_costWrappedConstructor constructor.1).symm
  | apparatus kind =>
      cases kind <;>
        simp [mapDeclaredCostConstructor,
          CIGSLT.materializeDeclaredCostConstructor,
          CostApparatusConstructor.grammarRule, costSignatureUnitConstructor,
          costSignatureProductConstructor, costSignedConstructor,
          costTokenStackEmptyConstructor, costTokenStackConsConstructor,
          costFundingConstructor, costContactConstructor,
          costSignatureUnitConstructorName,
          costSignatureProductConstructorName, costSignedConstructorName,
          costTokenStackEmptyConstructorName,
          costTokenStackConsConstructorName, costFundingConstructorName,
          costContactConstructorName, costSignatureSortName,
          costTokenStackSortName, mapGrammarRule, mapTermParam, mapTypeExpr,
          morphism.mapsInteractingSortName]

/-- Wire rendering commutes with intrinsic generated-constructor
reindexing. -/
@[simp]
theorem render_mapDeclaredCostConstructor
    {source target : CIGSLT} (morphism : source.Morphism target)
    (constructor : source.DeclaredCostConstructor) :
    target.renderDeclaredCostConstructor
        (morphism.mapDeclaredCostConstructor constructor) =
      (costPresentationSymbols
        morphism.underlying.structural.structural.symbols).constructor
        (source.renderDeclaredCostConstructor constructor) := by
  rw [← target.materializeDeclaredCostConstructor_label,
    morphism.materialize_mapDeclaredCostConstructor,
    ← source.materializeDeclaredCostConstructor_label]
  rfl

/-- Reindexing preserves the semantic role of every intrinsic generated
constructor.  In the base summand this uses reflection of both selected
interaction principals; without those laws a static node could become an
interaction boundary after transport. -/
theorem declaredCostConstructorRole_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (constructor : source.DeclaredCostConstructor) :
    target.declaredCostConstructorRole
        (morphism.mapDeclaredCostConstructor constructor) =
      source.declaredCostConstructorRole constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base constructor =>
      simp only [mapDeclaredCostConstructor,
        CIGSLT.declaredCostConstructorRole]
      by_cases sourcePrincipal :
          constructor = source.cut.program.constructor ∨
            constructor = source.cut.environment.constructor
      · have targetPrincipal :
            morphism.underlying.structural.structural.mapConstructor constructor =
                target.cut.program.constructor ∨
              morphism.underlying.structural.structural.mapConstructor constructor =
                target.cut.environment.constructor := by
          rcases sourcePrincipal with sourceProgram | sourceEnvironment
          · subst constructor
            exact Or.inl morphism.mapsProgramConstructor
          · subst constructor
            exact Or.inr morphism.mapsEnvironmentConstructor
        rw [if_pos targetPrincipal, if_pos sourcePrincipal]
      · have targetNotPrincipal :
            ¬ (morphism.underlying.structural.structural.mapConstructor constructor =
                  target.cut.program.constructor ∨
                morphism.underlying.structural.structural.mapConstructor constructor =
                  target.cut.environment.constructor) := by
          intro targetPrincipal
          apply sourcePrincipal
          rcases targetPrincipal with targetProgram | targetEnvironment
          · exact Or.inl (Subtype.ext
              (morphism.reflectsProgramConstructor constructor.1
                (congrArg Subtype.val targetProgram)))
          · exact Or.inr (Subtype.ext
              (morphism.reflectsEnvironmentConstructor constructor.1
                (congrArg Subtype.val targetEnvironment)))
        rw [if_neg targetNotPrincipal, if_neg sourcePrincipal]
  | wrapped constructor =>
      rfl
  | apparatus kind =>
      rfl

/-- Intrinsic generated-constructor reindexing sends identity to identity. -/
@[simp]
theorem mapDeclaredCostConstructor_id (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    (CIGSLT.Morphism.id source).mapDeclaredCostConstructor constructor =
      constructor := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base constructor =>
      apply Subtype.ext
      exact congrArg CostConstructor.base
        (StructuralMorphism.mapConstructor_id _ constructor)
  | wrapped constructor =>
      apply Subtype.ext
      exact congrArg CostConstructor.wrapped
        (StructuralMorphism.mapConstructor_id _ constructor)
  | apparatus kind => rfl

/-- Intrinsic generated-constructor reindexing respects composition. -/
theorem mapDeclaredCostConstructor_comp
    {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third)
    (constructor : first.DeclaredCostConstructor) :
    (CIGSLT.Morphism.comp left right).mapDeclaredCostConstructor constructor =
      right.mapDeclaredCostConstructor
        (left.mapDeclaredCostConstructor constructor) := by
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base constructor =>
      apply Subtype.ext
      exact congrArg CostConstructor.base
        (StructuralMorphism.mapConstructor_comp
          left.underlying.structural.structural
          right.underlying.structural.structural constructor)
  | wrapped constructor =>
      apply Subtype.ext
      exact congrArg CostConstructor.wrapped
        (StructuralMorphism.mapConstructor_comp
          left.underlying.structural.structural
          right.underlying.structural.structural constructor)
  | apparatus kind => rfl

/-- Static-fibre decoding commutes with the generated Cost symbol action.
The wrapped case uses both preservation and reflection of the interacting
sort; reflection is what prevents a previously foreign base sort from
entering the wrapped fibre after transport. -/
theorem decodeCostStaticTypeExpr_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (type : TypeExpr) :
    decodeCostStaticTypeExpr target color
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols)
          type) =
      (decodeCostStaticTypeExpr source color type).map
        (mapTypeExpr morphism.underlying.structural.structural.symbols) := by
  let symbols := morphism.underlying.structural.structural.symbols
  induction type with
  | base sort =>
      cases color with
      | base =>
          have decoded :=
            decodeTaggedPayload_mapTaggedName costBaseSortTag symbols.sort sort
          have mappedDecoded := congrArg (Option.map TypeExpr.base) decoded
          simpa [decodeCostStaticTypeExpr, decodeCostBaseSortName,
            mapTypeExpr, costPresentationSymbols, Option.map_map,
            Function.comp_def, symbols] using mappedDecoded
      | wrapped =>
          have decodedBase :
              decodeCostBaseSortName
                  ((costPresentationSymbols symbols).sort sort) =
                (decodeCostBaseSortName sort).map symbols.sort := by
            simpa [decodeCostBaseSortName, costPresentationSymbols] using
              decodeTaggedPayload_mapTaggedName costBaseSortTag symbols.sort sort
          by_cases wrapped : sort = costWrappedSortName
          · subst sort
            simp [decodeCostStaticTypeExpr, mapTypeExpr,
              morphism.mapsInteractingSortName]
          · have mappedNotWrapped :
                (costPresentationSymbols symbols).sort sort ≠
                  costWrappedSortName := by
              intro equality
              exact wrapped
                ((costPresentationSymbols_sort_eq_wrapped_iff symbols sort).mp
                  equality)
            cases decoded : decodeCostBaseSortName sort with
            | none =>
                simp [decodeCostStaticTypeExpr, mapTypeExpr, wrapped,
                  mappedNotWrapped, decoded, decodedBase, symbols]
            | some sourceSort =>
                have targetDecoded :
                    decodeCostBaseSortName
                        ((costPresentationSymbols symbols).sort sort) =
                      some (symbols.sort sourceSort) := by
                  simpa [decoded] using decodedBase
                by_cases interacting :
                    sourceSort =
                      source.theory.presentation.interactingSort.1.name
                · subst sourceSort
                  simp [decodeCostStaticTypeExpr, mapTypeExpr, wrapped,
                    mappedNotWrapped, decoded, targetDecoded,
                    morphism.mapsInteractingSortName, symbols]
                · have targetNotInteracting :
                      symbols.sort sourceSort ≠
                        target.theory.presentation.interactingSort.1.name := by
                    intro equality
                    exact interacting
                      (morphism.reflectsInteractingSort sourceSort equality)
                  simp [decodeCostStaticTypeExpr, mapTypeExpr, wrapped,
                    mappedNotWrapped, decoded, targetDecoded, interacting,
                    targetNotInteracting, symbols]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp only [decodeCostStaticTypeExpr, mapTypeExpr, domainHypothesis,
        codomainHypothesis]
      cases decodeCostStaticTypeExpr source color domain <;>
        cases decodeCostStaticTypeExpr source color codomain <;> rfl
  | multiBinder body inductionHypothesis =>
      simp only [decodeCostStaticTypeExpr, mapTypeExpr, inductionHypothesis]
      cases decodeCostStaticTypeExpr source color body <;> rfl
  | collection collectionType element inductionHypothesis =>
      simp only [decodeCostStaticTypeExpr, mapTypeExpr, inductionHypothesis]
      cases decodeCostStaticTypeExpr source color element <;> rfl

/-- Static type formation is natural under a continued morphism. -/
theorem mapTypeExpr_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (type : TypeExpr) :
    mapTypeExpr
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (mapTypeExpr (color.symbols source) type) =
      mapTypeExpr (color.symbols target)
        (mapTypeExpr morphism.underlying.structural.structural.symbols type) := by
  cases color with
  | base =>
      simp [CostStaticColor.symbols, mapTypeExpr_costBaseStaticSymbols]
  | wrapped =>
      simpa [CostStaticColor.symbols, mapTypeExpr_costWrappedStaticSymbols] using
        mapTypeExpr_costWrappedTypeExpr
          morphism.underlying.structural.structural.symbols
          source.theory.presentation.interactingSort.1.name
          target.theory.presentation.interactingSort.1.name
        morphism.mapsInteractingSortName morphism.reflectsInteractingSort type

/-- Mapping an authored sort and then placing it in a static Cost fibre is
the same as first placing it in that fibre and mapping the generated sort. -/
@[simp]
theorem mapLangSort_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor)
    (sort : LangSort source.theory.presentation.presentation.language) :
    WellSorted.mapLangSort morphism.costWholeStructural
        (color.mapLangSort source sort) =
      color.mapLangSort target
        (WellSorted.mapLangSort
          morphism.underlying.structural.structural sort) := by
  apply Subtype.ext
  have naturality := morphism.mapTypeExpr_costStatic_natural color
    (.base sort.1)
  exact TypeExpr.base.inj naturality

/-- Static parameter formation is natural under a continued morphism. -/
@[simp]
theorem mapTermParam_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (parameter : TermParam) :
    mapTermParam
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (mapTermParam (color.symbols source) parameter) =
      mapTermParam (color.symbols target)
        (mapTermParam
          morphism.underlying.structural.structural.symbols parameter) := by
  cases parameter <;>
    simp [mapTermParam, morphism.mapTypeExpr_costStatic_natural]

/-- Static pattern formation is natural under a continued morphism. -/
@[simp]
theorem mapPattern_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (pattern : Pattern) :
    mapPattern
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (mapPattern (color.symbols source) pattern) =
      mapPattern (color.symbols target)
        (mapPattern morphism.underlying.structural.structural.symbols pattern) := by
  cases color with
  | base =>
      exact mapPattern_costBaseStatic_natural
        morphism.underlying.structural.structural.symbols pattern
  | wrapped =>
      exact mapPattern_costWrappedStatic_natural
        morphism.underlying.structural.structural.symbols source.theory
          target.theory pattern

/-- Constructor names in either static colour commute with generated Cost
translation. -/
@[simp]
theorem mapConstructor_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (constructor : String) :
    (costPresentationSymbols
        morphism.underlying.structural.structural.symbols).constructor
        ((color.symbols source).constructor constructor) =
      (color.symbols target).constructor
        (morphism.underlying.structural.structural.symbols.constructor
          constructor) := by
  cases color <;>
    simp [CostStaticColor.symbols, costBaseStaticSymbols,
      costWrappedStaticSymbols]

/-- Static one-hole contexts are natural under the same symbol action. -/
theorem mapOneHoleContext_costStatic_natural
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) (context : OneHoleContext) :
    mapOneHoleContext
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (mapOneHoleContext (color.symbols source) context) =
      mapOneHoleContext (color.symbols target)
        (mapOneHoleContext
          morphism.underlying.structural.structural.symbols context) := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      have patternNaturality :
          (mapPattern
              (costPresentationSymbols
                morphism.underlying.structural.structural.symbols) ∘
            mapPattern (color.symbols source)) =
          (mapPattern (color.symbols target) ∘
            mapPattern
              morphism.underlying.structural.structural.symbols) := by
        funext pattern
        exact morphism.mapPattern_costStatic_natural color pattern
      simp only [mapOneHoleContext, List.map_map, inductionHypothesis,
        morphism.mapConstructor_costStatic_natural]
      rw [patternNaturality]
  | lambda binder inner inductionHypothesis =>
      simp [mapOneHoleContext, inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp [mapOneHoleContext, inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [mapOneHoleContext, inductionHypothesis,
        morphism.mapPattern_costStatic_natural]
  | substReplacement body inner inductionHypothesis =>
      simp [mapOneHoleContext, inductionHypothesis,
        morphism.mapPattern_costStatic_natural]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [mapOneHoleContext, List.map_map, inductionHypothesis,
        morphism.mapPattern_costStatic_natural]

end CIGSLT.Morphism

namespace CostStaticConstructorPreimage

/-- Reindex the exact authored preimage retained by one static generated
constructor.  No target-side search is performed. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    {color : CostStaticColor}
    {constructor : source.DeclaredCostConstructor}
    (preimage : CostStaticConstructorPreimage source color constructor) :
    CostStaticConstructorPreimage target color
      (morphism.mapDeclaredCostConstructor constructor) where
  sourceConstructor :=
    morphism.underlying.structural.structural.mapConstructor
      preimage.sourceConstructor
  wrapped := morphism.mapsWrappedConstructors _ preimage.wrapped
  labelMap := by
    rw [morphism.materialize_mapDeclaredCostConstructor]
    change (costPresentationSymbols
        morphism.underlying.structural.structural.symbols).constructor
        (source.materializeDeclaredCostConstructor constructor).label = _
    rw [preimage.labelMap,
      morphism.mapConstructor_costStatic_natural]
    rfl
  categoryMap := by
    have naturality := morphism.mapTypeExpr_costStatic_natural color
      (.base preimage.sourceConstructor.1.category)
    have categoryNaturality := TypeExpr.base.inj naturality
    calc
      (target.materializeDeclaredCostConstructor
          (morphism.mapDeclaredCostConstructor constructor)).category =
          (mapGrammarRule
            (costPresentationSymbols
              morphism.underlying.structural.structural.symbols)
            (source.materializeDeclaredCostConstructor constructor)).category :=
        congrArg GrammarRule.category
          (morphism.materialize_mapDeclaredCostConstructor constructor)
      _ = (costPresentationSymbols
            morphism.underlying.structural.structural.symbols).sort
          (source.materializeDeclaredCostConstructor constructor).category := rfl
      _ = (costPresentationSymbols
            morphism.underlying.structural.structural.symbols).sort
          ((color.symbols source).sort
            preimage.sourceConstructor.1.category) :=
        congrArg
          ((costPresentationSymbols
            morphism.underlying.structural.structural.symbols).sort)
          preimage.categoryMap
      _ = (color.symbols target).sort
          (morphism.underlying.structural.structural.symbols.sort
            preimage.sourceConstructor.1.category) := categoryNaturality
  parametersMap := by
    let sourceSymbols :=
      morphism.underlying.structural.structural.symbols
    let generatedSymbols := costPresentationSymbols sourceSymbols
    calc
      (target.materializeDeclaredCostConstructor
          (morphism.mapDeclaredCostConstructor constructor)).params =
          (mapGrammarRule generatedSymbols
            (source.materializeDeclaredCostConstructor constructor)).params :=
        congrArg GrammarRule.params
          (morphism.materialize_mapDeclaredCostConstructor constructor)
      _ = (source.materializeDeclaredCostConstructor constructor).params.map
          (mapTermParam generatedSymbols) := rfl
      _ = (preimage.sourceConstructor.1.params.map
            (mapTermParam (color.symbols source))).map
          (mapTermParam generatedSymbols) :=
        congrArg (List.map (mapTermParam generatedSymbols))
          preimage.parametersMap
      _ = (preimage.sourceConstructor.1.params.map
            (mapTermParam sourceSymbols)).map
          (mapTermParam (color.symbols target)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro parameter _membership
        exact morphism.mapTermParam_costStatic_natural color parameter
      _ = (morphism.underlying.structural.structural.mapConstructor
            preimage.sourceConstructor).1.params.map
          (mapTermParam (color.symbols target)) := rfl

end CostStaticConstructorPreimage

namespace CostRegionOccurrence

/-- Two occurrence witnesses are equal exactly when both their traversal
context and retained content are equal. -/
@[ext]
theorem ext {left right : CostRegionOccurrence}
    (context : left.context = right.context)
    (content : left.content = right.content) : left = right := by
  cases left
  cases right
  simp_all

/-- Map one exact foreign-region occurrence without quotienting equal
contents or forgetting its traversal context. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (occurrence : CostRegionOccurrence) : CostRegionOccurrence where
  context := CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
    occurrence.context
  content := mapPattern morphism.costWholeStructural.symbols occurrence.content

@[simp]
theorem map_context {source target : CIGSLT}
    (morphism : source.Morphism target) (occurrence : CostRegionOccurrence) :
    (occurrence.map morphism).context =
      CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
        occurrence.context :=
  rfl

@[simp]
theorem map_content {source target : CIGSLT}
    (morphism : source.Morphism target) (occurrence : CostRegionOccurrence) :
    (occurrence.map morphism).content =
      mapPattern morphism.costWholeStructural.symbols occurrence.content :=
  rfl

/-- Occurrence mapping is literally inert for the identity symbol action. -/
@[simp]
theorem map_id (source : CIGSLT) (occurrence : CostRegionOccurrence) :
    occurrence.map (CIGSLT.Morphism.id source) = occurrence := by
  apply CostRegionOccurrence.ext
  · change CIGSLT.mapOneHoleContext
        (costPresentationSymbols PresentationSymbols.id) occurrence.context =
      occurrence.context
    rw [costPresentationSymbols_id, CIGSLT.mapOneHoleContext_id]
  · change mapPattern (costPresentationSymbols PresentationSymbols.id)
        occurrence.content = occurrence.content
    rw [costPresentationSymbols_id, mapPattern_id]

/-- Occurrence mapping preserves chronological/contextual identity under
composition. -/
theorem map_comp {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third)
    (occurrence : CostRegionOccurrence) :
    occurrence.map (CIGSLT.Morphism.comp left right) =
      (occurrence.map left).map right := by
  apply CostRegionOccurrence.ext
  · change CIGSLT.mapOneHoleContext
        (costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols))
          occurrence.context =
        CIGSLT.mapOneHoleContext
          (costPresentationSymbols
            right.underlying.structural.structural.symbols)
          (CIGSLT.mapOneHoleContext
            (costPresentationSymbols
              left.underlying.structural.structural.symbols)
            occurrence.context)
    rw [costPresentationSymbols_comp, CIGSLT.mapOneHoleContext_comp]
  · change mapPattern
        (costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols))
          occurrence.content =
        mapPattern
          (costPresentationSymbols
            right.underlying.structural.structural.symbols)
          (mapPattern
            (costPresentationSymbols
              left.underlying.structural.structural.symbols)
            occurrence.content)
    rw [costPresentationSymbols_comp, mapPattern_comp]

/-- Computational witness that occurrence reindexing distributes over list
append.  Keeping this proof reducible lets dependent boundary tables transport
without an opaque equality cast. -/
def map_append {source target : CIGSLT}
    (morphism : source.Morphism target) :
    (left right : List CostRegionOccurrence) →
      (left ++ right).map (CostRegionOccurrence.map morphism) =
        left.map (CostRegionOccurrence.map morphism) ++
          right.map (CostRegionOccurrence.map morphism)
  | [], _ => rfl
  | occurrence :: occurrences, right =>
      congrArg (List.cons (occurrence.map morphism))
        (map_append morphism occurrences right)

end CostRegionOccurrence

namespace CostRegionBoundary

/-- Raw boundary records are determined by their five serializable fields. -/
@[ext]
theorem ext {left right : CostRegionBoundary}
    (type : left.type = right.type)
    (support : left.support = right.support)
    (targetType : left.targetType = right.targetType)
    (targetSupport : left.targetSupport = right.targetSupport)
    (content : left.content = right.content) : left = right := by
  cases left
  cases right
  simp_all

/-- Reindex the stable source/target fibre of one opaque boundary.  Source
types move under the original presentation map; restored types and content
move under the generated Cost presentation map. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (boundary : CostRegionBoundary) : CostRegionBoundary where
  type := mapTypeExpr
    morphism.underlying.structural.structural.symbols boundary.type
  support := boundary.support.map
    (mapTypeExpr morphism.underlying.structural.structural.symbols)
  targetType := mapTypeExpr morphism.costWholeStructural.symbols
    boundary.targetType
  targetSupport := boundary.targetSupport.map
    (mapTypeExpr morphism.costWholeStructural.symbols)
  content := mapPattern morphism.costWholeStructural.symbols boundary.content

@[simp]
theorem map_type {source target : CIGSLT}
    (morphism : source.Morphism target) (boundary : CostRegionBoundary) :
    (boundary.map morphism).type =
      mapTypeExpr morphism.underlying.structural.structural.symbols
        boundary.type :=
  rfl

@[simp]
theorem map_support {source target : CIGSLT}
    (morphism : source.Morphism target) (boundary : CostRegionBoundary) :
    (boundary.map morphism).support = boundary.support.map
      (mapTypeExpr morphism.underlying.structural.structural.symbols) :=
  rfl

@[simp]
theorem map_targetType {source target : CIGSLT}
    (morphism : source.Morphism target) (boundary : CostRegionBoundary) :
    (boundary.map morphism).targetType =
      mapTypeExpr morphism.costWholeStructural.symbols boundary.targetType :=
  rfl

@[simp]
theorem map_targetSupport {source target : CIGSLT}
    (morphism : source.Morphism target) (boundary : CostRegionBoundary) :
    (boundary.map morphism).targetSupport = boundary.targetSupport.map
      (mapTypeExpr morphism.costWholeStructural.symbols) :=
  rfl

@[simp]
theorem map_content {source target : CIGSLT}
    (morphism : source.Morphism target) (boundary : CostRegionBoundary) :
    (boundary.map morphism).content =
      mapPattern morphism.costWholeStructural.symbols boundary.content :=
  rfl

/-- Boundary reindexing is inert under the identity continued morphism. -/
@[simp]
theorem map_id (source : CIGSLT) (boundary : CostRegionBoundary) :
    boundary.map (CIGSLT.Morphism.id source) = boundary := by
  apply CostRegionBoundary.ext
  · change mapTypeExpr PresentationSymbols.id boundary.type = boundary.type
    exact mapTypeExpr_id boundary.type
  · change boundary.support.map (mapTypeExpr PresentationSymbols.id) =
      boundary.support
    calc
      boundary.support.map (mapTypeExpr PresentationSymbols.id) =
          boundary.support.map _root_.id :=
        List.map_congr_left fun type _ => mapTypeExpr_id type
      _ = boundary.support := List.map_id boundary.support
  · change mapTypeExpr (costPresentationSymbols PresentationSymbols.id)
        boundary.targetType = boundary.targetType
    rw [costPresentationSymbols_id, mapTypeExpr_id]
  · change boundary.targetSupport.map
        (mapTypeExpr (costPresentationSymbols PresentationSymbols.id)) =
      boundary.targetSupport
    rw [costPresentationSymbols_id]
    calc
      boundary.targetSupport.map (mapTypeExpr PresentationSymbols.id) =
          boundary.targetSupport.map _root_.id :=
        List.map_congr_left fun type _ => mapTypeExpr_id type
      _ = boundary.targetSupport := List.map_id boundary.targetSupport
  · change mapPattern (costPresentationSymbols PresentationSymbols.id)
        boundary.content = boundary.content
    rw [costPresentationSymbols_id, mapPattern_id]

/-- Boundary reindexing respects composition on both its source and
generated target indices. -/
theorem map_comp {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third)
    (boundary : CostRegionBoundary) :
    boundary.map (CIGSLT.Morphism.comp left right) =
      (boundary.map left).map right := by
  apply CostRegionBoundary.ext
  · change mapTypeExpr
        (left.underlying.structural.structural.symbols.comp
          right.underlying.structural.structural.symbols) boundary.type = _
    exact mapTypeExpr_comp _ _ _
  · change boundary.support.map
        (mapTypeExpr
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols)) =
      (boundary.support.map
        (mapTypeExpr left.underlying.structural.structural.symbols)).map
        (mapTypeExpr right.underlying.structural.structural.symbols)
    rw [List.map_map]
    exact List.map_congr_left fun type _ => mapTypeExpr_comp _ _ type
  · change mapTypeExpr
        (costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols))
        boundary.targetType = _
    rw [costPresentationSymbols_comp]
    exact mapTypeExpr_comp _ _ _
  · change boundary.targetSupport.map
        (mapTypeExpr
          (costPresentationSymbols
            (left.underlying.structural.structural.symbols.comp
              right.underlying.structural.structural.symbols))) =
      (boundary.targetSupport.map
        (mapTypeExpr
          (costPresentationSymbols
            left.underlying.structural.structural.symbols))).map
        (mapTypeExpr
          (costPresentationSymbols
            right.underlying.structural.structural.symbols))
    rw [costPresentationSymbols_comp, List.map_map]
    exact List.map_congr_left fun type _ => mapTypeExpr_comp _ _ type
  · change mapPattern
        (costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols))
        boundary.content =
      mapPattern
        (costPresentationSymbols
          right.underlying.structural.structural.symbols)
        (mapPattern
          (costPresentationSymbols
            left.underlying.structural.structural.symbols)
          boundary.content)
    rw [costPresentationSymbols_comp, mapPattern_comp]

end CostRegionBoundary

namespace CostStaticBinderThinning

/-- Reindex one exact retained/foreign binder classification.  A retained
entry uses static-type naturality; a foreign entry stays foreign by decoder
naturality, so no target extension can silently change the thinning shape. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor) :
    {sourceBound targetBound : List TypeExpr} →
      CostStaticBinderThinning source color sourceBound targetBound →
      CostStaticBinderThinning target color
        (sourceBound.map
          (mapTypeExpr morphism.underlying.structural.structural.symbols))
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .mapped sourceType tail => by
      simpa [CIGSLT.Morphism.costWholeStructural,
        morphism.mapTypeExpr_costStatic_natural color sourceType] using
        CostStaticBinderThinning.mapped
          (mapTypeExpr morphism.underlying.structural.structural.symbols
            sourceType)
          (map morphism color tail)
  | _, targetType :: _, .foreign _ rejected tail => by
      have targetRejected :
          decodeCostStaticTypeExpr target color
              (mapTypeExpr morphism.costWholeStructural.symbols targetType) =
            none := by
        change decodeCostStaticTypeExpr target color
            (mapTypeExpr
              (costPresentationSymbols
                morphism.underlying.structural.structural.symbols)
              targetType) = none
        rw [morphism.decodeCostStaticTypeExpr_natural color targetType,
          rejected]
        rfl
      exact CostStaticBinderThinning.foreign
        (mapTypeExpr morphism.costWholeStructural.symbols targetType)
        targetRejected (map morphism color tail)

/-- Filtering a target binder context through one static image commutes with
reindexing. -/
theorem sourceContextOfTarget_natural {source target : CIGSLT}
    (morphism : source.Morphism target) (color : CostStaticColor)
    (targetBound : List TypeExpr) :
    sourceContextOfTarget target color
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols)) =
      (sourceContextOfTarget source color targetBound).map
        (mapTypeExpr morphism.underlying.structural.structural.symbols) := by
  change sourceContextOfTarget target color
      (targetBound.map
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols))) = _
  induction targetBound with
  | nil => simp [sourceContextOfTarget]
  | cons targetType targetBound inductionHypothesis =>
      simp only [List.map_cons, sourceContextOfTarget]
      rw [morphism.decodeCostStaticTypeExpr_natural color targetType]
      cases decodeCostStaticTypeExpr source color targetType <;>
        simp [inductionHypothesis]

/-- The erased target-to-source index filter is natural under generated Cost
reindexing. -/
theorem targetToSourceIndex?_natural {source target : CIGSLT}
    (morphism : source.Morphism target) (color : CostStaticColor)
    (targetBound : List TypeExpr) (index : Nat) :
    targetToSourceIndex? target color
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols)) index =
      targetToSourceIndex? source color targetBound index := by
  change targetToSourceIndex? target color
      (targetBound.map
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols))) index = _
  induction targetBound generalizing index with
  | nil => cases index <;> rfl
  | cons targetType targetBound inductionHypothesis =>
      cases index with
      | zero =>
          simp only [List.map_cons, targetToSourceIndex?]
          rw [morphism.decodeCostStaticTypeExpr_natural color targetType]
          cases decodeCostStaticTypeExpr source color targetType <;> rfl
      | succ index =>
          simp only [List.map_cons, targetToSourceIndex?]
          rw [morphism.decodeCostStaticTypeExpr_natural color targetType]
          cases decodeCostStaticTypeExpr source color targetType <;>
            simp [inductionHypothesis]

/-- Reindexing changes binder types but not the retained/foreign position
selected by the proof-relevant thinning. -/
@[simp]
theorem toSourceIndex?_map {source target : CIGSLT}
    (morphism : source.Morphism target) (color : CostStaticColor)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (index : Nat) :
    (thinning.map morphism color).toSourceIndex? index =
      thinning.toSourceIndex? index := by
  rw [toSourceIndex?_eq_targetToSourceIndex?,
    targetToSourceIndex?_natural,
    ← thinning.toSourceIndex?_eq_targetToSourceIndex?]

end CostStaticBinderThinning

namespace TypedCostRegionBoundary

/-- Transport a typed boundary through the generated Cost presentation.
The target free context, binder support, result type, raw content, and
quotation-scope certificate all move together. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundary source color targetFree) :
    TypedCostRegionBoundary target color
      (targetFree.map morphism.costWholeStructural.symbols) where
  boundary := boundary.boundary.map morphism
  contentTyped := boundary.contentTyped.map morphism.costWholeStructural
  contentCanonicalBinderMetadata := by
    simpa using boundary.contentCanonicalBinderMetadata
  contentObjectPattern := by
    simpa using boundary.contentObjectPattern
  contentReflectiveScopeSafe := by
    change ReflectiveWellSorted.ReflectiveScopeSafeAt
      target.costWholeReflectionProfile
      (boundary.boundary.targetSupport.map
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols))).length
      (mapPattern
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        boundary.boundary.content)
    simpa using scope boundary.contentReflectiveScopeSafe

@[simp]
theorem map_boundary {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundary source color targetFree) :
    (boundary.map morphism scope).boundary = boundary.boundary.map morphism :=
  rfl

end TypedCostRegionBoundary

namespace CertifiedCostRegionBoundary

/-- Indexed boundary certificates are determined by their underlying raw
boundary.  All remaining fields are propositions or equations fixing the
displayed indices. -/
@[ext]
theorem ext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr}
    {content : Pattern}
    {left right : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType content}
    (boundary : left.typed.boundary = right.typed.boundary) : left = right := by
  cases left
  cases right
  cases TypedCostRegionBoundary.ext boundary
  rfl

/-- Reindex only the displayed target-type index of a certificate. -/
def castTargetType {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {firstType secondType : TypeExpr}
    {content : Pattern} (equality : firstType = secondType)
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport firstType content) :
    CertifiedCostRegionBoundary source color targetFree targetSupport
      secondType content :=
  equality ▸ boundary

/-- Reindex only the displayed raw-content index of a certificate. -/
def castContent {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr}
    {firstContent secondContent : Pattern}
    (equality : firstContent = secondContent)
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType firstContent) :
    CertifiedCostRegionBoundary source color targetFree targetSupport
      targetType secondContent :=
  equality ▸ boundary

@[simp]
theorem castTargetType_typed_boundary {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {firstType secondType : TypeExpr}
    {content : Pattern} (equality : firstType = secondType)
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport firstType content) :
    (boundary.castTargetType equality).typed.boundary =
      boundary.typed.boundary := by
  cases equality
  rfl

@[simp]
theorem castContent_typed_boundary {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr}
    {firstContent secondContent : Pattern}
    (equality : firstContent = secondContent)
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType firstContent) :
    (boundary.castContent equality).typed.boundary =
      boundary.typed.boundary := by
  cases equality
  rfl

/-- Reindex one certified boundary while preserving its exact decoded
source fibre and observed generated fibre. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr}
    {content : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType content) :
    CertifiedCostRegionBoundary target color
      (targetFree.map morphism.costWholeStructural.symbols)
      (targetSupport.map (mapTypeExpr morphism.costWholeStructural.symbols))
      (mapTypeExpr morphism.costWholeStructural.symbols targetType)
      (mapPattern morphism.costWholeStructural.symbols content) where
  typed := boundary.typed.map morphism scope
  content_eq := by
    simpa using congrArg
      (mapPattern morphism.costWholeStructural.symbols) boundary.content_eq
  targetSupport_eq := by
    simpa using congrArg
      (List.map (mapTypeExpr morphism.costWholeStructural.symbols))
      boundary.targetSupport_eq
  targetType_eq := by
    simpa using congrArg
      (mapTypeExpr morphism.costWholeStructural.symbols)
      boundary.targetType_eq

/-- Reindex a certificate whose observed result is explicitly in one static
source fibre.  Static-type naturality exposes the target index expected by a
mapped static plan. -/
def mapStatic {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {sourceType : TypeExpr}
    {content : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content) :
    CertifiedCostRegionBoundary target color
      (targetFree.map morphism.costWholeStructural.symbols)
      (targetSupport.map (mapTypeExpr morphism.costWholeStructural.symbols))
      (mapTypeExpr (color.symbols target)
        (mapTypeExpr
          morphism.underlying.structural.structural.symbols sourceType))
      (mapPattern morphism.costWholeStructural.symbols content) :=
  (boundary.map morphism scope).castTargetType
    (morphism.mapTypeExpr_costStatic_natural color sourceType)

@[simp]
theorem mapStatic_typed_boundary {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {sourceType : TypeExpr}
    {content : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content) :
    (boundary.mapStatic morphism scope).typed.boundary =
      boundary.typed.boundary.map morphism := by
  exact castTargetType_typed_boundary _ _

/-- Changing the displayed spelling of a statically mapped certificate does
not alter the mapped typed boundary retained in a finite occurrence table. -/
@[simp]
theorem castContent_mapStatic_typed {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {sourceType : TypeExpr}
    {content mappedContent : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content)
    (contentEquality :
      mapPattern morphism.costWholeStructural.symbols content =
        mappedContent) :
    ((boundary.mapStatic morphism scope).castContent
        contentEquality).typed = boundary.typed.map morphism scope := by
  apply TypedCostRegionBoundary.ext
  simp

@[simp]
theorem map_typed_boundary {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {targetType : TypeExpr}
    {content : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType content) :
    (boundary.map morphism scope).typed.boundary =
      boundary.typed.boundary.map morphism :=
  rfl

/-- Boundary certification is natural on the static fibres used by region
plans.  The proof compares the executable target certificate with the
structurally mapped source certificate; no second certifier is introduced. -/
theorem certify_mapStatic_eq_some {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {sourceType : TypeExpr}
    {content : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content)
    (certified : certifyCostRegionBoundary? source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content =
        some boundary) :
    certifyCostRegionBoundary? target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetSupport.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (mapTypeExpr (color.symbols target)
          (mapTypeExpr
            morphism.underlying.structural.structural.symbols sourceType))
        (mapPattern morphism.costWholeStructural.symbols content) =
      some (boundary.mapStatic morphism scope) := by
  let mapped := boundary.mapStatic morphism scope
  have mappedTyped := mapped.typed.contentTyped
  have mappedCanonical := mapped.typed.contentCanonicalBinderMetadata
  have mappedObject := mapped.typed.contentObjectPattern
  have mappedScope := mapped.typed.contentReflectiveScopeSafe
  rw [mapped.targetSupport_eq, mapped.content_eq, mapped.targetType_eq] at mappedTyped
  rw [mapped.content_eq] at mappedCanonical mappedObject
  rw [mapped.targetSupport_eq, mapped.content_eq] at mappedScope
  have mappedWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      target.costWholeReflectionProfile target.costWholeLanguage
      (targetFree.map morphism.costWholeStructural.symbols)
      (targetSupport.map
        (mapTypeExpr morphism.costWholeStructural.symbols))
      (mapTypeExpr (color.symbols target)
        (mapTypeExpr
          morphism.underlying.structural.structural.symbols sourceType))
      (mapPattern morphism.costWholeStructural.symbols content) :=
    ⟨⟨mappedTyped, mappedCanonical, mappedObject,
      mappedTyped.isWellScopedAt⟩, mappedScope⟩
  obtain ⟨targetBoundary, targetCertified⟩ :=
    exists_certifyCostRegionBoundary?_eq_some
      (source := target) (color := color)
      (targetFree := targetFree.map morphism.costWholeStructural.symbols)
      (targetSupport := targetSupport.map
        (mapTypeExpr morphism.costWholeStructural.symbols))
      (targetType := mapTypeExpr (color.symbols target)
        (mapTypeExpr
          morphism.underlying.structural.structural.symbols sourceType))
      (content := mapPattern morphism.costWholeStructural.symbols content)
      ⟨_, decodeCostStaticTypeExpr_mapTypeExpr target color _⟩
      mappedWellSorted
  rw [targetCertified]
  congr 1
  apply CertifiedCostRegionBoundary.ext
  apply CostRegionBoundary.ext
  · rw [certifyCostRegionBoundary?_sourceType_eq targetCertified]
    rw [mapStatic_typed_boundary]
    change _ = mapTypeExpr
        morphism.underlying.structural.structural.symbols
          boundary.typed.boundary.type
    rw [certifyCostRegionBoundary?_sourceType_eq certified]
  · rw [certifyCostRegionBoundary?_sourceSupport targetCertified]
    rw [mapStatic_typed_boundary]
    change _ = boundary.typed.boundary.support.map
      (mapTypeExpr
        morphism.underlying.structural.structural.symbols)
    rw [certifyCostRegionBoundary?_sourceSupport certified,
      CostStaticBinderThinning.sourceContextOfTarget_natural]
  · exact targetBoundary.targetType_eq.trans mapped.targetType_eq.symm
  · exact targetBoundary.targetSupport_eq.trans
      mapped.targetSupport_eq.symm
  · exact targetBoundary.content_eq.trans mapped.content_eq.symm

/-- Boundary certification remains natural after changing only the displayed
spelling of the structurally mapped content. -/
theorem certify_mapStatic_castContent_eq_some {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetSupport : List TypeExpr} {sourceType : TypeExpr}
    {content mappedContent : Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content)
    (certified : certifyCostRegionBoundary? source color targetFree
      targetSupport (mapTypeExpr (color.symbols source) sourceType) content =
        some boundary)
    (contentEquality :
      mapPattern morphism.costWholeStructural.symbols content = mappedContent) :
    certifyCostRegionBoundary? target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetSupport.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (mapTypeExpr (color.symbols target)
          (mapTypeExpr
            morphism.underlying.structural.structural.symbols sourceType))
        mappedContent =
      some ((boundary.mapStatic morphism scope).castContent contentEquality) := by
  subst mappedContent
  exact boundary.certify_mapStatic_eq_some morphism scope certified

end CertifiedCostRegionBoundary

namespace TypedCostRegionBoundaryTable

/-- Map a complete finite boundary table in its original occurrence order.
Repeated equal contents remain distinct entries because both the table and
its list index are mapped structurally. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext} :
    {occurrences : List CostRegionOccurrence} →
      TypedCostRegionBoundaryTable source color targetFree occurrences →
      TypedCostRegionBoundaryTable target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (occurrences.map (CostRegionOccurrence.map morphism))
  | [], .nil => .nil
  | _ :: _, .cons boundary content tail =>
      .cons (boundary.map morphism scope)
        (congrArg (mapPattern morphism.costWholeStructural.symbols) content)
        (map morphism scope color tail)

@[simp]
theorem map_nil {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) :
    map morphism scope color
        (TypedCostRegionBoundaryTable.nil (source := source)
          (color := color) (targetFree := targetFree)) =
      TypedCostRegionBoundaryTable.nil :=
  rfl

/-- Mapping distributes over chronological table append.  In particular,
duplicate boundary occurrences keep their left-to-right positions. -/
def map_append {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    (left : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences)
    (right : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences) :
    TypedCostRegionBoundaryTable.cast
        (CostRegionOccurrence.map_append morphism leftOccurrences
          rightOccurrences)
        (map morphism scope color
          (TypedCostRegionBoundaryTable.append left right)) =
      TypedCostRegionBoundaryTable.append
        (map morphism scope color left)
        (map morphism scope color right) :=
  match left with
  | .nil => rfl
  | @TypedCostRegionBoundaryTable.cons _ _ _ occurrence occurrences boundary
      content tail => by
      let mappedOccurrence := occurrence.map morphism
      let mappedBoundary := boundary.map morphism scope
      have mappedContent : mappedBoundary.boundary.content =
          mappedOccurrence.content := by
        exact congrArg (mapPattern morphism.costWholeStructural.symbols)
          content
      change TypedCostRegionBoundaryTable.cast
          (CostRegionOccurrence.map_append morphism
            (occurrence :: occurrences) rightOccurrences)
          (.cons mappedBoundary mappedContent
            (map morphism scope color
              (TypedCostRegionBoundaryTable.append tail right))) =
        .cons mappedBoundary mappedContent
          (TypedCostRegionBoundaryTable.append
            (map morphism scope color tail)
            (map morphism scope color right))
      change TypedCostRegionBoundaryTable.cast
          (congrArg (List.cons mappedOccurrence)
            (CostRegionOccurrence.map_append morphism occurrences
              rightOccurrences))
          (.cons mappedBoundary mappedContent
            (map morphism scope color
              (TypedCostRegionBoundaryTable.append tail right))) =
        .cons mappedBoundary mappedContent
          (TypedCostRegionBoundaryTable.append
            (map morphism scope color tail)
            (map morphism scope color right))
      rw [TypedCostRegionBoundaryTable.cast_cons]
      exact congrArg
        (TypedCostRegionBoundaryTable.cons mappedBoundary mappedContent)
        (map_append morphism scope color tail right)
      all_goals exact (CostRegionOccurrence.map_append morphism occurrences
        rightOccurrences)
termination_by leftOccurrences.length

/-- Componentwise table naturality assembles across chronological append.
The occurrence equality is the canonical composite from the two component
equalities and structural list mapping. -/
theorem map_append_of {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    {leftSourceOccurrences rightSourceOccurrences
      leftTargetOccurrences rightTargetOccurrences :
        List CostRegionOccurrence}
    (leftOccurrenceEquality : leftTargetOccurrences =
      leftSourceOccurrences.map (CostRegionOccurrence.map morphism))
    (rightOccurrenceEquality : rightTargetOccurrences =
      rightSourceOccurrences.map (CostRegionOccurrence.map morphism))
    (leftSource : TypedCostRegionBoundaryTable source color targetFree
      leftSourceOccurrences)
    (rightSource : TypedCostRegionBoundaryTable source color targetFree
      rightSourceOccurrences)
    (leftTarget : TypedCostRegionBoundaryTable target color
      (targetFree.map morphism.costWholeStructural.symbols)
      leftTargetOccurrences)
    (rightTarget : TypedCostRegionBoundaryTable target color
      (targetFree.map morphism.costWholeStructural.symbols)
      rightTargetOccurrences)
    (leftNatural : cast leftOccurrenceEquality leftTarget =
      map morphism scope color leftSource)
    (rightNatural : cast rightOccurrenceEquality rightTarget =
      map morphism scope color rightSource) :
    cast
        ((congrArg₂ List.append leftOccurrenceEquality
          rightOccurrenceEquality).trans
          (CostRegionOccurrence.map_append morphism leftSourceOccurrences
            rightSourceOccurrences).symm)
        (append leftTarget rightTarget) =
      map morphism scope color (append leftSource rightSource) := by
  subst leftTargetOccurrences
  subst rightTargetOccurrences
  have leftNatural' : leftTarget = map morphism scope color leftSource := by
    simpa using leftNatural
  have rightNatural' : rightTarget = map morphism scope color rightSource := by
    simpa using rightNatural
  rw [leftNatural', rightNatural']
  let appendEquality := CostRegionOccurrence.map_append morphism
    leftSourceOccurrences rightSourceOccurrences
  rw [TypedCostRegionBoundaryTable.cast_proof_irrel
    ((congrArg₂ List.append rfl rfl).trans appendEquality.symm)
    appendEquality.symm]
  have mapped := map_append morphism scope color leftSource rightSource
  have inverse := congrArg
    (TypedCostRegionBoundaryTable.cast appendEquality.symm) mapped
  simpa [TypedCostRegionBoundaryTable.cast_trans] using inverse.symm

end TypedCostRegionBoundaryTable

namespace TypedCostRegionBoundaryPacket

/-- Map one total occurrence/table packet without separating its dependent
index from the retained certificates. -/
def map {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (packet : TypedCostRegionBoundaryPacket source color targetFree) :
    TypedCostRegionBoundaryPacket target color
      (targetFree.map morphism.costWholeStructural.symbols) :=
  ⟨packet.1.map (CostRegionOccurrence.map morphism),
    TypedCostRegionBoundaryTable.map morphism scope color packet.2⟩

/-- Mapping total packets preserves chronological composition exactly. -/
theorem map_append {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (left right : TypedCostRegionBoundaryPacket source color targetFree) :
    map morphism scope color (append left right) =
      append (map morphism scope color left)
        (map morphism scope color right) := by
  apply ext_of_cast_eq
    (CostRegionOccurrence.map_append morphism left.1 right.1)
  exact TypedCostRegionBoundaryTable.map_append morphism scope color
    left.2 right.2

end TypedCostRegionBoundaryPacket

namespace CostCollectionTypingChoice

/-- Reindex the source-side declaration and element fibre retained by one
collection typing choice. -/
def map (symbols : PresentationSymbols) :
    CostCollectionTypingChoice → CostCollectionTypingChoice
  | .direct sourceElementType =>
      .direct (mapTypeExpr symbols sourceElementType)
  | .bare sourceRule sourceElementType =>
      .bare (mapGrammarRule symbols sourceRule)
        (mapTypeExpr symbols sourceElementType)

@[simp]
theorem sourceElementType_map (symbols : PresentationSymbols)
    (choice : CostCollectionTypingChoice) :
    (choice.map symbols).sourceElementType =
      mapTypeExpr symbols choice.sourceElementType := by
  cases choice <;> rfl

@[simp]
theorem map_id (choice : CostCollectionTypingChoice) :
    choice.map PresentationSymbols.id = choice := by
  cases choice <;>
    simp [map, mapTypeExpr_id, mapGrammarRule_id]

theorem map_comp (first second : PresentationSymbols)
    (choice : CostCollectionTypingChoice) :
    choice.map (first.comp second) =
      (choice.map first).map second := by
  cases choice <;>
    simp [map, mapTypeExpr_comp, mapGrammarRule_comp]

end CostCollectionTypingChoice

namespace WellSorted

/-- Presentation-symbol renaming preserves object-language shape for an
ordered element spine. -/
@[simp]
theorem isObjectPatternList_mapPattern_reindex
    (symbols : PresentationSymbols) (patterns : List Pattern) :
    isObjectPatternList (patterns.map (mapPattern symbols)) =
      isObjectPatternList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [isObjectPatternList, inductionHypothesis]

/-- A successful homogeneous element check remains successful after a
structural presentation map. -/
theorem checkElementsHaveType_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (checked : checkElementsHaveType source.language free bound elements
      elementType = true)
    (objects : isObjectPatternList elements = true) :
    checkElementsHaveType target.language
      (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (elements.map (mapPattern morphism.symbols))
      (mapTypeExpr morphism.symbols elementType) = true := by
  apply checkElementsHaveType_complete_of_objects
  · exact (checkElementsHaveType_sound checked).map morphism
  · simpa using objects

end WellSorted

namespace CIGSLT.Morphism

/-- Every selected source collection witness remains a selected witness in
the mapped target fibre.  This is the positive half of collection-plan
reindexing; excluding target-only candidates is a separate conservative
arrow law. -/
theorem maps_mem_costStaticCollectionTypingChoices
    {source target : CIGSLT} (morphism : source.Morphism target)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern)
    (expected : TypeExpr) (choice : CostCollectionTypingChoice)
    (membership : choice ∈ costStaticCollectionTypingChoices source color
      targetFree targetBound collectionType elements expected)
    (objects : WellSorted.isObjectPatternList elements = true) :
    choice.map morphism.underlying.structural.structural.symbols ∈
      costStaticCollectionTypingChoices target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetBound.map (mapTypeExpr morphism.costWholeStructural.symbols))
        collectionType
        (elements.map (mapPattern morphism.costWholeStructural.symbols))
        (mapTypeExpr morphism.costWholeStructural.symbols expected) := by
  rw [mem_costStaticCollectionTypingChoices_iff]
  rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
      targetBound collectionType elements expected choice membership with
    direct | bare
  · rcases direct with
      ⟨sourceElementType, choiceEquality, expectedEquality,
        elementsChecked⟩
    subst choice
    refine Or.inl ⟨
      mapTypeExpr morphism.underlying.structural.structural.symbols
        sourceElementType,
      rfl, ?_, ?_⟩
    · rw [expectedEquality]
      exact morphism.mapTypeExpr_costStatic_natural color
        (.collection collectionType sourceElementType)
    · have mappedChecked := WellSorted.checkElementsHaveType_map
        morphism.costWholeStructural elementsChecked objects
      change WellSorted.checkElementsHaveType target.costWholeLanguage
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (elements.map (mapPattern morphism.costWholeStructural.symbols))
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols)
          (mapTypeExpr (color.symbols source) sourceElementType)) = true at mappedChecked
      rw [morphism.mapTypeExpr_costStatic_natural] at mappedChecked
      exact mappedChecked
  · rcases bare with
      ⟨rule, sourceElementType, choiceEquality, ruleMembership,
        wrappedMembership, expectedEquality, parameterName, parameterShape,
        elementsChecked⟩
    subst choice
    refine Or.inr ⟨
      mapGrammarRule morphism.underlying.structural.structural.symbols rule,
      mapTypeExpr morphism.underlying.structural.structural.symbols
        sourceElementType,
      rfl, ?_, ?_, ?_, parameterName, ?_, ?_⟩
    · exact morphism.underlying.structural.structural.mapsTerms rule
        ruleMembership
    · exact (morphism.mapsWrappedLabelMembership rule.label).2
        wrappedMembership
    · change mapTypeExpr morphism.costWholeStructural.symbols expected =
        mapTypeExpr (color.symbols target)
          (.base
            (morphism.underlying.structural.structural.symbols.sort
              rule.category))
      rw [expectedEquality]
      exact morphism.mapTypeExpr_costStatic_natural color
        (.base rule.category)
    · simpa [mapGrammarRule, mapTermParam, mapTypeExpr] using
        congrArg
          (List.map
            (mapTermParam
              morphism.underlying.structural.structural.symbols))
          parameterShape
    · have mappedChecked := WellSorted.checkElementsHaveType_map
        morphism.costWholeStructural elementsChecked objects
      change WellSorted.checkElementsHaveType target.costWholeLanguage
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (elements.map (mapPattern morphism.costWholeStructural.symbols))
        (mapTypeExpr
          (costPresentationSymbols
            morphism.underlying.structural.structural.symbols)
          (mapTypeExpr (color.symbols source) sourceElementType)) = true at mappedChecked
      rw [morphism.mapTypeExpr_costStatic_natural] at mappedChecked
      exact mappedChecked

end CIGSLT.Morphism

end Mettapedia.GSLT.LanguageDef
