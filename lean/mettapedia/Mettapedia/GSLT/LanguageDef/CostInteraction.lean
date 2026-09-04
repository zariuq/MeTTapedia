import Mettapedia.GSLT.LanguageDef.CostFunctor

/-!
# The declaration-derived whole-redex Cost interaction

The generic Cost interaction retains the source cut as an ordered base core
and places one explicit signed/funding envelope around it.  The output contact
has a single fixed profile on the wrapped carrier; it does not overload the
source contact constructor.  The funded rule consumes exactly the head of an
ordered token stack and carries its tail into the contractum.

This module first constructs the exact schema data.  Validation, sorting, and
closure back into continued interactive GSLTs are proved in the subsequent
layer.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted
open ReflectionExtension

/-! ## Disjoint namespaces for generated schema variables -/

def costSourceSchemaTag : String := "source:$cost:"

def costSourceSchemaName (name : String) : String :=
  costSourceSchemaTag ++ name

def costAdministrativeSchemaTag : String := "administrative:$cost:"

def costAdministrativeSchemaName (name : String) : String :=
  costAdministrativeSchemaTag ++ name

/-- The sole operational rule name of the whole-redex Cost presentation. -/
def costWholeRedexRewriteName : String := "$cost:rewrite:whole-redex"

theorem costSourceSchemaName_injective :
    Function.Injective costSourceSchemaName := by
  intro left right equality
  exact (String.append_right_inj costSourceSchemaTag).mp equality

theorem costAdministrativeSchemaName_injective :
    Function.Injective costAdministrativeSchemaName := by
  intro left right equality
  exact (String.append_right_inj costAdministrativeSchemaTag).mp equality

theorem costSourceSchemaName_ne_administrative
    (sourceName administrativeName : String) :
    costSourceSchemaName sourceName ≠
      costAdministrativeSchemaName administrativeName := by
  intro equality
  have listEquality := congrArg String.toList equality
  simp [costSourceSchemaName, costSourceSchemaTag,
    costAdministrativeSchemaName, costAdministrativeSchemaTag] at listEquality

mutual
  /-- Rename every schema-level name without changing constructors, binders,
  de Bruijn indices, collection shape, order, or multiplicity. -/
  def mapPatternSchemaNames (mapName : String → String) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar (mapName name)
    | .apply constructor arguments =>
        .apply constructor (mapPatternListSchemaNames mapName arguments)
    | .lambda binder body =>
        .lambda (binder.map mapName) (mapPatternSchemaNames mapName body)
    | .multiLambda arity binders body =>
        .multiLambda arity (binders.map mapName)
          (mapPatternSchemaNames mapName body)
    | .subst body replacement =>
        .subst (mapPatternSchemaNames mapName body)
          (mapPatternSchemaNames mapName replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (mapPatternListSchemaNames mapName elements) (rest.map mapName)

  def mapPatternListSchemaNames (mapName : String → String) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        mapPatternSchemaNames mapName pattern ::
          mapPatternListSchemaNames mapName patterns
end

/-- Rename schema-local names in a premise while retaining declared relation
symbols and every premise constructor.  The `forAll` collection and parameter
are local binding names, so they receive the same injective action as the
patterns in its body. -/
def mapPremiseSchemaNames (mapName : String → String) : Premise → Premise
  | .freshness condition =>
      .freshness
        { varName := mapName condition.varName
          term := mapPatternSchemaNames mapName condition.term }
  | .congruence left right =>
      .congruence (mapPatternSchemaNames mapName left)
        (mapPatternSchemaNames mapName right)
  | .relationQuery relation arguments =>
      .relationQuery relation (mapPatternListSchemaNames mapName arguments)
  | .forAll collection parameter body =>
      .forAll (mapName collection) (mapName parameter)
        (mapPremiseSchemaNames mapName body)

/-- Rename the keys of an authored schema context without changing its sort
annotations. -/
def mapTypeContextSchemaNames (mapName : String → String)
    (context : List (String × TypeExpr)) : List (String × TypeExpr) :=
  context.map fun entry => (mapName entry.1, entry.2)

namespace WellSorted.FreeTypeContext

/-- Injective schema renaming commutes with first-match interpretation of an
authored type context. -/
theorem ofList_mapTypeContextSchemaNames
    (mapName : String → String) (injective : Function.Injective mapName)
    (context : List (String × TypeExpr)) (name : String) :
    ofList (mapTypeContextSchemaNames mapName context) (mapName name) =
      ofList context name := by
  induction context with
  | nil => rfl
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      by_cases equality : entryName = name
      · subst entryName
        simp [mapTypeContextSchemaNames, ofList]
      · have mappedInequality : mapName entryName ≠ mapName name :=
          fun mappedEquality => equality (injective mappedEquality)
        change ofList
            ((mapName entryName, entryType) ::
              mapTypeContextSchemaNames mapName context)
              (mapName name) =
          ofList ((entryName, entryType) :: context) name
        simp [ofList, equality, mappedInequality, inductionHypothesis]

end WellSorted.FreeTypeContext

/-- Rename every schema-local name of an equation.  Language symbols and the
equation's declaration name have already been handled by structural theory
transport and are deliberately left untouched here. -/
def mapEquationSchemaNames (mapName : String → String)
    (equation : Equation) : Equation :=
  { equation with
    typeContext := mapTypeContextSchemaNames mapName equation.typeContext
    premises := equation.premises.map (mapPremiseSchemaNames mapName)
    left := mapPatternSchemaNames mapName equation.left
    right := mapPatternSchemaNames mapName equation.right }

/-- Schema-local alpha-renaming preserves the quote/drop equation shape
recognized by the reflective validator. -/
theorem quoteDropShape_mapEquationSchemaNames
    (mapName : String → String) (declaration : ReflectivePresentationDecl)
    (equation : Equation)
    (shape : LanguageDef.QuoteDropShape declaration equation) :
    LanguageDef.QuoteDropShape declaration
      (mapEquationSchemaNames mapName equation) := by
  rw [LanguageDef.quoteDropShape_iff] at shape ⊢
  rcases shape with ⟨equationVariable, forward | reverse⟩
  · refine ⟨mapName equationVariable, Or.inl ?_⟩
    simp [mapEquationSchemaNames, forward.1, forward.2,
      mapPatternSchemaNames, mapPatternListSchemaNames]
  · refine ⟨mapName equationVariable, Or.inr ?_⟩
    simp [mapEquationSchemaNames, reverse.1, reverse.2,
      mapPatternSchemaNames, mapPatternListSchemaNames]

/-- Final base-fiber image of an authored equation.  Structural symbols are
translated first; schema-local variables are then moved into the collision-
free source namespace. -/
def costBaseEquationDecl (equation : Equation) : Equation :=
  mapEquationSchemaNames costSourceSchemaName (costBaseEquation equation)

/-- Final hereditary wrapped-fiber image of an authored equation. -/
def costWrappedEquationDecl (theory : IGSLT) (equation : Equation) : Equation :=
  mapEquationSchemaNames costSourceSchemaName
    (costWrappedEquation theory equation)

@[simp]
theorem costBaseEquationDecl_name (equation : Equation) :
    (costBaseEquationDecl equation).name =
      costBaseEquationName equation.name := rfl

@[simp]
theorem costWrappedEquationDecl_name (theory : IGSLT)
    (equation : Equation) :
    (costWrappedEquationDecl theory equation).name =
      costWrappedEquationName equation.name := rfl

@[simp]
theorem costBaseEquationDecl_premises (equation : Equation) :
    (costBaseEquationDecl equation).premises =
      equation.premises.map
        (mapPremiseSchemaNames costSourceSchemaName ∘
          mapPremise costBaseStaticSymbols) := by
  simp [costBaseEquationDecl, mapEquationSchemaNames, costBaseEquation,
    mapEquation]

@[simp]
theorem costWrappedEquationDecl_premises (theory : IGSLT)
    (equation : Equation) :
    (costWrappedEquationDecl theory equation).premises =
      equation.premises.map
        (mapPremiseSchemaNames costSourceSchemaName ∘
          mapPremise (costWrappedStaticSymbols theory)) := by
  simp [costWrappedEquationDecl, mapEquationSchemaNames,
    costWrappedEquation, mapEquation]

namespace CIGSLT

/-- The static equation theory of Cost consists of disjoint base and wrapped
images of the sole authored source equations. -/
def costStaticEquations (source : CIGSLT) : List Equation :=
  source.theory.presentation.presentation.language.equations.map
      costBaseEquationDecl ++
    source.theory.presentation.presentation.language.equations.map
      (costWrappedEquationDecl source.theory)

/-- The reflective static theory of Cost consists of disjoint base and
wrapped images of the exact authored presentation list. -/
def costStaticReflectivePresentations (source : CIGSLT) :
    List ReflectivePresentationDecl :=
  source.reflection.1.presentations.map
      costBaseReflectivePresentationDecl ++
    source.reflection.1.presentations.map
      (costWrappedReflectivePresentationDecl source.theory)

/-- Transform one source rule-local reflective selection for the funded
whole-redex rule.  Matching sees the base redex; substitution constructs the
wrapped contractum. -/
def costInteractionReflectiveRuleDecl
    (declaration : ReflectiveRuleDecl) : ReflectiveRuleDecl :=
  { name := costBaseReflectiveRuleName declaration.name
    rewriteRule := costWholeRedexRewriteName
    matchingPresentation :=
      costBaseReflectiveName declaration.matchingPresentation
    substitutionPresentation :=
      costWrappedReflectiveName declaration.substitutionPresentation }

/-- Preserve exactly the source selections attached to the selected
interaction rewrite.  Zero, one, or ambiguous selections remain zero, one,
or ambiguous after transport; no reflective behavior is guessed. -/
def costInteractionReflectiveRules (source : CIGSLT) :
    List ReflectiveRuleDecl :=
  (source.reflection.1.rules.filter
      fun declaration => declaration.rewriteRule ==
        source.theory.presentation.interactionRewrite.1.name).map
    costInteractionReflectiveRuleDecl

end CIGSLT

@[simp]
theorem mapPatternListSchemaNames_length (mapName : String → String)
    (patterns : List Pattern) :
    (mapPatternListSchemaNames mapName patterns).length = patterns.length := by
  induction patterns <;> simp_all [mapPatternListSchemaNames]

theorem mapPatternListSchemaNames_eq_map (mapName : String → String)
    (patterns : List Pattern) :
    mapPatternListSchemaNames mapName patterns =
      patterns.map (mapPatternSchemaNames mapName) := by
  induction patterns <;> simp_all [mapPatternListSchemaNames]

mutual
  /-- Schema-local renaming leaves canonical binder metadata unchanged. -/
  @[simp]
  theorem hasCanonicalBinderMetadata_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      (mapPatternSchemaNames mapName pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata := by
    cases pattern <;>
      simp [mapPatternSchemaNames, Pattern.hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadata_mapPatternSchemaNames,
        hasCanonicalBinderMetadataList_mapPatternSchemaNames]

  /-- List companion to
  `hasCanonicalBinderMetadata_mapPatternSchemaNames`. -/
  @[simp]
  theorem hasCanonicalBinderMetadataList_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      Pattern.hasCanonicalBinderMetadataList
          (mapPatternListSchemaNames mapName patterns) =
        Pattern.hasCanonicalBinderMetadataList patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames, Pattern.hasCanonicalBinderMetadataList,
        hasCanonicalBinderMetadata_mapPatternSchemaNames,
        hasCanonicalBinderMetadataList_mapPatternSchemaNames]
end

mutual
  /-- Schema-local renaming preserves the closed collection-tail fragment. -/
  @[simp]
  theorem schemaHasNoCollectionRest_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      schemaHasNoCollectionRest (mapPatternSchemaNames mapName pattern) =
        schemaHasNoCollectionRest pattern := by
    cases pattern <;>
      simp [mapPatternSchemaNames, schemaHasNoCollectionRest,
        schemaHasNoCollectionRest_mapPatternSchemaNames,
        schemaListHasNoCollectionRest_mapPatternSchemaNames]

  /-- List companion to
  `schemaHasNoCollectionRest_mapPatternSchemaNames`. -/
  @[simp]
  theorem schemaListHasNoCollectionRest_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      schemaListHasNoCollectionRest
          (mapPatternListSchemaNames mapName patterns) =
        schemaListHasNoCollectionRest patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames, schemaListHasNoCollectionRest,
        schemaHasNoCollectionRest_mapPatternSchemaNames,
        schemaListHasNoCollectionRest_mapPatternSchemaNames]
end

/-- Schema-local alpha-renaming preserves the exact instantiation fragment. -/
@[simp]
theorem schemaInstantiationStable_mapPatternSchemaNames
    (mapName : String → String) (pattern : Pattern) :
    schemaInstantiationStable (mapPatternSchemaNames mapName pattern) =
      schemaInstantiationStable pattern := by
  simp [schemaInstantiationStable]

mutual
  /-- Matcher reconstruction depends on schema shape, not metavariable
  spelling. -/
  @[simp]
  theorem isMatchCorrectAux_mapPatternSchemaNames
      (mapName : String → String) (pattern : Pattern) :
      Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux
          (mapPatternSchemaNames mapName pattern) =
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux pattern := by
    cases pattern <;>
      simp [mapPatternSchemaNames,
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectAux,
        isMatchCorrectListAux_mapPatternSchemaNames]

  /-- List companion to `isMatchCorrectAux_mapPatternSchemaNames`. -/
  @[simp]
  theorem isMatchCorrectListAux_mapPatternSchemaNames
      (mapName : String → String) (patterns : List Pattern) :
      Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux
          (mapPatternListSchemaNames mapName patterns) =
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux patterns := by
    cases patterns <;>
      simp [mapPatternListSchemaNames,
        Mettapedia.OSLF.MeTTaIL.Match.isMatchCorrectListAux,
        isMatchCorrectAux_mapPatternSchemaNames,
        isMatchCorrectListAux_mapPatternSchemaNames]
end

/-- Public matcher-correctness invariance under schema-local renaming. -/
@[simp]
theorem isMatchCorrect_mapPatternSchemaNames
    (mapName : String → String) (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect
        (mapPatternSchemaNames mapName pattern) =
      Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect pattern :=
  isMatchCorrectAux_mapPatternSchemaNames mapName pattern

/-- Renaming schema-local variables leaves the authored constructor
references of a pattern unchanged. -/
@[simp]
theorem mapPatternSchemaNames_constructorRefs
    (mapName : String → String) (pattern : Pattern) :
    (mapPatternSchemaNames mapName pattern).constructorRefs =
      pattern.constructorRefs := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments inductionHypothesis =>
      have listReferences :
          Pattern.constructorRefsList
              (mapPatternListSchemaNames mapName arguments) =
            Pattern.constructorRefsList arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [mapPatternListSchemaNames,
              Pattern.constructorRefsList]
            rw [inductionHypothesis argument (by simp)]
            rw [listInduction (fun nested nestedMembership =>
              inductionHypothesis nested (by simp [nestedMembership]))]
      cases arguments with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              simpa [mapPatternSchemaNames, mapPatternListSchemaNames,
                Pattern.constructorRefs] using listReferences
          | cons second tail =>
              cases tail with
              | nil =>
                  by_cases zip : constructor = "$zip"
                  · subst constructor
                    simpa [mapPatternSchemaNames,
                      mapPatternListSchemaNames,
                      Pattern.constructorRefs] using listReferences
                  by_cases map : constructor = "$map"
                  · subst constructor
                    cases second <;>
                      simpa [mapPatternSchemaNames,
                        mapPatternListSchemaNames,
                        Pattern.constructorRefs] using listReferences
                  by_cases evaluate : constructor = "$eval"
                  · subst constructor
                    simpa [mapPatternSchemaNames,
                      mapPatternListSchemaNames,
                      Pattern.constructorRefs] using listReferences
                  · simpa [mapPatternSchemaNames,
                      mapPatternListSchemaNames,
                      Pattern.constructorRefs, zip, map, evaluate] using
                        listReferences
              | cons third tail =>
                  simpa [mapPatternSchemaNames,
                    mapPatternListSchemaNames,
                    Pattern.constructorRefs] using listReferences
  | hlambda binder body inductionHypothesis =>
      simpa [mapPatternSchemaNames, Pattern.constructorRefs] using
        inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [mapPatternSchemaNames, Pattern.constructorRefs] using
        inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPatternSchemaNames, Pattern.constructorRefs,
        bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPatternSchemaNames, Pattern.constructorRefs]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [mapPatternListSchemaNames,
            Pattern.constructorRefsList]
          rw [inductionHypothesis element (by simp)]
          rw [listInduction (fun nested nestedMembership =>
            inductionHypothesis nested (by simp [nestedMembership]))]

/-- Structural symbol transport and schema-local alpha-renaming act on
disjoint parts of a pattern, hence commute exactly. -/
@[simp]
theorem mapPattern_mapPatternSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (pattern : Pattern) :
    mapPattern symbols (mapPatternSchemaNames mapName pattern) =
      mapPatternSchemaNames mapName (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn <;>
    simp_all [mapPattern, mapPatternSchemaNames,
      mapPatternListSchemaNames_eq_map, List.map_map]

/-- The same commuting square holds pointwise for pattern lists. -/
@[simp]
theorem mapPatternList_mapPatternListSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (patterns : List Pattern) :
    mapPatternListSchemaNames mapName
        (patterns.map (mapPattern symbols)) =
      (mapPatternListSchemaNames mapName patterns).map
        (mapPattern symbols) := by
  simp only [mapPatternListSchemaNames_eq_map, List.map_map]
  apply List.map_congr_left
  intro pattern _membership
  exact (mapPattern_mapPatternSchemaNames symbols mapName pattern).symm

/-- Structural symbol transport commutes with schema-local renaming in
authored premises.  Declared relation symbols move only structurally; local
quantifier and freshness names move only by alpha-renaming. -/
@[simp]
theorem mapPremise_mapPremiseSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (premise : Premise) :
    mapPremise symbols (mapPremiseSchemaNames mapName premise) =
      mapPremiseSchemaNames mapName (mapPremise symbols premise) := by
  induction premise with
  | freshness condition =>
      cases condition
      simp [mapPremise, mapPremiseSchemaNames]
  | congruence left right =>
      simp [mapPremise, mapPremiseSchemaNames]
  | relationQuery relation arguments =>
      simp [mapPremise, mapPremiseSchemaNames,
        mapPatternListSchemaNames_eq_map, List.map_map]
  | forAll collection parameter body inductionHypothesis =>
      simp [mapPremise, mapPremiseSchemaNames, inductionHypothesis]

/-- Structural sort transport commutes with renaming the metavariable keys of
a schema context. -/
@[simp]
theorem mapTypeContext_mapTypeContextSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (context : List (String × TypeExpr)) :
    mapTypeContext symbols (mapTypeContextSchemaNames mapName context) =
      mapTypeContextSchemaNames mapName (mapTypeContext symbols context) := by
  simp [mapTypeContext, mapTypeContextSchemaNames, List.map_map,
    Function.comp_def]

/-- Equation transport is independent of the collision-free choice of local
schema names. -/
@[simp]
theorem mapEquation_mapEquationSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (equation : Equation) :
    mapEquation symbols (mapEquationSchemaNames mapName equation) =
      mapEquationSchemaNames mapName (mapEquation symbols equation) := by
  rcases equation with ⟨name, context, premises, left, right⟩
  simp [mapEquation, mapEquationSchemaNames, List.map_map]

namespace CIGSLT.Morphism

/-- Base reflective presentations are natural under the generated Cost
symbol action. -/
theorem mapReflectivePresentation_costBase {source target : CIGSLT}
    (morphism : source.Morphism target)
    (declaration : ReflectivePresentationDecl) :
    mapReflectivePresentation
        (costReflectiveSymbols morphism.reflectiveSymbols)
        (costBaseReflectivePresentationDecl declaration) =
      costBaseReflectivePresentationDecl
        (mapReflectivePresentation morphism.reflectiveSymbols declaration) := by
  cases declaration
  simp [costBaseReflectivePresentationDecl, mapReflectivePresentation,
    costBaseStaticReflectiveSymbols, costBaseStaticSymbols,
    costBaseLanguageDefSymbolMap, costReflectiveSymbols, reflectiveSymbols]

/-- Wrapped reflective presentations are natural because continued maps
preserve and reflect the distinguished interacting sort. -/
theorem mapReflectivePresentation_costWrapped {source target : CIGSLT}
    (morphism : source.Morphism target)
    (declaration : ReflectivePresentationDecl) :
    mapReflectivePresentation
        (costReflectiveSymbols morphism.reflectiveSymbols)
        (costWrappedReflectivePresentationDecl source.theory declaration) =
      costWrappedReflectivePresentationDecl target.theory
        (mapReflectivePresentation morphism.reflectiveSymbols declaration) := by
  cases declaration
  simp [costWrappedReflectivePresentationDecl, mapReflectivePresentation,
    costWrappedStaticReflectiveSymbols, costWrappedStaticSymbols,
    costReflectiveSymbols, reflectiveSymbols,
    morphism.map_costWrappedCategory]

/-- Rule-local reflective selections commute with continued structural maps:
the whole-redex rewrite is fixed, while the source presentation references
move inside their reserved tags. -/
theorem mapReflectiveRule_costInteraction {source target : CIGSLT}
    (morphism : source.Morphism target)
    (declaration : ReflectiveRuleDecl) :
    mapReflectiveRule
        (costReflectiveSymbols morphism.reflectiveSymbols)
        (costInteractionReflectiveRuleDecl declaration) =
      costInteractionReflectiveRuleDecl
        (mapReflectiveRule morphism.reflectiveSymbols declaration) := by
  cases declaration
  simp [mapReflectiveRule, costInteractionReflectiveRuleDecl,
    costWholeRedexRewriteName, costReflectiveSymbols, reflectiveSymbols]

/-- A continued theory map carries each final base-fiber equation declaration
to the declaration generated from the mapped source equation. -/
theorem mapEquation_costBaseEquationDecl {source target : CIGSLT}
    (morphism : source.Morphism target) (equation : Equation)
    (premisesEmpty : equation.premises = []) :
    mapEquation
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        (costBaseEquationDecl equation) =
      costBaseEquationDecl
        (mapEquation morphism.underlying.structural.structural.symbols
          equation) := by
  unfold costBaseEquationDecl
  rw [mapEquation_mapEquationSchemaNames,
    mapEquation_costBase_natural _ equation premisesEmpty]

/-- The corresponding hereditary wrapped declaration is natural because a
continued morphism preserves and reflects the selected interacting fiber. -/
theorem mapEquation_costWrappedEquationDecl {source target : CIGSLT}
    (morphism : source.Morphism target) (equation : Equation)
    (premisesEmpty : equation.premises = []) :
    mapEquation
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        (costWrappedEquationDecl source.theory equation) =
      costWrappedEquationDecl target.theory
        (mapEquation morphism.underlying.structural.structural.symbols
          equation) := by
  unfold costWrappedEquationDecl
  rw [mapEquation_mapEquationSchemaNames,
    mapEquation_costWrapped_natural _ source.theory target.theory
      morphism.mapsInteractingSortName morphism.reflectsInteractingSort
      equation premisesEmpty]

/-- The Cost equation list is functorial as an authored subtheory: every
source declaration maps into the corresponding base or wrapped declaration
generated from the mapped equation in the target. -/
theorem mapsCostStaticEquations {source target : CIGSLT}
    (morphism : source.Morphism target) (equation : Equation)
    (membership : equation ∈ source.costStaticEquations) :
    mapEquation
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        equation ∈ target.costStaticEquations := by
  rw [CIGSLT.costStaticEquations] at membership ⊢
  rcases List.mem_append.mp membership with
    baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨mapEquation
        morphism.underlying.structural.structural.symbols sourceEquation,
      morphism.underlying.structural.structural.mapsEquations
        sourceEquation sourceMembership, ?_⟩
    exact (morphism.mapEquation_costBaseEquationDecl sourceEquation
      (source.equationsRetypable sourceEquation sourceMembership).premiseFree).symm
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceEquation, sourceMembership, rfl⟩
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨mapEquation
        morphism.underlying.structural.structural.symbols sourceEquation,
      morphism.underlying.structural.structural.mapsEquations
        sourceEquation sourceMembership, ?_⟩
    exact (morphism.mapEquation_costWrappedEquationDecl sourceEquation
      (source.equationsRetypable sourceEquation sourceMembership).premiseFree).symm

/-- Continued structural maps carry both tagged copies of every authored
reflective presentation into the corresponding target copies. -/
theorem mapsCostStaticReflectivePresentations {source target : CIGSLT}
    (morphism : source.Morphism target)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈ source.costStaticReflectivePresentations) :
    mapReflectivePresentation
        (costReflectiveSymbols morphism.reflectiveSymbols) declaration ∈
      target.costStaticReflectivePresentations := by
  rw [CIGSLT.costStaticReflectivePresentations] at membership ⊢
  rcases List.mem_append.mp membership with
      baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨mapReflectivePresentation
        morphism.reflectiveSymbols sourceDeclaration,
      morphism.mapsReflectivePresentations sourceDeclaration sourceMembership, ?_⟩
    exact (morphism.mapReflectivePresentation_costBase
      sourceDeclaration).symm
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourceDeclaration, sourceMembership, rfl⟩
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨mapReflectivePresentation
        morphism.reflectiveSymbols sourceDeclaration,
      morphism.mapsReflectivePresentations sourceDeclaration sourceMembership, ?_⟩
    exact (morphism.mapReflectivePresentation_costWrapped
      sourceDeclaration).symm

/-- The selected rule-local reflective subtheory is natural: preservation of
the distinguished interaction rewrite carries the source filter predicate to
the target filter predicate. -/
theorem mapsCostInteractionReflectiveRules {source target : CIGSLT}
    (morphism : source.Morphism target)
    (declaration : ReflectiveRuleDecl)
    (membership : declaration ∈ source.costInteractionReflectiveRules) :
    mapReflectiveRule
        (costReflectiveSymbols morphism.reflectiveSymbols) declaration ∈
      target.costInteractionReflectiveRules := by
  rw [CIGSLT.costInteractionReflectiveRules] at membership ⊢
  rcases List.mem_map.mp membership with
    ⟨sourceDeclaration, selectedMembership, rfl⟩
  have sourceMembership := (List.mem_filter.mp selectedMembership).1
  have selectedName : sourceDeclaration.rewriteRule =
      source.theory.presentation.interactionRewrite.1.name :=
    beq_iff_eq.mp (List.mem_filter.mp selectedMembership).2
  let targetDeclaration := mapReflectiveRule
    morphism.reflectiveSymbols sourceDeclaration
  have targetMembership : targetDeclaration ∈
      target.reflection.1.rules :=
    morphism.mapsReflectiveRules sourceDeclaration sourceMembership
  have targetSelectedName : targetDeclaration.rewriteRule =
      target.theory.presentation.interactionRewrite.1.name := by
    change morphism.underlying.structural.structural.symbols.rewrite
        sourceDeclaration.rewriteRule =
      target.theory.presentation.interactionRewrite.1.name
    rw [selectedName]
    exact congrArg RewriteRule.name morphism.mapsInteractionRewriteValue
  have targetSelectedMembership : targetDeclaration ∈
      target.reflection.1.rules.filter
        (fun candidate => candidate.rewriteRule ==
          target.theory.presentation.interactionRewrite.1.name) :=
    List.mem_filter.mpr ⟨targetMembership,
      (beq_iff_eq.mpr targetSelectedName)⟩
  apply List.mem_map.mpr
  refine ⟨targetDeclaration, targetSelectedMembership, ?_⟩
  exact (morphism.mapReflectiveRule_costInteraction sourceDeclaration).symm

end CIGSLT.Morphism

@[simp]
theorem attach_flatMap_value (values : List α) (mapValue : α → List β) :
    values.attach.flatMap (fun entry => mapValue entry.1) =
      values.flatMap mapValue := by
  unfold List.flatMap
  rw [List.attach_map_val]

mutual
  /-- Schema renaming acts pointwise on binder metadata as well. -/
  @[simp]
  theorem mapPatternSchemaNames_patternBinderNames
      (mapName : String → String) (pattern : Pattern) :
      LanguageDef.patternBinderNames
          (mapPatternSchemaNames mapName pattern) =
        (LanguageDef.patternBinderNames pattern).map mapName := by
    cases pattern with
    | bvar index =>
        simp [mapPatternSchemaNames, LanguageDef.patternBinderNames]
    | fvar name =>
        simp [mapPatternSchemaNames, LanguageDef.patternBinderNames]
    | apply constructor arguments =>
        simpa [mapPatternSchemaNames, LanguageDef.patternBinderNames] using
          mapPatternListSchemaNames_patternBinderNames mapName arguments
    | lambda binder body =>
        cases binder <;>
          simp [mapPatternSchemaNames, LanguageDef.patternBinderNames,
            mapPatternSchemaNames_patternBinderNames mapName body]
    | multiLambda arity binders body =>
        simp [mapPatternSchemaNames, LanguageDef.patternBinderNames,
          mapPatternSchemaNames_patternBinderNames mapName body,
          List.map_append]
    | subst body replacement =>
        simp [mapPatternSchemaNames, LanguageDef.patternBinderNames,
          mapPatternSchemaNames_patternBinderNames mapName body,
          mapPatternSchemaNames_patternBinderNames mapName replacement,
          List.map_append]
    | collection collectionType elements rest =>
        simpa [mapPatternSchemaNames, LanguageDef.patternBinderNames] using
          mapPatternListSchemaNames_patternBinderNames mapName elements

  /-- Binder metadata is renamed pointwise over pattern lists. -/
  @[simp]
  theorem mapPatternListSchemaNames_patternBinderNames
      (mapName : String → String) (patterns : List Pattern) :
      (mapPatternListSchemaNames mapName patterns).attach.flatMap
          (fun entry => LanguageDef.patternBinderNames entry.1) =
        (patterns.attach.flatMap
          (fun entry => LanguageDef.patternBinderNames entry.1)).map mapName := by
    rw [attach_flatMap_value, attach_flatMap_value]
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        have tailEquality :=
          mapPatternListSchemaNames_patternBinderNames mapName patterns
        rw [attach_flatMap_value, attach_flatMap_value] at tailEquality
        simp [mapPatternListSchemaNames,
          mapPatternSchemaNames_patternBinderNames mapName pattern,
          tailEquality, List.map_append]
end

@[simp]
theorem mapPatternListSchemaNames_append (mapName : String → String)
    (left right : List Pattern) :
    mapPatternListSchemaNames mapName (left ++ right) =
      mapPatternListSchemaNames mapName left ++
        mapPatternListSchemaNames mapName right := by
  induction left <;>
    simp_all [mapPatternListSchemaNames]

mutual
  /-- Schema renaming acts pointwise on free metavariable names. -/
  @[simp]
  theorem mapPatternSchemaNames_freeFvarNames
      (mapName : String → String) (pattern : Pattern) :
      (mapPatternSchemaNames mapName pattern).freeFvarNames =
        pattern.freeFvarNames.map mapName := by
    cases pattern with
    | bvar index => simp [mapPatternSchemaNames, Pattern.freeFvarNames]
    | fvar name => simp [mapPatternSchemaNames, Pattern.freeFvarNames]
    | apply constructor arguments =>
        simpa [mapPatternSchemaNames, Pattern.freeFvarNames] using
          mapPatternListSchemaNames_freeFvarNames mapName arguments
    | lambda binder body =>
        simpa [mapPatternSchemaNames, Pattern.freeFvarNames] using
          mapPatternSchemaNames_freeFvarNames mapName body
    | multiLambda arity binders body =>
        simpa [mapPatternSchemaNames, Pattern.freeFvarNames] using
          mapPatternSchemaNames_freeFvarNames mapName body
    | subst body replacement =>
        simp [mapPatternSchemaNames, Pattern.freeFvarNames,
          mapPatternSchemaNames_freeFvarNames mapName body,
          mapPatternSchemaNames_freeFvarNames mapName replacement,
          List.map_append]
    | collection collectionType elements rest =>
        have elementsEquality :=
          mapPatternListSchemaNames_freeFvarNames mapName elements
        cases rest <;>
          simp [mapPatternSchemaNames, Pattern.freeFvarNames,
            elementsEquality, List.map_append]

  /-- The free-name action extends pointwise over pattern lists. -/
  @[simp]
  theorem mapPatternListSchemaNames_freeFvarNames
      (mapName : String → String) (patterns : List Pattern) :
      (mapPatternListSchemaNames mapName patterns).flatMap
          Pattern.freeFvarNames =
        (patterns.flatMap Pattern.freeFvarNames).map mapName := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [mapPatternListSchemaNames,
          mapPatternSchemaNames_freeFvarNames mapName pattern,
          mapPatternListSchemaNames_freeFvarNames mapName patterns,
          List.map_append]
end

/-- Rename schema names throughout a one-hole context. -/
def mapOneHoleContextSchemaNames (mapName : String → String) :
    OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply constructor before inner after =>
      .apply constructor
        (mapPatternListSchemaNames mapName before)
        (mapOneHoleContextSchemaNames mapName inner)
        (mapPatternListSchemaNames mapName after)
  | .lambda binder inner =>
      .lambda (binder.map mapName)
        (mapOneHoleContextSchemaNames mapName inner)
  | .multiLambda arity binders inner =>
      .multiLambda arity (binders.map mapName)
        (mapOneHoleContextSchemaNames mapName inner)
  | .substBody inner replacement =>
      .substBody (mapOneHoleContextSchemaNames mapName inner)
        (mapPatternSchemaNames mapName replacement)
  | .substReplacement body inner =>
      .substReplacement (mapPatternSchemaNames mapName body)
        (mapOneHoleContextSchemaNames mapName inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType
        (mapPatternListSchemaNames mapName before)
        (mapOneHoleContextSchemaNames mapName inner)
        (mapPatternListSchemaNames mapName after) (rest.map mapName)

@[simp]
theorem mapOneHoleContextSchemaNames_fill (mapName : String → String)
    (context : OneHoleContext) (pattern : Pattern) :
    (mapOneHoleContextSchemaNames mapName context).fill
        (mapPatternSchemaNames mapName pattern) =
      mapPatternSchemaNames mapName (context.fill pattern) := by
  induction context <;>
    simp_all [mapOneHoleContextSchemaNames, mapPatternSchemaNames,
      mapPatternListSchemaNames, OneHoleContext.fill]

/-- Structural symbol transport and schema-local alpha-renaming commute on
one-hole contexts, just as they do on the patterns stored in each frame. -/
@[simp]
theorem mapOneHoleContext_mapOneHoleContextSchemaNames
    (symbols : LanguageDefSymbolMap) (mapName : String → String)
    (context : OneHoleContext) :
    CIGSLT.mapOneHoleContext symbols
        (mapOneHoleContextSchemaNames mapName context) =
      mapOneHoleContextSchemaNames mapName
        (CIGSLT.mapOneHoleContext symbols context) := by
  induction context <;>
    simp_all [CIGSLT.mapOneHoleContext, mapOneHoleContextSchemaNames,
      mapPattern_mapPatternSchemaNames,
      mapPatternList_mapPatternListSchemaNames]

/-- Schema alpha-renaming preserves the constructor-slot origin of a
one-hole context.  Binder display names may change; binder shape and every
constructor position remain fixed. -/
theorem SignatureContext.mapSchemaNames
    {language : LanguageDef} {sourceSort targetSort : String}
    {context : OneHoleContext}
    (mapName : String → String)
    (derived : SignatureContext language sourceSort targetSort context) :
    SignatureContext language sourceSort targetSort
      (mapOneHoleContextSchemaNames mapName context) := by
  induction derived with
  | hole => exact .hole _
  | simpleArg ruleMembership parameters beforeLength afterLength
      innerDerived inductionHypothesis =>
      apply SignatureContext.simpleArg ruleMembership parameters
      · simpa using beforeLength
      · simpa using afterLength
      · exact inductionHypothesis
  | abstractionArg ruleMembership parameters beforeLength afterLength
      innerDerived inductionHypothesis =>
      apply SignatureContext.abstractionArg ruleMembership parameters
      · simpa using beforeLength
      · simpa using afterLength
      · exact inductionHypothesis
  | collectionElement ruleMembership parameters innerDerived
      inductionHypothesis =>
      exact SignatureContext.collectionElement ruleMembership parameters
        inductionHypothesis

/-- Schema alpha-renaming preserves both constructor positions and the proof
that the hole path avoids the two selected continuation slots. -/
theorem ContinuationStableContext.mapSchemaNames
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {sourceSort targetSort : String} {context : OneHoleContext}
    (mapName : String → String)
    (stable : ContinuationStableContext cut sourceSort targetSort context) :
    ContinuationStableContext cut sourceSort targetSort
      (mapOneHoleContextSchemaNames mapName context) := by
  induction stable with
  | hole => exact .hole _
  | simpleArg ruleMembership parameters beforeLength afterLength notSelected
      innerStable inductionHypothesis =>
      apply ContinuationStableContext.simpleArg ruleMembership parameters
      · simpa using beforeLength
      · simpa using afterLength
      · exact notSelected
      · exact inductionHypothesis
  | abstractionArg ruleMembership parameters beforeLength afterLength
      notSelected innerStable inductionHypothesis =>
      apply ContinuationStableContext.abstractionArg ruleMembership parameters
      · simpa using beforeLength
      · simpa using afterLength
      · exact notSelected
      · exact inductionHypothesis
  | collectionElement ruleMembership parameters notSelected innerStable
      inductionHypothesis =>
      exact ContinuationStableContext.collectionElement ruleMembership
        parameters notSelected inductionHypothesis

@[simp]
theorem matchesParameterRepresentation_mapPatternSchemaNames_iff
    (mapName : String → String) (parameter : TermParam) (pattern : Pattern) :
    MatchesParameterRepresentation parameter
        (mapPatternSchemaNames mapName pattern) ↔
      MatchesParameterRepresentation parameter pattern := by
  cases parameter with
  | simple name type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation]
  | abstractionNamed binder name type =>
      cases pattern with
      | bvar index =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | fvar name =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | apply name arguments =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | lambda actualBinder body =>
          cases actualBinder <;>
            simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | multiLambda arity binders body =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | subst body replacement =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | collection collectionType elements rest =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
  | multiAbstractionNamed binders name type =>
      cases pattern with
      | bvar index =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | fvar name =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | apply name arguments =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | lambda binder body =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | multiLambda arity actualBinders body =>
          cases actualBinders with
          | nil =>
              simp [MatchesParameterRepresentation, mapPatternSchemaNames]
          | cons binder binders =>
              simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | subst body replacement =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]
      | collection collectionType elements rest =>
          simp [MatchesParameterRepresentation, mapPatternSchemaNames]

namespace WellSorted

mutual
  /-- Renaming rule-local schema variables preserves typing whenever the
  target free-variable context transports every source assignment. -/
  theorem HasType.mapSchemaNames
      {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (mapName : String → String)
      (mapsFree : ∀ name type,
        sourceFree name = some type → targetFree (mapName name) = some type)
      (typed : HasType language sourceFree bound pattern type) :
      HasType language targetFree bound
        (mapPatternSchemaNames mapName pattern) type := by
    cases typed with
    | @bvar bound index type lookup =>
        simpa [mapPatternSchemaNames] using
          (HasType.bvar (free := targetFree) lookup)
    | @fvar bound name type lookup =>
        simpa [mapPatternSchemaNames] using
          (HasType.fvar (bound := bound) (mapsFree name type lookup))
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.constructor membership notBare
            (argumentsTyped.mapSchemaNames mapName mapsFree))
    | @lambda bound binder body domain codomain bodyTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.lambda (bodyTyped.mapSchemaNames mapName mapsFree))
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.multiLambda (bodyTyped.mapSchemaNames mapName mapsFree))
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.subst
            (bodyTyped.mapSchemaNames mapName mapsFree)
            (replacementTyped.mapSchemaNames mapName mapsFree))
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.collection (rest := rest.map mapName)
            (elementsTyped.mapSchemaNames mapName mapsFree))
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simpa [mapPatternSchemaNames] using
          (HasType.collectionConstructor (rest := rest.map mapName)
            membership parameterShape
            (elementsTyped.mapSchemaNames mapName mapsFree))

  /-- Schema renaming preserves ordered constructor-argument typing. -/
  theorem ArgumentsHaveTypes.mapSchemaNames
      {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (mapName : String → String)
      (mapsFree : ∀ name type,
        sourceFree name = some type → targetFree (mapName name) = some type)
      (typed : ArgumentsHaveTypes language sourceFree bound
        arguments parameters) :
      ArgumentsHaveTypes language targetFree bound
        (mapPatternListSchemaNames mapName arguments) parameters := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        apply ArgumentsHaveTypes.cons
        · exact (matchesParameterRepresentation_mapPatternSchemaNames_iff
            mapName parameter argument).2 representation
        · exact parameterType
        · exact argumentTyped.mapSchemaNames mapName mapsFree
        · exact argumentsTyped.mapSchemaNames mapName mapsFree

  /-- Schema renaming preserves pointwise collection-element typing. -/
  theorem ElementsHaveType.mapSchemaNames
      {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (mapName : String → String)
      (mapsFree : ∀ name type,
        sourceFree name = some type → targetFree (mapName name) = some type)
      (typed : ElementsHaveType language sourceFree bound
        elements elementType) :
      ElementsHaveType language targetFree bound
        (mapPatternListSchemaNames mapName elements) elementType := by
    cases typed with
    | nil bound elementType => exact .nil bound elementType
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.mapSchemaNames mapName mapsFree)
          (elementsTyped.mapSchemaNames mapName mapsFree)
end

mutual
  /-- Extending a language's constructor declarations preserves typing.
  No equality, rewrite, or evaluator authority is involved in this weakening. -/
  theorem HasType.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : HasType sourceLanguage free bound pattern type) :
      HasType targetLanguage free bound pattern type := by
    cases typed with
    | @bvar bound index type lookup => exact .bvar lookup
    | @fvar bound name type lookup => exact .fvar lookup
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        exact .constructor (includes rule membership) notBare
          (argumentsTyped.weakenTerms includes)
    | @lambda bound binder body domain codomain bodyTyped =>
        exact .lambda (bodyTyped.weakenTerms includes)
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        exact .multiLambda (bodyTyped.weakenTerms includes)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        exact .subst (bodyTyped.weakenTerms includes)
          (replacementTyped.weakenTerms includes)
    | @collection bound collectionType elements rest elementType elementsTyped =>
        exact .collection (elementsTyped.weakenTerms includes)
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        exact .collectionConstructor (includes rule membership) parameterShape
          (elementsTyped.weakenTerms includes)

  theorem ArgumentsHaveTypes.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : ArgumentsHaveTypes sourceLanguage free bound
        arguments parameters) :
      ArgumentsHaveTypes targetLanguage free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        exact .cons representation parameterType
          (argumentTyped.weakenTerms includes)
          (argumentsTyped.weakenTerms includes)

  theorem ElementsHaveType.weakenTerms
      {sourceLanguage targetLanguage : LanguageDef}
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (includes : ∀ rule, rule ∈ sourceLanguage.terms →
        rule ∈ targetLanguage.terms)
      (typed : ElementsHaveType sourceLanguage free bound
        elements elementType) :
      ElementsHaveType targetLanguage free bound elements elementType := by
    cases typed with
    | nil bound elementType => exact .nil bound elementType
    | cons elementTyped elementsTyped =>
        exact .cons (elementTyped.weakenTerms includes)
          (elementsTyped.weakenTerms includes)
end

end WellSorted

namespace CIGSLT

/-- Administrative variable carrying the signature consumed by the generated
rule.  Its namespace is disjoint from every transported source variable. -/
def costSignatureVariable (_source : CIGSLT) : String :=
  costAdministrativeSchemaName "signature"

/-- Administrative variable carrying the unconsumed token-stack tail. -/
def costStackTailVariable (_source : CIGSLT) : String :=
  costAdministrativeSchemaName "stack-tail"

theorem costSourceSchemaName_ne_signature (source : CIGSLT) (name : String) :
    costSourceSchemaName name ≠ source.costSignatureVariable := by
  exact costSourceSchemaName_ne_administrative name "signature"

theorem costSourceSchemaName_ne_stackTail (source : CIGSLT) (name : String) :
    costSourceSchemaName name ≠ source.costStackTailVariable := by
  exact costSourceSchemaName_ne_administrative name "stack-tail"

theorem costSignatureVariable_ne_stackTail (source : CIGSLT) :
    source.costSignatureVariable ≠ source.costStackTailVariable := by
  intro equality
  have listEquality := congrArg String.toList equality
  simp [costSignatureVariable, costStackTailVariable,
    costAdministrativeSchemaName, costAdministrativeSchemaTag] at listEquality

/-- Retype the selected source rewrite context exactly as the generated base
constructors retype their two continuation positions. -/
def costRetypedSourceContext (source : CIGSLT) : List (String × TypeExpr) :=
  source.theory.presentation.interactionRewrite.1.typeContext.map fun entry =>
    (costSourceSchemaName entry.1,
      if entry.1 = source.cut.program.continuationVariable.name ∨
        entry.1 = source.cut.environment.continuationVariable.name then
        costWrappedTypeExpr
          source.theory.presentation.interactingSort.1.name entry.2
      else
        costBaseTypeExpr entry.2)

/-- Complete type context of the whole-redex Cost rule. -/
def costWholeRedexTypeContext (source : CIGSLT) :
    List (String × TypeExpr) :=
  source.costRetypedSourceContext ++
    [(source.costSignatureVariable, .base costSignatureSortName),
      (source.costStackTailVariable, .base costTokenStackSortName)]

/-- The exact ordered interaction core in the tagged base namespace. -/
def costBaseInteractionCore (source : CIGSLT) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (mapPattern costBaseLanguageDefSymbolMap source.cut.sourceShape.core)

/-- The source cut's pre-existing envelope, transported to the base copy. -/
def costBaseSourceEnvelope (source : CIGSLT) : OneHoleContext :=
  mapOneHoleContextSchemaNames costSourceSchemaName
    (mapOneHoleContext costBaseLanguageDefSymbolMap
      source.cut.sourceShape.envelope)

/-- The wrapped contractum with all source schema names transported into the
reserved Cost namespace. -/
def costMappedContractum (source : CIGSLT) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (source.continuationRetyping.mapContractum
      source.theory.presentation.interactionRewrite.1.right)

/-- Administrative envelope that signs the complete base redex and pairs it
with a funding stack whose head carries the same signature. -/
def costFundingEnvelope (source : CIGSLT) : OneHoleContext :=
  .apply costContactConstructorName []
    (.apply costSignedConstructorName [] .hole
      [.fvar source.costSignatureVariable])
    [.apply costFundingConstructorName
      [.apply costTokenStackConsConstructorName
        [.fvar source.costSignatureVariable,
          .fvar source.costStackTailVariable]]]

/-- Compose the administrative funding envelope with any envelope already
authored around the source interaction core. -/
def costWholeRedexEnvelope (source : CIGSLT) : OneHoleContext :=
  source.costFundingEnvelope.comp source.costBaseSourceEnvelope

/-- Left side of the generated whole-redex funded interaction. -/
def costWholeRedexSource (source : CIGSLT) : Pattern :=
  source.costWholeRedexEnvelope.fill source.costBaseInteractionCore

/-- Right side of the generated interaction: the wrapped source contractum
and the unconsumed funding tail remain under the explicit wrapped contact. -/
def costWholeRedexTarget (source : CIGSLT) : Pattern :=
  .apply costContactConstructorName
    [source.costMappedContractum,
      .apply costFundingConstructorName
        [.fvar source.costStackTailVariable]]

/-- The generic whole-redex rule schema.  It has no callback or host-side
premise: reduction authority is ordinary authored rewrite data. -/
def costWholeRedexRewrite (source : CIGSLT) : RewriteRule where
  name := costWholeRedexRewriteName
  typeContext := source.costWholeRedexTypeContext
  premises := []
  left := source.costWholeRedexSource
  right := source.costWholeRedexTarget

@[simp]
theorem costBaseSourceEnvelope_fill (source : CIGSLT) :
    source.costBaseSourceEnvelope.fill source.costBaseInteractionCore =
      mapPatternSchemaNames costSourceSchemaName
        (mapPattern costBaseLanguageDefSymbolMap
          source.theory.presentation.interactionRewrite.1.left) := by
  rw [costBaseSourceEnvelope, costBaseInteractionCore,
    mapOneHoleContextSchemaNames_fill, mapOneHoleContext_fill,
    source.cut.sourceShape.fillsSource]

/-- Positive shape control: the generated source is exactly one explicit
wrapped contact between a signed source redex and a matching funded stack. -/
theorem costWholeRedexSource_eq (source : CIGSLT) :
    source.costWholeRedexSource =
      .apply costContactConstructorName
        [.apply costSignedConstructorName
          [mapPatternSchemaNames costSourceSchemaName
            (mapPattern costBaseLanguageDefSymbolMap
              source.theory.presentation.interactionRewrite.1.left),
            .fvar source.costSignatureVariable],
          .apply costFundingConstructorName
            [.apply costTokenStackConsConstructorName
              [.fvar source.costSignatureVariable,
                .fvar source.costStackTailVariable]]] := by
  rw [costWholeRedexSource, costWholeRedexEnvelope,
    OneHoleContext.fill_comp, costBaseSourceEnvelope_fill]
  rfl

/-- The generated rule carries the exact tail variable through unchanged;
there is no rule that creates a replacement token. -/
theorem costWholeRedexTarget_funding_tail (source : CIGSLT) :
    source.costWholeRedexTarget =
      .apply costContactConstructorName
        [source.costMappedContractum,
          .apply costFundingConstructorName
            [.fvar source.costStackTailVariable]] :=
  rfl

namespace Morphism

/-- Transport of the source interaction core commutes with its embedding in
the collision-free Cost base namespace. -/
theorem map_costBaseInteractionCore {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costBaseInteractionCore =
      target.costBaseInteractionCore := by
  rw [costBaseInteractionCore, costBaseInteractionCore,
    mapPattern_mapPatternSchemaNames,
    mapPattern_costBasePresentation_natural,
    morphism.mapsCorePattern]

/-- Transport of the source cut envelope commutes with both the base-fibre
embedding and the collision-free schema-name action. -/
theorem map_costBaseSourceEnvelope {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOneHoleContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costBaseSourceEnvelope =
      target.costBaseSourceEnvelope := by
  rw [costBaseSourceEnvelope, costBaseSourceEnvelope,
    mapOneHoleContext_mapOneHoleContextSchemaNames,
    CIGSLT.mapOneHoleContext_costBasePresentation_natural,
    morphism.mapsSourceEnvelope]

/-- The signing and funding frames contain only fixed Cost apparatus
constructors and administrative variables. -/
theorem map_costFundingEnvelope {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOneHoleContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costFundingEnvelope =
      target.costFundingEnvelope := by
  simp [costFundingEnvelope, mapOneHoleContext, mapPattern,
    costContactConstructorName, costSignedConstructorName,
    costFundingConstructorName, costTokenStackConsConstructorName,
    costSignatureVariable, costStackTailVariable]

/-- The complete generated redex envelope is natural as a composition of
the fixed administrative envelope and the transported source envelope. -/
theorem map_costWholeRedexEnvelope {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapOneHoleContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costWholeRedexEnvelope =
      target.costWholeRedexEnvelope := by
  rw [costWholeRedexEnvelope, costWholeRedexEnvelope,
    CIGSLT.mapOneHoleContext_contextComp,
    morphism.map_costFundingEnvelope,
    morphism.map_costBaseSourceEnvelope]

/-- Retyping the selected rewrite context commutes with a continued theory
map.  The two continuation-variable names are structural invariants, while
their types follow the wrapped/base type naturality squares. -/
theorem map_costRetypedSourceContext {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapTypeContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costRetypedSourceContext =
      target.costRetypedSourceContext := by
  rw [costRetypedSourceContext, costRetypedSourceContext,
    ← morphism.mapsInteractionRewriteTypeContext]
  simp only [mapTypeContext, List.map_map]
  apply List.map_congr_left
  intro entry _membership
  rcases entry with ⟨name, type⟩
  rw [← morphism.mapsProgramContinuationVariableName,
    ← morphism.mapsEnvironmentContinuationVariableName]
  by_cases selected :
      name = source.cut.program.continuationVariable.name ∨
        name = source.cut.environment.continuationVariable.name
  · simp [selected,
      mapTypeExpr_costWrappedTypeExpr
        morphism.underlying.structural.structural.symbols
        source.theory.presentation.interactingSort.1.name
        target.theory.presentation.interactingSort.1.name
        morphism.mapsInteractingSortName morphism.reflectsInteractingSort]
  · simp [selected, mapTypeExpr_costBaseTypeExpr]

/-- The hereditary wrapped contractum, including collision-free schema
renaming, is natural in continued theory maps. -/
theorem map_costMappedContractum {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costMappedContractum =
      target.costMappedContractum := by
  unfold costMappedContractum
  rw [mapPattern_mapPatternSchemaNames, morphism.mapContractum_natural,
    morphism.mapsInteractionRewriteRight]

/-- The complete generated schema context, including the two fixed
administrative variables, is natural in continued theory maps. -/
theorem map_costWholeRedexTypeContext {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapTypeContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costWholeRedexTypeContext =
      target.costWholeRedexTypeContext := by
  rw [costWholeRedexTypeContext, costWholeRedexTypeContext]
  rw [show
    mapTypeContext
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        (source.costRetypedSourceContext ++
          [(source.costSignatureVariable, .base costSignatureSortName),
            (source.costStackTailVariable, .base costTokenStackSortName)]) =
      mapTypeContext
          (costLanguageDefSymbolMap
            morphism.underlying.structural.structural.symbols)
          source.costRetypedSourceContext ++
        mapTypeContext
          (costLanguageDefSymbolMap
            morphism.underlying.structural.structural.symbols)
          [(source.costSignatureVariable, .base costSignatureSortName),
            (source.costStackTailVariable, .base costTokenStackSortName)] by
      simp [mapTypeContext]]
  rw [morphism.map_costRetypedSourceContext]
  simp [mapTypeContext, mapTypeExpr, costSignatureSortName,
    costTokenStackSortName, costSignatureVariable,
    costStackTailVariable]

/-- The funded source schema is natural: its only non-administrative payload
is the exact mapped source interaction rewrite. -/
theorem map_costWholeRedexSource {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costWholeRedexSource =
      target.costWholeRedexSource := by
  rw [source.costWholeRedexSource_eq, target.costWholeRedexSource_eq]
  simp [mapPattern, costSignedConstructorName,
    costFundingConstructorName, costTokenStackConsConstructorName,
    costContactConstructorName, mapPattern_mapPatternSchemaNames,
    morphism.mapsInteractionRewriteLeft, costSignatureVariable,
    costStackTailVariable]

/-- The funded target schema is natural; the funding tail is unchanged and
the hereditary contractum follows `mapContractum_natural`. -/
theorem map_costWholeRedexTarget {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costWholeRedexTarget =
      target.costWholeRedexTarget := by
  simp [costWholeRedexTarget, mapPattern, costFundingConstructorName,
    costContactConstructorName, morphism.map_costMappedContractum,
    costStackTailVariable]

/-- The single generated funded rewrite is transported exactly. -/
theorem map_costWholeRedexRewrite {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapRewriteRule
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        source.costWholeRedexRewrite =
      target.costWholeRedexRewrite := by
  simp only [mapRewriteRule, costWholeRedexRewrite, List.map_nil]
  rw [morphism.map_costWholeRedexTypeContext,
    morphism.map_costWholeRedexSource,
    morphism.map_costWholeRedexTarget]
  rfl

end Morphism

end CIGSLT

end Mettapedia.GSLT.LanguageDef
