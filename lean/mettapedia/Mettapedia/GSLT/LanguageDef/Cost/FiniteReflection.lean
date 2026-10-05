import Mettapedia.GSLT.LanguageDef.Cost.FiniteStatic

/-!
# Reflection transport over finite continuation decoration

Reflection remains an explicit admitted profile over the generated language.
The declaration maps and selected-cut filter are the existing Cost maps.
Constructor and equation witnesses are transported through signature
extension and schema renaming; a finite profile does not acquire reflection
merely by having an ordinary well-sorted funded rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open StructuralMorphism ReflectionExtension

namespace ReflectiveWitnessTransport

/-- Transport the existing validator witness through a signature inclusion
and a name-preserving equation map that retains the quote/drop shape. -/
def extend {source target : LanguageDef} {declaration : ReflectivePresentationDecl}
    (types : ∀ name ∈ source.typeNames, name ∈ target.typeNames)
    (terms : ∀ term ∈ source.terms, term ∈ target.terms)
    (labelsNodup : (target.terms.map (·.label)).Nodup)
    (equationNamesNodup : (target.equations.map (·.name)).Nodup)
    (mapEquation : Equation → Equation)
    (equationNames : ∀ equation, (mapEquation equation).name = equation.name)
    (equations : ∀ equation ∈ source.equations, mapEquation equation ∈ target.equations)
    (shape : ∀ equation, LanguageDef.QuoteDropShape declaration equation →
      LanguageDef.QuoteDropShape declaration (mapEquation equation))
    (witness : LanguageDef.ReflectivePresentationWitness source declaration) :
    LanguageDef.ReflectivePresentationWitness target declaration := by
  have termUnique (term : GrammarRule) (name : String)
      (unique : source.terms.filter (fun term => term.label == name) = [term]) :
      target.terms.filter (fun term => term.label == name) = [term] := by
    have selected : term ∈ source.terms.filter (fun term => term.label == name) := by
      rw [unique]; exact List.mem_singleton_self _
    have named := beq_iff_eq.mp (List.mem_filter.mp selected).2
    simpa only [named] using LanguageDef.filter_terms_by_label_eq_singleton
      target.terms term labelsNodup (terms term (List.mem_filter.mp selected).1)
  have selected : witness.equation ∈ source.equations.filter
      (fun equation => equation.name == declaration.quoteDropEquation) := by
    rw [witness.equationUnique]; exact List.mem_singleton_self _
  have named := beq_iff_eq.mp (List.mem_filter.mp selected).2
  refine {
    quote := witness.quote
    drop := witness.drop
    unit := witness.unit
    equation := mapEquation witness.equation
    quoteParameter := witness.quoteParameter
    dropParameter := witness.dropParameter
    processSort := types _ witness.processSort
    nameSort := types _ witness.nameSort
    sortsDistinct := witness.sortsDistinct
    quoteUnique := termUnique _ _ witness.quoteUnique
    quoteCategory := witness.quoteCategory
    quoteParameters := witness.quoteParameters
    dropUnique := termUnique _ _ witness.dropUnique
    dropCategory := witness.dropCategory
    dropParameters := witness.dropParameters
    unitUnique := termUnique _ _ witness.unitUnique
    unitCategory := witness.unitCategory
    unitParameters := witness.unitParameters
    equationUnique := ?_
    equationShape := shape _ witness.equationShape }
  simpa only [equationNames, named] using LanguageDef.filter_equations_by_name_eq_singleton
    target.equations (mapEquation witness.equation) equationNamesNodup
    (equations _ (List.mem_filter.mp selected).1)

end ReflectiveWitnessTransport

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

theorem costStaticReflectivePresentationNames_nodup (profile : ContinuationDecorationProfile cut)
    (reflection : AdmittedProfile theory.presentation.presentation.language) :
    ((profile.costStaticReflectivePresentations reflection.1).map (·.name)).Nodup := by
  rw [costStaticReflectivePresentations, List.map_append, List.map_map,
    List.map_map, List.nodup_append]
  have sourceNodup := presentationNames_nodup_of_validate_eq_nil reflection.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def, costBaseReflectivePresentationDecl,
      costBaseStaticSymbols, costBaseStaticReflectiveSymbols, mapReflectivePresentation] using
      sourceNodup.map costBaseReflectiveName_injective
  · simpa [Function.comp_def, costWrappedReflectivePresentationDecl,
      costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols, mapReflectivePresentation] using
      sourceNodup.map costWrappedReflectiveName_injective
  · intro baseName baseMember wrappedName wrappedMember same
    obtain ⟨baseDeclaration, _, rfl⟩ := List.mem_map.mp baseMember
    obtain ⟨wrappedDeclaration, _, rfl⟩ := List.mem_map.mp wrappedMember
    exact costBaseReflectiveName_ne_wrapped _ _ same

theorem costInteractionReflectiveRuleNames_nodup (profile : ContinuationDecorationProfile cut)
    (reflection : AdmittedProfile theory.presentation.presentation.language) :
    ((profile.costInteractionReflectiveRules reflection.1).map (·.name)).Nodup := by
  have sourceNodup := ruleNames_nodup_of_validate_eq_nil reflection.2
  have selectedSublist : (reflection.1.rules.filter fun declaration =>
      declaration.rewriteRule == theory.presentation.interactionRewrite.1.name).Sublist
      reflection.1.rules := List.filter_sublist
  have filtered := selectedSublist.map (fun declaration => declaration.name)
  have names := sourceNodup.sublist filtered
  unfold costInteractionReflectiveRules
  rw [List.map_map]
  simpa [Function.comp_def, CIGSLT.costInteractionReflectiveRuleDecl] using
    names.map costBaseReflectiveRuleName_injective

/-- The concrete intermediate witness retains its declaration choices after
the apparatus extension and the existing source-variable namespace map. -/
def extendReflectiveWitness (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) (declaration : ReflectivePresentationDecl)
    (witness : LanguageDef.ReflectivePresentationWitness
      profile.reflectiveRetypingLanguage declaration) :
    LanguageDef.ReflectivePresentationWitness profile.costWholeLanguage declaration :=
  ReflectiveWitnessTransport.extend (source := profile.reflectiveRetypingLanguage)
    profile.generatedTypeNames_mem_costWhole
    profile.generatedTerms_mem_costWhole
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil profile.costCoreLanguage
      (profile.costCoreLanguage_validate noDuplicates))
    profile.costStaticEquationNames_nodup
    (mapEquationSchemaNames costSourceSchemaName) (fun _ => rfl)
    (by
      intro equation member
      rcases List.mem_append.mp member with base | wrapped
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
        exact List.mem_append_left _ (List.mem_map.mpr ⟨original, originalMember, rfl⟩)
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp wrapped
        exact List.mem_append_right _ (List.mem_map.mpr ⟨original, originalMember, rfl⟩))
    (quoteDropShape_mapEquationSchemaNames costSourceSchemaName declaration) witness

theorem costInteractionReflectiveRule_validate (profile : ContinuationDecorationProfile cut)
    (reflection : AdmittedProfile theory.presentation.presentation.language)
    (declaration : ReflectiveRuleDecl)
    (member : declaration ∈ profile.costInteractionReflectiveRules reflection.1) :
    profile.costWholeLanguage.validateReflectiveRule
      (profile.costStaticReflectivePresentations reflection.1) declaration = [] := by
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  have originalValid := rule_validate_eq_nil_of_validate_eq_nil reflection.2
    (List.mem_filter.mp selected).1
  obtain ⟨witness⟩ := LanguageDef.reflectiveRuleWitness_of_validate_eq_nil
    theory.presentation.presentation.language reflection.1.presentations original originalValid
  have matchingSelected : witness.matchingPresentation ∈ reflection.1.presentations.filter
      (fun candidate => candidate.name == original.matchingPresentation) := by
    rw [witness.matchingUnique]; exact List.mem_singleton_self _
  have substitutionSelected : witness.substitutionPresentation ∈ reflection.1.presentations.filter
      (fun candidate => candidate.name == original.substitutionPresentation) := by
    rw [witness.substitutionUnique]; exact List.mem_singleton_self _
  have matchingName := beq_iff_eq.mp (List.mem_filter.mp matchingSelected).2
  have substitutionName := beq_iff_eq.mp (List.mem_filter.mp substitutionSelected).2
  have names := profile.costStaticReflectivePresentationNames_nodup reflection
  apply LanguageDef.ReflectiveRuleWitness.validate
    (witness := {
      rewrite := profile.costWholeRedexRewrite
      matchingPresentation := costBaseReflectivePresentationDecl witness.matchingPresentation
      substitutionPresentation := costWrappedReflectivePresentationDecl theory witness.substitutionPresentation
      rewriteUnique := by
        change [profile.costWholeRedexRewrite].filter _ = _
        simp [costWholeRedexRewrite, CIGSLT.costInteractionReflectiveRuleDecl]
      matchingUnique := ?_
      substitutionUnique := ?_ })
  · have unique := LanguageDef.filter_by_string_key_eq_singleton
      (fun candidate : ReflectivePresentationDecl => candidate.name)
      (profile.costStaticReflectivePresentations reflection.1)
      (costBaseReflectivePresentationDecl witness.matchingPresentation) names
      (List.mem_append_left _ (List.mem_map.mpr
        ⟨witness.matchingPresentation, (List.mem_filter.mp matchingSelected).1, rfl⟩))
    simpa [costBaseReflectivePresentationDecl, mapReflectivePresentation,
      costBaseStaticReflectiveSymbols, CIGSLT.costInteractionReflectiveRuleDecl, matchingName] using unique
  · have unique := LanguageDef.filter_by_string_key_eq_singleton
      (fun candidate : ReflectivePresentationDecl => candidate.name)
      (profile.costStaticReflectivePresentations reflection.1)
      (costWrappedReflectivePresentationDecl theory witness.substitutionPresentation) names
      (List.mem_append_right _ (List.mem_map.mpr
        ⟨witness.substitutionPresentation, (List.mem_filter.mp substitutionSelected).1, rfl⟩))
    simpa [costWrappedReflectivePresentationDecl, mapReflectivePresentation,
      costWrappedStaticReflectiveSymbols, CIGSLT.costInteractionReflectiveRuleDecl,
      substitutionName] using unique

/-- Generated reflection is admitted from the existing concrete validator
witnesses for the two retyped static presentations. -/
theorem costWholeReflectionProfile_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (reflection : AdmittedProfile theory.presentation.presentation.language)
    (retyped : ∀ declaration ∈ reflection.1.presentations,
      Nonempty (LanguageDef.ReflectivePresentationWitness profile.reflectiveRetypingLanguage
        (costBaseReflectivePresentationDecl declaration)) ∧
      Nonempty (LanguageDef.ReflectivePresentationWitness profile.reflectiveRetypingLanguage
        (costWrappedReflectivePresentationDecl theory declaration))) :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate profile.costWholeLanguage
      (profile.costWholeReflectionProfile reflection.1) = [] := by
  unfold Mettapedia.OSLF.MeTTaIL.Reflection.validate
  simp only [costWholeReflectionProfile,
    profile.costStaticReflectivePresentationNames_nodup reflection,
    profile.costInteractionReflectiveRuleNames_nodup reflection, if_true,
    List.nil_append, List.append_eq_nil_iff]
  constructor
  · apply List.flatMap_eq_nil_iff.mpr
    intro declaration member
    rcases List.mem_append.mp member with base | wrapped
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
      obtain ⟨witness⟩ := (retyped original originalMember).1
      exact (profile.extendReflectiveWitness noDuplicates _ witness).validate
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp wrapped
      obtain ⟨witness⟩ := (retyped original originalMember).2
      exact (profile.extendReflectiveWitness noDuplicates _ witness).validate
  · apply List.flatMap_eq_nil_iff.mpr
    exact profile.costInteractionReflectiveRule_validate reflection

end ContinuationDecorationProfile

/-! ## The two-slot case

The whole language of a wrappable theory is the one of its two-slot profile.
What the theory stores (the sorted redex and contractum, the retyped equations
and reflective presentations) supplies the hypotheses of the general theorems.
-/

namespace WrappableIGSLT

open ContinuationDecorationProfile (ofRetypingPlan)
open ContinuationRetypingPlan WellSorted

theorem lookup_costRetypedSourceContext (source : WrappableIGSLT) (name : String) :
    lookupTypeContext source.costRetypedSourceContext
        (costSourceSchemaName name) =
      source.continuationRetyping.generatedFreeContext name :=
  (ofRetypingPlan source.continuationRetyping).lookup_costRetypedSourceContext name

theorem costWholeRedexFreeContext_source (source : WrappableIGSLT)
    (name : String) (type : TypeExpr)
    (lookup : source.continuationRetyping.generatedFreeContext name =
      some type) :
    source.costWholeRedexFreeContext (costSourceSchemaName name) =
      some type :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexFreeContext_source name type
    lookup

@[simp]
theorem costWholeRedexFreeContext_signature (source : WrappableIGSLT) :
    source.costWholeRedexFreeContext source.costSignatureVariable =
      some (.base costSignatureSortName) :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexFreeContext_signature

@[simp]
theorem costWholeRedexFreeContext_stackTail (source : WrappableIGSLT) :
    source.costWholeRedexFreeContext source.costStackTailVariable =
      some (.base costTokenStackSortName) :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexFreeContext_stackTail

theorem costWholeRedexSource_hasType (source : WrappableIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      source.costWholeRedexSource costWrappedSortName :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexSource_hasType
    source.redexRetypable

theorem costWholeRedexTarget_hasType (source : WrappableIGSLT) :
    HasSort source.costCoreLanguage source.costWholeRedexFreeContext []
      source.costWholeRedexTarget costWrappedSortName :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexTarget_hasType
    source.wrappable

@[simp]
theorem costWholeRedexTarget_freeFvarNames (source : WrappableIGSLT) :
    source.costWholeRedexTarget.freeFvarNames =
      source.theory.presentation.interactionRewrite.1.right.freeFvarNames.map
          costSourceSchemaName ++
        [source.costStackTailVariable] :=
  (ofRetypingPlan source.continuationRetyping).costWholeRedexTarget_freeFvarNames

/-- The source's validated premise-free cut supplies every variable used by
the generated contractum. -/
theorem costWholeRedex_rightFvar_mem_left (source : WrappableIGSLT)
    (name : String)
    (membership :
      name ∈ LanguageDef.patternFvarNames [] source.costWholeRedexTarget) :
    name ∈ LanguageDef.patternFvarNames [] source.costWholeRedexSource := by
  rw [patternFvarNames_nil] at membership ⊢
  exact (ofRetypingPlan source.continuationRetyping).costWholeRedex_rightFvar_mem_left
    name membership

/-- Every tagged base or wrapped presentation in the generated static theory
passes the final language's exact reflective validator. -/
theorem costStaticReflectivePresentation_validate (source : WrappableIGSLT)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈ source.costStaticReflectivePresentations) :
    source.costWholeLanguage.validateReflectivePresentation declaration = [] := by
  rcases List.mem_append.mp membership with base | wrapped
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
    obtain ⟨witness⟩ := LanguageDef.reflectivePresentationWitness_of_validate_eq_nil _ _
      (source.reflectivePresentationsRetypable original originalMember).1
    exact ((ofRetypingPlan source.continuationRetyping).extendReflectiveWitness
      source.continuationRetyping.noDuplicates _ witness).validate
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp wrapped
    obtain ⟨witness⟩ := LanguageDef.reflectivePresentationWitness_of_validate_eq_nil _ _
      (source.reflectivePresentationsRetypable original originalMember).2
    exact ((ofRetypingPlan source.continuationRetyping).extendReflectiveWitness
      source.continuationRetyping.noDuplicates _ witness).validate

/-- The generic Cost interaction is an ordinary validated language
presentation: its only reduction authority is the generated whole-redex
rewrite over the already validated Cost signature. -/
theorem costWholeLanguage_validate (source : WrappableIGSLT) :
    source.costWholeLanguage.validate = [] :=
  (ofRetypingPlan source.continuationRetyping).costWholeLanguage_validate
    source.continuationRetyping.noDuplicates source.redexRetypable source.wrappable
    (fun equation member => (source.equationsRetypable equation member).premiseFree)
    (fun equation member => (source.equationsRetypable equation member).baseWellSorted)
    (fun equation member => (source.equationsRetypable equation member).wrappedWellSorted)

/-- The generated reflective interpretation validates independently against
the generated five-field Cost language. -/
theorem costWholeReflectionProfile_validate (source : WrappableIGSLT) :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate source.costWholeLanguage
      source.costWholeReflectionProfile = [] :=
  (ofRetypingPlan source.continuationRetyping).costWholeReflectionProfile_validate
    source.continuationRetyping.noDuplicates source.reflection
    (fun declaration member =>
      ⟨LanguageDef.reflectivePresentationWitness_of_validate_eq_nil _ _
          (source.reflectivePresentationsRetypable declaration member).1,
        LanguageDef.reflectivePresentationWitness_of_validate_eq_nil _ _
          (source.reflectivePresentationsRetypable declaration member).2⟩)

/-- The admitted reflection fibre over the generated Cost core. -/
def costWholeAdmittedReflection (source : WrappableIGSLT) :
    ReflectionExtension.AdmittedProfile source.costWholeLanguage :=
  ⟨source.costWholeReflectionProfile,
    source.costWholeReflectionProfile_validate⟩

/-- The validated structural output of the generic Cost interaction layer. -/
def costWholePresentation (source : WrappableIGSLT) : ValidatedLanguageDef where
  language := source.costWholeLanguage
  valid := source.costWholeLanguage_validate

namespace Morphism

/-- A morphism of wrappable theories carries the complete generated Cost
presentation structurally: inherited and apparatus declarations follow the
Cost-core map, static equations follow the authored source equations, and the
single funded interaction follows the selected continuation cut. -/
def costWholeStructural {source target : WrappableIGSLT}
    (morphism : source.Morphism target) :
    StructuralMorphism source.costWholePresentation
      target.costWholePresentation where
  symbols := costLanguageDefSymbolMap
    morphism.underlying.structural.structural.symbols
  mapsTypes declaration membership := by
    change List.Mem declaration source.costCoreLanguage.types at membership
    change List.Mem (mapTypeDecl
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        declaration) target.costCoreLanguage.types
    exact morphism.costCoreStructural.mapsTypes declaration membership
  mapsTerms constructor membership := by
    change List.Mem constructor source.costCoreLanguage.terms at membership
    change List.Mem (mapGrammarRule
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        constructor) target.costCoreLanguage.terms
    exact morphism.costCoreStructural.mapsTerms constructor membership
  mapsEquations equation membership := by
    change List.Mem equation source.costStaticEquations at membership
    change List.Mem (mapEquation
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        equation) target.costStaticEquations
    exact morphism.mapsCostStaticEquations equation membership
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [source.costWholeRedexRewrite] at membership
    change List.Mem (mapRewriteRule
        (costLanguageDefSymbolMap
          morphism.underlying.structural.structural.symbols)
        rewrite) [target.costWholeRedexRewrite]
    cases membership with
    | head =>
        rw [morphism.map_costWholeRedexRewrite]
        exact List.Mem.head _
    | tail _ impossible => cases impossible

end Morphism

/-- The complete declaration-derived Cost presentation is functorial on
wrappable theories. No section is read. -/
def costWholeFunctor : CategoryTheory.Functor WrappableIGSLT ValidatedLanguageDef where
  obj source := source.costWholePresentation
  map morphism := morphism.costWholeStructural
  map_id source := by
    apply StructuralMorphism.ext
    exact costLanguageDefSymbolMap_id
  map_comp first second := by
    apply StructuralMorphism.ext
    exact costLanguageDefSymbolMap_comp
      first.underlying.structural.structural.symbols
      second.underlying.structural.structural.symbols

end WrappableIGSLT

namespace CIGSLT

/-- The complete declaration-derived Cost presentation is functorial on
continued interactive theories: forget the section, then apply the functor on
wrappable theories. -/
def costWholeFunctor : CategoryTheory.Functor CIGSLT ValidatedLanguageDef :=
  toWrappable.comp WrappableIGSLT.costWholeFunctor

end CIGSLT

end Mettapedia.GSLT.LanguageDef
