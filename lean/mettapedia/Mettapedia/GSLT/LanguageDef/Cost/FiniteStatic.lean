import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionValidation
import Mettapedia.GSLT.LanguageDef.StructuralCoproduct

/-!
# Static equations over finite continuation decoration

The finite generator uses the existing base and wrapped equation maps. Each
copy must remain well sorted after the actual positional retyping. Validation
is derived from these sorting judgments, source binding availability, and the
generated namespaces; equation admission is not an assumed closure field.

The output retains the selected funded interaction and all source equations.
Coverage of other source rewrite rules is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism WellSorted

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

def costStaticEquations (_profile : ContinuationDecorationProfile cut) : List Equation :=
  theory.presentation.presentation.language.equations.map costBaseEquationDecl ++
    theory.presentation.presentation.language.equations.map (costWrappedEquationDecl theory)

def costWholeLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.costCoreLanguage with
    name := "$cost:interaction:" ++ theory.presentation.presentation.language.name
    equations := profile.costStaticEquations
    rewrites := [profile.costWholeRedexRewrite] }

/-- Intermediate host for the existing unrenamed equation images. -/
def reflectiveRetypingLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.generatedLanguage with equations :=
      theory.presentation.presentation.language.equations.map costBaseEquation ++
      theory.presentation.presentation.language.equations.map (costWrappedEquation theory) }

theorem ofRetypingPlan_costWholeLanguage (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeLanguage =
      source.costWholeLanguage := by
  unfold costWholeLanguage CIGSLT.costWholeLanguage
  rw [ofRetypingPlan_costCoreLanguage, ofRetypingPlan_costWholeRedexRewrite]
  rfl

theorem ofRetypingPlan_reflectiveRetypingLanguage {sourceTheory : IGSLT}
    {sourceCut : InteractionCutPresentation sourceTheory}
    (plan : ContinuationRetypingPlan sourceCut) :
    (ofRetypingPlan plan).reflectiveRetypingLanguage =
      Mettapedia.GSLT.LanguageDef.reflectiveRetypingLanguage plan := by
  unfold reflectiveRetypingLanguage Mettapedia.GSLT.LanguageDef.reflectiveRetypingLanguage
  rw [ofRetypingPlan_generatedLanguage]

theorem costStaticEquationNames_nodup (profile : ContinuationDecorationProfile cut) :
    (profile.costStaticEquations.map (·.name)).Nodup := by
  rw [costStaticEquations, List.map_append, List.map_map, List.map_map, List.nodup_append]
  have sourceNodup := LanguageDef.equationNames_nodup_of_validate_eq_nil
    theory.presentation.presentation.language theory.presentation.presentation.valid
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using sourceNodup.map costBaseEquationName_injective
  · simpa [Function.comp_def] using sourceNodup.map costWrappedEquationName_injective
  · intro baseName baseMember wrappedName wrappedMember same
    obtain ⟨baseEquation, _, rfl⟩ := List.mem_map.mp baseMember
    obtain ⟨wrappedEquation, _, rfl⟩ := List.mem_map.mp wrappedMember
    exact costBaseEquationName_ne_wrapped _ _ same

theorem generatedTerms_mem_costWhole (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (member : term ∈ profile.generatedLanguage.terms) :
    term ∈ profile.costWholeLanguage.terms := List.mem_append_left _ member

theorem generatedTypeNames_mem_costWhole (profile : ContinuationDecorationProfile cut)
    (name : String) (member : name ∈ profile.generatedLanguage.typeNames) :
    name ∈ profile.costWholeLanguage.typeNames := by
  change name ∈ profile.costCoreLanguage.typeNames
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ member

private theorem sourceName_not_constructor (profile : ContinuationDecorationProfile cut)
    (name : String) :
    costSourceSchemaName name ∉ profile.costWholeLanguage.terms.map (·.label) := by
  intro member
  obtain ⟨term, declared, same⟩ := List.mem_map.mp member
  obtain ⟨suffix, prefixed⟩ := profile.costCoreTerm_label_has_costPrefix term declared
  exact CIGSLT.costSourceSchemaName_ne_costPrefix name suffix (same.symm.trans prefixed)

/-- One common validation argument serves both static colors. It accepts
sorting evidence for the computed image, never its desired validator result. -/
theorem mappedEquation_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (symbols : LanguageDefSymbolMap)
    (sortsDeclared : ∀ name ∈ theory.presentation.presentation.language.typeNames,
      symbols.sort name ∈ profile.costWholeLanguage.typeNames)
    (equation : Equation)
    (member : equation ∈ theory.presentation.presentation.language.equations)
    (premiseFree : equation.premises = [])
    (sorted : EquationWellSorted profile.generatedLanguage (mapEquation symbols equation)) :
    profile.costWholeLanguage.validateEquation
      (mapEquationSchemaNames costSourceSchemaName (mapEquation symbols equation)) = [] := by
  have transported := sorted.mapSchemaNames_weakenTerms
    profile.generatedTerms_mem_costWhole costSourceSchemaName costSourceSchemaName_injective
  obtain ⟨type, leftTyped, rightTyped⟩ := transported
  have labels := LanguageDef.constructorLabels_nodup_of_validate_eq_nil
    profile.costCoreLanguage (profile.costCoreLanguage_validate noDuplicates)
  have patterns : LanguageDef.validateRulePatterns
      s!"equation {(mapEquation symbols equation).name}"
      (profile.costWholeLanguage.terms.map (·.label))
      (mapTypeContextSchemaNames costSourceSchemaName (mapTypeContext symbols equation.typeContext)) []
      (mapPatternSchemaNames costSourceSchemaName (mapPattern symbols equation.left))
      (mapPatternSchemaNames costSourceSchemaName (mapPattern symbols equation.right)) = [] := by
    apply validateRulePatterns_noPremises_eq_nil
    · simpa [Pattern.isWellScoped, mapEquation] using leftTyped.isWellScopedAt
    · simpa [Pattern.isWellScoped, mapEquation] using rightTyped.isWellScopedAt
    · intro name membership
      have combined := List.mem_eraseDups.mp membership
      rw [patternFvarNames_nil, patternFvarNames_nil,
        mapPatternSchemaNames_freeFvarNames, mapPatternSchemaNames_freeFvarNames,
        mapPattern_freeFvarNames, mapPattern_freeFvarNames, ← List.map_append] at combined
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp combined
      exact profile.sourceName_not_constructor original
    · intro name membership
      have combined := List.mem_eraseDups.mp membership
      rw [mapPatternSchemaNames_patternBinderNames, mapPatternSchemaNames_patternBinderNames,
        mapPattern_patternBinderNames, mapPattern_patternBinderNames, ← List.map_append] at combined
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp combined
      exact profile.sourceName_not_constructor original
    · intro entry membership
      simp only [mapTypeContextSchemaNames, mapTypeContext, List.map_map, List.mem_map] at membership
      obtain ⟨original, _, rfl⟩ := membership
      exact profile.sourceName_not_constructor original.1
    · intro name rightMember
      have raw := List.mem_eraseDups.mp rightMember
      rw [patternFvarNames_nil, mapPatternSchemaNames_freeFvarNames,
        mapPattern_freeFvarNames] at raw
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp raw
      have leftMember := rightFvar_mem_left_of_validatedEquation_noPremises
        theory.presentation.presentation.language theory.presentation.presentation.valid
        equation member premiseFree original (by simpa [patternFvarNames_nil] using originalMember)
      rw [patternFvarNames_nil, mapPatternSchemaNames_freeFvarNames, mapPattern_freeFvarNames]
      exact List.mem_map.mpr ⟨original, by simpa [patternFvarNames_nil] using leftMember, rfl⟩
  unfold LanguageDef.validateEquation
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · constructor
    · apply List.flatMap_eq_nil_iff.mpr
      intro entry entryMember
      apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
      intro name nameMember
      simp only [mapEquationSchemaNames, mapEquation, mapTypeContextSchemaNames,
        mapTypeContext, List.map_map, List.mem_map] at entryMember
      obtain ⟨original, originalMember, rfl⟩ := entryMember
      change name ∈ (mapTypeExpr symbols original.2).baseNames at nameMember
      rw [StructuralCoproduct.mapTypeExpr_baseNames] at nameMember
      obtain ⟨originalName, originalNameMember, rfl⟩ := List.mem_map.mp nameMember
      exact sortsDeclared originalName (equationTypeContext_baseName_mem_of_validate_eq_nil
        theory.presentation.presentation.language theory.presentation.presentation.valid
        equation member original originalMember originalName originalNameMember)
    · simp [mapEquationSchemaNames, mapEquation, premiseFree]
  · exact leftTyped.validatePatternConstructors_eq_nil labels _
  · exact rightTyped.validatePatternConstructors_eq_nil labels _
  · simp [mapEquationSchemaNames, mapEquation, premiseFree]
  · simpa [mapEquationSchemaNames, mapEquation, premiseFree] using patterns

theorem costStaticEquation_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (premiseFree : ∀ equation ∈ theory.presentation.presentation.language.equations,
      equation.premises = [])
    (baseSorted : ∀ equation ∈ theory.presentation.presentation.language.equations,
      EquationWellSorted profile.generatedLanguage (costBaseEquation equation))
    (wrappedSorted : ∀ equation ∈ theory.presentation.presentation.language.equations,
      EquationWellSorted profile.generatedLanguage (costWrappedEquation theory equation))
    (equation : Equation) (member : equation ∈ profile.costStaticEquations) :
    profile.costWholeLanguage.validateEquation equation = [] := by
  rcases List.mem_append.mp member with base | wrapped
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp base
    apply profile.mappedEquation_validate noDuplicates costBaseStaticSymbols _ original originalMember
      (premiseFree original originalMember) (baseSorted original originalMember)
    intro name nameMember
    exact profile.generatedTypeNames_mem_costWhole _
      (profile.costBaseSortName_mem_generated nameMember)
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp wrapped
    apply profile.mappedEquation_validate noDuplicates (costWrappedStaticSymbols theory) _
      original originalMember (premiseFree original originalMember) (wrappedSorted original originalMember)
    intro name nameMember
    apply profile.generatedTypeNames_mem_costWhole
    change (if name = theory.presentation.interactingSort.1.name then
      costWrappedSortName else costBaseSortName name) ∈ profile.generatedLanguage.typeNames
    split
    · exact profile.costWrappedSortName_mem_generated
    · exact profile.costBaseSortName_mem_generated nameMember

theorem costWholeLanguage_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable)
    (premiseFree : ∀ equation ∈ theory.presentation.presentation.language.equations,
      equation.premises = [])
    (baseSorted : ∀ equation ∈ theory.presentation.presentation.language.equations,
      EquationWellSorted profile.generatedLanguage (costBaseEquation equation))
    (wrappedSorted : ∀ equation ∈ theory.presentation.presentation.language.equations,
      EquationWellSorted profile.generatedLanguage (costWrappedEquation theory equation)) :
    profile.costWholeLanguage.validate = [] := by
  have coreValid := profile.costCoreLanguage_validate noDuplicates
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil profile.costCoreLanguage coreValid
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil profile.costCoreLanguage coreValid
  · exact profile.costStaticEquationNames_nodup
  · exact List.nodup_singleton _
  · intro term member
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _ coreValid term member
  · exact profile.costStaticEquation_validate noDuplicates premiseFree baseSorted wrappedSorted
  · intro rule member
    obtain rfl := List.mem_singleton.mp member
    exact profile.costWholeRedexRewrite_validate noDuplicates redexTyped contractumTyped

/-- Every admitted former two-slot input satisfies the generalized static
gate by its existing equation typing evidence. -/
theorem ofRetypingPlan_costWholeLanguage_validate (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costWholeLanguage.validate = [] := by
  apply costWholeLanguage_validate _ source.continuationRetyping.noDuplicates
    ((ofRetypingPlan_redexRetypable_iff _).mpr source.redexRetypable)
    ((ofRetypingPlan_wrappable_iff _).mpr source.wrappable)
  · exact fun equation member => (source.equationsRetypable equation member).premiseFree
  · intro equation member
    rw [ofRetypingPlan_generatedLanguage]
    exact (source.equationsRetypable equation member).baseWellSorted
  · intro equation member
    rw [ofRetypingPlan_generatedLanguage]
    exact (source.equationsRetypable equation member).wrappedWellSorted

#print axioms costWholeLanguage_validate
#print axioms ofRetypingPlan_costWholeLanguage_validate

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
