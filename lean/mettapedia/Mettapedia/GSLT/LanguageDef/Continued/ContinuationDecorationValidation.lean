import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecoration

/-!
# Validation of finite continuation signatures

The finite decoration profile already retains the authored constructors and
the selected continuation positions.  Its generated signature is valid
exactly when its constructor closure contains no duplicate declarations.
No hereditary closure or iteration property is assumed by this criterion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open ContinuationRetypingPlan
open StructuralMorphism

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

@[simp]
theorem generatedLanguage_typeNames (profile : ContinuationDecorationProfile cut) :
    profile.generatedLanguage.typeNames =
      theory.presentation.presentation.language.typeNames.map costBaseSortName ++
        [costWrappedSortName] := by
  change (((theory.presentation.presentation.language.types.map fun (declaration : TypeDecl) =>
    { declaration with name := costBaseSortName declaration.name }) ++
    [TypeDecl.plain costWrappedSortName]).map TypeDecl.name) = _
  rw [List.map_append, List.map_map]
  simp only [LanguageDef.typeNames, List.map_map]
  rfl

theorem generatedTypeNames_nodup (profile : ContinuationDecorationProfile cut) :
    profile.generatedLanguage.typeNames.Nodup := by
  rw [generatedLanguage_typeNames, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · exact (LanguageDef.typeNames_nodup_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid).map costBaseSortName_injective
  · intro generated generatedMember reserved reservedMember
    simp only [List.mem_singleton] at reservedMember
    subst reserved
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp generatedMember
    exact costBaseSortName_ne_wrapped source

theorem generatedLanguage_constructorLabels (profile : ContinuationDecorationProfile cut) :
    profile.generatedLanguage.terms.map (·.label) =
      (theory.presentation.presentation.language.terms.map (·.label)).map
          costBaseConstructorName ++
        profile.wrappedLabels.map costWrappedConstructorName := by
  change ((theory.presentation.presentation.language.terms.map profile.baseConstructor ++
    profile.constructorClosure.map
      (fun constructor => costWrappedConstructor (theory := theory) constructor.1)).map
        (·.label)) = _
  rw [List.map_append]
  simp only [wrappedLabels, List.map_map]
  rfl

theorem generatedConstructorLabels_nodup (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) :
    (profile.generatedLanguage.terms.map (·.label)).Nodup := by
  rw [generatedLanguage_constructorLabels, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      theory.presentation.presentation.language
      theory.presentation.presentation.valid).map costBaseConstructorName_injective
  · exact (noDuplicates.map
      (authoredConstructorLabel_injective theory.presentation.presentation)).map
        costWrappedConstructorName_injective
  · intro base baseMember wrapped wrappedMember
    obtain ⟨sourceBase, _, rfl⟩ := List.mem_map.mp baseMember
    obtain ⟨sourceWrapped, _, rfl⟩ := List.mem_map.mp wrappedMember
    exact costBaseConstructorName_ne_wrapped sourceBase sourceWrapped

theorem costBaseSortName_mem_generated (profile : ContinuationDecorationProfile cut)
    {sort : String} (member : sort ∈ theory.presentation.presentation.language.typeNames) :
    costBaseSortName sort ∈ profile.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨sort, member, rfl⟩)

theorem costWrappedSortName_mem_generated (profile : ContinuationDecorationProfile cut) :
    costWrappedSortName ∈ profile.generatedLanguage.typeNames := by
  rw [generatedLanguage_typeNames]
  simp

theorem generatedTerm_category_mem (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (member : term ∈ profile.generatedLanguage.terms) :
    term.category ∈ profile.generatedLanguage.typeNames := by
  rcases List.mem_append.mp member with base | wrapped
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp base
    exact profile.costBaseSortName_mem_generated
      (LanguageDef.termCategory_mem_of_validate_eq_nil _
        theory.presentation.presentation.valid source sourceMember)
  · obtain ⟨source, _, rfl⟩ := List.mem_map.mp wrapped
    change (if source.1.category = theory.presentation.interactingSort.1.name
      then costWrappedSortName else costBaseSortName source.1.category) ∈ _
    split
    · exact profile.costWrappedSortName_mem_generated
    · exact profile.costBaseSortName_mem_generated
        (LanguageDef.termCategory_mem_of_validate_eq_nil _
          theory.presentation.presentation.valid source.1 source.2)

private theorem mappedParameter_baseName_mem
    (profile : ContinuationDecorationProfile cut) (source : GrammarRule)
    (sourceMember : source ∈ theory.presentation.presentation.language.terms)
    (parameter : TermParam) (parameterMember : parameter ∈ source.params)
    (wrapped : Bool) (name : String)
    (nameMember : name ∈ (TermParam.typeExpr
      (mapParameterType
        (if wrapped then costWrappedTypeExpr theory.presentation.interactingSort.1.name
          else costBaseTypeExpr) parameter)).baseNames) :
    name ∈ profile.generatedLanguage.typeNames := by
  have sourceNameDeclared (sourceName : String)
      (member : sourceName ∈ parameter.typeExpr.baseNames) :
      sourceName ∈ theory.presentation.presentation.language.typeNames :=
    LanguageDef.termParam_baseName_mem_of_validate_eq_nil _
      theory.presentation.presentation.valid source sourceMember parameter parameterMember
      sourceName member
  cases wrapped with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, mapParameterType_typeExpr,
        costBaseTypeExpr_baseNames] at nameMember
      obtain ⟨sourceName, sourceNameMember, rfl⟩ := List.mem_map.mp nameMember
      exact profile.costBaseSortName_mem_generated
        (sourceNameDeclared sourceName sourceNameMember)
  | true =>
      simp only [↓reduceIte, mapParameterType_typeExpr,
        costWrappedTypeExpr_baseNames] at nameMember
      obtain ⟨sourceName, sourceNameMember, rfl⟩ := List.mem_map.mp nameMember
      split
      · exact profile.costWrappedSortName_mem_generated
      · exact profile.costBaseSortName_mem_generated
          (sourceNameDeclared sourceName sourceNameMember)

theorem generatedTerm_parameter_baseName_mem (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (termMember : term ∈ profile.generatedLanguage.terms)
    (parameter : TermParam) (parameterMember : parameter ∈ term.params)
    (name : String) (nameMember : name ∈ parameter.typeExpr.baseNames) :
    name ∈ profile.generatedLanguage.typeNames := by
  rcases List.mem_append.mp termMember with base | wrapped
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp base
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp parameterMember
    apply mappedParameter_baseName_mem profile source sourceMember entry.1
      (List.fst_mem_of_mem_zipIdx entryMember)
      (profile.selectedParameter source entry.2) name
    by_cases selected : profile.selectedParameter source entry.2 = true <;>
      simpa only [baseParameter, selected, Bool.false_eq_true, ↓reduceIte] using nameMember
  · obtain ⟨source, _, rfl⟩ := List.mem_map.mp wrapped
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp parameterMember
    exact mappedParameter_baseName_mem profile source.1 source.2 original originalMember
      true name nameMember

theorem generatedTerm_syntaxPattern_eq_nil (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (member : term ∈ profile.generatedLanguage.terms) :
    term.syntaxPattern = [] := by
  rcases List.mem_append.mp member with base | wrapped
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp base
    rfl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp wrapped
    rfl

/-- Every finite continuation selection has a valid generated signature when
its retained constructor closure has no duplicate declarations. -/
theorem generatedLanguage_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) :
    profile.generatedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · exact profile.generatedTypeNames_nodup
  · exact profile.generatedConstructorLabels_nodup noDuplicates
  · exact profile.generatedTerm_category_mem
  · exact profile.generatedTerm_parameter_baseName_mem
  · intro term member
    exact Or.inl (profile.generatedTerm_syntaxPattern_eq_nil term member)

/-- Duplicate closure declarations are exactly the validation obstruction;
neither continuation multiplicity nor rebuilt introductions are excluded. -/
theorem generatedLanguage_validate_iff (profile : ContinuationDecorationProfile cut) :
    profile.generatedLanguage.validate = [] ↔ profile.constructorClosure.Nodup := by
  constructor
  · intro valid
    have labels := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ valid
    rw [generatedLanguage_constructorLabels] at labels
    exact ((List.nodup_append.mp labels).2.1.of_map _).of_map _
  · exact profile.generatedLanguage_validate

/-- The validated signature is derived from the retained finite profile. -/
def generatedPresentation (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) : ValidatedLanguageDef where
  language := profile.generatedLanguage
  valid := profile.generatedLanguage_validate noDuplicates

/-- A source constructor's tagged base label resolves uniquely in the
generated signature. -/
theorem baseConstructor_filter_generated (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) (constructor : GrammarRule)
    (membership : constructor ∈ theory.presentation.presentation.language.terms) :
    profile.generatedLanguage.terms.filter
        (fun candidate => candidate.label == (profile.baseConstructor constructor).label) =
      [profile.baseConstructor constructor] :=
  LanguageDef.filter_terms_by_label_eq_singleton
    profile.generatedLanguage.terms (profile.baseConstructor constructor)
    (profile.generatedConstructorLabels_nodup noDuplicates)
    (profile.baseConstructor_mem constructor membership)

/-- A closure constructor's wrapped label resolves uniquely in the generated
signature. -/
theorem wrappedConstructor_filter_generated (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (constructor : DeclaredConstructor theory.presentation.presentation)
    (membership : constructor ∈ profile.constructorClosure) :
    profile.generatedLanguage.terms.filter
        (fun candidate => candidate.label ==
          (costWrappedConstructor (theory := theory) constructor.1).label) =
      [costWrappedConstructor (theory := theory) constructor.1] :=
  LanguageDef.filter_terms_by_label_eq_singleton
    profile.generatedLanguage.terms
    (costWrappedConstructor (theory := theory) constructor.1)
    (profile.generatedConstructorLabels_nodup noDuplicates)
    (profile.wrappedConstructor_mem constructor membership)

/-- Repeating an authored constructor in the closure is rejected, even though
each copy separately carries valid declaration-membership evidence. -/
theorem duplicateClosure_rejected (profile : ContinuationDecorationProfile cut)
    (constructor : DeclaredConstructor theory.presentation.presentation) :
    ({ profile with constructorClosure := constructor :: constructor ::
        profile.constructorClosure }.generatedLanguage).validate ≠ [] := by
  intro valid
  have noDuplicates := (generatedLanguage_validate_iff _).mp valid
  simp at noDuplicates

end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile
