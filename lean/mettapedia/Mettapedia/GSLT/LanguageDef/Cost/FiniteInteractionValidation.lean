import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteraction
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Validation of the finite selected-cut Cost language

The generated funded rule passes the ordinary language validator from the
actual finite profile's redex and contractum typing.  Schema hygiene follows
from the disjoint generated namespaces, and output-variable availability
follows from the validated premise-free authored cut.

The result validates the selected operational fragment.  It does not install
the source's static equations or reflective rule annotations, prove coverage
of its other rules, or supply a canonical section for another Cost iteration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism WellSorted
open RewriteValidationCertificate

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

theorem costCoreTerm_label_has_costPrefix (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (member : term ∈ profile.costCoreLanguage.terms) :
    ∃ suffix, term.label = "$cost:" ++ suffix := by
  rcases List.mem_append.mp member with generated | apparatus
  · rcases List.mem_append.mp generated with base | wrapped
    · obtain ⟨source, _, rfl⟩ := List.mem_map.mp base
      refine ⟨"base-constructor:" ++ source.label, ?_⟩
      change "$cost:base-constructor:" ++ source.label = _
      rw [show "$cost:base-constructor:" = "$cost:" ++ "base-constructor:" by decide,
        String.append_assoc]
    · obtain ⟨source, _, rfl⟩ := List.mem_map.mp wrapped
      refine ⟨"wrapped-constructor:" ++ source.1.label, ?_⟩
      change "$cost:wrapped-constructor:" ++ source.1.label = _
      rw [show "$cost:wrapped-constructor:" = "$cost:" ++ "wrapped-constructor:" by decide,
        String.append_assoc]
  · have labels : term.label ∈
        (costCoreConstructors theory.presentation.interactingSort.1.name).map (·.label) :=
      List.mem_map.mpr ⟨term, apparatus, rfl⟩
    change term.label ∈ costCoreConstructorSuffixes.map costApparatusConstructorName at labels
    obtain ⟨suffix, _, same⟩ := List.mem_map.mp labels
    refine ⟨"apparatus-constructor:" ++ suffix, same.symm.trans ?_⟩
    change "$cost:apparatus-constructor:" ++ suffix = _
    rw [show "$cost:apparatus-constructor:" = "$cost:" ++ "apparatus-constructor:" by decide,
      String.append_assoc]

private theorem generatedName_not_constructor (profile : ContinuationDecorationProfile cut)
    (name : String)
    (generated : (∃ original, name = costSourceSchemaName original) ∨
      ∃ administrative, name = costAdministrativeSchemaName administrative) :
    name ∉ profile.costWholeRedexLanguage.terms.map (·.label) := by
  intro member
  obtain ⟨term, termMember, same⟩ := List.mem_map.mp member
  obtain ⟨suffix, prefixed⟩ := profile.costCoreTerm_label_has_costPrefix term termMember
  have namePrefix : name = "$cost:" ++ suffix := same.symm.trans prefixed
  rcases generated with ⟨original, rfl⟩ | ⟨administrative, rfl⟩
  · exact CIGSLT.costSourceSchemaName_ne_costPrefix original suffix namePrefix
  · exact CIGSLT.costAdministrativeSchemaName_ne_costPrefix administrative suffix namePrefix

@[simp]
theorem costWholeRedexSource_freeFvarNames (profile : ContinuationDecorationProfile cut) :
    profile.costWholeRedexSource.freeFvarNames =
      theory.presentation.interactionRewrite.1.left.freeFvarNames.map costSourceSchemaName ++
        [costAdministrativeSchemaName "signature", costAdministrativeSchemaName "signature",
          costAdministrativeSchemaName "stack-tail"] := by
  simp [costWholeRedexSource, costMappedRedex, Pattern.freeFvarNames]

@[simp]
theorem costWholeRedexTarget_freeFvarNames (profile : ContinuationDecorationProfile cut) :
    profile.costWholeRedexTarget.freeFvarNames =
      theory.presentation.interactionRewrite.1.right.freeFvarNames.map costSourceSchemaName ++
        [costAdministrativeSchemaName "stack-tail"] := by
  simp [costWholeRedexTarget, costMappedContractum, mapContractum, Pattern.freeFvarNames]

@[simp]
theorem costWholeRedexSource_patternBinderNames (profile : ContinuationDecorationProfile cut) :
    LanguageDef.patternBinderNames profile.costWholeRedexSource =
      (LanguageDef.patternBinderNames theory.presentation.interactionRewrite.1.left).map
        costSourceSchemaName := by
  simp [costWholeRedexSource, costMappedRedex, LanguageDef.patternBinderNames]

@[simp]
theorem costWholeRedexTarget_patternBinderNames (profile : ContinuationDecorationProfile cut) :
    LanguageDef.patternBinderNames profile.costWholeRedexTarget =
      (LanguageDef.patternBinderNames theory.presentation.interactionRewrite.1.right).map
        costSourceSchemaName := by
  simp [costWholeRedexTarget, costMappedContractum, mapContractum,
    LanguageDef.patternBinderNames]

private theorem fvars_generated (profile : ContinuationDecorationProfile cut) (name : String)
    (member : name ∈ (LanguageDef.patternFvarNames [] profile.costWholeRedexSource ++
      LanguageDef.patternFvarNames [] profile.costWholeRedexTarget).eraseDups) :
    (∃ original, name = costSourceSchemaName original) ∨
      ∃ administrative, name = costAdministrativeSchemaName administrative := by
  have combined := List.mem_eraseDups.mp member
  rw [patternFvarNames_nil, patternFvarNames_nil,
    costWholeRedexSource_freeFvarNames, costWholeRedexTarget_freeFvarNames] at combined
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at combined
  rcases combined with (⟨original, _, same⟩ | same | same | same) |
    ⟨original, _, same⟩ | same
  · exact Or.inl ⟨original, same.symm⟩
  · exact Or.inr ⟨"signature", same⟩
  · exact Or.inr ⟨"signature", same⟩
  · exact Or.inr ⟨"stack-tail", same⟩
  · exact Or.inl ⟨original, same.symm⟩
  · exact Or.inr ⟨"stack-tail", same⟩

private theorem binders_generated (profile : ContinuationDecorationProfile cut) (name : String)
    (member : name ∈ (LanguageDef.patternBinderNames profile.costWholeRedexSource ++
      LanguageDef.patternBinderNames profile.costWholeRedexTarget).eraseDups) :
    ∃ original, name = costSourceSchemaName original := by
  have combined := List.mem_eraseDups.mp member
  rw [costWholeRedexSource_patternBinderNames, costWholeRedexTarget_patternBinderNames]
    at combined
  rcases List.mem_append.mp combined with left | right
  · obtain ⟨original, _, same⟩ := List.mem_map.mp left
    exact ⟨original, same.symm⟩
  · obtain ⟨original, _, same⟩ := List.mem_map.mp right
    exact ⟨original, same.symm⟩

private theorem contextName_generated (profile : ContinuationDecorationProfile cut)
    (entry : String × TypeExpr) (member : entry ∈ profile.costWholeRedexTypeContext) :
    (∃ original, entry.1 = costSourceSchemaName original) ∨
      ∃ administrative, entry.1 = costAdministrativeSchemaName administrative := by
  rcases List.mem_append.mp member with source | administrative
  · obtain ⟨original, _, rfl⟩ := List.mem_map.mp source
    exact Or.inl ⟨original.1, rfl⟩
  · rcases List.mem_cons.mp administrative with rfl | tail
    · exact Or.inr ⟨"signature", rfl⟩
    · obtain rfl := List.mem_singleton.mp tail
      exact Or.inr ⟨"stack-tail", rfl⟩

/-- The source's validated premise-free cut supplies every variable used by
the decorated contractum. Administrative stack tails also occur on the left. -/
theorem costWholeRedex_rightFvar_mem_left (profile : ContinuationDecorationProfile cut)
    (name : String) (member : name ∈ profile.costWholeRedexTarget.freeFvarNames) :
    name ∈ profile.costWholeRedexSource.freeFvarNames := by
  rw [costWholeRedexTarget_freeFvarNames] at member
  rcases List.mem_append.mp member with source | administrative
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp source
    have sourceClean := validateRulePatterns_eq_nil_of_validateRewrite_eq_nil _ _
      (validateRewrite_eq_nil_of_validate_eq_nil _ theory.presentation.presentation.valid
        theory.presentation.interactionRewrite.1 cut.interactionRewrite_mem)
    rw [cut.interactionPremisesEmpty] at sourceClean
    have available := rightFvar_mem_left_of_validateRulePatterns_noPremises_eq_nil
      _ _ _ _ _ sourceClean original (by simpa only [patternFvarNames_nil] using originalMember)
    rw [costWholeRedexSource_freeFvarNames]
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨original, by simpa only [patternFvarNames_nil] using available, rfl⟩)
  · obtain rfl := List.mem_singleton.mp administrative
    rw [costWholeRedexSource_freeFvarNames]
    exact List.mem_append_right _ (by simp)

private theorem retypedType_baseName_mem (profile : ContinuationDecorationProfile cut)
    (type : TypeExpr)
    (known : ∀ name ∈ type.baseNames, name ∈ theory.presentation.presentation.language.typeNames)
    (wrapped : Bool) (name : String)
    (member : name ∈ (if wrapped then
      costWrappedTypeExpr theory.presentation.interactingSort.1.name type
        else costBaseTypeExpr type).baseNames) :
    name ∈ profile.costWholeRedexLanguage.typeNames := by
  change name ∈ profile.costCoreLanguage.typeNames
  rw [costCoreLanguage_typeNames]
  apply List.mem_append_left
  cases wrapped with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, costBaseTypeExpr_baseNames] at member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact profile.costBaseSortName_mem_generated (known original originalMember)
  | true =>
      simp only [↓reduceIte, costWrappedTypeExpr_baseNames] at member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      split
      · exact profile.costWrappedSortName_mem_generated
      · exact profile.costBaseSortName_mem_generated (known original originalMember)

theorem costWholeRedexTypeContext_baseName_mem (profile : ContinuationDecorationProfile cut)
    (entry : String × TypeExpr) (entryMember : entry ∈ profile.costWholeRedexTypeContext)
    (name : String) (member : name ∈ entry.2.baseNames) :
    name ∈ profile.costWholeRedexLanguage.typeNames := by
  rcases List.mem_append.mp entryMember with source | administrative
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp source
    exact retypedType_baseName_mem profile original.2
      (rewriteTypeContext_baseName_mem_of_validate_eq_nil _
        theory.presentation.presentation.valid theory.presentation.interactionRewrite.1
        cut.interactionRewrite_mem original originalMember)
      (profile.selectedVariable original.1) name member
  · rcases List.mem_cons.mp administrative with rfl | tail
    · obtain rfl := List.mem_singleton.mp member
      exact profile.signature_mem_costCoreLanguage
    · obtain rfl := List.mem_singleton.mp tail
      obtain rfl := List.mem_singleton.mp member
      exact profile.stack_mem_costCoreLanguage

/-- The proof certificate is built from the actual generated schema, rather
than accepting its validation as another field of the continuation profile. -/
theorem costWholeRedexRewrite_certificate (profile : ContinuationDecorationProfile cut)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable) :
    Certificate profile.costWholeRedexLanguage profile.costWholeRedexRewrite where
  contextTypes := profile.costWholeRedexTypeContext_baseName_mem
  premiseTypes := by intro type member; cases member
  leftDeclared := by
    intro reference member
    obtain ⟨rule, declared, label, arity⟩ :=
      (profile.costWholeRedexSource_hasType redexTyped).constructorReferencesDeclared reference member
    exact List.mem_map.mpr ⟨rule, declared, Prod.ext label arity⟩
  rightDeclared := by
    intro reference member
    obtain ⟨rule, declared, label, arity⟩ :=
      (profile.costWholeRedexTarget_hasType contractumTyped).constructorReferencesDeclared reference member
    exact List.mem_map.mpr ⟨rule, declared, Prod.ext label arity⟩
  premisesDeclared := by intro pattern member; cases member
  allPatternsScoped := by
    have left : profile.costWholeRedexSource.isWellScoped = true := by
      simpa only [Pattern.isWellScoped, List.length_nil] using
        (profile.costWholeRedexSource_hasType redexTyped).isWellScopedAt
    have right : profile.costWholeRedexTarget.isWellScoped = true := by
      simpa only [Pattern.isWellScoped, List.length_nil] using
        (profile.costWholeRedexTarget_hasType contractumTyped).isWellScopedAt
    change (profile.costWholeRedexSource.isWellScoped &&
      profile.costWholeRedexTarget.isWellScoped && true) = true
    rw [left, right]
    rfl
  fvarsAvoidConstructors := by
    intro name member
    apply generatedName_not_constructor profile name
    apply fvars_generated profile name
    simpa only [costWholeRedexRewrite, List.flatMap_nil, List.append_nil] using member
  bindersAvoidConstructors := by
    intro name member
    apply generatedName_not_constructor profile name
    apply Or.inl
    apply binders_generated profile name
    simpa only [costWholeRedexRewrite, List.flatMap_nil, List.append_nil] using member
  contextAvoidsConstructors := fun entry member =>
    generatedName_not_constructor profile entry.1 (contextName_generated profile entry member)
  rightBound := by
    intro name member
    change name ∈ LanguageDef.patternFvarNames [] profile.costWholeRedexSource ++ []
    rw [List.append_nil, patternFvarNames_nil]
    apply profile.costWholeRedex_rightFvar_mem_left
    simpa only [costWholeRedexRewrite, List.mem_eraseDups, patternFvarNames_nil] using member

theorem costWholeRedexRewrite_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable) :
    profile.costWholeRedexLanguage.validateRewrite profile.costWholeRedexRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil profile.costCoreLanguage
      (profile.costCoreLanguage_validate noDuplicates))
    (profile.costWholeRedexRewrite_certificate redexTyped contractumTyped)

private theorem costCoreTerm_syntaxPattern_eq_nil (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule) (member : term ∈ profile.costCoreLanguage.terms) :
    term.syntaxPattern = [] := by
  rcases List.mem_append.mp member with generated | apparatus
  · exact profile.generatedTerm_syntaxPattern_eq_nil term generated
  · simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false] at apparatus
    rcases apparatus with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The exact selected-cut language validates at the ordinary public gate.
Other source rules and reflective annotations remain separate obligations. -/
theorem costWholeRedexLanguage_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable) :
    profile.costWholeRedexLanguage.validate = [] := by
  have coreValid := profile.costCoreLanguage_validate noDuplicates
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil profile.costCoreLanguage coreValid
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil profile.costCoreLanguage coreValid
  · exact List.nodup_singleton _
  · exact LanguageDef.termCategory_mem_of_validate_eq_nil profile.costCoreLanguage coreValid
  · exact LanguageDef.termParam_baseName_mem_of_validate_eq_nil profile.costCoreLanguage coreValid
  · intro term member
    exact Or.inl (costCoreTerm_syntaxPattern_eq_nil profile term member)
  · intro rule member
    obtain rfl := List.mem_singleton.mp member
    exact profile.costWholeRedexRewrite_validate noDuplicates redexTyped contractumTyped

/-- A validated selected-cut operational fragment, derived without requiring
the stronger continued-theory or iteration interface. -/
def costWholeRedexPresentation (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable) :
    ValidatedLanguageDef where
  language := profile.costWholeRedexLanguage
  valid := profile.costWholeRedexLanguage_validate noDuplicates redexTyped contractumTyped

#print axioms costWholeRedexRewrite_validate
#print axioms costWholeRedexLanguage_validate

end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile
