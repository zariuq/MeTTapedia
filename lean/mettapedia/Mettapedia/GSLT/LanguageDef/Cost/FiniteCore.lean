import Mettapedia.GSLT.LanguageDef.CostInteraction
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationValidation
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension

/-!
# Cost apparatus over finite continuation bundles

The existing signature, signing, stack and funding constructors extend the
declaration-derived continuation signature for an arbitrary finite bundle.
No canonical section or iteration closure is needed to build this signature.
The former two-slot construction is recovered by its exact profile comparison.

Validation of this signature does not assert that its terms carry linear
authority, or that every well-sorted term is an executable funded program.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

set_option autoImplicit false

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Append the existing Cost apparatus to the exact finite continuation
signature, retaining every selected operand parameter. -/
def costCoreLanguage (profile : ContinuationDecorationProfile cut) : LanguageDef :=
  { profile.generatedLanguage with
    name := "$cost:core:" ++ theory.presentation.presentation.language.name
    types := profile.generatedLanguage.types ++ costCoreTypes
    terms := profile.generatedLanguage.terms ++
      costCoreConstructors theory.presentation.interactingSort.1.name }

theorem costCoreLanguage_typeNames (profile : ContinuationDecorationProfile cut) :
    profile.costCoreLanguage.typeNames = profile.generatedLanguage.typeNames ++
      costCoreSortSuffixes.map costApparatusSortName := by
  simp [costCoreLanguage, costCoreTypes, LanguageDef.typeNames,
    TypeDecl.plain, List.map_map]

/-- The finite-bundle extension uses exactly the apparatus of the existing
Cost construction when no additional continuation is selected. -/
theorem ofRetypingPlan_costCoreLanguage (source : CIGSLT) :
    (ofRetypingPlan source.continuationRetyping).costCoreLanguage =
      source.costCoreLanguage := by
  unfold costCoreLanguage CIGSLT.costCoreLanguage
  rw [ofRetypingPlan_generatedLanguage]

/-- Extending the signature does not alter the types of its already
decorated constructors. -/
theorem hasType_costCoreLanguage (profile : ContinuationDecorationProfile cut)
    {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {type : TypeExpr}
    (typed : HasType profile.generatedLanguage free bound term type) :
    HasType profile.costCoreLanguage free bound term type := by
  exact typed.weakenTerms (fun _ membership => List.mem_append_left _ membership)

theorem signature_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costSignatureSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costSignatureSortName])

theorem key_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costKeySortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costKeySortName])

theorem stack_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costTokenStackSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_right _ (by simp [costCoreSortSuffixes, costTokenStackSortName])

theorem wrapped_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costWrappedSortName ∈ profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ profile.costWrappedSortName_mem_generated

theorem interacting_mem_costCoreLanguage (profile : ContinuationDecorationProfile cut) :
    costBaseSortName theory.presentation.interactingSort.1.name ∈
      profile.costCoreLanguage.typeNames := by
  rw [costCoreLanguage_typeNames]
  exact List.mem_append_left _ (profile.costBaseSortName_mem_generated
    (List.mem_map.mpr ⟨theory.presentation.interactingSort.1,
      theory.presentation.interactingSort.2, rfl⟩))

/-- Each fixed apparatus row validates from its actual declared sorts.
The generated source prefix is not expanded to establish this fact. -/
theorem apparatus_validate (profile : ContinuationDecorationProfile cut)
    (term : GrammarRule)
    (membership : term ∈ costCoreConstructors theory.presentation.interactingSort.1.name) :
    profile.costCoreLanguage.validateTerm term = [] := by
  have signature := profile.signature_mem_costCoreLanguage
  have key := profile.key_mem_costCoreLanguage
  have stack := profile.stack_mem_costCoreLanguage
  have wrapped := profile.wrapped_mem_costCoreLanguage
  have interacting := profile.interacting_mem_costCoreLanguage
  simp only [costCoreConstructors, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [costSignatureUnitConstructor, costSignatureProductConstructor,
      costKeyLeafConstructor, costKeyBranchConstructor, costSignatureCommitConstructor,
      costSignedConstructor, costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor, LanguageDef.validateTerm,
      signature, key, stack, wrapped, interacting, LanguageDef.validateTypeExpr_eq_nil_iff,
      TypeExpr.baseNames, TermParam.typeExpr]

/-- Finite continuation decoration and the fixed Cost apparatus jointly pass
ordinary language validation. Only actual duplicate declarations are excluded. -/
theorem costCoreLanguage_validate (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) :
    profile.costCoreLanguage.validate = [] := by
  change ((ConstructorSignatureExtension.ofLists costCoreTypes
    (costCoreConstructors theory.presentation.interactingSort.1.name)
    (some ("$cost:core:" ++ theory.presentation.presentation.language.name))).apply
      { toLanguageDef := profile.generatedLanguage }).toLanguageDef.validate = []
  apply ConstructorSignatureExtension.apply_language_validate
  · exact profile.generatedLanguage_validate noDuplicates
  · rfl
  · rfl
  · change (costCoreSortSuffixes.map costApparatusSortName).Nodup
    exact (show costCoreSortSuffixes.Nodup by decide).map costApparatusSortName_injective
  · intro generated generatedMembership apparatusMembership
    rw [generatedLanguage_typeNames] at generatedMembership
    change generated ∈ costCoreSortSuffixes.map costApparatusSortName at apparatusMembership
    obtain ⟨suffix, _, apparatusEq⟩ := List.mem_map.mp apparatusMembership
    rcases List.mem_append.mp generatedMembership with base | wrapped
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp base
      exact costBaseSortName_ne_apparatus name suffix apparatusEq.symm
    · simp only [List.mem_singleton] at wrapped
      exact costWrappedSortName_ne_apparatus suffix (wrapped.symm.trans apparatusEq.symm)
  · change (costCoreConstructorSuffixes.map costApparatusConstructorName).Nodup
    exact (show costCoreConstructorSuffixes.Nodup by decide).map
      costApparatusConstructorName_injective
  · intro generated generatedMembership apparatusMembership
    rw [generatedLanguage_constructorLabels] at generatedMembership
    change generated ∈ costCoreConstructorSuffixes.map costApparatusConstructorName
      at apparatusMembership
    obtain ⟨suffix, _, apparatusEq⟩ := List.mem_map.mp apparatusMembership
    rcases List.mem_append.mp generatedMembership with base | wrapped
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp base
      exact costBaseConstructorName_ne_apparatus name suffix apparatusEq.symm
    · obtain ⟨name, _, rfl⟩ := List.mem_map.mp wrapped
      exact costWrappedConstructorName_ne_apparatus name suffix apparatusEq.symm
  · intro term membership
    exact profile.apparatus_validate term membership

/-- A validated Cost core on the existing finite continuation profile. -/
def costCorePresentation (profile : ContinuationDecorationProfile cut)
    (noDuplicates : profile.constructorClosure.Nodup) : ValidatedLanguageDef where
  language := profile.costCoreLanguage
  valid := profile.costCoreLanguage_validate noDuplicates

/-- Adding the funding apparatus cannot turn an unwrapped source constructor
into a term of the wrapped sort. This is a typing boundary, independent of
which particular source constructor is an active introduction. -/
theorem baseHead_not_wrapped_in_costCore (profile : ContinuationDecorationProfile cut)
    {free : FreeTypeContext} {bound : List TypeExpr} (label : String)
    (arguments : List Pattern) :
    ¬ HasSort profile.costCoreLanguage free bound
      (.apply (costBaseConstructorName label) arguments) costWrappedSortName := by
  intro typed
  obtain ⟨rule, membership, named, result, -, -⟩ := typed.apply_inv
  rcases List.mem_append.mp membership with generated | apparatus
  · rcases List.mem_append.mp generated with base | wrapped
    · obtain ⟨original, -, rfl⟩ := List.mem_map.mp base
      exact costBaseSortName_ne_wrapped original.category (TypeExpr.base.inj result).symm
    · obtain ⟨original, -, rfl⟩ := List.mem_map.mp wrapped
      exact costBaseConstructorName_ne_wrapped label original.1.label named.symm
  · have labelMember : rule.label ∈
        (costCoreConstructors theory.presentation.interactingSort.1.name).map (·.label) :=
      List.mem_map.mpr ⟨rule, apparatus, rfl⟩
    change rule.label ∈ costCoreConstructorSuffixes.map costApparatusConstructorName at labelMember
    obtain ⟨suffix, -, equality⟩ := List.mem_map.mp labelMember
    exact costBaseConstructorName_ne_apparatus label suffix (equality.trans named).symm

#print axioms costCoreLanguage_validate
#print axioms baseHead_not_wrapped_in_costCore

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
