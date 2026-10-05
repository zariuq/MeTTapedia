import Mettapedia.GSLT.LanguageDef.CostInteraction

/-!
# Typing in the core language of a decoration profile

The core language itself, with its validation, is defined beside the apparatus
it adds. Here are the two typing facts that need the typing lemmas for
signature extension: decorated terms keep their types in the core, and adding
the apparatus cannot give an unwrapped source constructor the wrapped sort.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

set_option autoImplicit false

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Extending the signature does not alter the types of its already
decorated constructors. -/
theorem hasType_costCoreLanguage (profile : ContinuationDecorationProfile cut)
    {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {type : TypeExpr}
    (typed : HasType profile.generatedLanguage free bound term type) :
    HasType profile.costCoreLanguage free bound term type := by
  exact typed.weakenTerms (fun _ membership => List.mem_append_left _ membership)

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

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
