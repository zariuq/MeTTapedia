import Mettapedia.OSLF.Framework.DisplayedRewriteSiteTransport

/-!
# Validated languages with selected OSLF source sites

A sparse syntactic OSLF construction needs more input than a bare language:
it needs the finite displayed occurrences requested by the consuming
translation.  This module packages that input and its morphisms.

A morphism is a structural language map whose transported source
selection is covered by the target selection.  These objects and morphisms
form a category.  Append-only request growth gives a canonical morphism, so a
later generator can treat the appended suffix as a compilation delta.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

/-- A validated operational language together with the finite source
occurrences whose native typing structure has been requested. -/
structure DisplayedLanguage where
  definition : ValidatedLanguageDef
  selectedSites : DisplayedSiteSelection definition.language

/-- A structural language map that carries every selected source site to
a site selected by the target. -/
structure DisplayedLanguageMorphism
    (source target : DisplayedLanguage) where
  structural : StructuralMorphism source.definition target.definition
  mapsSelected : DisplayedSiteSelection.Covers
    (DisplayedRewriteSite.mapSelection structural source.selectedSites)
    target.selectedSites

namespace DisplayedLanguageMorphism

@[ext]
theorem ext {source target : DisplayedLanguage}
    {first second : DisplayedLanguageMorphism source target}
    (structural : first.structural = second.structural) : first = second := by
  cases first
  cases second
  cases structural
  rfl

/-- Identity preserves the selected-site list exactly. -/
noncomputable def id (object : DisplayedLanguage) :
    DisplayedLanguageMorphism object object where
  structural := StructuralMorphism.id object.definition
  mapsSelected := by
    rw [DisplayedRewriteSite.mapSelection_id]
    exact DisplayedSiteSelection.covers_refl object.selectedSites

/-- Composition transports the first coverage proof through the second
structural map, then composes it with the second coverage proof. -/
noncomputable def comp
    {first second third : DisplayedLanguage}
    (earlier : DisplayedLanguageMorphism first second)
    (later : DisplayedLanguageMorphism second third) :
    DisplayedLanguageMorphism first third where
  structural := StructuralMorphism.comp earlier.structural later.structural
  mapsSelected := by
    rw [DisplayedRewriteSite.mapSelection_comp]
    exact DisplayedSiteSelection.covers_trans
      (DisplayedRewriteSite.mapSelection_preserves_covers later.structural
        earlier.mapsSelected)
      later.mapsSelected

end DisplayedLanguageMorphism

noncomputable instance : CategoryTheory.Category DisplayedLanguage where
  Hom := DisplayedLanguageMorphism
  id := DisplayedLanguageMorphism.id
  comp := DisplayedLanguageMorphism.comp
  id_comp morphism := by
    apply DisplayedLanguageMorphism.ext
    apply StructuralMorphism.ext
    rfl
  comp_id morphism := by
    apply DisplayedLanguageMorphism.ext
    apply StructuralMorphism.ext
    rfl
  assoc first second third := by
    apply DisplayedLanguageMorphism.ext
    apply StructuralMorphism.ext
    rfl

/-- Forget selected sites, retaining the validated operational language. -/
noncomputable def forgetDisplayedSites :
    CategoryTheory.Functor DisplayedLanguage ValidatedLanguageDef where
  obj object := object.definition
  map morphism := morphism.structural
  map_id object := by
    apply StructuralMorphism.ext
    rfl
  map_comp earlier later := by
    apply StructuralMorphism.ext
    rfl

/-- The same validated language at one particular selection. -/
def DisplayedLanguage.atSelection (definition : ValidatedLanguageDef)
    (selection : DisplayedSiteSelection definition.language) :
    DisplayedLanguage :=
  ⟨definition, selection⟩

/-- Logical request inclusion gives a canonical structural morphism over the
identity language. -/
noncomputable def selectionInclusion (definition : ValidatedLanguageDef)
    {smaller larger : DisplayedSiteSelection definition.language}
    (coverage : DisplayedSiteSelection.Covers smaller larger) :
    DisplayedLanguage.atSelection definition smaller ⟶
      DisplayedLanguage.atSelection definition larger where
  structural := StructuralMorphism.id definition
  mapsSelected := by
    change DisplayedSiteSelection.Covers
      (DisplayedRewriteSite.mapSelection
        (StructuralMorphism.id definition) smaller)
      larger
    rw [DisplayedRewriteSite.mapSelection_id]
    exact coverage

/-- An append-only request delta induces the canonical inclusion into the
extended sparse-generation input. -/
noncomputable def appendOnlyInclusion (definition : ValidatedLanguageDef)
    {base extended : DisplayedSiteSelection definition.language}
    (extension : DisplayedSiteSelection.AppendOnlyExtension base extended) :
    DisplayedLanguage.atSelection definition base ⟶
      DisplayedLanguage.atSelection definition extended :=
  selectionInclusion definition
    (DisplayedSiteSelection.appendOnlyExtension_covers extension)

/-! ## Positive and negative controls -/

/-- A singleton request has an identity morphism and therefore is a genuine
object of the displayed-language category. -/
theorem singleton_identity_inhabited (definition : ValidatedLanguageDef)
    (site : DisplayedRewriteSite definition.language) :
    Nonempty
      (DisplayedLanguage.atSelection definition [site] ⟶
        DisplayedLanguage.atSelection definition [site]) :=
  ⟨𝟙 _⟩

/-- A nonempty site request cannot map to an empty target selection.  This is
the negative control ensuring that the coverage field is not vacuous. -/
theorem no_morphism_from_singleton_to_empty
    (source target : ValidatedLanguageDef)
    (site : DisplayedRewriteSite source.language) :
    ¬ Nonempty
      (DisplayedLanguage.atSelection source [site] ⟶
        DisplayedLanguage.atSelection target []) := by
  rintro ⟨morphism⟩
  have sourceMember :
      DisplayedRewriteSite.map morphism.structural site ∈
        DisplayedRewriteSite.mapSelection morphism.structural [site] := by
    simp [DisplayedRewriteSite.mapSelection]
  have targetMember := morphism.mapsSelected _ sourceMember
  exact List.not_mem_nil targetMember

#print axioms DisplayedLanguageMorphism.id
#print axioms DisplayedLanguageMorphism.comp
#print axioms forgetDisplayedSites
#print axioms selectionInclusion
#print axioms appendOnlyInclusion
#print axioms singleton_identity_inhabited
#print axioms no_morphism_from_singleton_to_empty

end Mettapedia.OSLF.Framework
