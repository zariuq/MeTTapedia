import Mettapedia.OSLF.Framework.DisplayedLanguage

/-!
# Occurrence-preserving displayed languages

Logical coverage is enough to compare which OSLF sites are available, but it
forgets order and multiplicity.  Generated declaration names, incremental
compilation, proof provenance, and exact result bags cannot use that quotient:
they need a chosen occurrence of every transported source site.

This module defines the stronger category used by syntax-generating
translations.  A morphism carries a strictly monotone map between the two
authored site lists and proves that every selected target occurrence is the
transported source occurrence.  Forgetting the chosen positions yields the
coverage category from `DisplayedLanguage`.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

/-- A validated operational language with an ordered, multiplicity-aware
list of displayed source occurrences. -/
structure DisplayedOccurrenceLanguage where
  definition : ValidatedLanguageDef
  selectedSites : DisplayedSiteSelection definition.language

namespace DisplayedOccurrenceLanguage

/-- Forget occurrence-sensitive morphisms while retaining the same object
data used by the logical coverage category. -/
def toDisplayedLanguage
    (object : DisplayedOccurrenceLanguage) : DisplayedLanguage :=
  ⟨object.definition, object.selectedSites⟩

/-- View a validated language at one ordered site request. -/
def atSelection (definition : ValidatedLanguageDef)
    (selection : DisplayedSiteSelection definition.language) :
    DisplayedOccurrenceLanguage :=
  ⟨definition, selection⟩

end DisplayedOccurrenceLanguage

/-- A structural language map together with a chosen order-preserving
embedding of source site occurrences into target site occurrences.

The equation on `siteAt` retains duplicates as distinct positions.  A
coverage-only morphism may lawfully coalesce them; this stronger morphism may
not. -/
structure DisplayedOccurrenceMorphism
    (source target : DisplayedOccurrenceLanguage) where
  structural : StructuralMorphism source.definition target.definition
  position : _root_.Fin source.selectedSites.length →
    _root_.Fin target.selectedSites.length
  position_strictMono : ∀ {first second},
    first.val < second.val →
      (position first).val < (position second).val
  siteAt : ∀ sourcePosition,
    target.selectedSites[position sourcePosition] =
      DisplayedRewriteSite.map structural
        source.selectedSites[sourcePosition]

namespace DisplayedOccurrenceMorphism

@[ext]
theorem ext {source target : DisplayedOccurrenceLanguage}
    {first second : DisplayedOccurrenceMorphism source target}
    (structural : first.structural = second.structural)
    (position : first.position = second.position) : first = second := by
  cases first
  cases second
  cases structural
  cases position
  rfl

/-- Identity retains every occurrence at its original authored position. -/
noncomputable def id (object : DisplayedOccurrenceLanguage) :
    DisplayedOccurrenceMorphism object object where
  structural := StructuralMorphism.id object.definition
  position := fun sourcePosition => sourcePosition
  position_strictMono := fun {_ _} less => less
  siteAt := by
    intro sourcePosition
    simp [DisplayedRewriteSite.map_id]

/-- Composition composes the two chosen occurrence embeddings. -/
noncomputable def comp
    {first second third : DisplayedOccurrenceLanguage}
    (earlier : DisplayedOccurrenceMorphism first second)
    (later : DisplayedOccurrenceMorphism second third) :
    DisplayedOccurrenceMorphism first third where
  structural := StructuralMorphism.comp earlier.structural later.structural
  position := later.position ∘ earlier.position
  position_strictMono := fun less =>
    later.position_strictMono (earlier.position_strictMono less)
  siteAt := by
    intro sourcePosition
    change third.selectedSites[later.position (earlier.position sourcePosition)] =
      DisplayedRewriteSite.map
        (StructuralMorphism.comp earlier.structural later.structural)
        first.selectedSites[sourcePosition]
    rw [later.siteAt, earlier.siteAt]
    exact (DisplayedRewriteSite.map_comp earlier.structural later.structural
      first.selectedSites[sourcePosition]).symm

end DisplayedOccurrenceMorphism

noncomputable instance : CategoryTheory.Category
    DisplayedOccurrenceLanguage where
  Hom := DisplayedOccurrenceMorphism
  id := DisplayedOccurrenceMorphism.id
  comp := DisplayedOccurrenceMorphism.comp
  id_comp morphism := by
    apply DisplayedOccurrenceMorphism.ext
    · apply StructuralMorphism.ext
      simp [DisplayedOccurrenceMorphism.comp, DisplayedOccurrenceMorphism.id,
        StructuralMorphism.comp, StructuralMorphism.id,
        PresentationSymbols.comp, PresentationSymbols.id]
    · funext sourcePosition
      simp [DisplayedOccurrenceMorphism.comp, DisplayedOccurrenceMorphism.id]
  comp_id morphism := by
    apply DisplayedOccurrenceMorphism.ext
    · apply StructuralMorphism.ext
      simp [DisplayedOccurrenceMorphism.comp, DisplayedOccurrenceMorphism.id,
        StructuralMorphism.comp, StructuralMorphism.id,
        PresentationSymbols.comp, PresentationSymbols.id]
    · funext sourcePosition
      simp [DisplayedOccurrenceMorphism.comp, DisplayedOccurrenceMorphism.id]
  assoc first second third := by
    apply DisplayedOccurrenceMorphism.ext
    · apply StructuralMorphism.ext
      rfl
    · rfl

namespace DisplayedOccurrenceMorphism

/-- A chosen occurrence embedding implies logical site coverage. -/
theorem mapsSelected {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    DisplayedSiteSelection.Covers
      (DisplayedRewriteSite.mapSelection morphism.structural
        source.selectedSites)
      target.selectedSites := by
  intro targetSite targetMembership
  unfold DisplayedRewriteSite.mapSelection at targetMembership
  rw [List.mem_map] at targetMembership
  obtain ⟨sourceSite, sourceMembership, rfl⟩ := targetMembership
  obtain ⟨sourcePosition, sourceAt⟩ := List.mem_iff_get.mp sourceMembership
  rw [← sourceAt]
  have siteEquality :
      DisplayedRewriteSite.map morphism.structural
          (source.selectedSites.get sourcePosition) =
        target.selectedSites.get (morphism.position sourcePosition) :=
    (morphism.siteAt sourcePosition).symm
  rw [siteEquality]
  exact List.get_mem target.selectedSites (morphism.position sourcePosition)

end DisplayedOccurrenceMorphism

/-- Erase the chosen occurrence embedding to its logical coverage map. -/
noncomputable def forgetOccurrencePositions :
    DisplayedOccurrenceLanguage ⥤ DisplayedLanguage where
  obj object := object.toDisplayedLanguage
  map morphism :=
    { structural := morphism.structural
      mapsSelected := morphism.mapsSelected }
  map_id object := by
    apply DisplayedLanguageMorphism.ext
    apply StructuralMorphism.ext
    change (StructuralMorphism.id object.definition).symbols =
      (StructuralMorphism.id object.definition).symbols
    rfl
  map_comp earlier later := by
    apply DisplayedLanguageMorphism.ext
    apply StructuralMorphism.ext
    rfl

/-- Pointwise structural reindexing preserves every selected occurrence at
the same list position.  This is the cartesian lift of a language map for the
ordered-site family: logical symbols may change, while occurrence order and
multiplicity do not. -/
noncomputable def reindexSelection
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (selection : DisplayedSiteSelection source.language) :
    DisplayedOccurrenceLanguage.atSelection source selection ⟶
      DisplayedOccurrenceLanguage.atSelection target
        (DisplayedRewriteSite.mapSelection morphism selection) where
  structural := morphism
  position := fun sourcePosition =>
    ⟨sourcePosition.val, by
      simp [DisplayedOccurrenceLanguage.atSelection,
        DisplayedRewriteSite.mapSelection]⟩
  position_strictMono := fun less => less
  siteAt := by
    intro sourcePosition
    change
      (selection.map (DisplayedRewriteSite.map morphism)).get _ =
        DisplayedRewriteSite.map morphism (selection.get sourcePosition)
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]

/-- Appending a compilation delta gives the canonical occurrence-preserving
inclusion: old positions and their declaration names remain stable. -/
noncomputable def appendSelectionEmbedding
    (definition : ValidatedLanguageDef)
    (base delta : DisplayedSiteSelection definition.language) :
    DisplayedOccurrenceLanguage.atSelection definition base ⟶
      DisplayedOccurrenceLanguage.atSelection definition
        (base ++ delta) where
  structural := StructuralMorphism.id definition
  position := fun sourcePosition =>
    ⟨sourcePosition, by
      change sourcePosition.val < (base ++ delta).length
      simpa [List.length_append] using lt_of_lt_of_le sourcePosition.isLt
        (Nat.le_add_right base.length delta.length)⟩
  position_strictMono := by
    intro first second less
    exact less
  siteAt := by
    intro sourcePosition
    change _root_.Fin base.length at sourcePosition
    have targetBound : sourcePosition.val < (base ++ delta).length := by
      simpa [List.length_append] using lt_of_lt_of_le sourcePosition.isLt
        (Nat.le_add_right base.length delta.length)
    change (base ++ delta).get ⟨sourcePosition.val, targetBound⟩ =
      DisplayedRewriteSite.map (StructuralMorphism.id definition)
        (base.get sourcePosition)
    rw [List.get_eq_getElem, List.get_eq_getElem,
      List.getElem_append_left sourcePosition.isLt]
    simp [DisplayedRewriteSite.map_id]

/-! ## Positive and negative controls -/

namespace DisplayedOccurrenceCanary

/-- Existing declaration positions survive a one-site append exactly. -/
theorem append_preserves_first_position :
    ∀ (definition : ValidatedLanguageDef)
      (first second : DisplayedRewriteSite definition.language),
      (appendSelectionEmbedding definition [first] [second]).position
          ⟨0, by simp [DisplayedOccurrenceLanguage.atSelection]⟩ =
        ⟨0, by simp [DisplayedOccurrenceLanguage.atSelection]⟩ :=
  by
  intro definition first second
  rfl

/-- There is no order-preserving embedding from two occurrences into one.
This is the cardinality control distinguishing occurrence compilation from
logical coverage. -/
theorem no_two_occurrences_into_one
    (definition : ValidatedLanguageDef)
    (first second : DisplayedRewriteSite definition.language) :
    IsEmpty
      (DisplayedOccurrenceLanguage.atSelection definition [first, second] ⟶
        DisplayedOccurrenceLanguage.atSelection definition [first]) := by
  constructor
  intro morphism
  let firstPosition :
      _root_.Fin
        (DisplayedOccurrenceLanguage.atSelection definition
          [first, second]).selectedSites.length :=
    ⟨0, by simp [DisplayedOccurrenceLanguage.atSelection]⟩
  let secondPosition :
      _root_.Fin
        (DisplayedOccurrenceLanguage.atSelection definition
          [first, second]).selectedSites.length :=
    ⟨1, by simp [DisplayedOccurrenceLanguage.atSelection]⟩
  have ordered :
      (morphism.position firstPosition).val <
        (morphism.position secondPosition).val :=
    morphism.position_strictMono (by
      simp [firstPosition, secondPosition])
  have firstBound := (morphism.position firstPosition).isLt
  have secondBound := (morphism.position secondPosition).isLt
  change (morphism.position firstPosition).val < 1 at firstBound
  change (morphism.position secondPosition).val < 1 at secondBound
  omega

end DisplayedOccurrenceCanary

#print axioms DisplayedOccurrenceMorphism.id
#print axioms DisplayedOccurrenceMorphism.comp
#print axioms DisplayedOccurrenceMorphism.mapsSelected
#print axioms forgetOccurrencePositions
#print axioms reindexSelection
#print axioms appendSelectionEmbedding
#print axioms DisplayedOccurrenceCanary.append_preserves_first_position
#print axioms DisplayedOccurrenceCanary.no_two_occurrences_into_one

end Mettapedia.OSLF.Framework
