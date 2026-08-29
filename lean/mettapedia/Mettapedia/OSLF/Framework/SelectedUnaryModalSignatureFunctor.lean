import Mathlib.Data.Fintype.Card
import Mettapedia.OSLF.Framework.SelectedUnaryModalSignature

/-!
# Functorial selected-modal signature generation

An occurrence-preserving map embeds a finite authored site list into a larger
one.  This module extends that finite embedding canonically to natural-number
slots and uses the reversible generated namespace to obtain a structural map
of the emitted `LanguageDef`s.

The resulting functor is the first literal GSLT-to-GSLT slice of OSLF in this
development.  It covers only the modal signature; generated typing judgments,
rules, and semantic adequacy remain separate constructions.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace DisplayedOccurrenceMorphism

/-- Strict preservation of authored order makes the chosen finite position
map injective. -/
theorem position_injective
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    Function.Injective morphism.position := by
  intro first second equality
  have valuesEqual := congrArg Fin.val equality
  rcases Nat.lt_trichotomy first.val second.val with less | equal | greater
  · exact (Nat.ne_of_lt (morphism.position_strictMono less) valuesEqual).elim
  · exact Fin.ext equal
  · exact (Nat.ne_of_gt (morphism.position_strictMono greater) valuesEqual).elim

/-- A finite occurrence embedding cannot shrink the selected-site count. -/
theorem selectedSiteCount_le
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    source.selectedSites.length ≤ target.selectedSites.length := by
  simpa using Fintype.card_le_of_injective morphism.position
    morphism.position_injective

/-- Canonical total extension of a finite monotone occurrence embedding.
Inside the source prefix it is the authored map; after that prefix it shifts
by the difference in list lengths. -/
def extendPosition
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) (index : Nat) : Nat :=
  if inSource : index < source.selectedSites.length
  then (morphism.position ⟨index, inSource⟩).val
  else index + (target.selectedSites.length - source.selectedSites.length)

theorem extendPosition_of_lt
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target)
    {index : Nat} (inSource : index < source.selectedSites.length) :
    morphism.extendPosition index =
      (morphism.position ⟨index, inSource⟩).val := by
  simp [extendPosition, inSource]

theorem extendPosition_of_not_lt
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target)
    {index : Nat} (outsideSource : ¬ index < source.selectedSites.length) :
    morphism.extendPosition index =
      index + (target.selectedSites.length - source.selectedSites.length) := by
  simp [extendPosition, outsideSource]

@[simp]
theorem extendPosition_id (object : DisplayedOccurrenceLanguage) :
    (DisplayedOccurrenceMorphism.id object).extendPosition = _root_.id := by
  funext index
  by_cases inSource : index < object.selectedSites.length
  · simp [extendPosition, inSource, DisplayedOccurrenceMorphism.id]
  · simp [extendPosition, inSource]

@[simp]
theorem extendPosition_comp
    {first second third : DisplayedOccurrenceLanguage}
    (earlier : DisplayedOccurrenceMorphism first second)
    (later : DisplayedOccurrenceMorphism second third) :
    (DisplayedOccurrenceMorphism.comp earlier later).extendPosition =
      later.extendPosition ∘ earlier.extendPosition := by
  funext index
  by_cases inFirst : index < first.selectedSites.length
  · have inSecond :
        (earlier.position ⟨index, inFirst⟩).val <
          second.selectedSites.length :=
      (earlier.position ⟨index, inFirst⟩).isLt
    simp [extendPosition, inFirst, inSecond,
      DisplayedOccurrenceMorphism.comp]
  · have firstSecond := earlier.selectedSiteCount_le
    have secondThird := later.selectedSiteCount_le
    have afterFirstOutside :
        ¬ index +
            (second.selectedSites.length - first.selectedSites.length) <
          second.selectedSites.length := by
      omega
    simp [extendPosition, inFirst, afterFirstOutside]
    omega

end DisplayedOccurrenceMorphism

namespace SelectedUnaryModalSignature

open SelectedModalNaming

/-- Total action on constructor names.  Names outside the reversible private
modal namespace are preserved exactly. -/
def mapConstructorName
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target)
    (label : String) : String :=
  match slot? label with
  | some slot => SelectedModalNaming.label (morphism.extendPosition slot)
  | none => label

@[simp]
theorem mapConstructorName_label
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) (slot : Nat) :
    mapConstructorName morphism (SelectedModalNaming.label slot) =
      SelectedModalNaming.label (morphism.extendPosition slot) := by
  simp [mapConstructorName]

@[simp]
theorem mapConstructorName_id (object : DisplayedOccurrenceLanguage) :
    mapConstructorName (DisplayedOccurrenceMorphism.id object) = id := by
  funext label
  cases decoded : slot? label with
  | none => simp [mapConstructorName, decoded]
  | some slot =>
      rw [show label = SelectedModalNaming.label slot by
        exact (label_of_slot?_eq_some decoded).symm]
      simp

@[simp]
theorem mapConstructorName_comp
    {first second third : DisplayedOccurrenceLanguage}
    (earlier : DisplayedOccurrenceMorphism first second)
    (later : DisplayedOccurrenceMorphism second third) :
    mapConstructorName (DisplayedOccurrenceMorphism.comp earlier later) =
      mapConstructorName later ∘ mapConstructorName earlier := by
  funext label
  cases decoded : slot? label with
  | none => simp [mapConstructorName, decoded]
  | some slot =>
      rw [show label = SelectedModalNaming.label slot by
        exact (label_of_slot?_eq_some decoded).symm]
      simp

/-- Symbol action induced on the generated signature. -/
def symbols
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    PresentationSymbols where
  sort := id
  constructor := mapConstructorName morphism
  relation := id
  equation := id
  rewrite := id

@[simp]
theorem symbols_id (object : DisplayedOccurrenceLanguage) :
    symbols (DisplayedOccurrenceMorphism.id object) = PresentationSymbols.id := by
  ext name <;> simp [symbols, PresentationSymbols.id]

@[simp]
theorem symbols_comp
    {first second third : DisplayedOccurrenceLanguage}
    (earlier : DisplayedOccurrenceMorphism first second)
    (later : DisplayedOccurrenceMorphism second third) :
    symbols (DisplayedOccurrenceMorphism.comp earlier later) =
      PresentationSymbols.comp (symbols earlier) (symbols later) := by
  ext name <;> simp [symbols, PresentationSymbols.comp]

theorem extendPosition_lt
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target)
    {slot : Nat} (slotBound : slot < source.selectedSites.length) :
    morphism.extendPosition slot < target.selectedSites.length := by
  rw [morphism.extendPosition_of_lt slotBound]
  exact (morphism.position ⟨slot, slotBound⟩).isLt

/-- Structural image map between the two generated modal signatures. -/
noncomputable def mapMorphism
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    StructuralMorphism (validatedLanguage source) (validatedLanguage target) where
  symbols := symbols morphism
  mapsTypes declaration membership := by
    simp only [validatedLanguage, language] at membership ⊢
    simpa [mapTypeDecl, symbols] using membership
  mapsTerms rule membership := by
    simp only [validatedLanguage, language] at membership ⊢
    unfold modalTerms modalTermsForSiteCount modalTermsFrom at membership ⊢
    obtain ⟨slot, slotMembership, rfl⟩ := List.mem_map.mp membership
    apply List.mem_map.mpr
    refine ⟨morphism.extendPosition slot, ?_, ?_⟩
    · rw [List.mem_range'] at slotMembership ⊢
      obtain ⟨offset, offsetBound, slotEquality⟩ := slotMembership
      have slotBound : slot < source.selectedSites.length := by omega
      exact ⟨morphism.extendPosition slot,
        extendPosition_lt morphism slotBound, by omega⟩
    · simp [mapGrammarRule, modalRule, symbols, mapTypeExpr, mapTermParam]
  mapsEquations equation membership := by
    exact (List.not_mem_nil membership).elim
  mapsRewrites rewrite membership := by
    exact (List.not_mem_nil membership).elim

/-- Selected modal signature generation is an honest functor from
occurrence-preserving displayed GSLTs to validated GSLTs. -/
noncomputable def functor :
    CategoryTheory.Functor DisplayedOccurrenceLanguage
      ValidatedLanguageDef where
  obj := validatedLanguage
  map := mapMorphism
  map_id object := by
    apply StructuralMorphism.ext
    exact symbols_id object
  map_comp earlier later := by
    apply StructuralMorphism.ext
    exact symbols_comp earlier later

/-! ## Positive and negative controls -/

namespace FunctorCanary

/-- The incremental append embedding induces a genuine structural map from
the one-declaration singleton slice into the two-declaration two-site slice. -/
theorem append_maps_singleton_signature
    (source : ValidatedLanguageDef)
    (first second : DisplayedRewriteSite source.language) :
    Nonempty
      (validatedLanguage (.atSelection source [first]) ⟶
        validatedLanguage (.atSelection source [first, second])) :=
  ⟨functor.map (appendSelectionEmbedding source [first] [second])⟩

/-- A foreign constructor name is outside the private generated namespace and
therefore survives every generated structural map. -/
theorem foreign_name_is_fixed
    {source target : DisplayedOccurrenceLanguage}
    (morphism : DisplayedOccurrenceMorphism source target) :
    mapConstructorName morphism "foreign" = "foreign" := by
  rfl

end FunctorCanary

#print axioms DisplayedOccurrenceMorphism.selectedSiteCount_le
#print axioms DisplayedOccurrenceMorphism.extendPosition_comp
#print axioms mapConstructorName_comp
#print axioms mapMorphism
#print axioms functor
#print axioms FunctorCanary.append_maps_singleton_signature
#print axioms FunctorCanary.foreign_name_is_fixed

end SelectedUnaryModalSignature

end Mettapedia.OSLF.Framework
