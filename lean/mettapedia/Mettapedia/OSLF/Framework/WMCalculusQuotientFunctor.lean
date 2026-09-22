import Mettapedia.OSLF.Framework.WMCalculusGeneratedFreeReading

/-!
# Functorial WM observational quotient

A strict reading morphism descends to observational state classes exactly
when its state map carries source agreement to target agreement. Query
surjectivity is sufficient for this, but not necessary: an uncovered target
query might still be redundant on the image. The quotient construction is
therefore a functor on the maximal agreement-preserving arrow class. The
existing non-covering counterexample shows why arbitrary strict arrows do
not admit this descent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusReadingCategory
open Mettapedia.OSLF.Framework.WMCalculusGeneratedFreeReading

/-- A lawful reading, viewed in the category whose arrows preserve
behavioral agreement. Objects impose no extra separation assumption. -/
structure BehavioralReading where
  model : LawfulReading

/-- The exact state-agreement compatibility condition for quotient descent.
Query coverage is one way, but not the only way, to establish it. -/
structure BehavioralHom (source target : BehavioralReading) where
  readingMap : source.model ⟶ target.model
  agree_forward : ∀ first second,
    source.model.reading.Agree .state first second →
      target.model.reading.Agree .state
        (readingMap.mapState first) (readingMap.mapState second)

instance : Category BehavioralReading where
  Hom := BehavioralHom
  id source :=
    { readingMap := 𝟙 source.model
      agree_forward := by intro first second agree; exact agree }
  comp first second :=
    { readingMap := first.readingMap ≫ second.readingMap
      agree_forward := by
        intro a b agree
        exact second.agree_forward _ _
          (first.agree_forward _ _ agree) }
  id_comp := by intro first second hom; cases hom; rfl
  comp_id := by intro first second hom; cases hom; rfl
  assoc := by intro first second third fourth f g h; cases f; cases g; cases h; rfl

/-- Query coverage provides one concrete certificate for a behavioral arrow.
This constructor does not make coverage necessary for such an arrow. -/
def BehavioralHom.ofQueryCovering {source target : BehavioralReading}
    (readingMap : source.model ⟶ target.model)
    (covers : Function.Surjective readingMap.mapQuery) : source ⟶ target where
  readingMap := readingMap
  agree_forward := by
    intro first second agree
    exact readingMap.agree_map covers .state agree

/-- A strict arrow admits a quotient map commuting with the raw quotient
arrows exactly when it preserves all source state agreements. -/
theorem descends_iff_agree_forward {source target : LawfulReading}
    (readingMap : source ⟶ target) :
    (∃ quotientMap : quotientObject source ⟶ quotientObject target,
      quotientArrow source ≫ quotientMap =
        readingMap ≫ quotientArrow target) ↔
      ∀ first second,
        source.reading.Agree .state first second →
          target.reading.Agree .state
            (readingMap.mapState first) (readingMap.mapState second) := by
  rw [factorsThroughQuotient_iff]
  constructor
  · intro compatible first second agree
    have descended := compatible first second agree
    change classOf target.reading (readingMap.mapState first) =
      classOf target.reading (readingMap.mapState second) at descended
    exact (classOf_eq_iff_agree target.reading _ _).1 descended
  · intro forward first second agree
    change classOf target.reading (readingMap.mapState first) =
      classOf target.reading (readingMap.mapState second)
    exact (classOf_eq_iff_agree target.reading _ _).2
      (forward first second agree)

/-- The quotient map induced by a behavior-preserving backend interpretation.
Its source and target states are observational classes, not raw states. -/
def quotientMap {source target : BehavioralReading} (hom : source ⟶ target) :
    quotientObject source.model ⟶ quotientObject target.model :=
  factorArrow (hom.readingMap ≫ quotientArrow target.model) (by
    intro first second agree
    change classOf target.model.reading
        (hom.readingMap.mapState first) =
      classOf target.model.reading
        (hom.readingMap.mapState second)
    apply (classOf_eq_iff_agree target.model.reading _ _).2
    exact hom.agree_forward first second agree)

@[simp] theorem quotientMap_state {source target : BehavioralReading}
    (hom : source ⟶ target) (state : source.model.State) :
    (quotientMap hom).mapState (classOf source.model.reading state) =
      classOf target.model.reading (hom.readingMap.mapState state) := rfl

@[simp] theorem quotientMap_query {source target : BehavioralReading}
    (hom : source ⟶ target) (query : source.model.Query) :
    (quotientMap hom).mapQuery query = hom.readingMap.mapQuery query := rfl

@[simp] theorem quotientMap_evidence {source target : BehavioralReading}
    (hom : source ⟶ target) (evidence : source.model.Evidence) :
    (quotientMap hom).mapEvidence evidence =
      hom.readingMap.mapEvidence evidence := rfl

/-- Quotienting the identity does not change any observational class. -/
theorem quotientMap_id (source : BehavioralReading) :
    quotientMap (𝟙 source) = 𝟙 (quotientObject source.model) := by
  apply ReadingMorphism.ext
  · funext state
    induction state using Quotient.inductionOn with
    | _ raw => rfl
  · rfl
  · rfl

/-- Quotienting a composite is composition of the quotient maps. -/
theorem quotientMap_comp {first middle last : BehavioralReading}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    quotientMap (f ≫ g) = quotientMap f ≫ quotientMap g := by
  apply ReadingMorphism.ext
  · funext state
    induction state using Quotient.inductionOn with
    | _ raw => rfl
  · rfl
  · rfl

/-- The observational quotient is a genuine functor on the exact arrow
class for which behavioral equality transports. -/
def observationalQuotient : BehavioralReading ⥤ SeparatedReading where
  obj source :=
    { model := quotientObject source.model
      separated := quotientObject_separated source.model }
  map hom := quotientMap hom
  map_id source := quotientMap_id source
  map_comp f g := quotientMap_comp f g

/-- The free generated reading maps uniquely to every object produced by
this functor, because each such object is observationally separated. -/
noncomputable def generatedToQuotient (source : BehavioralReading) :
    generatedSeparated ⟶ observationalQuotient.obj source :=
  generatedTo (quotientObject source.model)
    (quotientObject_separated source.model)

/-- Naturality of the free interpretation is forced by initiality: there
is exactly one arrow from the generated reading to either quotient object.
This is a commuting square, not a claim that raw backend histories agree. -/
theorem generatedToQuotient_natural {source target : BehavioralReading}
    (hom : source ⟶ target) :
    generatedToQuotient source ≫ observationalQuotient.map hom =
      generatedToQuotient target :=
  generatedSeparated_isInitial.hom_ext _ _

/-- The family of canonical free interpretations is a natural
transformation into the observational quotient functor. -/
noncomputable def generatedToQuotientNat :
    (Functor.const BehavioralReading).obj generatedSeparated ⟶
      observationalQuotient where
  app source := generatedToQuotient source
  naturality := by
    intro source target hom
    simpa using (generatedToQuotient_natural hom).symm

end Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor
