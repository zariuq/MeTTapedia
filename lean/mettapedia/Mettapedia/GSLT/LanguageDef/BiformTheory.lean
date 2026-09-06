import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Products.Basic
import Mettapedia.GSLT.Core.ProofRelevantTranslationCategory
import Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
/-!
# Proof-relevant biform theories

A biform theory has a declarative face and an algorithmic face.  The
declarative face is a closed theory in a Pi-institution.  The algorithmic
face is a proof-relevant GSLT, so a transition retains the particular rule
occurrence that produced it.  A meaning formula assigns a native sentence to
each retained event, and `meaning_sound` requires that sentence to be a
theorem of the declarative face.

This is the precise seam between an executable intermediate language and a
little-theories graph:

* equations and transitions belong to the GSLT;
* mathematical meaning belongs to the native institution;
* event evidence keeps distinct algorithms or rule occurrences apart; and
* a biform route transports the logical theory, the event evidence, and the
  meaning formula by one commuting law.

The construction deliberately does not turn semantic theoremhood into an
executable checker.  A NIK authority may be attached only when an independent
certificate/replay theorem is supplied.  It also does not manufacture a
meaning formula for a multi-step path: composing local meanings requires the
composition principles of the particular native theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.ProofRelevant

universe uSignature uHom uSentence uTerm

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]

/-! ## Biform theories -/

/-- The semantic admission condition for an event-indexed meaning assignment.
It is kept separate from `BiformTheory` so negative canaries can show that an
algorithm and a proposed meaning assignment do not form a biform theory. -/
def MeaningSound
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (logical : PiInstitution.TheoryObject institution)
    (algorithm : ProofRelevantGSLT.{uTerm})
    (meaning : algorithm.Event →
      institution.sentence.obj logical.signature) : Prop :=
  ∀ event, meaning event ∈ logical.theory.1

/-- A proof-relevant algorithm together with the native sentence describing
the meaning of every retained primitive event. -/
structure BiformTheory
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  logical : PiInstitution.TheoryObject institution
  algorithm : ProofRelevantGSLT.{uTerm}
  meaning : algorithm.Event →
    institution.sentence.obj logical.signature
  meaning_sound : MeaningSound institution logical algorithm meaning

namespace BiformTheory

variable {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- The meaning theorem carried by one concrete algorithmic event. -/
theorem event_meaning
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
    (event : theory.algorithm.Event) :
    theory.meaning event ∈ theory.logical.theory.1 :=
  theory.meaning_sound event

/-! ## Biform routes -/

/-- A route between biform theories transports native theorems and retained
algorithmic events, with one equation saying that their meaning readings
commute.  The operational component is proof-relevant and locally covered;
it cannot invent an event leaving a translated source state. -/
structure Hom
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution) where
  logical : PiInstitution.TheoryHom source.logical target.logical
  operational : Translation source.algorithm target.algorithm
  meaning_natural : ∀ event : source.algorithm.Event,
    institution.sentence.map logical.mapSignature (source.meaning event) =
      target.meaning (operational.mapEvent event)

namespace Hom

variable
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
  {first middle last :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}

/-- A biform route sends the theorem explaining a source event to the theorem
explaining its translated target event. -/
theorem mapped_event_meaning
    (route : Hom first middle) (event : first.algorithm.Event) :
    middle.meaning (route.operational.mapEvent event) ∈
      middle.logical.theory.1 := by
  have translated := route.logical.preserves (first.meaning_sound event)
  rw [route.meaning_natural] at translated
  exact translated

/-- Identity changes neither an event nor its meaning. -/
def identity
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution) :
    Hom theory theory where
  logical := PiInstitution.TheoryHom.identity theory.logical
  operational := Translation.id theory.algorithm
  meaning_natural := by
    intro event
    change institution.sentence.map
      (CategoryTheory.CategoryStruct.id theory.logical.signature)
        (theory.meaning event) =
      theory.meaning ((Translation.id theory.algorithm).mapEvent event)
    rw [institution.sentence.map_id_apply, Translation.mapEvent_id]

/-- Biform routes compose in execution order. -/
def comp (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  logical := PiInstitution.TheoryHom.comp earlier.logical later.logical
  operational := Translation.comp earlier.operational later.operational
  meaning_natural := by
    intro event
    change institution.sentence.map
        (CategoryTheory.CategoryStruct.comp earlier.logical.mapSignature
          later.logical.mapSignature)
        (first.meaning event) =
      last.meaning
        ((Translation.comp earlier.operational later.operational).mapEvent event)
    rw [institution.sentence.map_comp_apply]
    rw [earlier.meaning_natural]
    rw [later.meaning_natural]
    rw [Translation.mapEvent_comp]

@[simp]
theorem identity_map_event
    (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
    (event : theory.algorithm.Event) :
    (identity theory).operational.mapEvent event = event :=
  Translation.mapEvent_id event

@[simp]
theorem comp_map_event (earlier : Hom first middle) (later : Hom middle last)
    (event : first.algorithm.Event) :
    (comp earlier later).operational.mapEvent event =
      later.operational.mapEvent (earlier.operational.mapEvent event) :=
  Translation.mapEvent_comp earlier.operational later.operational event

end Hom

#print axioms event_meaning
#print axioms Hom.mapped_event_meaning
#print axioms Hom.comp

end BiformTheory
end Mettapedia.GSLT.LanguageDef

/-! ## The category of biform theories and its projections -/

namespace Mettapedia.GSLT.LanguageDef.BiformTheory

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uSignature uHom uSentence uTerm

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- Two biform routes are equal when their native-theory map and their full
proof-relevant operational translation are equal.  The commuting law is
proof-irrelevant. -/
@[ext]
theorem Hom.ext_data
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    {left right : Hom source target}
    (logical : left.logical = right.logical)
    (operational : left.operational = right.operational) :
    left = right := by
  cases left
  cases right
  cases logical
  cases operational
  rfl

/-- Biform routes compose strictly without quotienting their proof-relevant
event translations. -/
instance biformTheoryCategory : CategoryTheory.Category
    (BiformTheory.{uSignature, uHom, uSentence, uTerm} institution) where
  Hom := Hom
  id := Hom.identity
  comp earlier later := Hom.comp earlier later
  id_comp route := by
    apply Hom.ext_data
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.id_comp route.logical.mapSignature
    · exact Translation.identity_comp route.operational
  comp_id route := by
    apply Hom.ext_data
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.comp_id route.logical.mapSignature
    · exact Translation.comp_identity route.operational
  assoc earlier middle later := by
    apply Hom.ext_data
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.assoc earlier.logical.mapSignature
        middle.logical.mapSignature later.logical.mapSignature
    · exact Translation.comp_assoc earlier.operational middle.operational
        later.operational

/-- Retain only the little-theory map of a biform route. -/
def logicalProjection :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤
      PiInstitution.TheoryObject institution where
  obj theory := theory.logical
  map route := route.logical
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Retain the complete proof-relevant operational translation of a biform
route. -/
def operationalProjection :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤
      ProofRelevantGSLT.{uTerm} where
  obj theory := theory.algorithm
  map route := route.operational
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Retained proof occurrences vary functorially over biform routes.  This is
the operational event functor composed with the biform operational
projection; it is independent of the logical and authority projections. -/
def retainedEvents :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤ Type uTerm :=
  operationalProjection ⋙ Mettapedia.GSLT.ProofRelevant.eventFunctor

@[simp]
theorem retainedEvents_map_apply
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (route : source ⟶ target) (event : source.algorithm.Event) :
    (retainedEvents.map route) event = route.operational.mapEvent event :=
  rfl

/-- The semantic NIK view is induced by the logical projection.  It carries
closed theorem scope and meaning, but no checker or certificate realization. -/
def semanticTargetFunctor :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤
      CertifiedTheoryCategory.TheoryObject.{0, uSignature, uSentence} :=
  logicalProjection ⋙ ClosedTheorySemanticTarget.closedTheoryFunctor

/-! ## The biform category as a compatibility locus -/

/-- Retain the native-theory map and the full proof-relevant operational map
together.  This is the comparison with the product of the two independently
meaningful route categories; event-meaning compatibility cuts out its image. -/
def jointProjection :
    BiformTheory.{uSignature, uHom, uSentence, uTerm} institution ⥤
      (PiInstitution.TheoryObject institution × ProofRelevantGSLT.{uTerm}) :=
  logicalProjection.prod' operationalProjection

/-- The two independently meaningful components of one biform route.  This
explicit homwise readout keeps their universe levels independent; it is
definitionally the morphism map of `jointProjection`. -/
def routePair
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (route : Hom source target) :
    PiInstitution.TheoryHom source.logical target.logical ×
      Translation source.algorithm target.algorithm :=
  (route.logical, route.operational)

/-- A logical/operational pair is compatible when translating an event and
then reading its native meaning agrees with translating that meaning in the
native theory. -/
def Compatible
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (pair : PiInstitution.TheoryHom source.logical target.logical ×
      Translation source.algorithm target.algorithm) : Prop :=
  ∀ event : source.algorithm.Event,
    institution.sentence.map pair.1.mapSignature (source.meaning event) =
      target.meaning (pair.2.mapEvent event)

/-- Every biform route lands in the compatibility locus. -/
theorem jointProjection_map_compatible
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (route : Hom source target) :
    Compatible (routePair route) :=
  route.meaning_natural

/-- The image of the joint projection is exactly the compatible pairs.  Thus
the biform route category is neither an arbitrary product nor a second graph:
its extra content is precisely the commuting event-meaning square. -/
theorem jointProjection_map_range_iff_compatible
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (pair : PiInstitution.TheoryHom source.logical target.logical ×
      Translation source.algorithm target.algorithm) :
    (∃ route : Hom source target, routePair route = pair) ↔
      Compatible pair := by
  constructor
  · rintro ⟨route, rfl⟩
    exact route.meaning_natural
  · intro compatible
    let route : source ⟶ target :=
      { logical := pair.1
        operational := pair.2
        meaning_natural := compatible }
    exact ⟨route, rfl⟩

/-- Logical and proof-relevant operational data jointly determine a biform
route.  This is the homwise content of faithfulness, stated without imposing
an unnecessary equality among the independent universe levels of native
sentences, signature arrows, and operational evidence. -/
theorem jointProjection_map_injective
    {source target :
      BiformTheory.{uSignature, uHom, uSentence, uTerm} institution} :
    Function.Injective
      (routePair : Hom source target →
        PiInstitution.TheoryHom source.logical target.logical ×
          Translation source.algorithm target.algorithm) := by
  intro left right equalImages
  apply Hom.ext_data
  · exact congrArg Prod.fst equalImages
  · exact congrArg Prod.snd equalImages

#print axioms Hom.ext_data
#print axioms biformTheoryCategory
#print axioms logicalProjection
#print axioms operationalProjection
#print axioms retainedEvents
#print axioms retainedEvents_map_apply
#print axioms semanticTargetFunctor
#print axioms jointProjection
#print axioms routePair
#print axioms Compatible
#print axioms jointProjection_map_compatible
#print axioms jointProjection_map_range_iff_compatible
#print axioms jointProjection_map_injective

end Mettapedia.GSLT.LanguageDef.BiformTheory
