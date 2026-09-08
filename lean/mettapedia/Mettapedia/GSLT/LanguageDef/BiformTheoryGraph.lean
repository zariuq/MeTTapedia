import Mathlib.CategoryTheory.Products.Basic
import Mettapedia.GSLT.Core.ProofRelevantTranslationCategory
import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.GSLT.LanguageDef.TheoryGraph

/-!
# Biform theories over the theory graph

A biform theory combines a closed logical theory with a proof-relevant
algorithm whose retained events carry formulas explaining their mathematical
meaning.  The biform category of one institution fixes the logic.  Here the
logical component is an object of the theory graph, so the institution may
vary along an arrow: a simple type theory, a dependent type theory, or
another native logic can be connected without first translating all of them
into one syntax.

An arrow is a compatibility cell between two independent translations: an
arrow of the theory graph transports native sentences, and a proof-relevant
GSLT translation transports operational events, with the meaning square
commuting.  The fixed-institution biform category embeds faithfully as the
vertical fibre over that institution, through the fibre inclusion of the
theory graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.BiformTheoryGraph

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uSignature uHom uSentence uTerm

/-- The admission condition for an event-meaning assignment in its selected
native closed theory. -/
def MeaningSound
    (logical : TheoryGraph.Object.{uSignature, uHom, uSentence})
    (algorithm : ProofRelevantGSLT.{uTerm})
    (meaning : algorithm.Event →
      logical.institution.sentence.obj logical.logical.signature) : Prop :=
  ∀ event, meaning event ∈ logical.logical.theory.1

/-- A theory-graph object equipped with one proof-relevant operational model
and a theorem explaining every retained primitive event. -/
structure Object where
  logical : TheoryGraph.Object.{uSignature, uHom, uSentence}
  algorithm : ProofRelevantGSLT.{uTerm}
  meaning : algorithm.Event →
    logical.institution.sentence.obj logical.logical.signature
  meaning_sound : MeaningSound logical algorithm meaning

namespace Object

/-- Every retained event carries a theorem in the object's own native logic. -/
theorem event_meaning
    (object : Object.{uSignature, uHom, uSentence, uTerm})
    (event : object.algorithm.Event) :
    object.meaning event ∈ object.logical.logical.theory.1 :=
  object.meaning_sound event

end Object

/-- A biform arrow makes native sentence translation along the theory graph
and proof-relevant event translation commute. -/
structure Hom
    (source target : Object.{uSignature, uHom, uSentence, uTerm}) where
  logical : source.logical ⟶ target.logical
  operational : Translation source.algorithm target.algorithm
  meaning_natural : ∀ event : source.algorithm.Event,
    TheoryGraph.translateSentence
        (TheoryGraph.Hom.institution logical) (TheoryGraph.Hom.mapSignature logical)
        (source.meaning event) =
      target.meaning (operational.mapEvent event)

namespace Hom

variable
  {first middle last : Object.{uSignature, uHom, uSentence, uTerm}}

/-- Biform arrows are determined by their logical and operational
translations.  The compatibility square is proof-irrelevant. -/
@[ext]
theorem ext_data {left right : Hom first middle}
    (logical : left.logical = right.logical)
    (operational : left.operational = right.operational) :
    left = right := by
  cases left
  cases right
  cases logical
  cases operational
  rfl

/-- Translating an event preserves its native meaning theorem. -/
theorem mapped_event_meaning (route : Hom first middle)
    (event : first.algorithm.Event) :
    middle.meaning (route.operational.mapEvent event) ∈
      middle.logical.logical.theory.1 := by
  have translated := TheoryGraph.Hom.preserves route.logical (first.meaning_sound event)
  rw [route.meaning_natural] at translated
  exact translated

/-- Identity changes neither native meaning nor retained event identity. -/
def identity (object : Object.{uSignature, uHom, uSentence, uTerm}) :
    Hom object object where
  logical := CategoryTheory.CategoryStruct.id object.logical
  operational := Translation.id object.algorithm
  meaning_natural := by
    intro event
    rw [TheoryGraph.translateSentence_id, Translation.mapEvent_id]

/-- Biform arrows compose by composing both faces; the two meaning squares
paste into the composite square. -/
def comp (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  logical := earlier.logical ≫ later.logical
  operational := Translation.comp earlier.operational later.operational
  meaning_natural := by
    intro event
    rw [TheoryGraph.translateSentence_comp, earlier.meaning_natural, later.meaning_natural,
      Translation.mapEvent_comp]

end Hom

instance instQuiver : Quiver
    (Object.{uSignature, uHom, uSentence, uTerm}) where
  Hom := Hom

instance instCategory : CategoryTheory.Category
    (Object.{uSignature, uHom, uSentence, uTerm}) where
  id := Hom.identity
  comp := Hom.comp
  id_comp route := by
    apply Hom.ext_data
    · exact CategoryTheory.Category.id_comp route.logical
    · exact Translation.identity_comp route.operational
  comp_id route := by
    apply Hom.ext_data
    · exact CategoryTheory.Category.comp_id route.logical
    · exact Translation.comp_identity route.operational
  assoc earlier middle later := by
    apply Hom.ext_data
    · exact CategoryTheory.Category.assoc earlier.logical middle.logical later.logical
    · exact Translation.comp_assoc earlier.operational middle.operational
        later.operational

/-! ## Independent projections and their compatibility locus -/

/-- Forget algorithms while retaining the theory-graph arrow. -/
def logicalProjection :
    CategoryTheory.Functor Object.{uSignature, uHom, uSentence, uTerm}
      TheoryGraph.Object.{uSignature, uHom, uSentence} where
  obj object := object.logical
  map route := route.logical
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget native logical meaning while retaining the complete
proof-relevant operational translation. -/
def operationalProjection :
    CategoryTheory.Functor Object.{uSignature, uHom, uSentence, uTerm}
      ProofRelevantGSLT.{uTerm} where
  obj object := object.algorithm
  map route := route.operational
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Retained operational occurrences vary functorially along biform arrows. -/
def retainedEvents :
    CategoryTheory.Functor Object.{uSignature, uHom, uSentence, uTerm}
      (Type uTerm) :=
  operationalProjection ⋙ Mettapedia.GSLT.ProofRelevant.eventFunctor

/-- Forget the operational model and read each native closed theory through
the common semantic NIK interface. -/
def semanticTargetFunctor :
    CategoryTheory.Functor Object.{uSignature, uHom, uSentence, uTerm}
      CertifiedTheoryCategory.TheoryObject.{0, uSignature, uSentence} :=
  logicalProjection ⋙ TheoryGraph.semanticTargetFunctor

/-- The independently meaningful components of one biform arrow. -/
def routePair
    {source target : Object.{uSignature, uHom, uSentence, uTerm}}
    (route : Hom source target) :
    (source.logical ⟶ target.logical) × Translation source.algorithm target.algorithm :=
  (route.logical, route.operational)

/-- A logical/operational pair is a biform arrow exactly when event meanings
commute across the pair. -/
def Compatible
    {source target : Object.{uSignature, uHom, uSentence, uTerm}}
    (pair : (source.logical ⟶ target.logical) ×
      Translation source.algorithm target.algorithm) : Prop :=
  ∀ event : source.algorithm.Event,
    TheoryGraph.translateSentence
        (TheoryGraph.Hom.institution pair.1) (TheoryGraph.Hom.mapSignature pair.1)
        (source.meaning event) =
      target.meaning (pair.2.mapEvent event)

/-- The image of biform arrows is exactly the compatibility locus, not the
whole product of logical and operational arrows. -/
theorem routePair_range_iff_compatible
    {source target : Object.{uSignature, uHom, uSentence, uTerm}}
    (pair : (source.logical ⟶ target.logical) ×
      Translation source.algorithm target.algorithm) :
    (∃ route : Hom source target, routePair route = pair) ↔
      Compatible pair := by
  constructor
  · rintro ⟨route, rfl⟩
    exact route.meaning_natural
  · intro compatible
    exact ⟨⟨pair.1, pair.2, compatible⟩, rfl⟩

/-- Logical and operational actions jointly determine a biform arrow. -/
theorem routePair_injective
    {source target : Object.{uSignature, uHom, uSentence, uTerm}} :
    Function.Injective (routePair : Hom source target → _) := by
  intro left right equal
  apply Hom.ext_data
  · exact congrArg Prod.fst equal
  · exact congrArg Prod.snd equal

/-! ## Fixed-institution biform categories are vertical fibres -/

section Fibre

variable {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- The theory-graph object of a closed theory of one fixed institution. -/
abbrev fixedLogical (theory : PiInstitution.TheoryObject institution) :
    TheoryGraph.Object.{uSignature, uHom, uSentence} :=
  (TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).obj theory

/-- A vertical arrow of the theory graph translates sentences exactly as its
theory morphism does. -/
theorem translateSentence_fibre
    {source target : PiInstitution.TheoryObject institution}
    (route : PiInstitution.TheoryHom source target)
    (formula : institution.sentence.obj source.signature) :
    TheoryGraph.translateSentence
        (TheoryGraph.Hom.institution
          ((TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map route))
        (TheoryGraph.Hom.mapSignature
          ((TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map route))
        formula =
      institution.sentence.map route.mapSignature formula := by
  show TheoryGraph.translateSentence
      ((Grothendieck.ι TheoryGraph.closedTheories
        ⟨CategoryTheory.Cat.of Signature, institution⟩).map route).base
      ((Grothendieck.ι TheoryGraph.closedTheories
        ⟨CategoryTheory.Cat.of Signature, institution⟩).map route).fiber.mapSignature
      formula = _
  simp only [Grothendieck.ι]
  rw [TheoryGraph.theoryHom_comp_mapSignature, TheoryGraph.eqToHom_mapSignature]
  change institution.sentence.map
    (CategoryTheory.CategoryStruct.id source.signature ≫ route.mapSignature) formula = _
  rw [CategoryTheory.Category.id_comp]

/-- Regard an ordinary biform theory as an object over the theory graph
without changing its logic, algorithm, or event meanings. -/
def fixedObject (theory : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution) :
    Object.{uSignature, uHom, uSentence, uTerm} where
  logical := fixedLogical theory.logical
  algorithm := theory.algorithm
  meaning := theory.meaning
  meaning_sound := theory.meaning_sound

/-- An ordinary biform route is the vertical arrow over the identity
institution translation. -/
def Hom.ofFixed
    {source target : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (route : BiformTheory.Hom source target) :
    Hom (fixedObject source) (fixedObject target) where
  logical := (TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map route.logical
  operational := route.operational
  meaning_natural := by
    intro event
    rw [translateSentence_fibre]
    exact route.meaning_natural event

/-- The ordinary biform category embeds as a vertical fibre. -/
def fixedFiber (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor
      (BiformTheory.{uSignature, uHom, uSentence, uTerm} institution)
      Object.{uSignature, uHom, uSentence, uTerm} where
  obj := fixedObject
  map := Hom.ofFixed
  map_id theory := by
    apply Hom.ext_data
    · exact (TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map_id theory.logical
    · rfl
  map_comp earlier later := by
    apply Hom.ext_data
    · exact (TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map_comp
        earlier.logical later.logical
    · rfl

/-- The vertical biform embedding retains distinct ordinary routes. -/
theorem fixedFiber_map_injective
    {source target : BiformTheory.{uSignature, uHom, uSentence, uTerm} institution} :
    Function.Injective
      (fun route : BiformTheory.Hom source target => (fixedFiber institution).map route) := by
  intro left right equal
  apply BiformTheory.Hom.ext_data
  · haveI := TheoryGraph.fibre_faithful
      (⟨CategoryTheory.Cat.of Signature, institution⟩ : PiInstitutionCategory.Object)
    exact (TheoryGraph.fibre ⟨CategoryTheory.Cat.of Signature, institution⟩).map_injective
      (congrArg Hom.logical equal)
  · exact congrArg Hom.operational equal

/-- The fixed-institution biform category is a faithful vertical fibre. -/
instance fixedFiber_faithful (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    (fixedFiber institution).Faithful where
  map_injective := by
    intro source target left right equal
    exact (fixedFiber_map_injective (institution := institution) (source := source)
      (target := target)) equal

end Fibre

#print axioms Object.event_meaning
#print axioms Hom.mapped_event_meaning
#print axioms instCategory
#print axioms semanticTargetFunctor
#print axioms fixedFiber_faithful
#print axioms routePair_range_iff_compatible

end Mettapedia.GSLT.LanguageDef.BiformTheoryGraph
