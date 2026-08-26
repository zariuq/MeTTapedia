import Mathlib.CategoryTheory.Whiskering
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# Indexed and lax OSLF modal transport

OSLF is contravariant on bounded operational maps because native predicates
pull back along term maps.  Consequently, a diagram of bounded GSLTs indexed
by `J` determines a diagram of exact modal predicate theories indexed by
`Jᵒᵖ`.

Growing languages usually have only forward operational maps: old steps are
preserved, but a later stage may add new behavior at an old term.  Predicate
pullback then preserves the modal laws only in one direction.  This module
packages those one-sided laws as a lax modal category and lifts OSLF
pointwise to arbitrary forward operational diagrams.

This is a construction on explicit diagram categories.  Promoting it to the
free filtered-colimit completion `Ind(C)` would additionally require the
appropriate continuity or accessibility theorem; contravariance suggests a
pro-object on the native side.  No such preservation theorem is assumed
here.
-/

namespace Mettapedia.OSLF.Framework.IndexedModalFunctor

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

universe uTerm uIndex vIndex

/-! ## One-sided modal maps -/

/-- A modal predicate theory viewed in the category whose morphisms preserve
the generated modalities in the directions forced by forward simulation. -/
structure ForwardModalPredicateTheory where
  modal : ModalPredicateTheory.{uTerm}

namespace ForwardModalPredicateTheory

/-- A lax modal map.  The variance of the two laws is forced by predicate
pullback along a forward simulation:

* source diamonds map into target diamonds;
* target boxes pull back into source boxes.

The `source` and `target` below are modal predicate theories; when the map is
induced by a GSLT translation, their order is already reversed. -/
structure Hom (source target : ForwardModalPredicateTheory.{uTerm}) where
  mapPred : CompleteLatticeHom (Set source.modal.State) (Set target.modal.State)
  map_diamond_lax : forall predicate,
    target.modal.diamond (mapPred predicate) <=
      mapPred (source.modal.diamond predicate)
  map_box_lax : forall predicate,
    mapPred (source.modal.box predicate) <=
      target.modal.box (mapPred predicate)

namespace Hom

/-- Complete-lattice homomorphisms are monotone.  This local lemma avoids
depending on a particular bundled-order-hom coercion. -/
private theorem map_mono
    {source target : ForwardModalPredicateTheory.{uTerm}}
    (map : CompleteLatticeHom
      (Set source.modal.State) (Set target.modal.State)) :
    Monotone map := by
  intro left right order
  calc
    map left <= map left ⊔ map right := le_sup_left
    _ = map (left ⊔ right) := (map_sup map left right).symm
    _ = map right := congrArg map (sup_eq_right.mpr order)

@[ext]
theorem ext {source target : ForwardModalPredicateTheory.{uTerm}}
    {first second : Hom source target}
    (mapPred : first.mapPred = second.mapPred) : first = second := by
  cases first
  cases second
  cases mapPred
  rfl

/-- Identity is exact, hence lax in both required directions. -/
def id (theory : ForwardModalPredicateTheory.{uTerm}) : Hom theory theory where
  mapPred := CompleteLatticeHom.id _
  map_diamond_lax := by
    intro predicate
    exact le_rfl
  map_box_lax := by
    intro predicate
    exact le_rfl

/-- Lax modal maps compose. -/
def comp {first middle last : ForwardModalPredicateTheory.{uTerm}}
    (earlier : Hom first middle) (later : Hom middle last) : Hom first last where
  mapPred := later.mapPred.comp earlier.mapPred
  map_diamond_lax := by
    intro predicate
    exact (later.map_diamond_lax (earlier.mapPred predicate)).trans
      (map_mono later.mapPred (earlier.map_diamond_lax predicate))
  map_box_lax := by
    intro predicate
    exact (map_mono later.mapPred (earlier.map_box_lax predicate)).trans
      (later.map_box_lax (earlier.mapPred predicate))

end Hom

instance : CategoryTheory.Category ForwardModalPredicateTheory where
  Hom := Hom
  id := Hom.id
  comp earlier later := Hom.comp earlier later
  id_comp morphism := by
    apply Hom.ext
    rfl
  comp_id morphism := by
    apply Hom.ext
    rfl
  assoc first second third := by
    apply Hom.ext
    rfl

end ForwardModalPredicateTheory

/-! ## Forward simulations induce lax modal maps -/

namespace OperationalTranslation

/-- A forward operational translation gives the diamond inclusion that
remains valid without outgoing step reflection. -/
theorem preimage_diamond_le
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (predicate : Set target.Term) :
    gsltDiamond source (Set.preimage translation.mapTerm predicate) <=
      Set.preimage translation.mapTerm (gsltDiamond target predicate) := by
  intro sourceTerm sourceDiamond
  obtain ⟨sourceTarget, sourceStep, targetMeaning⟩ :=
    (gsltDiamond_spec source
      (Set.preimage translation.mapTerm predicate) sourceTerm).mp sourceDiamond
  apply (gsltDiamond_spec target predicate
    (translation.mapTerm sourceTerm)).mpr
  exact ⟨translation.mapTerm sourceTarget,
    translation.mapStep sourceStep, targetMeaning⟩

/-- A forward operational translation gives the contravariant box inclusion
that remains valid without incoming step reflection. -/
theorem preimage_box_le
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (predicate : Set target.Term) :
    Set.preimage translation.mapTerm (gsltBox target predicate) <=
      gsltBox source (Set.preimage translation.mapTerm predicate) := by
  intro sourceTerm targetBox
  apply (gsltBox_spec source
    (Set.preimage translation.mapTerm predicate) sourceTerm).mpr
  intro sourcePredecessor sourceStep
  exact (gsltBox_spec target predicate
    (translation.mapTerm sourceTerm)).mp targetBox
      (translation.mapTerm sourcePredecessor)
      (translation.mapStep sourceStep)

/-- Predicate pullback along any forward operational translation is a lax
modal map. -/
def pullbackLax
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    ForwardModalPredicateTheory.Hom
      ⟨oslfModalObject target⟩ ⟨oslfModalObject source⟩ where
  mapPred := CompleteLatticeHom.setPreimage translation.mapTerm
  map_diamond_lax := preimage_diamond_le translation
  map_box_lax := preimage_box_le translation

end OperationalTranslation

/-- The operational modal fragment generated by one GSLT, regarded as a lax
modal object. -/
def oslfForwardModalObject (theory : GSLT.{uTerm}) :
    ForwardModalPredicateTheory.{uTerm} :=
  ⟨oslfModalObject theory⟩

/-- OSLF on forward operational maps is a contravariant lax-modal functor. -/
def oslfForwardModalFunctor :
    CategoryTheory.Functor
      (OperationalTheory.{uTerm})ᵒᵖ ForwardModalPredicateTheory.{uTerm} where
  obj object := oslfForwardModalObject object.unop.theory
  map translation := OperationalTranslation.pullbackLax translation.unop
  map_id object := by
    apply ForwardModalPredicateTheory.Hom.ext
    rfl
  map_comp earlier later := by
    apply ForwardModalPredicateTheory.Hom.ext
    rfl

/-! ## Exact maps embed in the lax category -/

/-- Forget equality of modal transport while retaining the corresponding
one-sided laws. -/
def forgetExactModal :
    CategoryTheory.Functor
      ModalPredicateTheory.{uTerm} ForwardModalPredicateTheory.{uTerm} where
  obj theory := ⟨theory⟩
  map translation :=
    { mapPred := translation.mapPred
      map_diamond_lax := by
        intro predicate
        rw [<- translation.map_diamond predicate]
      map_box_lax := by
        intro predicate
        rw [translation.map_box predicate] }
  map_id object := by
    apply ForwardModalPredicateTheory.Hom.ext
    rfl
  map_comp earlier later := by
    apply ForwardModalPredicateTheory.Hom.ext
    rfl

/-! ## Pointwise lifts to indexed families -/

/-- Pointwise OSLF for an arbitrary forward diagram.  Contravariance changes
the index from `J` to `Jᵒᵖ`; stage maps become lax modal pullbacks. -/
def forwardIndexedOSLF
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : IndexedOperational.Diagram.{uTerm, uIndex, vIndex} Index) :
    CategoryTheory.Functor Indexᵒᵖ ForwardModalPredicateTheory.{uTerm} :=
  diagram.op.comp oslfForwardModalFunctor

/-- Pointwise exact OSLF for a diagram whose maps have both outgoing and
incoming local coverage. -/
def exactIndexedOSLF
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : CategoryTheory.Functor Index
      ModallyCoveredTheory.{uTerm}) :
    CategoryTheory.Functor Indexᵒᵖ ModalPredicateTheory.{uTerm} :=
  diagram.op.comp oslfModalFunctor

/-! ## Functoriality in the whole indexed family

A natural transformation between forward diagrams is itself reversed by
predicate pullback.  Thus pointwise OSLF is contravariant not only in each
fibre but also in the category of diagrams.  These functors are the precise
diagram-category form of indexed OSLF; they do not assume an `Ind`-completion
or preservation of filtered colimits. -/

/-- Forward indexed OSLF as a functor on the category of `Index`-shaped
operational diagrams. -/
def forwardIndexedOSLFFunctor
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index] :
    CategoryTheory.Functor
      (CategoryTheory.Functor Index OperationalTheory.{uTerm})ᵒᵖ
      (CategoryTheory.Functor Indexᵒᵖ
        ForwardModalPredicateTheory.{uTerm}) where
  obj diagram := forwardIndexedOSLF diagram.unop
  map transformation :=
    CategoryTheory.Functor.whiskerRight
      (CategoryTheory.NatTrans.op transformation.unop)
      oslfForwardModalFunctor
  map_id diagram := by
    ext stage
    rfl
  map_comp first second := by
    ext stage
    rfl

/-- Exact indexed OSLF as a functor on diagrams whose stage maps have both
outgoing and incoming local coverage. -/
def exactIndexedOSLFFunctor
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index] :
    CategoryTheory.Functor
      (CategoryTheory.Functor Index ModallyCoveredTheory.{uTerm})ᵒᵖ
      (CategoryTheory.Functor Indexᵒᵖ ModalPredicateTheory.{uTerm}) where
  obj diagram := exactIndexedOSLF diagram.unop
  map transformation :=
    CategoryTheory.Functor.whiskerRight
      (CategoryTheory.NatTrans.op transformation.unop)
      oslfModalFunctor
  map_id diagram := by
    ext stage
    rfl
  map_comp first second := by
    ext stage
    rfl

/-! ## Exactness canaries -/

/-- Positive: a bounded operational map's lax diamond law is actually an
equality. -/
theorem modal_pullback_diamond_exact
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target)
    (predicate : Set target.Term) :
    gsltDiamond source (Set.preimage translation.mapTerm predicate) =
      Set.preimage translation.mapTerm (gsltDiamond target predicate) := by
  exact
    (Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
      translation.toCoveredTranslation predicate).symm

/-- Positive: a bounded operational map's lax box law is actually an
equality. -/
theorem modal_pullback_box_exact
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target)
    (predicate : Set target.Term) :
    Set.preimage translation.mapTerm (gsltBox target predicate) =
      gsltBox source (Set.preimage translation.mapTerm predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.ModalTranslation.preimage_box
    translation predicate

section AxiomAudit

#print axioms OperationalTranslation.preimage_diamond_le
#print axioms OperationalTranslation.preimage_box_le
#print axioms oslfForwardModalFunctor
#print axioms forwardIndexedOSLF
#print axioms exactIndexedOSLF
#print axioms forwardIndexedOSLFFunctor
#print axioms exactIndexedOSLFFunctor
#print axioms modal_pullback_diamond_exact
#print axioms modal_pullback_box_exact

end AxiomAudit

end Mettapedia.OSLF.Framework.IndexedModalFunctor
