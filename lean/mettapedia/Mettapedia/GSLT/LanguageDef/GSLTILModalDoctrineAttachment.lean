import Mettapedia.GSLT.LanguageDef.GSLTILOperationalEquipment
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# Attachment of the OSLF modal doctrine to the operational equipment

The semantic modal fragment of OSLF is functorial on a stricter class of
tight operational arrows than forward simulation alone.  Exact diamond
pullback requires outgoing coverage; exact box pullback additionally requires
incoming coverage.  These bounded maps form `ModallyCoveredTheory`.

This module makes their attachment to the GSLT operational equipment
explicit.  A bounded modal map forgets to a tight operational translation,
its companion is a represented loose route, and its OSLF predicate action is
pullback along the very same tight term map.

Thus the modal doctrine is contravariant structure over a subcategory of the
tight waist.  It is not the loose-route equipment itself, and not every tight
operational arrow supports exact modal reindexing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ModalDoctrineAttachment

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

universe uTerm

/-! ## The modal base embeds into the tight operational base -/

/-- Forget both modal back conditions while retaining equation and step
preservation. -/
def forgetModalTight :
    CategoryTheory.Functor ModallyCoveredTheory.{uTerm}
      OperationalTheory.{uTerm} :=
  CategoryTheory.Functor.comp forgetIncoming forgetCoverage

@[simp] theorem forgetModalTight_obj
    (system : ModallyCoveredTheory.{uTerm}) :
    (forgetModalTight.obj system).theory = system.theory :=
  rfl

@[simp] theorem forgetModalTight_map
    {source target : ModallyCoveredTheory.{uTerm}}
    (translation : source ⟶ target) :
    forgetModalTight.map translation =
      translation.toCoveredTranslation.toOperational := by
  apply OperationalTranslation.ext
  rfl

/-- The modal term family is the operational term-carrier family restricted
along the modal inclusion. -/
def modalTermCarrier :
    CategoryTheory.Functor ModallyCoveredTheory.{uTerm} (Type uTerm) :=
  CategoryTheory.Functor.comp forgetModalTight termCarrier

@[simp] theorem modalTermCarrier_obj
    (system : ModallyCoveredTheory.{uTerm}) :
    modalTermCarrier.obj system = system.theory.Term :=
  rfl

/-! ## Every bounded modal map has a represented companion -/

/-- Regard a bounded modal map as the represented companion of its tight
operational translation. -/
def modalAsRepresentedRoute
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target) :
    RepresentedOperationalRoute source target where
  related := companion translation.mapTerm
  representation := Representation.companionSelf translation.mapTerm
  mapEquiv := translation.mapEquiv
  mapStep := translation.cover.mapStep

@[simp] theorem modalAsRepresentedRoute_related
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target) :
    (modalAsRepresentedRoute translation).related =
      companion translation.mapTerm :=
  rfl

@[simp] theorem modalAsRepresentedRoute_toOperational
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target) :
    (modalAsRepresentedRoute translation).toOperationalTranslation =
      translation.toCoveredTranslation.toOperational := by
  apply OperationalTranslation.ext
  rfl

/-- Composition in the modal base becomes composition in the represented
operational sublayer. -/
theorem modalAsRepresentedRoute_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : ModalTranslation first middle)
    (later : ModalTranslation middle last) :
    (modalAsRepresentedRoute (earlier.comp later)
        ).toOperationalTranslation =
      (RepresentedOperationalRoute.comp
        (modalAsRepresentedRoute earlier)
        (modalAsRepresentedRoute later)).toOperationalTranslation := by
  apply OperationalTranslation.ext
  rfl

/-! ## The logical action uses the same tight map -/

/-- OSLF predicate transport is inverse image along the selected tight map
after that map descends to equation classes; no second translation is hidden
in the logical layer. -/
theorem oslf_pullback_uses_tight_map
    {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target)
    (predicate : Set (SemanticTerm target)) :
    (ModalTranslation.pullback translation).mapPred predicate =
      Set.preimage translation.onSemanticTheories.mapTerm predicate :=
  rfl

/-- The exact attachment criterion: a forward tight arrow supports both OSLF
modalities exactly iff it extends to the bounded modal base. -/
theorem exact_modal_reindexing_iff_bounded_extension
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    ((∀ predicate : Set target.Term,
        Set.preimage translation.mapTerm (gsltDiamond target predicate) =
          gsltDiamond source (Set.preimage translation.mapTerm predicate)) ∧
      (∀ predicate : Set target.Term,
        Set.preimage translation.mapTerm (gsltBox target predicate) =
          gsltBox source (Set.preimage translation.mapTerm predicate))) ↔
      ∃ modal : ModalTranslation source target,
        modal.toCoveredTranslation.toOperational = translation :=
  OperationalTranslation.modalCommutation_iff_hasModalExtension translation

#print axioms forgetModalTight_map
#print axioms modalAsRepresentedRoute_toOperational
#print axioms modalAsRepresentedRoute_comp
#print axioms oslf_pullback_uses_tight_map
#print axioms exact_modal_reindexing_iff_bounded_extension
#print axioms Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.Canary.forward_only_does_not_preserve_diamond
#print axioms Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.Canary.outgoing_coverage_does_not_preserve_box

end Mettapedia.GSLT.LanguageDef.GSLTIL.ModalDoctrineAttachment
