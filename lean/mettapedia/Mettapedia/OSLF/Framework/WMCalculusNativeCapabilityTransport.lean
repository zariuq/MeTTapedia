import Mettapedia.OSLF.Framework.WMCalculusNativeCapability
import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

/-!
# Supported WM answer families under backend maps

A partial capability has no answer section over every state-query request.
Over the supported-request subfunctor, however, its checked answer graph
has a canonical section and is isomorphic to that support context. A
backend map transports this isomorphism when it preserves support, in
addition to the ordinary WM reading operations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityTransport

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusSemantics

/-- Projection from supported answers to supported requests, rather than
to all requests. -/
def graphToSupport {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    (supportedGraph capability).toFunctor ⟶
      (supportPredicate capability).toFunctor where
  app X := TypeCat.ofHom (fun answer =>
    ⟨answer.1.1, answer.2.1⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext answer
    apply Subtype.ext
    rfl

/-- Extraction is a section only on the subcontext of supported requests. -/
def supportAnswerSection {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    (supportPredicate capability).toFunctor ⟶
      (supportedGraph capability).toFunctor where
  app X := TypeCat.ofHom (fun request =>
    ⟨(request.1, R.extract request.1.1 request.1.2),
      ⟨request.2, rfl⟩⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext request
    apply Subtype.ext
    rfl

/-- The support-restricted section is a left inverse of projection. -/
theorem supportAnswerSection_leftInverse {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    supportAnswerSection capability ≫ graphToSupport capability =
      𝟙 (supportPredicate capability).toFunctor := by
  ext X request
  apply Subtype.ext
  rfl

/-- A checked supported answer is exactly the extracted answer. -/
theorem supportAnswerSection_rightInverse {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    graphToSupport capability ≫ supportAnswerSection capability =
      𝟙 (supportedGraph capability).toFunctor := by
  ext X answer
  apply Subtype.ext
  exact congrArg (Prod.mk answer.1.1) answer.2.2

/-- A partial WM answer family is total relative to its exact support,
not relative to the whole state-query context. -/
def supportedAnswerIso {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    (supportedGraph capability).toFunctor ≅
      (supportPredicate capability).toFunctor where
  hom := graphToSupport capability
  inv := supportAnswerSection capability
  hom_inv_id := supportAnswerSection_rightInverse capability
  inv_hom_id := supportAnswerSection_leftInverse capability

variable {State₁ Query₁ V₁ State₂ Query₂ V₂ : Type}
  {source : WMReading State₁ Query₁ V₁}
  {target : WMReading State₂ Query₂ V₂}
  (hom : ReadingMorphism source target)
  (sourceCapability : WMCapability source)
  (targetCapability : WMCapability target)
  (preservesSupport : ∀ state query,
    sourceCapability.supports state query →
      targetCapability.supports (hom.mapState state) (hom.mapQuery query))

/-- Admissible requests map to admissible requests. Operation-preserving
reading maps alone do not supply this extra capability law. -/
def supportMap :
    (supportPredicate sourceCapability).toFunctor ⟶
      (supportPredicate targetCapability).toFunctor where
  app X := TypeCat.ofHom (fun request =>
    ⟨(hom.mapState request.1.1, hom.mapQuery request.1.2),
      preservesSupport request.1.1 request.1.2 request.2⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext request
    apply Subtype.ext
    rfl

/-- Checked answers map to checked answers, retaining admissibility. -/
def supportedGraphMap :
    (supportedGraph sourceCapability).toFunctor ⟶
      (supportedGraph targetCapability).toFunctor where
  app X := TypeCat.ofHom (fun answer =>
    ⟨((hom.mapState answer.1.1.1, hom.mapQuery answer.1.1.2),
        hom.mapEvidence answer.1.2),
      ⟨preservesSupport answer.1.1.1 answer.1.1.2 answer.2.1,
        by rw [← hom.extract_comm, answer.2.2]⟩⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext answer
    apply Subtype.ext
    rfl

/-- The supported projection commutes with the backend map. -/
theorem supportedGraphMap_projection :
    supportedGraphMap hom sourceCapability targetCapability preservesSupport ≫
        graphToSupport targetCapability =
      graphToSupport sourceCapability ≫
        supportMap hom sourceCapability targetCapability preservesSupport := by
  ext X answer
  apply Subtype.ext
  rfl

/-- Supported extraction commutes with backend interpretation. The
support proof is transported rather than silently fabricated. -/
theorem supportedGraphMap_section :
    supportMap hom sourceCapability targetCapability preservesSupport ≫
        supportAnswerSection targetCapability =
      supportAnswerSection sourceCapability ≫
        supportedGraphMap hom sourceCapability targetCapability preservesSupport := by
  ext X request
  apply Subtype.ext
  exact congrArg (Prod.mk
    (hom.mapState request.1.1, hom.mapQuery request.1.2))
      (hom.extract_comm request.1.1 request.1.2).symm

end Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityTransport
