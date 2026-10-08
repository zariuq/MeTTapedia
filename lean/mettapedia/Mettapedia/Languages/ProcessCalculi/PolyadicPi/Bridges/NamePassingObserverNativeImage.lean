import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverFunctor
import Mettapedia.CategoryTheory.FunctorOriginImage
import Mettapedia.TypeTheory.DisplayedPresheafTheoryRestrictionIso

/-!
# Native logic of the observer image with retained elaborations

The observer image keeps each actual protocol client together with its
source elaboration. It is categorically equivalent to the source observer
category. The canonical native product and classifier comparisons are
therefore invertible on this image. Forgetting the elaboration recovers
the independently authored protocol client and its actual rho observation;
no equivalence with the full protocol-context category is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverNativeImage

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafTheoryRestriction
open NamePassingLambda NamePassingContexts NamePassingObserverFunctor NamePassingObserverAdequacy

abbrev RetainedScope := Mettapedia.CategoryTheory.FunctorOriginImage.Object translation

def observerEquivalence : SourceScope ≌ RetainedScope :=
  Mettapedia.CategoryTheory.FunctorOriginImage.equivalence translation

def actualProtocol : RetainedScope ⥤ ProtocolScope :=
  Mettapedia.CategoryTheory.FunctorOriginImage.forget translation

theorem actualProtocol_is_translation : observerEquivalence.functor ⋙ actualProtocol = translation :=
  Mettapedia.CategoryTheory.FunctorOriginImage.embed_forget translation

/-- Admission and retained elaboration have the same underlying clients,
while the latter also remembers which elaboration was supplied. -/
theorem admitted_iff_retained {before after : SourceScope}
    (client : ProtocolContexts.Context before.context after.context) :
    Admitted client ↔ ∃ retained :
        observerEquivalence.functor.obj before ⟶ observerEquivalence.functor.obj after,
      (actualProtocol.map retained) = client := by
  constructor
  · rintro ⟨origin, agrees⟩
    exact ⟨⟨client, origin, agrees⟩, rfl⟩
  · rintro ⟨retained, rfl⟩
    exact ⟨retained.source, retained.agrees⟩

/-- Native logical transport uses the retained observer category. It
does not add quantification over unelaborated target clients. -/
noncomputable def productComparisonIso
    (P : RetainedScopeᵒᵖ ⥤ Type) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    restrictFamily observerEquivalence.functor P (piDisplayed A B) ≅
      piDisplayed (restrictFamily observerEquivalence.functor P A)
        (reindexDisplayed (totalComparison observerEquivalence.functor P A).hom
          (restrictFamily observerEquivalence.functor (totalSpace A) B)) :=
  DisplayedPresheafTheoryRestrictionIso.productIso observerEquivalence.functor P A B

theorem productComparisonIso_canonical
    (P : RetainedScopeᵒᵖ ⥤ Type) (A : DisplayedFamily P)
    (B : DisplayedFamily (totalSpace A)) :
    (productComparisonIso P A B).hom =
      productComparison observerEquivalence.functor P A B :=
  DisplayedPresheafTheoryRestrictionIso.productIso_hom observerEquivalence.functor P A B

noncomputable def classifierComparisonIso :
    observerEquivalence.functor.op ⋙ Mettapedia.GSLT.Topos.omegaFunctor (C := RetainedScope) ≅
      Mettapedia.GSLT.Topos.omegaFunctor (C := SourceScope) :=
  DisplayedPresheafTheoryRestrictionIso.classifierIso observerEquivalence.functor

/-- The retained logical observer executes its independently stored target
client. Its agreement equation connects that execution to the source. -/
theorem retained_client_execution {before after : SourceScope}
    (client : observerEquivalence.functor.obj before ⟶ observerEquivalence.functor.obj after)
    (source : Expr before.context) :
    MayReturn (client.source.plug source) ↔
      ProtocolMayReturn ((actualProtocol.map client).plug (program source)) := by
  change MayReturn (client.source.plug source) ↔ ProtocolMayReturn (client.target.plug (program source))
  rw [← client.agrees]
  exact context_mayReturn_iff client.source source

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverNativeImage
