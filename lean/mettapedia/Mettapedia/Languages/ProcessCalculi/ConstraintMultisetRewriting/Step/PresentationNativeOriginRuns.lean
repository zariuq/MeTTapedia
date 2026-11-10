import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuns

/-!
# Source-reference runs retain origin-aware native events

Erasing a parsed reference retains its complete origin-indexed candidate.
Every path admitted by that profile has canonical source references. Forgetting
the origin is a separate map to the base native step, and may identify events
which a reference observer distinguishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Interface

variable {S : Signature} {O : Type} [DecidableEq O] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}
  (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
  (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop)

structure SourceObject
    (_catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
    (_authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop) where
  state : NativeState S O Γ sort

instance sourceQuiver : Quiver (SourceObject catalogue authorized) where
  Hom source target := SourceEvent catalogue authorized source.state target.state

def forgetReferences : SourceObject catalogue authorized ⥤q
    EffectCore.EventObject (profile catalogue authorized).effectCore (profile catalogue authorized).eventAdmission where
  obj source := source.state
  map event := event.event

theorem reference_star_surjective (source : SourceObject catalogue authorized) :
    Function.Surjective ((forgetReferences catalogue authorized).star source) := by
  rintro ⟨target, event⟩
  obtain ⟨reference, _⟩ := QuoteReference.canonical event.firing.origin
  exact ⟨⟨⟨target⟩, event, reference⟩, rfl⟩

/-- This profile retains all valid reference parses. No claim is made that an
arbitrary additional source filter would cover all native origin events. -/
theorem reference_paths_surjective (source : SourceObject catalogue authorized) :
    Function.Surjective ((forgetReferences catalogue authorized).pathStar source) :=
  Prefunctor.pathStar_surjective _ (reference_star_surjective catalogue authorized) source

theorem reference_composition {source middle target : SourceObject catalogue authorized}
    (first : @Quiver.Path _ (sourceQuiver catalogue authorized) source middle)
    (second : @Quiver.Path _ (sourceQuiver catalogue authorized) middle target) :
    (forgetReferences catalogue authorized).mapPath (first.comp second) =
      ((forgetReferences catalogue authorized).mapPath first).comp
        ((forgetReferences catalogue authorized).mapPath second) :=
  Prefunctor.mapPath_comp _ first second

def forgetOrigins : SourceObject catalogue authorized ⥤q
    EffectCore.EventObject (base (S := S) (O := O) (Γ := Γ) (sort := sort)).effectCore
      (base (S := S) (O := O) (Γ := Γ) (sort := sort)).eventAdmission :=
  (forgetReferences catalogue authorized) ⋙q Step.Origins.erase base describe catalogue authorized

theorem forget_origin_event {source target : SourceObject catalogue authorized}
    (event : SourceEvent catalogue authorized source.state target.state) :
    (forgetOrigins catalogue authorized).map event = event.erase catalogue authorized := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins
