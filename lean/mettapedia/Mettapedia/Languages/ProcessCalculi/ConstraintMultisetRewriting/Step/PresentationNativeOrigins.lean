import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Origins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationQuoteReference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativePreparation

/-!
# Source rule references at the native activation boundary

The catalogue returns stored rule data. The existing native step performs
opening, solving, guard admission and publication, with the full firing and
its recipes retained. The origin profile separately checks lookup agreement
and permission for the reference. These are interpretation parameters, not
an evaluator callback returning an assumed successful transition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface

variable {S : Signature} {O : Type} [DecidableEq O] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}

abbrev RuleData (s : NativeState S O Γ sort) :=
  RuleInstance (Term (signature S (ContextualActivatedStep.source s.locals s.state.declarations)) Γ sort)

abbrev Catalogue := (s : NativeState S O Γ sort) → Nat → Option (RuleData s)
abbrev Candidate := Step.Origins.Candidate (Firing := NativeFiring (S := S) (O := O) (Γ := Γ) (sort := sort)) Nat

def describe {s : NativeState S O Γ sort} (firing : NativeFiring s) : RuleData s := firing.rule

abbrev base := (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep

def profile (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
    (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop) :=
  Step.Origins.profile base describe catalogue authorized

variable (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
  (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop)

structure SourceEvent (source target : NativeState S O Γ sort) where
  event : (profile catalogue authorized).effectCore.Event (profile catalogue authorized).eventAdmission source target
  reference : QuoteReference.Parsed event.firing.origin

def SourceEvent.erase {source target : NativeState S O Γ sort}
    (event : SourceEvent catalogue authorized source target) : base.effectCore.Event base.eventAdmission source target :=
  Step.Origins.forgetEvent base describe catalogue authorized event.event

theorem SourceEvent.origin {source target : NativeState S O Γ sort}
    (event : SourceEvent catalogue authorized source target) :
    catalogue source event.event.firing.origin = some event.event.firing.firing.rule ∧
      authorized source event.event.firing.origin event.event.firing.firing := event.event.permitted.2

/-- A real native event is reflected once its declared origin and permission
are supplied. The source reference is an actual canonical grammar derivation. -/
theorem lift_native_event {source target : NativeState S O Γ sort} (key : Nat)
    (event : base.effectCore.Event base.eventAdmission source target)
    (resolved : catalogue source key = some event.firing.rule) (permitted : authorized source key event.firing) :
    ∃ lifted : SourceEvent catalogue authorized source target,
      lifted.erase catalogue authorized = event ∧ lifted.event.firing.origin = key := by
  obtain ⟨reference, _⟩ := QuoteReference.canonical key
  refine ⟨⟨Step.Origins.liftEvent base describe catalogue authorized key event resolved permitted, reference⟩, ?_, rfl⟩
  exact Step.Origins.forget_lift base describe catalogue authorized key event resolved permitted

/-- The reference authorizes the actual stored rule; its physical opening and
published endpoint still come from the native firing, including recipes. -/
theorem SourceEvent.prepared_source {source target : NativeState S O Γ sort}
    (code : Intrinsic.HeadPresentation (SchemaPreparation.TargetSignature source.locals source.state.declarations))
    (event : SourceEvent catalogue authorized source target) :
    catalogue source event.event.firing.origin = some event.event.firing.firing.rule ∧
      authorized source event.event.firing.origin event.event.firing.firing ∧
      ∃ physical, NativePreparation.prepare? code event.event.firing.firing = some physical ∧
        SchemaPreparation.readSourceViews? source.locals source.state.declarations code Γ sort
          (SchemaPreparation.printViews physical) =
            some (SchemaPreparation.viewsOf source.locals source.state.declarations event.event.firing.firing.prepared) ∧
        ∃ admitted : event.event.firing.firing.Realized,
          publishedState event.event.firing.firing.recipes
            (event.event.firing.firing.pinned admitted).firing = target :=
  ⟨event.origin catalogue authorized |>.1, event.origin catalogue authorized |>.2,
    NativePreparation.event_source_views code (event.erase catalogue authorized)⟩

theorem unauthorized_has_no_event {source target : NativeState S O Γ sort} (key : Nat)
    (denied : ∀ firing, ¬ authorized source key firing) :
    ¬ ∃ event : SourceEvent catalogue authorized source target, event.event.firing.origin = key := by
  rintro ⟨event, same⟩
  exact denied event.event.firing.firing (same ▸ (event.origin catalogue authorized).2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins
