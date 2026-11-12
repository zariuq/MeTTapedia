import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedEffects

/-!
# The authored Execute rule for an origin-aware native profile

Exact codecs belong to represented states and candidates. Their interpretation
into the origin-aware native profile preserves every prepared result, before
permission is considered. The semantic native carriers remain unrestricted.
Reflection at a specified represented endpoint additionally requires injective
state interpretation; existence of a represented result needs no such law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.MeTTaIL.Engine
open Interface

universe uR uC

variable {S : Signature} {O : Type} [DecidableEq O] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}
  (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
  (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop)
  {Represented : Type uR} {Selected : Represented → Type uC}
  (representation : (profile catalogue authorized).effectCore.Representation Represented Selected)
  (code : Encoding Represented Selected)
  (decision : Decisions representation.effect
    (representation.admission (profile catalogue authorized).eventAdmission))

theorem authored_execution_iff_represented {source target : Represented} (candidate : Selected source) :
    atState (code.state.view (sort := ()) target) ∈ rewriteStepWithPremisesUsing
      (effectQueries representation.effect
        (representation.admission (profile catalogue authorized).eventAdmission)
        code decision).relations authoredLanguage
      (request (code.state.view (sort := ()) source) (code.firing.view (sort := ()) ⟨source, candidate⟩)) ↔
      ∃ event : representation.effect.Event
        (representation.admission (profile catalogue authorized).eventAdmission) source target,
        event.firing = candidate := by
  rw [authored_root_execution]
  exact execution_iff_event _ _ code decision (t := target) candidate

theorem authored_execution_iff (faithful : Function.Injective representation.state)
    {source target : Represented} (candidate : Selected source) :
    atState (code.state.view (sort := ()) target) ∈ rewriteStepWithPremisesUsing
      (effectQueries representation.effect
        (representation.admission (profile catalogue authorized).eventAdmission)
        code decision).relations authoredLanguage
      (request (code.state.view (sort := ()) source) (code.firing.view (sort := ()) ⟨source, candidate⟩)) ↔
      ∃ event : SourceEvent catalogue authorized (representation.state source) (representation.state target),
        event.event.firing = representation.firing candidate := by
  rw [authored_execution_iff_represented, representation.event_iff faithful]
  constructor
  · rintro ⟨event, same⟩
    obtain ⟨reference, _⟩ := QuoteReference.canonical event.firing.origin
    exact ⟨⟨event, reference⟩, same⟩
  · rintro ⟨event, same⟩
    exact ⟨event.event, same⟩

theorem authored_execution_preserves {source target : Represented} (candidate : Selected source)
    (executed : atState (code.state.view (sort := ()) target) ∈ rewriteStepWithPremisesUsing
      (effectQueries representation.effect
        (representation.admission (profile catalogue authorized).eventAdmission)
        code decision).relations authoredLanguage
      (request (code.state.view (sort := ()) source) (code.firing.view (sort := ()) ⟨source, candidate⟩))) :
    ∃ event : SourceEvent catalogue authorized (representation.state source) (representation.state target),
      event.event.firing = representation.firing candidate := by
  obtain ⟨event, same⟩ := (authored_execution_iff_represented _ _ _ _ _ candidate).mp executed
  let native := representation.mapEvent event
  obtain ⟨reference, _⟩ := QuoteReference.canonical native.firing.origin
  exact ⟨⟨native, reference⟩, congrArg representation.firing same⟩

theorem native_event_has_authored_execution {source : Represented} {target : NativeState S O Γ sort}
    (candidate : Selected source) (event : SourceEvent catalogue authorized (representation.state source) target)
    (selected : event.event.firing = representation.firing candidate) :
    ∃ representedTarget : Represented, representation.state representedTarget = target ∧
      atState (code.state.view (sort := ()) representedTarget) ∈ rewriteStepWithPremisesUsing
        (effectQueries representation.effect
          (representation.admission (profile catalogue authorized).eventAdmission)
          code decision).relations authoredLanguage
        (request (code.state.view (sort := ()) source) (code.firing.view (sort := ()) ⟨source, candidate⟩)) := by
  obtain ⟨representedTarget, lifted, sameTarget, sameCandidate⟩ :=
    representation.event_reflects candidate event.event selected
  exact ⟨representedTarget, sameTarget,
    (authored_execution_iff_represented _ _ _ _ _ candidate).mpr ⟨lifted, sameCandidate⟩⟩

theorem source_encoding_retains_origin {source : Represented} {first second : Selected source}
    (same : code.firing.view (sort := ()) ⟨source, first⟩ = code.firing.view (sort := ()) ⟨source, second⟩) :
    (representation.firing first).origin = (representation.firing second).origin := by
  have equal := code.firing.view_injective same
  have candidates : first = second := eq_of_heq (Sigma.mk.inj equal).2
  exact congrArg (fun candidate => (representation.firing candidate).origin) candidates

theorem source_encoding_retains_recipes {source : Represented} {first second : Selected source}
    (same : code.firing.view (sort := ()) ⟨source, first⟩ = code.firing.view (sort := ()) ⟨source, second⟩) :
    (representation.firing first).firing.recipes = (representation.firing second).firing.recipes := by
  have equal := code.firing.view_injective same
  have candidates : first = second := eq_of_heq (Sigma.mk.inj equal).2
  exact congrArg (fun candidate => (representation.firing candidate).firing.recipes) candidates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins
