import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationComposition

/-!
# The authored Execute rule for an origin-aware native profile

An exact candidate encoding and explicit decisions interpret the authored
queries. The origin-aware native profile supplies their semantics. No encoding
of every possible semantic native state is asserted: the chosen presentation
must provide its actual recovery laws. The complete candidate, including its
origin and publication recipes, is the value being encoded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.MeTTaIL.Engine
open Interface

variable {S : Signature} {O : Type} [DecidableEq O] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}
  (catalogue : Catalogue (S := S) (O := O) (Γ := Γ) (sort := sort))
  (authorized : (s : NativeState S O Γ sort) → Nat → NativeFiring s → Prop)
  (code : Encoding (NativeState S O Γ sort) (Candidate (S := S) (O := O) (Γ := Γ) (sort := sort)))
  (decision : Decisions (profile catalogue authorized).effectCore (profile catalogue authorized).eventAdmission)

theorem authored_execution_iff {source target : NativeState S O Γ sort} (candidate : Candidate source) :
    atState (code.state.view (sort := ()) target) ∈ rewriteStepWithPremisesUsing
      (effectQueries (profile catalogue authorized).effectCore (profile catalogue authorized).eventAdmission
        code decision).relations authoredLanguage
      (request (code.state.view (sort := ()) source) (code.firing.view (sort := ()) ⟨source, candidate⟩)) ↔
      ∃ event : SourceEvent catalogue authorized source target, event.event.firing = candidate := by
  rw [authored_root_execution]
  rw [execution_iff_event]
  constructor
  · rintro ⟨event, same⟩
    obtain ⟨reference, _⟩ := QuoteReference.canonical event.firing.origin
    exact ⟨⟨event, reference⟩, same⟩
  · rintro ⟨event, same⟩
    exact ⟨event.event, same⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem source_encoding_retains_origin {source : NativeState S O Γ sort} {first second : Candidate source}
    (same : code.firing.view (sort := ()) ⟨source, first⟩ = code.firing.view (sort := ()) ⟨source, second⟩) :
    first.origin = second.origin := by
  have equal := code.firing.view_injective same
  have candidates : first = second := eq_of_heq (Sigma.mk.inj equal).2
  exact congrArg (fun candidate => candidate.origin) candidates

omit [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem source_encoding_retains_recipes {source : NativeState S O Γ sort} {first second : Candidate source}
    (same : code.firing.view (sort := ()) ⟨source, first⟩ = code.firing.view (sort := ()) ⟨source, second⟩) :
    first.firing.recipes = second.firing.recipes := by
  have equal := code.firing.view_injective same
  have candidates : first = second := eq_of_heq (Sigma.mk.inj equal).2
  exact congrArg (fun candidate => candidate.firing.recipes) candidates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOrigins
