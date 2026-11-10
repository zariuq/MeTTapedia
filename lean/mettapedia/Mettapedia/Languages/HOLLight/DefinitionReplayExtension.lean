import Mettapedia.Languages.HOLLight.DefinitionReplayModels

/-! # Extending an accepted definition history

Sequential reference admission agrees with concatenation. Its existing
constant-history construction proves that the earlier theorem cache is
retained, allowing all earlier semantic interpretations to be reused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.DefinitionReplayExtension

open Mettapedia.Languages.OpenTheory

theorem reference_append (before : ExportCodec.State) (first second : List Lean.Json) :
    SourceProfile.referenceDefinitions? before (first ++ second) =
      (SourceProfile.referenceDefinitions? before first).bind
        (fun middle => SourceProfile.referenceDefinitions? middle second) := by
  induction first generalizing before with
  | nil => rfl
  | cons input rest ih =>
      simp only [List.cons_append, SourceProfile.referenceDefinitions?]
      split
      · rfl
      · cases step : ExportCodec.receive? emptyAxiomPolicy before input with
        | none => simp
        | some middle => simpa only [step, bind, Option.bind] using ih middle

theorem cache_inclusion {before after : ExportCodec.State} {inputs : List Lean.Json}
    (accepted : SourceProfile.referenceDefinitions? before inputs = some after) :
    ∀ fact ∈ before.received.registered.cache, fact ∈ after.received.registered.cache := by
  obtain ⟨events, constants, replayed⟩ :=
    DefinitionReplayModels.reference_definitions_events before inputs after accepted
  obtain ⟨history, cache⟩ := DefinitionReplayModels.replay_constant_history before.received.registered
    (events.map ExportReplay.Event.command) after.received.registered
    (by
      intro command member
      obtain ⟨event, present, rfl⟩ := List.mem_map.mp member
      exact constants event present)
    (DefinitionReplayModels.replay_registered_commands before.received events after.received replayed)
  intro fact member
  have included : fact ∈ after.received.registered.cache.toList := by
    rw [cache]
    exact List.mem_append_left _ (by simpa using member)
  simpa using included

theorem reference_append_accepted {before middle after : ExportCodec.State} {first second : List Lean.Json}
    (earlier : SourceProfile.referenceDefinitions? before first = some middle)
    (later : SourceProfile.referenceDefinitions? middle second = some after) :
    SourceProfile.referenceDefinitions? before (first ++ second) = some after := by
  rw [reference_append, earlier]
  exact later

#print axioms reference_append
#print axioms cache_inclusion
#print axioms reference_append_accepted

end Mettapedia.Languages.HOLLight.DefinitionReplayExtension
