import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingReachability
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintPresentationControls

/-!
# Hidden binding records participate in streaming validity

The invariant detects malformed records in saved alternatives, source frames,
collection markers and completed answers. These are construction-law negative
controls, not a new admission scan over source programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingBindingControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Streaming.BindingInvariant

def badBindings : Subst := [("x",.var "y"),("y",.symbol "a")]
def atom : Atom := .symbol "ok"
def base : Streaming.State := {world := {state := Effects.empty},agenda := []}

theorem bad_bindings_not_idempotent : ¬Unifying.Idempotent badBindings :=
  PeTTaConstraintPresentationControls.unresolved_binding_chain_is_not_idempotent

def hiddenAlternative : Streaming.State :=
  {base with agenda := [.execute ⟨.returned [⟨atom,[]⟩],[]⟩,
    .execute ⟨.evaluate badBindings atom,[]⟩]}

theorem hidden_alternative_is_not_ignored : ¬stateRefines [] hiddenAlternative := by
  intro good
  have hidden := good.1 (.execute ⟨.evaluate badBindings atom,[]⟩) (by simp [hiddenAlternative])
  have bindings := hidden.1
  simp only [Unifying.ControlRefines] at bindings
  exact bad_bindings_not_idempotent bindings.1

def hiddenFrame : Streaming.State :=
  {base with agenda := [.execute ⟨.returned [⟨atom,[]⟩],[.source (.collect badBindings)]⟩]}

theorem hidden_source_frame_is_not_ignored : ¬stateRefines [] hiddenFrame := by
  intro good
  have active := (head_and_tail good rfl).1
  have saved := active.2 (.source (.collect badBindings)) (by simp)
  exact bad_bindings_not_idempotent saved.1

def hiddenCollector : Streaming.State :=
  {base with agenda := [.collect 0 badBindings [] []]}

theorem hidden_collector_is_not_ignored : ¬stateRefines [] hiddenCollector := by
  intro good
  exact bad_bindings_not_idempotent (head_and_tail good rfl).1.1.1

def hiddenAnswer : Streaming.State :=
  {base with answers := [⟨atom,badBindings⟩]}

theorem hidden_completed_answer_is_not_ignored : ¬stateRefines [] hiddenAnswer := by
  intro good
  have returned := good.2 ⟨atom,badBindings⟩ (by simp [hiddenAnswer])
  exact bad_bindings_not_idempotent returned.1

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingBindingControls
