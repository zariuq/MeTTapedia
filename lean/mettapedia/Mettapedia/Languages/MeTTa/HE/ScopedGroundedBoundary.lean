import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# The local scoped grounded-operation boundary

The effective method observes service updates at the call site. A scoped
operation is not bypassed by a legacy callback, and its freshness premise
can inspect the actual logical caller rather than just visible arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation

theorem WorldServices.groundedAt_unscoped {Context World : Type}
    (services : WorldServices Context World) (unscoped : services.scopedGroundedCall = none)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (call : Entry.Value) (outcome : GroundedResult Entry.Value) (after : World) :
    services.groundedAt label world live scope frame call outcome after ↔
      services.groundedCall label world call outcome after := by
  simp only [WorldServices.groundedAt, unscoped]

/-- Updating the old service after construction changes the effective
callback; no previously captured default callback is used. -/
theorem WorldServices.groundedAt_updated {Context World : Type}
    (services : WorldServices Context World) (unscoped : services.scopedGroundedCall = none)
    (operation : Context → World → Entry.Value → GroundedResult Entry.Value → World → Prop)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (call : Entry.Value) (outcome : GroundedResult Entry.Value) (after : World) :
    ({ services with groundedCall := operation }).groundedAt label world live scope frame call outcome after ↔
      operation label world call outcome after := by
  simp only [WorldServices.groundedAt, unscoped]

theorem WorldServices.groundedAt_scoped {Context World : Type}
    (services : WorldServices Context World)
    (operation : Context → World → List Atom → List String → Frame → Entry.Value → GroundedResult Entry.Value → World → Prop)
    (selected : services.scopedGroundedCall = some operation)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (call : Entry.Value) (outcome : GroundedResult Entry.Value) (after : World) :
    services.groundedAt label world live scope frame call outcome after ↔
      operation label world live scope frame call outcome after := by
  simp only [WorldServices.groundedAt, selected]

namespace ScopedGroundedControls

def guarded : WorldServices Unit Unit where
  contextPayload _ := .int 0
  nativeCall _ _ _ _ _ _ _ _ := False
  groundedCall _ _ call outcome _ := call = .symbol "fresh" ∧ outcome = .ok [(.var "x", Bindings.empty)]
  scopedGroundedCall := some (fun _ _ _ scope frame _ outcome _ =>
    ∃ name, name ∉ scope ∧ name ∉ specBindingVars frame.bindings ∧
      outcome = .ok [(.var name, Bindings.empty)])

theorem fresh_empty_caller :
    guarded.groundedAt () () [] [] Frame.empty (.symbol "fresh")
      (.ok [(.var "x", Bindings.empty)]) () := by
  exact ⟨"x", by simp, by simp [Frame.empty, Bindings.empty, specBindingVars], rfl⟩

theorem legacy_callback_cannot_bypass_caller_scope :
    guarded.groundedCall () () (.symbol "fresh") (.ok [(.var "x", Bindings.empty)]) () ∧
    ¬guarded.groundedAt () () [] [] Controls.argumentAliasFrame (.symbol "fresh")
      (.ok [(.var "x", Bindings.empty)]) () := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro ⟨name, _, fresh, same⟩
  have key : name = "x" := by simpa using same.symm
  subst name
  exact fresh (by decide)

end ScopedGroundedControls
end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
