import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation

/-!
# Source-level let continuations preserve the reached world and binding packets

An arbitrary completed initializer is lifted above the actual binding frame.
The subsequent body control is built by the existing scoped unifier; it is not
replaced with a value-only callback. Successful, clashing and exhausted binding
outcomes are distinct. A successful one-value initializer reaches the body as
an evaluation request, including when the body names an authored operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaBindingContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts PeTTaActivation

theorem bind_singleton (pattern body value : Atom) (bindings bound : Subst)
    (unified : unifyBinding bindings pattern value = .ok bound) :
    bindAnswers pattern body [⟨value, bindings⟩] = some [.evaluate bound body] := by
  simp [bindAnswers, unified]

theorem bind_singleton_clash (pattern body value : Atom) (bindings : Subst)
    (clashed : unifyBinding bindings pattern value = .clash) :
    bindAnswers pattern body [⟨value, bindings⟩] = some [] := by
  simp [bindAnswers, clashed]

theorem bind_singleton_exhausted (pattern body value : Atom) (bindings : Subst)
    (exhausted : unifyBinding bindings pattern value = .exhausted) :
    bindAnswers pattern body [⟨value, bindings⟩] = none := by
  simp [bindAnswers, exhausted]

/-- This composes the initializer's independent source path with the actual let continuation. -/
theorem initializer_then_binding (registry : SpaceSemantics.Program)
    (before after : Configuration) (bindings : Subst) (pattern initializer body : Atom)
    (answers : List Answer) (continued : List Control)
    (initialized : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings initializer)
      { after with control := .returned answers, frames := [] })
    (bound : bindAnswers pattern body answers = some continued) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "let", pattern, initializer, body]))
      { after with control := .sequence continued [], frames := before.frames } := by
  have entered : Transition registry
      (atExpression before bindings (.expression [.symbol "let", pattern, initializer, body]))
      (atExpression { before with frames := .bind pattern body :: before.frames } bindings initializer) :=
    .let_enter rfl
  have lifted := steps_append_frames initialized (.bind pattern body :: before.frames)
  have ran : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := .bind pattern body :: before.frames } bindings initializer)
      { after with control := .returned answers, frames := .bind pattern body :: before.frames } := by
    simpa [appendFrames, atExpression] using lifted
  exact (Relation.ReflTransGen.head entered ran).tail (.binding_return rfl rfl bound)

/-- Body activation retains initializer effects and its produced substitution. -/
theorem initializer_then_body (registry : SpaceSemantics.Program)
    (before after : Configuration) (incoming produced bound : Subst)
    (pattern initializer body value : Atom)
    (initialized : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } incoming initializer)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (unified : unifyBinding produced pattern value = .ok bound) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before incoming (.expression [.symbol "let", pattern, initializer, body]))
      (atExpression { after with frames := .sequence [] [] :: before.frames } bound body) := by
  have ready := initializer_then_binding registry before after incoming pattern initializer body
    [⟨value, produced⟩] [.evaluate bound body] initialized (bind_singleton _ _ _ _ _ unified)
  exact ready.tail (.sequence_enter rfl)

/-- A known written operation remains a function request in a let body. -/
theorem known_operation_in_let_body (registry : SpaceSemantics.Program)
    (before after : Configuration) (incoming produced bound : Subst)
    (pattern initializer value : Atom) (head : String) (arguments : List Atom)
    (initialized : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } incoming initializer)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (unified : unifyBinding produced pattern value = .ok bound)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : callable registry head = true) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before incoming (.expression [.symbol "let", pattern, initializer,
        .expression (.symbol head :: arguments)]))
      { after with
        control := .arguments bound (.function head) arguments [] 0
        frames := .sequence [] [] :: before.frames } := by
  have body := initializer_then_body registry before after incoming produced bound pattern initializer
    (.expression (.symbol head :: arguments)) value initialized unified
  exact body.tail (.call_enter rfl ordinary
    (callable_with_privateCode registry after.privateCode head recognized))

/-- A failed pattern does not run the body or restore the world from before the initializer. -/
theorem initializer_then_clash (registry : SpaceSemantics.Program)
    (before after : Configuration) (incoming produced : Subst) (pattern initializer body value : Atom)
    (initialized : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } incoming initializer)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (clashed : unifyBinding produced pattern value = .clash) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before incoming (.expression [.symbol "let", pattern, initializer, body]))
      { after with control := .returned [], frames := before.frames } := by
  have ready := initializer_then_binding registry before after incoming pattern initializer body
    [⟨value, produced⟩] [] initialized (bind_singleton_clash _ _ _ _ clashed)
  exact ready.tail (.sequence_done rfl)

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaBindingContexts
