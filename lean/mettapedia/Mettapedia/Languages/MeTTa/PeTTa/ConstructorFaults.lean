import Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRecoveryFrames

/-!
# Constructor operand prefixes and escaping faults

Both direct data traversal and native-cons expansion retain an actual operand
prefix without replay. At an escaping fault their different argument waiters
compute the same caller recovery and retain the same reached world. A nested
handler remains in charge until the fault has escaped it. General reflection
of arbitrary constructor runs is not inferred from these transport laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Unifying

theorem data_head_prefix {registry : SpaceSemantics.Program} {before pending : Configuration}
    (bindings : Subst) (first : Atom) (rest held : List Atom) (index : Nat)
    (path : Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings first,frames := []} pending)
    (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {before with control := .arguments bindings .data (first :: rest) held index,frames}
      (appendFrames pending (.argument .data rest held index :: frames)) := by
  have entered : Transition registry
      {before with control := .arguments bindings .data (first :: rest) held index,frames}
      {before with
        control := .evaluate bindings first
        frames := .argument .data rest held index :: frames} := step_transition rfl
  have lifted := steps_append_frames path (.argument .data rest held index :: frames)
  simpa only [appendFrames,List.nil_append] using Relation.ReflTransGen.head entered lifted

theorem escaping_fault_same_recovery (registry : SpaceSemantics.Program) (pending : Configuration)
    (reason : Effects.Fault) (faulted : pending.control = .fault reason)
    (outside : NoCallBoundary pending.frames) (frames : List Frame)
    (rest held : List Atom) (index : Nat) (tail : Atom) :
    step registry (appendFrames pending (.argument .data rest held index :: frames)) =
      step registry (appendFrames pending (.argument (.function "cons-atom") [tail] [] 0 :: frames)) := by
  exact (fault_step_after_waiter registry pending reason faulted outside frames .data rest held index).trans
    (fault_step_after_waiter registry pending reason faulted outside frames
      (.function "cons-atom") [tail] [] 0).symm

/-- The actual source operand path, not a promised constructor equivalence,
supplies the reached effects. The independently specified caller recovery
then gives exactly the same full endpoint for the two constructions. -/
theorem head_fault_paths {registry : SpaceSemantics.Program} {before pending : Configuration}
    (bindings : Subst) (first tail : Atom) (rest held : List Atom) (index : Nat)
    (path : Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings first,frames := []} pending)
    (reason : Effects.Fault) (faulted : pending.control = .fault reason)
    (outside : NoCallBoundary pending.frames) (frames caller : List Frame) (earned : List Answer)
    (recovery : Recovers [] frames earned caller) :
    Relation.ReflTransGen (Transition registry)
        {before with control := .arguments bindings .data (first :: rest) held index,frames}
        {pending with control := .returned earned,frames := caller} ∧
      Relation.ReflTransGen (Transition registry)
        {before with control := .evaluate bindings (cons first tail),frames}
        {pending with control := .returned earned,frames := caller} := by
  have directStep : step registry
      (appendFrames pending (.argument .data rest held index :: frames)) =
      some {pending with control := .returned earned,frames := caller} := by
    simpa only [appendFrames,recovery.computed,Option.map_some] using
      fault_step_after_waiter registry pending reason faulted outside frames .data rest held index
  have expandedStep : step registry
      (appendFrames pending (.argument (.function "cons-atom") [tail] [] 0 :: frames)) =
      some {pending with control := .returned earned,frames := caller} :=
    (escaping_fault_same_recovery registry pending reason faulted outside frames rest held index tail).symm.trans directStep
  exact ⟨(data_head_prefix bindings first rest held index path frames).tail (step_transition directStep),
    (head_prefix bindings first tail path frames).tail (step_transition expandedStep)⟩

/-- In the absence of a caller handler the expansion does not turn an
escaping source fault into successful empty answers. -/
theorem head_fault_stays_uncaught (registry : SpaceSemantics.Program) (pending : Configuration)
    (reason : Effects.Fault) (faulted : pending.control = .fault reason)
    (outside : NoCallBoundary pending.frames) (frames : List Frame)
    (uncaught : recoverDynamic [] frames = none)
    (tail : Atom) :
    step registry (appendFrames pending (.argument (.function "cons-atom") [tail] [] 0 :: frames)) = none := by
  simpa only [appendFrames,uncaught,Option.map_none] using
    fault_step_after_waiter registry pending reason faulted outside frames
      (.function "cons-atom") [tail] [] 0

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine
