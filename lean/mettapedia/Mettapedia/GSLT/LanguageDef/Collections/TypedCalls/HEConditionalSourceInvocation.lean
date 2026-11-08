import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceFrontier

/-!
# Actual conditional equation invocation and retained branch delivery

The complete source frontier, fresh parameter bindings, and producer boundary
derive a real invocation in the existing stateful semantics. The delivered
branch is still source syntax: its later ordinary return/evaluation boundary
remains distinct from this equation invocation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceInvocation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type.Presentation
open HEConditionalEquationFrames (query)
open HEIfSourceSelection.Range (space)

theorem source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World)
    (view : environment.view world label = space) (live : List Atom) (scope : List String)
    (caller : Option Atom) (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = [])
    (yesPlain : ¬FunctionPending policy yes) (noPlain : ¬FunctionPending policy no)
    (owned : NonGroundedCallRel environment.dispatch (query condition yes no).erase) :
    ∃ after : Frame,
      Stateful.InvocationRel environment label world live scope caller (query condition yes no) before
        [(if condition then yes else no, after)] world (policy := policy) := by
  obtain ⟨work, after, frontier, bound, unified, read⟩ :=
    HEConditionalSourceFrontier.complete_singleton policy live before condition yes no yesClosed noClosed
  have plain : ¬FunctionPending policy (if condition then yes else no) := by
    cases condition <;> assumption
  have produced : Stateful.BoundaryRel environment label world live scope (some (query condition yes no).erase)
      .producer (after.read policy (Entry.Value.ofAtom work.body)) after
      [(if condition then yes else no, after)] world (policy := policy) := by
    rw [read]
    exact .producerRaw plain
  have bodies : Stateful.InvocationEquationsRel environment label world live scope (query condition yes no) before
      [work] [(if condition then yes else no, after)] world (policy := policy) := by
    simpa only [List.append_nil] using Stateful.InvocationEquationsRel.cons bound unified produced .nil
  exact ⟨after, .equations owned (by simpa only [view] using frontier) (by simp) bodies⟩

theorem retained_source {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World)
    (view : environment.view world label = space) (live : List Atom) (scope : List String)
    (caller : Option Atom) (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = [])
    (yesPlain : ¬FunctionPending policy yes) (noPlain : ¬FunctionPending policy no)
    (owned : NonGroundedCallRel environment.dispatch (query condition yes no).erase)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ after : Frame,
      RecursiveMachine.Contextual.WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world, label, .work (.invocation live scope caller (query condition yes no) before), stack, emitted⟩
        ⟨world, label, .returning [(if condition then yes else no, after)], stack, emitted⟩ := by
  obtain ⟨after, produced⟩ := source environment policy label world view live scope caller before condition yes no
    yesClosed noClosed yesPlain noPlain owned
  exact ⟨after, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.task_complete
      (task := .invocation live scope caller (query condition yes no) before) produced stack) emitted⟩

namespace Range

open HEIfSourceSelection.Range (yes no)
open HEBinaryNumericSource (primitiveEnvironment primitiveDispatch)

theorem branch_delivery (services : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (lower upper : Int) :
    ∃ after : Frame,
      Stateful.InvocationRel (primitiveEnvironment services) space () live scope caller
        (query (decide (lower ≥ upper)) (Entry.Value.ofAtom yes) (Entry.Value.ofAtom (no lower upper))) before
        [(if lower ≥ upper then Entry.Value.ofAtom yes else Entry.Value.ofAtom (no lower upper), after)] ()
        (policy := policy) := by
  simpa only [decide_eq_true_eq] using
    source (primitiveEnvironment services) policy space () rfl live scope caller before
      (decide (lower ≥ upper)) (Entry.Value.ofAtom yes) (Entry.Value.ofAtom (no lower upper))
      (by simp [Entry.Value.erase_ofAtom, yes, TypeSubst.typeVars, TypeSubst.typeVarsList])
      (by simp [Entry.Value.erase_ofAtom, no, HEFreshEquationFrames.Range.number, TypeSubst.typeVars, TypeSubst.typeVarsList])
      (by simp [FunctionPending, Minimal.IsFunction, yes, Entry.Value.erase_ofAtom])
      (by simp [FunctionPending, Minimal.IsFunction, no, Entry.Value.erase_ofAtom])
      (by simp [NonGroundedCallRel, Minimal.HostCall, primitiveEnvironment, primitiveDispatch,
        query, Entry.Value.erase, Minimal.embeddedInstruction])

end Range

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceInvocation
