import Mettapedia.Machines.BoundaryCore
import Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus

/-!
# The shared protocol at a retained stateful HE native boundary

A site is the actual post-argument call cursor. A reply certifies one local
host operation and the binding/provenance preparation of its complete reply.
Finished plans resume the caller; resumable plans enter the existing boundary
batch. Both preserve the reached world, caller stack and publication prefix.
The continuation need not be an evaluator: finite retained observations use
the same factorization.

This is a protocol instance over the source host contract, not a proof of a
particular C callback or native binding codec.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BoundaryCore
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open NativeDispatchFocus

structure Site {Context World : Type} (environment : WorldEnvironment Context World) where
  state : WorldConfiguration Context World
  path : CallPath Context
  live : List Atom
  scope : List String
  value : Entry.Value
  expected : Atom
  activation : Completed.Frame
  operator : Atom
  arguments : List Atom
  atCall : state.control = path.fill (.work (.call live scope value expected activation))
  shape : value.erase = .expression (operator :: arguments)
  executable : environment.dispatch.executable operator
  notError : ¬IsErrorRel value.erase

structure Reply {Context World : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) where
  outcome : GroundedResult Entry.Value
  reached : World
  plan : NativeReplyPlan
  produced : environment.services.groundedAt (site.path.active site.state.context) site.state.world site.live site.scope site.activation site.value outcome reached
  prepared : NativeOutcomeRel policy environment.dispatch site.operator site.arguments site.value (some site.expected) site.activation outcome plan

structure ResumeFrame {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} where
  reply : Reply policy site
  rows : List Result
  selected : reply.plan = .resume rows

def ResumeFrame.state {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (frame : ResumeFrame (site := site) (policy := policy)) :
    WorldConfiguration Context World :=
  {site.state with world := frame.reply.reached, control := site.path.fill (.work (.boundaryBatch site.live site.scope none
    (.native site.value (some site.expected) (environment.dispatch.valueProvenance site.operator site.arguments)) frame.rows))}

def protocol {Context World O : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (resume : WorldConfiguration Context World → List O) :
    Protocol List (Reply policy site) (ResumeFrame (site := site) (policy := policy)) O O (· ++ ·) where
  early reply := match reply.plan with
    | .done rows => resume {site.state with world := reply.reached, control := site.path.fill (.returning rows)}
    | .resume _ => []
  enter reply := match chosen : reply.plan with
    | .done _ => []
    | .resume rows => [⟨reply, rows, chosen⟩]
  leave := fun _ answer => [answer]
  select := id

theorem protocol_run {Context World O : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (resume : WorldConfiguration Context World → List O)
    (reply : Reply policy site) :
    (protocol policy site resume).run (fun frame => resume frame.state) reply =
      resume (resumeAt environment.dispatch site.path site.state site.live site.scope site.value site.expected
        site.operator site.arguments reply.reached reply.plan) := by
  cases reply with
  | mk outcome reached plan produced prepared =>
    cases plan <;> simp [Protocol.run, protocol, ResumeFrame.state, resumeAt, RetainedNativeDispatch.resumeNative]

theorem reply_transition {Context World : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (reply : Reply policy site) :
    WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      site.state (resumeAt environment.dispatch site.path site.state site.live site.scope site.value site.expected
        site.operator site.arguments reply.reached reply.plan) :=
  focused_step environment policy site.path site.state site.live site.scope site.value site.expected site.activation
    site.operator site.arguments reply.outcome reply.reached reply.plan site.atCall site.shape site.executable site.notError
    reply.produced reply.prepared

theorem frame_transition {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (frame : ResumeFrame (site := site) (policy := policy)) :
    WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      site.state frame.state := by
  simpa only [frame.selected, resumeAt, RetainedNativeDispatch.resumeNative, ResumeFrame.state] using
    reply_transition policy site frame.reply

/-- All permitted primitive outcomes participate in the source equivalence.
No completed call or evaluator result is supplied to the protocol. -/
theorem source_completion_iff {Context World : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (answers : List Result) (finalWorld : World) :
    site.state.SourceRel environment policy answers finalWorld ↔
      ∃ reply : Reply policy site,
        (resumeAt environment.dispatch site.path site.state site.live site.scope site.value site.expected
          site.operator site.arguments reply.reached reply.plan).SourceRel environment policy answers finalWorld := by
  rw [focused_source_iff environment policy site.path site.state site.live site.scope site.value site.expected
    site.activation site.operator site.arguments answers finalWorld site.atCall site.shape site.executable site.notError]
  constructor
  · rintro ⟨outcome, reached, plan, produced, prepared, suffix⟩
    exact ⟨⟨outcome, reached, plan, produced, prepared⟩, suffix⟩
  · rintro ⟨reply, suffix⟩
    exact ⟨reply.outcome, reply.reached, reply.plan, reply.produced, reply.prepared, suffix⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundary
