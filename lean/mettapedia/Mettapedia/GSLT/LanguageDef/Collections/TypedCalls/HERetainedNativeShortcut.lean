import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundary
import Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcut

/-!
# Checked completed-native regions in the shared boundary protocol

The protocol is the existing stateful native boundary. Its body may resume
the source-derived completed-return shortcut instead of its canonical queue.
The admission decision reads only the producer provenance and literal demand.
Decline retains the reached world and the exact canonical return cursor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeShortcut

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BoundaryCore
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open HERetainedNativeBoundary

def checkedCursor {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (reply : Reply policy site) : WorldConfiguration Context World :=
  CompletedNativeShortcut.resumeChecked environment.dispatch site.path site.state site.live site.scope
    site.value site.expected site.operator site.arguments reply.reached reply.plan

def checkedBody {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (frame : ResumeFrame (site := site) (policy := policy)) :
    WorldConfiguration Context World := checkedCursor frame.reply

/-- This is the existing protocol with a different, independently justified
body cursor, not a second evaluator or a proof-carrying answer table. -/
theorem protocol_run {Context World O : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (resume : WorldConfiguration Context World → List O)
    (reply : Reply policy site) :
    (HERetainedNativeBoundary.protocol policy site resume).run (fun frame => resume (checkedBody frame)) reply =
      resume (checkedCursor reply) := by
  cases reply with
  | mk outcome reached plan produced prepared =>
    cases plan <;> simp [Protocol.run, HERetainedNativeBoundary.protocol, checkedBody, checkedCursor,
      CompletedNativeShortcut.resumeChecked, NativeDispatchFocus.resumeAt, RetainedNativeDispatch.resumeNative]

theorem cursor_source_iff {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (reply : Reply policy site) (answers : List Result) (finalWorld : World) :
    (NativeDispatchFocus.resumeAt environment.dispatch site.path site.state site.live site.scope site.value site.expected
      site.operator site.arguments reply.reached reply.plan).SourceRel environment policy answers finalWorld ↔
      (checkedCursor reply).SourceRel environment policy answers finalWorld :=
  CompletedNativeShortcut.resume_source_iff environment policy site.path site.state site.live site.scope site.value
    site.expected site.operator site.arguments reply.reached reply.plan answers finalWorld

/-- Both preservation and no invention are earned from the native source
constructors. No complete call result is an input to admission. -/
theorem source_completion_iff {Context World : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (answers : List Result) (finalWorld : World) :
    site.state.SourceRel environment policy answers finalWorld ↔
      ∃ reply : Reply policy site, (checkedCursor reply).SourceRel environment policy answers finalWorld := by
  rw [HERetainedNativeBoundary.source_completion_iff policy site answers finalWorld]
  exact exists_congr fun reply => cursor_source_iff reply answers finalWorld

/-- The shortcut's source meaning is realized by the existing world machine;
this statement does not introduce a new machine with an assumed answer. -/
theorem observed_completion_iff {Context World : Type} {environment : WorldEnvironment Context World}
    (policy : Policy) (site : Site environment) (answers : List Result) (finalWorld : World) :
    site.state.SourceRel environment policy answers finalWorld ↔
      ∃ (reply : Reply policy site) (final : WorldConfiguration Context World),
        WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch
          environment.lookup policy (checkedCursor reply) final ∧
        worldObserve final = some answers ∧ final.world = finalWorld := by
  rw [source_completion_iff policy site answers finalWorld]
  exact exists_congr fun reply => RecursiveExecution.Contextual.Stateful.source_iff_observed (checkedCursor reply) answers finalWorld

theorem canonical_run_of_checked_source {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {site : Site environment} (reply : Reply policy site) {answers : List Result} {finalWorld : World}
    (completed : (checkedCursor reply).SourceRel environment policy answers finalWorld) :
    WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch
      environment.lookup policy site.state ⟨finalWorld, site.state.context, .returning [], [], answers⟩ :=
  RecursiveExecution.Contextual.Stateful.source_to_finished
    ((source_completion_iff policy site answers finalWorld).mpr ⟨reply, completed⟩)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeShortcut
