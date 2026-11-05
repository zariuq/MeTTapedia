import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRoundControls

/-!
Uniform admission of the actual mixed-store round, independently of its
execution outcome. Zero copy capacity permits suspension, not reference
handoff. A retained caller tail and duplicate guard declarations lie outside
the whole-leaf admission profile and remain visible to source execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilLeafAdmission (GuardProfile)
open CTLUntilScopedRound (Decoded)
open CTLUntilScopedRound.Controls (query query_template query_legs initial_frame initial_decoded)
open ScopedQuerySource.Controls (call)
open ScopedNestedQueryExecution.Controls renaming caller → fixtureCaller,
  template → fixtureTemplate, legs → fixtureLegs, program → fixtureProgram,
  request → fixtureRequest, initial → fixtureInitial, full → fixtureFull,
  noCopy → fixtureNoCopy, execute → fixtureExecute, completed → fixtureCompleted

def fixture_guard : GuardProfile FlatQueryRowCodec.integers 10 query fixtureProgram where
  occurrence := 0
  row := by
    change some (NamedPresenceSource.declaration fixtureRequest) = some (NamedPresenceSource.declaration
      (CTLUntilPublicationSource.request FlatQueryRowCodec.integers .self 10 0))
    exact congrArg some (CTLUntilLeafAdmission.declaration_same_fields _ _ rfl rfl)
  otherHeads := by
    intro index equation found different
    cases index with
    | zero => exact (different rfl).elim
    | succ index => simp [fixtureProgram] at found
  leftEvaluated := by decide +kernel
  rightEvaluated := by decide +kernel

theorem fixture_names_distinct :
    [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup := by
  decide +kernel

theorem fixture_admission :
    AdmissionFrame FlatQueryRowCodec.integers 10 20 0 query query.legs fixtureCaller where
  frame := initial_frame
  resultFresh := by decide +kernel
  temporaryFresh := by decide +kernel
  finished := rfl
  output := rfl

theorem full_not_reference : ScopedQueryAdmission.NoReference fixtureFull := by
  have valid := admitted FlatQueryRowCodec.integers 10 20 0 query fixture_names_distinct
    fixtureProgram fixture_guard query.legs fixtureCaller fixtureInitial () [9] [] fixture_admission initial_decoded
  simpa only [query_template, query_legs, fixtureFull, fixtureExecute] using valid

def noCopyState : State Unit := {fixtureInitial with allocator := Allocator.empty 0 8}

theorem no_copy_decoded : Decoded FlatQueryRowCodec.integers query.handles noCopyState := initial_decoded

theorem no_copy_not_reference : ScopedQueryAdmission.NoReference fixtureNoCopy := by
  have valid := admitted FlatQueryRowCodec.integers 10 20 0 query fixture_names_distinct
    fixtureProgram fixture_guard query.legs fixtureCaller noCopyState () [9] [] fixture_admission no_copy_decoded
  simpa only [query_template, query_legs, noCopyState, fixtureNoCopy, fixtureExecute] using valid

#guard fixtureCompleted fixtureFull
def zero_copy_suspends : Bool := match fixtureNoCopy.stop with
  | .suspended .allocation _ => true
  | _ => false
#guard zero_copy_suspends

def retainedCaller : Control := {fixtureCaller with
  goals := [.evaluate (call "quote" [.symbol "pending"]) (.var "answer")]}

theorem retained_tail_not_admitted :
    ¬AdmissionFrame FlatQueryRowCodec.integers 10 20 0 query query.legs retainedCaller := by
  intro frame
  have empty := frame.finished
  simp [retainedCaller] at empty

def retainedExecution := ScopedNestedQueryExecution.run fixtureProgram
  (GuardedNestedQuerySource.leaf fixtureProgram query.template Unit) query.legs
  retainedCaller fixtureInitial () [9] []

def retained_tail_handoff : Bool := match retainedExecution.stop with
  | .reference saved =>
    match saved.2.scopes.head?.bind (fun scope => scope.frontier.head?) with
    | some (control, _, _) => control.goals.tail == retainedCaller.goals
    | none => false
  | _ => false

#guard retained_tail_handoff
#guard retainedExecution.events.isEmpty

def duplicatedProgram : SpaceSemantics.Program := {fixtureProgram with equations :=
  [NamedPresenceSource.declaration fixtureRequest, NamedPresenceSource.declaration fixtureRequest]}

theorem duplicate_guard_has_no_profile :
    ¬Nonempty (GuardProfile FlatQueryRowCodec.integers 10 query duplicatedProgram) := by
  rintro ⟨profile⟩
  by_cases first : profile.occurrence = 0
  · exact (profile.otherHeads 1 (NamedPresenceSource.declaration fixtureRequest) rfl (by omega)) rfl
  · exact (profile.otherHeads 0 (NamedPresenceSource.declaration fixtureRequest) rfl (Ne.symm first)) rfl

#print axioms fixture_admission
#print axioms full_not_reference
#print axioms no_copy_not_reference
#print axioms retained_tail_not_admitted
#print axioms duplicate_guard_has_no_profile

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmission.Controls
