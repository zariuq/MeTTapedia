import Mettapedia.Languages.VibeITP.Spec.ProtocolRuns

/-! The ordered transcript of actual successful challenge registrations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolRegistrations

open ProtocolExecution ProtocolObserved ProtocolChallengePreservation ProtocolRuns

def event (state : State) : Instr → Option Term
  | .challengeAdd source _ => state.terms source
  | _ => none

theorem event_tracked {ε : Type} {capability : Capability ε}
    {before after : ObservedState} (instruction : Instr) {goal : Term}
    (registered : event before.kernel instruction = some goal)
    (accepted : step capability before instruction = .ok after) : Tracked after.kernel goal := by
  cases instruction <;> simp only [event] at registered
  all_goals try cases registered
  rename_i source destination
  obtain ⟨transition, _⟩ := staticStep_success accepted
  obtain ⟨statement, read, _, shape⟩ := challengeAdd_success transition
  have same : statement = goal := Option.some.inj (read.symm.trans registered)
  right
  refine ⟨destination, ?_⟩
  rw [shape]
  simp [setSlot, same]

def instructions {ε : Type} (capability : Capability ε) : ObservedState → List Instr → List Term
  | _, [] => []
  | state, instruction :: rest =>
    match step capability state instruction with
    | .error _ => []
    | .ok next => (event state.kernel instruction).toList ++ instructions capability next rest

def files {ε : Type} (capability : Capability ε) : ObservedState → List (List Instr) → List Term
  | _, [] => []
  | state, items :: rest =>
    match ProtocolRuns.runInstrs capability state 0 items with
    | .error _ => []
    | .ok next => instructions capability state items ++ files capability next rest

theorem instructions_tracked {ε : Type} {capability : Capability ε} (items : List Instr)
    {before after : ObservedState} (index : Nat)
    (accepted : ProtocolRuns.runInstrs capability before index items = .ok after) :
    ∀ goal ∈ instructions capability before items, Tracked after.kernel goal := by
  induction items generalizing before index with
  | nil => simp [instructions]
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [ProtocolRuns.runInstrs, transition] at accepted
    | ok next =>
      have following : ProtocolRuns.runInstrs capability next (index + 1) rest = .ok after := by
        simpa only [ProtocolRuns.runInstrs, transition] using accepted
      intro goal member
      simp only [instructions, transition, List.mem_append] at member
      rcases member with newest | later
      · have registered : event before.kernel instruction = some goal := by
          simpa using newest
        exact runInstrs_tracked rest (index + 1) (event_tracked instruction registered transition) following
      · exact ih (index + 1) following goal later

theorem files_tracked {ε : Type} {capability : Capability ε} (items : List (List Instr))
    {before after : ObservedState} (file : Nat)
    (accepted : ProtocolRuns.runFiles capability before file items = .ok after) :
    ∀ goal ∈ files capability before items, Tracked after.kernel goal := by
  induction items generalizing before file with
  | nil => simp [files]
  | cons current rest ih =>
    cases transition : ProtocolRuns.runInstrs capability before 0 current with
    | error error => rcases error with ⟨index, error⟩; simp [ProtocolRuns.runFiles, transition] at accepted
    | ok next =>
      have following : ProtocolRuns.runFiles capability next (file + 1) rest = .ok after := by
        simpa only [ProtocolRuns.runFiles, transition] using accepted
      intro goal member
      simp only [files, transition, List.mem_append] at member
      rcases member with currentFile | later
      · exact runFiles_tracked rest (file + 1) (instructions_tracked current 0 transition goal currentFile)
          following
      · exact ih (file + 1) following goal later

def check {ε : Type} (capability : Capability ε) (setup proofs : List (List UInt8)) : List Term :=
  match decodeFiles 0 (setup ++ proofs) with
  | .error _ => []
  | .ok decoded =>
    match ProtocolRuns.runFiles capability initial 0 (decoded.take setup.length) with
    | .error _ => []
    | .ok prepared => files capability initial (decoded.take setup.length) ++
      if proofs.isEmpty then [] else files capability (proofBoundary prepared) (decoded.drop setup.length)

end Mettapedia.Languages.VibeITP.Spec.ProtocolRegistrations
