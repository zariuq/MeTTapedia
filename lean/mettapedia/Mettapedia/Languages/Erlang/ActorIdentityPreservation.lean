import Mettapedia.Languages.Erlang.ActorIdentity

/-! The actual actor transition functions preserve the canonical pid store.
The result holds after every finite supplied schedule, including prefixes
with outstanding messages and processes waiting at mailbox operations. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Erlang.ActorSystem

theorem CanonicalPids.request {system next : ActorSystem} (valid : CanonicalPids system)
    {index : Nat} {process : LocalProcess} (found : system.processes[index]? = some process)
    (request : ActorRequest) (continuation : Continuation)
    (accepted : system.request? index process request continuation = .ok (some next)) : CanonicalPids next := by
  cases request with
  | self =>
    cases accepted
    constructor
    refine Eq.trans ?_ valid.identities
    exact identities_set found rfl
  | send receiver message =>
    cases accepted
    constructor
    refine Eq.trans ?_ valid.identities
    exact identities_set found rfl
  | spawn function =>
    cases function with
    | literal _ | pid _ | tuple _ | cons _ _ => simp [request?] at accepted
    | closure arity function captured =>
      cases arity with
      | succ arity => simp [request?] at accepted
      | zero =>
        simp only [request?] at accepted
        rw [valid.no_collision] at accepted
        simp only [Bool.false_eq_true, if_false] at accepted
        cases childResult : (applyClosure system.program (.closure 0 function captured) [] []).mapError ActorError.sequential with
        | error error =>
          rw [childResult] at accepted
          change (Except.error error : Except ActorError (Option ActorSystem)) = .ok (some next) at accepted
          cases accepted
        | ok child =>
          rw [childResult] at accepted
          change Except.ok (some {system with
            processes := system.processes.set index (resume process [.pid system.nextPid] continuation) ++
              [⟨system.nextPid, child, {}⟩]
            nextPid := system.nextPid + 1}) = Except.ok (some next) at accepted
          cases accepted
          constructor
          rw [List.map_append, identities_set
            (replacement := resume process [.pid system.nextPid] continuation) found rfl, valid.identities]
          exact List.range_succ.symm
  | peekMessage =>
    cases accepted
    constructor
    refine Eq.trans ?_ valid.identities
    exact identities_set found rfl
  | nextMessage =>
    simp only [request?] at accepted
    cases cursor : process.mailbox.normalize.next? with
    | none => simp [cursor] at accepted
    | some box =>
      rw [cursor] at accepted
      cases accepted
      constructor
      refine Eq.trans ?_ valid.identities
      exact identities_set found rfl
  | removeMessage =>
    simp only [request?] at accepted
    cases cursor : process.mailbox.normalize.remove? with
    | none => simp [cursor] at accepted
    | some box =>
      rw [cursor] at accepted
      cases accepted
      constructor
      refine Eq.trans ?_ valid.identities
      exact identities_set found rfl
  | waitInfinity =>
    simp only [request?] at accepted
    split at accepted
    · cases accepted
    · cases accepted
      constructor
      refine Eq.trans ?_ valid.identities
      exact identities_set found rfl

theorem CanonicalPids.execute {system next : ActorSystem} (valid : CanonicalPids system)
    {index : Nat} (accepted : system.execute? index = .ok (some next)) : CanonicalPids next := by
  unfold execute? at accepted
  cases found : system.processes[index]? with
  | none =>
    rw [found] at accepted
    change (Except.ok none : Except ActorError (Option ActorSystem)) = .ok (some next) at accepted
    cases accepted
  | some process =>
    simp only [found] at accepted
    cases machine : process.machine with
    | request request continuation =>
      exact valid.request found request continuation (by simpa only [machine] using accepted)
    | evaluate _ _ _ | returned _ _ | choose _ _ _ _ | halted _ =>
      simp only [machine] at accepted
      cases advanced : (process.machine.step? system.program).mapError ActorError.sequential with
      | error error =>
        rw [← machine, advanced] at accepted
        change (Except.error error : Except ActorError (Option ActorSystem)) = .ok (some next) at accepted
        cases accepted
      | ok progress =>
        rw [← machine, advanced] at accepted
        cases progress with
        | none => cases accepted
        | some target =>
          cases accepted
          constructor
          refine Eq.trans ?_ valid.identities
          exact identities_set found rfl

theorem CanonicalPids.step {system next : ActorSystem} (valid : CanonicalPids system)
    (choice : ActorChoice) (accepted : system.step? choice = .ok (some next)) : CanonicalPids next := by
  cases choice with
  | execute index => exact valid.execute accepted
  | deliver index =>
    exact valid.deliver (Except.ok.inj accepted)

theorem CanonicalPids.runChoices {system next : ActorSystem} (valid : CanonicalPids system)
    (choices : List ActorChoice) (accepted : ActorSystem.runChoices choices system = .ok next) : CanonicalPids next := by
  induction choices generalizing system with
  | nil => cases accepted; exact valid
  | cons choice choices ih =>
    unfold ActorSystem.runChoices at accepted
    cases result : system.step? choice with
    | error error =>
      rw [result] at accepted
      change Except.error error = Except.ok next at accepted
      cases accepted
    | ok progress =>
      rw [result] at accepted
      change ActorSystem.runChoices choices (progress.getD system) = .ok next at accepted
      cases progress with
      | none => exact ih valid accepted
      | some intermediate => exact ih (valid.step choice result) accepted

theorem started_run_canonical (program : Program) (choices : List ActorChoice) {next : ActorSystem}
    (accepted : ActorSystem.runChoices choices (ActorSystem.begin program) = .ok next) : CanonicalPids next :=
  (CanonicalPids.begin program).runChoices choices accepted

end Mettapedia.Languages.Erlang.ActorSystem
