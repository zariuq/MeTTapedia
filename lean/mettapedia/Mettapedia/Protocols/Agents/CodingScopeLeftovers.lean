/-!
# What a coding run leaves in its scope

A coding session's run lives in a scope (a control group). The worker and the
commands it starts are processes of that scope, and so is anything a command
leaves running: a background job belongs to the scope, not to the command or
the worker that started it. The scope is active while it holds any process.

The earlier runtime read an active scope as a running session and reaped a
dead run only once its scope was gone. A background job therefore kept a
finished session's scope active with nobody to end it: the session could not
be resumed (`old_reserve_refused`), and a run whose worker died was never
settled (`old_observe_strands`).

The rule kept here ends the scope once the claimed run is over: the manifest
says started or ended, and the worker the state records is gone. Under the
invariant every launch maintains (`Wf`: a living worker either has still to
claim a reserved launch, or is the recorded owner) that rule never ends a
living worker (`endLeftovers_spares_worker`), leaves a finished session's scope
empty (`observe_empties_finished`), settles a dead run in the same observation
(`observe_settles_dead`) and lets a resume reserve again
(`reserve_after_leftovers`).

Both conditions of the rule are needed. Without the manifest's phase, the
state of the run before a reserved launch condemns the worker that is about to
claim it (`phase_blind_ends_launch`). Judging by the recorded status instead
of the recorded worker ends a worker that has recorded its ending and is still
handing its report over (`status_guard_ends_reporter`).

These are protocol-level statements about an abstract state, not a refinement
proof of the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CodingScopeLeftovers

/-- The manifest's phase: no pin yet, a launch reserved, a run claimed, a run
ended. -/
inductive Phase where
  | none
  | reserved
  | started
  | ended
  deriving DecidableEq, Repr

structure Session where
  phase : Phase
  /-- The recorded state says the run is running. -/
  running : Bool
  /-- The worker the state records, by launch number. -/
  owner : Option Nat
  /-- The worker process living in the scope, if any. -/
  worker : Option Nat
  /-- Processes in the scope that commands left behind. -/
  strays : Nat
  /-- The next launch's number. -/
  fresh : Nat
  deriving DecidableEq, Repr

def scopeActive (s : Session) : Bool := s.worker.isSome || s.strays != 0

def ownerAlive (s : Session) : Bool := s.owner.isSome && s.worker == s.owner

/-- The claimed run is over: started or ended, and its recorded worker gone. -/
def over (s : Session) : Bool :=
  (s.phase == .started || s.phase == .ended) && s.owner.isSome && !ownerAlive s

/-- Stopping a scope ends every process in it. -/
def stopScope (s : Session) : Session := { s with worker := none, strays := 0 }

def endLeftovers (s : Session) : Session :=
  if over s && scopeActive s then stopScope s else s

/-- Settlement of a dead run: recorded as running, worker gone, scope gone. -/
def settle (s : Session) : Session :=
  if s.running && !ownerAlive s && !scopeActive s then { s with running := false } else s

inductive Step where
  /-- A resume reserves a launch unless the session is occupied. -/
  | reserve
  /-- The reserved launch starts its worker in a fresh scope. -/
  | launch
  /-- The worker claims the reserved run and is recorded as its owner. -/
  | claim
  /-- A command of the claimed run leaves a background job. -/
  | spawn
  /-- The worker records its ending; it lives on to hand its report over. -/
  | finish
  /-- The worker exits or dies, wherever it was. -/
  | exit
  /-- The sessions are observed: leftovers end, a dead run is settled. -/
  | observe
  deriving DecidableEq, Repr

def step (s : Session) : Step → Session
  | .reserve =>
      let t := endLeftovers s
      if scopeActive t then t else { t with phase := .reserved, running := false }
  | .launch =>
      if s.phase == .reserved && !scopeActive s then
        { s with worker := some s.fresh, fresh := s.fresh + 1 }
      else s
  | .claim =>
      match s.worker with
      | some w =>
          if s.phase == .reserved then
            { s with phase := .started, running := true, owner := some w }
          else s
      | none => s
  | .spawn =>
      if ownerAlive s && s.phase == .started then { s with strays := s.strays + 1 } else s
  | .finish =>
      if ownerAlive s && s.phase == .started then
        { s with phase := .ended, running := false }
      else s
  | .exit => { s with worker := none }
  | .observe => settle (endLeftovers s)

def run (s : Session) (steps : List Step) : Session := steps.foldl step s

def fresh : Session :=
  { phase := .none, running := false, owner := none, worker := none, strays := 0, fresh := 0 }

/-- A living worker has still to claim a reserved launch, or is the recorded
owner. -/
def Wf (s : Session) : Prop :=
  ∀ w, s.worker = some w → s.phase = .reserved ∨ s.owner = some w

theorem wf_fresh : Wf fresh := by
  intro w h
  simp [fresh] at h

/-- Under the invariant, a run that is over has no living worker. -/
theorem over_no_worker (s : Session) (h : Wf s) (ho : over s = true) : s.worker = none := by
  cases hw : s.worker with
  | none => rfl
  | some w =>
      rcases h w hw with hp | hown
      · simp [over, hp] at ho
      · simp [over, ownerAlive, hw, hown] at ho

/-- Ending leftovers never ends a living worker. -/
theorem endLeftovers_spares_worker (s : Session) (h : Wf s) :
    (endLeftovers s).worker = s.worker := by
  unfold endLeftovers
  split
  · rename_i hg
    have ho : over s = true := by
      cases hov : over s <;> simp [hov] at hg ⊢
    simp [stopScope, over_no_worker s h ho]
  · rfl

theorem wf_endLeftovers (s : Session) (h : Wf s) : Wf (endLeftovers s) := by
  unfold endLeftovers
  split
  · intro w hw
    simp [stopScope] at hw
  · exact h

theorem wf_settle (s : Session) (h : Wf s) : Wf (settle s) := by
  unfold settle
  split
  · intro w hw
    exact h w hw
  · exact h

/-- Every step keeps the invariant. -/
theorem wf_step (s : Session) (a : Step) (h : Wf s) : Wf (step s a) := by
  cases a with
  | reserve =>
      have ht := wf_endLeftovers s h
      simp only [step]
      split
      · exact ht
      · rename_i hact
        intro w hw
        left
        rfl
  | launch =>
      simp only [step]
      split
      · rename_i hg
        intro w _
        left
        have : s.phase = .reserved := by
          cases hp : s.phase <;> simp [hp] at hg ⊢
        exact this
      · exact h
  | claim =>
      simp only [step]
      split
      · rename_i w hw
        split
        · intro w' hw'
          right
          simp [hw] at hw'
          simp [hw']
        · exact h
      · exact h
  | spawn =>
      simp only [step]
      split
      · intro w hw
        exact h w hw
      · exact h
  | finish =>
      simp only [step]
      split
      · rename_i hg
        intro w hw
        right
        have hw' : s.worker = some w := hw
        have halive : ownerAlive s = true := by
          cases ha : ownerAlive s <;> simp [ha] at hg ⊢
        simp [ownerAlive, hw'] at halive
        exact halive.2.symm
      · exact h
  | exit =>
      intro w hw
      simp [step] at hw
  | observe => exact wf_settle _ (wf_endLeftovers s h)

theorem wf_run (s : Session) (steps : List Step) (h : Wf s) : Wf (run s steps) := by
  induction steps generalizing s with
  | nil => exact h
  | cons a rest ih => exact ih (step s a) (wf_step s a h)

/-- An observation never ends a living worker, whatever happened before. -/
theorem observe_spares_worker (steps : List Step) :
    (step (run fresh steps) .observe).worker = (run fresh steps).worker := by
  have h := wf_run fresh steps wf_fresh
  have hs : (settle (endLeftovers (run fresh steps))).worker
      = (endLeftovers (run fresh steps)).worker := by
    unfold settle
    split <;> rfl
  simp only [step, hs]
  exact endLeftovers_spares_worker _ h

/-- Once a run is over, an observation leaves nothing in its scope. -/
theorem observe_empties_over (s : Session) (ho : over s = true) :
    scopeActive (step s .observe) = false := by
  have he : scopeActive (endLeftovers s) = false := by
    unfold endLeftovers
    cases ha : scopeActive s
    · simp [ho, ha]
    · simp [ho, stopScope, scopeActive]
  simp only [step]
  unfold settle
  split
  · simpa [scopeActive] using he
  · exact he

/-- A finished session keeps no processes: its worker gone, an observation
empties its scope. -/
theorem observe_empties_finished (s : Session) (o : Nat)
    (hp : s.phase = .ended) (hown : s.owner = some o) (hw : s.worker = none) :
    scopeActive (step s .observe) = false := by
  apply observe_empties_over
  simp [over, ownerAlive, hp, hown, hw]

/-- A dead run is settled in the observation that ends its leftovers. -/
theorem observe_settles_dead (s : Session) (o : Nat)
    (hp : s.phase = .started) (hown : s.owner = some o) (hw : s.worker = none) :
    (step s .observe).running = false := by
  have ho : over s = true := by simp [over, ownerAlive, hp, hown, hw]
  simp only [step]
  unfold settle endLeftovers
  cases ha : scopeActive s <;> cases hr : s.running <;>
    simp [ho, hr, stopScope, scopeActive, ownerAlive, hown, hw] at *
  all_goals simp_all

/-- A run that finished and left a background job. -/
def finishedWithStray : Session :=
  run fresh [.reserve, .launch, .claim, .spawn, .finish, .exit]

/-- A run whose worker died and left a background job. -/
def deadWithStray : Session :=
  run fresh [.reserve, .launch, .claim, .spawn, .exit]

/-- A resume reserves again after a run that left a background job. -/
theorem reserve_after_leftovers :
    (step finishedWithStray .reserve).phase = .reserved
      ∧ scopeActive (step finishedWithStray .reserve) = false := by
  decide

/-- The earlier reservation: an active scope is a running session. -/
def oldReserve (s : Session) : Session :=
  if scopeActive s then s else { s with phase := .reserved, running := false }

/-- The earlier observation: settle, never end a scope. -/
def oldObserve (s : Session) : Session := settle s

/-- The earlier rule: a finished session with a background job keeps its
processes and refuses every resume. -/
theorem old_reserve_refused :
    oldReserve (oldObserve finishedWithStray) = finishedWithStray
      ∧ scopeActive finishedWithStray = true
      ∧ finishedWithStray.worker = none := by
  decide

/-- The earlier rule: a dead run with a background job stays recorded as
running, observation after observation. -/
theorem old_observe_strands :
    oldObserve deadWithStray = deadWithStray
      ∧ deadWithStray.running = true
      ∧ deadWithStray.worker = none := by
  decide

/-- A rule that does not read the manifest's phase. -/
def phaseBlind (s : Session) : Session :=
  if s.owner.isSome && !ownerAlive s && scopeActive s then stopScope s else s

/-- It ends the worker of a reserved launch: the recorded owner is the run
before, which is gone. -/
theorem phase_blind_ends_launch :
    let s := run finishedWithStray [.reserve, .launch]
    s.worker = some 1 ∧ (phaseBlind s).worker = none ∧ (endLeftovers s).worker = some 1 := by
  decide

/-- A rule that judges by the recorded status instead of the recorded worker. -/
def statusGuard (s : Session) : Session :=
  if (s.phase == .started || s.phase == .ended) && !s.running && scopeActive s then stopScope s
  else s

/-- It ends a worker that has recorded its ending and still hands its report
over. -/
theorem status_guard_ends_reporter :
    let s := run fresh [.reserve, .launch, .claim, .finish]
    s.worker = some 0 ∧ (statusGuard s).worker = none ∧ (endLeftovers s).worker = some 0 := by
  decide

end Mettapedia.Protocols.Agents.CodingScopeLeftovers
