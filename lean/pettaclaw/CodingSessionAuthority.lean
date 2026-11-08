/-!
# Coding-session authority: resumes, the systemd scope and the turn-start reaper

A coding session's worker runs in a systemd scope named after the session. A resume launches the
worker in the background, so for a moment the launch is pending and `systemctl is-active` still
says inactive. The agent's reaper runs at every turn begin. When `state.json` says running, the
scope is inactive and the recorded worker is dead, it marks the session interrupted. It reads
first and writes later (`mark_state` runs after the observation), so other steps interleave.

The model separates the reaper's observation (`reapRead`) from its publication (`reapPublish`).
A launch that is delayed may register at any later moment.

Two safety properties:
* **No ending over a live run.** `log` records, for each ending a reaper or a settlement
  publishes, whether the run it marked was alive.
* **One authority per reservation.** A worker obtains authority, and so may write the session's
  state or do any work, only by consuming its run token. A token is consumed at most once, and
  only while it is the newest reservation.

What the traces and theorems show:
* **The current protocol.** A crashed run is observed by a reaper, which then pauses. A resume
  launches the next run, and that run starts. The paused publication marks the live run
  interrupted (`current_marks_live_run`). A launch delayed past a later run's whole life still
  starts afterwards (`current_stale_launch_starts`).
* **Settling first is not enough.** A resume that settles the previous ending before it
  launches loses to the same paused reaper (`settle_only_marks_live_run`).
* **A stop must revoke.** A `work-stop` while the launch is still pending leaves the token valid
  under the current protocol, so the launch starts after the stop (`current_stopped_launch_starts`).
  The fixed stop revokes the reservation (`fixed_stopped_launch_never_starts`).
* **The fix** has three parts, plus the revoking stop:
  - The reaper's publication changes the state only if it still says running and names the run
    the reaper observed.
  - A resume settles the previous ending, then reserves a fresh run token, superseding any
    earlier one. All of this happens under the session lock, as one step.
  - A worker consumes its token under the lock before any other work. It starts only if that
    token is the current reservation, and otherwise exits.
  With these, no ending is published over a live run (`fixed_never_marks_live_run`). Tokens are
  consumed at most once (`fixed_tokens_consumed_once`), and only the newest reservation can be
  consumed (`fixed_reservation_is_newest`). A delayed launch finds its token superseded and exits
  (`fixed_stale_launch_exits`), in either order of registration (`fixed_superseded_first_exits`). No timeout reclaims a reservation: a launch that never starts
  leaves the session reserved, and the next resume supersedes it.

Correspondence with the code: `reserved = some t` is the manifest's run token `t` in phase
`reserved`. Consuming it is the manifest's change from `reserved` to `started` under the lock,
which makes the token single-use: a second start with the same token fails, even after the run
has ended and while `t` is still the newest token. Conditional writes consult the manifest's run
and phase.

Scope:
* That at most one worker runs is systemd's uniqueness of unit names, assumed: a registration
  needs an inactive scope. Concurrent resumes may leave several launches pending, and any of
  them may register later, which over-approximates systemd.
* Each step is atomic. The reaper's two steps, a resume's settle-and-reserve, a worker's
  consumption, and every other write of `state.json` under the session lock are the units the
  fix requires.
* Every worker here consumes tokens. A worker frozen before the token protocol does not, so it
  is outside the fixed protocol: the resume guard refuses such a pin, and its session resumes
  through a re-pin to the current runtime. `current_stale_launch_starts` is the counterexample
  that rules out allowing it.
* Authority covers the session's metadata and the start of work. External effects already in
  flight belong to the one worker that systemd lets run. A token says nothing about them.
-/

namespace PettaClaw.CodingSessionAuthority

structure State where
  /-- `state.json` says running. -/
  running : Bool
  /-- The run that `state.json` names. -/
  owner : Nat
  /-- The run whose worker is alive, if any. -/
  worker : Option Nat
  /-- The run whose scope is active, if any. -/
  active : Option Nat
  /-- Launches whose scope has not registered yet. -/
  launches : List Nat
  nextRun : Nat
  /-- The run token a worker may consume (fixed protocol). -/
  reserved : Option Nat
  /-- Tokens consumed by starting workers, newest first. -/
  consumed : List Nat
  /-- Observations a paused reaper will publish: the owner it saw dead. -/
  pending : List Nat
  /-- For each ending published by a reaper or a settlement: was the run it marked alive? -/
  log : List Bool
  deriving DecidableEq, Repr

inductive Step where
  | resume
  | register (run : Nat)
  | start
  | finish
  | crash
  | reapRead
  | reapPublish
  /-- `work-stop`: the scope is stopped; under the fixed protocol a reservation is revoked too. -/
  | stop
  deriving DecidableEq, Repr

inductive Protocol where
  | current
  | settleOnly
  | fixed
  deriving DecidableEq, Repr

/-- What the reaper and the settlement require before marking an ending. -/
def stale (s : State) : Bool := s.running && s.active.isNone && s.worker != some s.owner

def mark (s : State) : State :=
  { s with running := false, log := (s.worker == some s.owner) :: s.log }

/-- A settlement under the lock: observe and publish in one step. -/
def settle (s : State) : State := if stale s then mark s else s

def launch (s : State) : State :=
  { s with launches := s.nextRun :: s.launches, nextRun := s.nextRun + 1 }

def reserve (s : State) : State :=
  { launch s with reserved := some s.nextRun }

def step (p : Protocol) (s : State) : Step → State
  | .resume =>
    if s.active.isSome then s
    else match p with
      | .current => launch s
      | .settleOnly => launch (settle s)
      | .fixed => reserve (settle s)
  | .register r =>
    if r ∈ s.launches ∧ s.active = none then
      { s with active := some r, worker := some r, launches := s.launches.filter (· ≠ r) }
    else s
  | .start =>
    match s.active with
    | none => s
    | some r =>
      if s.worker = some r then
        match p with
        | .fixed =>
          if s.reserved = some r then
            { s with running := true, owner := r, reserved := none, consumed := r :: s.consumed }
          else { s with active := none, worker := none }
        | _ => { s with running := true, owner := r }
      else s
  | .finish =>
    match s.active with
    | some _ => { s with running := false, active := none, worker := none }
    | none => s
  | .crash =>
    match s.active with
    | some _ => { s with active := none, worker := none }
    | none => s
  | .stop =>
    match p with
    | .fixed => { s with active := none, worker := none, reserved := none }
    | _ => { s with active := none, worker := none }
  | .reapRead => if stale s then { s with pending := s.owner :: s.pending } else s
  | .reapPublish =>
    match s.pending with
    | [] => s
    | o :: rest =>
      let s' := { s with pending := rest }
      match p with
      | .fixed => if s'.running && s'.owner == o then mark s' else s'
      | _ => mark s'

def run (p : Protocol) (s : State) (steps : List Step) : State := steps.foldl (step p) s

def fresh : State :=
  { running := false, owner := 0, worker := none, active := none, launches := [], nextRun := 0,
    reserved := none, consumed := [], pending := [], log := [] }

/-! ## The stale reaper: a crash, an observation, a resume, a start, the publication -/

def staleReaper : List Step :=
  [.resume, .register 0, .start, .crash, .reapRead, .resume, .register 1, .start, .reapPublish]

theorem current_marks_live_run : (run .current fresh staleReaper).log = [true] := by decide

theorem settle_only_marks_live_run :
    (run .settleOnly fresh staleReaper).log = [true, false] := by decide

theorem fixed_stale_reaper_skips : (run .fixed fresh staleReaper).log = [false] := by decide

/-! ## The stale launch: a launch delayed past a later run's whole life -/

def staleLaunch : List Step :=
  [.resume, .resume, .register 1, .start, .finish, .register 0, .start]

theorem current_stale_launch_starts :
    (run .current fresh staleLaunch).running = true ∧ (run .current fresh staleLaunch).owner = 0 := by
  decide

theorem fixed_stale_launch_exits :
    (run .fixed fresh staleLaunch).running = false ∧ (run .fixed fresh staleLaunch).consumed = [1] ∧
      (run .fixed fresh staleLaunch).worker = none := by decide

/-- The other order: the superseded launch registers first. It exits without authority, and the
newest launch then registers and starts. Exactly one obtains authority. -/
def supersededFirst : List Step :=
  [.resume, .resume, .register 0, .start, .register 1, .start]

theorem fixed_superseded_first_exits :
    (run .fixed fresh supersededFirst).consumed = [1] ∧
      (run .fixed fresh supersededFirst).owner = 1 := by decide

/-- A stop while the launch is still pending: under the current protocol the launch starts
afterwards anyway; with the revocation it never obtains authority. -/
def stoppedLaunch : List Step := [.resume, .stop, .register 0, .start]

theorem current_stopped_launch_starts : (run .current fresh stoppedLaunch).running = true := by
  decide

theorem fixed_stopped_launch_never_starts :
    (run .fixed fresh stoppedLaunch).running = false ∧
      (run .fixed fresh stoppedLaunch).consumed = [] := by decide

/-! ## The fixed protocol -/

def Inv (s : State) : Prop :=
  (∀ x, s.worker = some x → s.active = some x) ∧
  (∀ r, s.active = some r → r < s.nextRun ∧ r ∉ s.launches) ∧
  (∀ r ∈ s.launches, r < s.nextRun) ∧
  (s.running = true → s.owner < s.nextRun ∧ s.owner ∉ s.launches) ∧
  (∀ o ∈ s.pending, o < s.nextRun ∧ o ∉ s.launches ∧ s.active ≠ some o) ∧
  (∀ b ∈ s.log, b = false) ∧
  (∀ t, s.reserved = some t → t + 1 = s.nextRun ∧ t ∉ s.consumed) ∧
  (∀ t ∈ s.consumed, t < s.nextRun) ∧
  s.consumed.Nodup

theorem fresh_inv : Inv fresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [fresh]

theorem settle_inv (s : State) (h : Inv s) : Inv (settle s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  unfold settle
  split
  · rename_i hs
    simp only [stale, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    obtain ⟨⟨_, _⟩, hw⟩ := hs
    refine ⟨h1, h2, h3, by simp [mark], h5, ?_, h7, h8, h9⟩
    intro b hb
    simp only [mark, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simpa using hw
    · exact h6 b hb
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem settle_active (s : State) : (settle s).active = s.active := by
  unfold settle; split <;> rfl

theorem reserve_inv (s : State) (h : Inv s) (hnone : s.active = none) : Inv (reserve s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, ?_, ?_, h9⟩
  · intro x hx
    have := h1 x hx
    rw [hnone] at this; cases this
  · intro r hr; simp [reserve, launch, hnone] at hr
  · intro r hr
    simp only [reserve, launch, List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp [reserve, launch]
    · have := h3 r hr; simp [reserve, launch]; omega
  · intro hrun
    obtain ⟨hlt, hnot⟩ := h4 hrun
    simp only [reserve, launch, List.mem_cons, not_or]
    exact ⟨by omega, by omega, hnot⟩
  · intro o ho
    obtain ⟨hlt, hnot, hact⟩ := h5 o ho
    simp only [reserve, launch, List.mem_cons, not_or]
    exact ⟨by omega, ⟨by omega, hnot⟩, hact⟩
  · intro t ht
    simp only [reserve, launch, Option.some.injEq] at ht
    subst ht
    refine ⟨rfl, fun hm => ?_⟩
    have := h8 _ hm
    omega
  · intro t ht
    have := h8 t ht
    simp [reserve, launch]; omega

theorem fixed_preserves_inv (s : State) (t : Step) (h : Inv s) : Inv (step .fixed s t) := by
  have hI := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases t with
  | resume =>
    simp only [step]
    split
    · exact hI
    · rename_i hact
      have hnone : s.active = none := by simpa using hact
      exact reserve_inv _ (settle_inv s hI) (by rw [settle_active]; exact hnone)
  | register r =>
    simp only [step]
    split
    · rename_i hc
      obtain ⟨hr, hnone⟩ := hc
      refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, h9⟩
      · intro x hx; simp at hx; simp [hx]
      · intro r' hr'; simp at hr'; subst hr'; exact ⟨h3 _ hr, by simp⟩
      · intro r' hr'; exact h3 r' (List.mem_filter.1 hr').1
      · intro hrun
        obtain ⟨hlt, hnot⟩ := h4 hrun
        exact ⟨hlt, fun hm => hnot (List.mem_filter.1 hm).1⟩
      · intro o ho
        obtain ⟨hlt, hnot, _⟩ := h5 o ho
        refine ⟨hlt, fun hm => hnot (List.mem_filter.1 hm).1, ?_⟩
        intro heq; simp at heq; subst heq; exact hnot hr
    · exact hI
  | start =>
    simp only [step]
    cases hact : s.active with
    | none => exact hI
    | some r =>
      simp only
      split
      · split
        · rename_i hres
          obtain ⟨hlt, hnot⟩ := h2 r hact
          obtain ⟨_, hnc⟩ := h7 r hres
          refine ⟨fun x hx => by have := h1 x hx; rw [hact] at this; exact this,
            fun r' hr' => h2 r' (by rw [hact]; exact hr'), h3, fun _ => ⟨hlt, hnot⟩,
            fun o ho => by have := h5 o ho; rw [hact] at this; exact this, h6, ?_, ?_, ?_⟩
          · intro t ht; simp at ht
          · intro t ht
            simp only [List.mem_cons] at ht
            rcases ht with rfl | ht
            · exact hlt
            · exact h8 t ht
          · exact List.nodup_cons.2 ⟨hnc, h9⟩
        · refine ⟨?_, ?_, h3, h4, ?_, h6, h7, h8, h9⟩
          · intro x hx; simp at hx
          · intro r' hr'; simp at hr'
          · intro o ho
            obtain ⟨hlt, hnot, _⟩ := h5 o ho
            exact ⟨hlt, hnot, by simp⟩
      · exact hI
  | finish =>
    simp only [step]
    cases hact : s.active with
    | none => exact hI
    | some r =>
      refine ⟨?_, ?_, h3, ?_, ?_, h6, h7, h8, h9⟩
      · intro x hx; simp at hx
      · intro r' hr'; simp at hr'
      · intro hrun; simp at hrun
      · intro o ho
        obtain ⟨hlt, hnot, _⟩ := h5 o ho
        exact ⟨hlt, hnot, by simp⟩
  | crash =>
    simp only [step]
    cases hact : s.active with
    | none => exact hI
    | some r =>
      refine ⟨?_, ?_, h3, h4, ?_, h6, h7, h8, h9⟩
      · intro x hx; simp at hx
      · intro r' hr'; simp at hr'
      · intro o ho
        obtain ⟨hlt, hnot, _⟩ := h5 o ho
        exact ⟨hlt, hnot, by simp⟩
  | stop =>
    simp only [step]
    refine ⟨?_, ?_, h3, h4, ?_, h6, ?_, h8, h9⟩
    · intro x hx; simp at hx
    · intro r' hr'; simp at hr'
    · intro o ho
      obtain ⟨hlt, hnot, _⟩ := h5 o ho
      exact ⟨hlt, hnot, by simp⟩
    · intro t ht; simp at ht
  | reapRead =>
    simp only [step]
    split
    · rename_i hs
      simp only [stale, Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
      obtain ⟨⟨hrun, hnone⟩, _⟩ := hs
      refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9⟩
      intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · obtain ⟨hlt, hnot⟩ := h4 hrun
        exact ⟨hlt, hnot, by simp [hnone]⟩
      · exact h5 o ho
    · exact hI
  | reapPublish =>
    simp only [step]
    cases hp : s.pending with
    | nil => exact hI
    | cons o rest =>
      have hrest : ∀ o' ∈ rest, o' < s.nextRun ∧ o' ∉ s.launches ∧ s.active ≠ some o' :=
        fun o' ho' => h5 o' (by simp [hp, ho'])
      have ho := h5 o (by simp [hp])
      simp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨_, hown⟩ := hc
        refine ⟨h1, h2, h3, by simp [mark], hrest, ?_, h7, h8, h9⟩
        intro b hb
        simp only [mark, List.mem_cons] at hb
        rcases hb with rfl | hb
        · show (s.worker == some s.owner) = false
          cases hw : s.worker with
          | none => rfl
          | some x =>
            have hx := h1 x hw
            have hne : x ≠ s.owner := by
              intro hxo; rw [hxo, hown] at hx; exact ho.2.2 hx
            simp [hne]
        · exact h6 b hb
      · exact ⟨h1, h2, h3, h4, hrest, h6, h7, h8, h9⟩

theorem fixed_run_inv (s : State) (steps : List Step) (h : Inv s) :
    Inv (run .fixed s steps) := by
  unfold run
  induction steps generalizing s with
  | nil => exact h
  | cons t rest ih => exact ih (step .fixed s t) (fixed_preserves_inv s t h)

/-- No ending is ever published over a live run. -/
theorem fixed_never_marks_live_run (steps : List Step) :
    ∀ b ∈ (run .fixed fresh steps).log, b = false :=
  (fixed_run_inv fresh steps fresh_inv).2.2.2.2.2.1

/-- Each run token is consumed at most once. -/
theorem fixed_tokens_consumed_once (steps : List Step) :
    (run .fixed fresh steps).consumed.Nodup :=
  (fixed_run_inv fresh steps fresh_inv).2.2.2.2.2.2.2.2

/-- The token a worker can consume is the newest resume's: every earlier reservation is
superseded. -/
theorem fixed_reservation_is_newest (steps : List Step) (t : Nat)
    (h : (run .fixed fresh steps).reserved = some t) : t + 1 = (run .fixed fresh steps).nextRun :=
  ((fixed_run_inv fresh steps fresh_inv).2.2.2.2.2.2.1 t h).1

/-- The live worker is the active scope's. -/
theorem one_live_worker (steps : List Step) (x : Nat)
    (h : (run .fixed fresh steps).worker = some x) : (run .fixed fresh steps).active = some x :=
  (fixed_run_inv fresh steps fresh_inv).1 x h

end PettaClaw.CodingSessionAuthority

#print axioms PettaClaw.CodingSessionAuthority.current_marks_live_run
#print axioms PettaClaw.CodingSessionAuthority.settle_only_marks_live_run
#print axioms PettaClaw.CodingSessionAuthority.fixed_stale_reaper_skips
#print axioms PettaClaw.CodingSessionAuthority.current_stale_launch_starts
#print axioms PettaClaw.CodingSessionAuthority.fixed_stale_launch_exits
#print axioms PettaClaw.CodingSessionAuthority.fixed_superseded_first_exits
#print axioms PettaClaw.CodingSessionAuthority.current_stopped_launch_starts
#print axioms PettaClaw.CodingSessionAuthority.fixed_stopped_launch_never_starts
#print axioms PettaClaw.CodingSessionAuthority.fixed_preserves_inv
#print axioms PettaClaw.CodingSessionAuthority.fixed_never_marks_live_run
#print axioms PettaClaw.CodingSessionAuthority.fixed_tokens_consumed_once
#print axioms PettaClaw.CodingSessionAuthority.fixed_reservation_is_newest
#print axioms PettaClaw.CodingSessionAuthority.one_live_worker
