/-!
# Coding-session launches: one reservation, one bundle, one live authority

`CodingSessionAuthority` assumes that a resume checks liveness and reserves in one step, and that
a launch carries its run identity from the reservation to the worker. A review of the deployed
code found both assumptions broken at the adapter. This model makes each break a decided trace
and proves the protocol that restores the steps.

The state:
* the session manifest: its run token, its bundle and its phase;
* the launches made so far: each is a descriptor (token, bundle) or the bundle alone;
* the workers those launches started: what each presented, whether it consumed, whether it is
  alive.

Under the current protocol:
* **A launch rereads the token.** It keeps its bundle and then takes the manifest's newest token.
  A delayed launch of bundle `a` then consumes the reservation of a later re-pin to bundle `b`,
  and runs `a` under `b`'s authority (`current_launch_takes_other_token`).
* **A resume reserves without rechecking liveness.** The liveness check ran earlier, outside the
  lock, so a resume can replace the token of a worker that has started and is alive. That worker
  loses its authority mid-run (`current_resume_revokes_live_worker`).

The fixed protocol:
* a reservation refuses while a consumed worker is alive;
* a launch carries the reservation's descriptor unchanged;
* a consumption requires that the descriptor's token and bundle both equal the manifest's, in
  phase reserved.

With these:
* every live worker that consumed holds the manifest's token and runs the manifest's bundle
  (`fixed_live_authority_is_bound`);
* both traces are refused (`fixed_launch_keeps_own_token`, `fixed_resume_spares_live_worker`).

Scope: workers are indexed by launch; the lock makes each step atomic; the scope check inside the
lock is represented by the live-worker check. Effects of a worker are not modelled.
-/

namespace PettaClaw.CodingSessionLaunch

inductive Phase where
  | reserved
  | started
  | ended
  deriving DecidableEq, Repr

structure Manifest where
  run : Nat
  bundle : Nat
  phase : Phase
  deriving DecidableEq, Repr

structure Worker where
  token : Nat
  bundle : Nat
  consumed : Bool
  alive : Bool
  deriving DecidableEq, Repr

structure State where
  manifest : Manifest
  nextRun : Nat
  /-- Launch descriptors, by launch index: the reserved (token, bundle). -/
  launches : Nat → Option (Nat × Nat)
  nextLaunch : Nat
  /-- The worker each launch started, by launch index. -/
  workers : Nat → Option Worker

inductive Step where
  /-- A resume or re-pin reserving a run on a bundle. -/
  | reserve (bundle : Nat)
  /-- The launch with this index starts its worker. -/
  | launch (index : Nat)
  /-- The worker of this launch consumes its token. -/
  | consume (index : Nat)
  /-- The worker of this launch ends or dies. -/
  | stop (index : Nat)
  deriving DecidableEq, Repr

inductive Protocol where
  | current
  | fixed
  deriving DecidableEq, Repr

/-- Some worker has consumed and is alive. -/
def liveConsumed (s : State) : Prop := ∃ i w, s.workers i = some w ∧ w.consumed = true ∧ w.alive = true

def anyLive (s : State) (n : Nat) : Bool :=
  (List.range n).any fun i =>
    match s.workers i with
    | some w => w.consumed && w.alive
    | none => false

def setWorker (s : State) (i : Nat) (w : Worker) : State :=
  { s with workers := fun j => if j = i then some w else s.workers j }

def reserveAt (s : State) (b : Nat) : State :=
  { s with manifest := { run := s.nextRun, bundle := b, phase := .reserved },
           nextRun := s.nextRun + 1,
           launches := fun j => if j = s.nextLaunch then some (s.nextRun, b) else s.launches j,
           nextLaunch := s.nextLaunch + 1 }

/-- A consumption: the worker gains authority and the manifest moves to started; otherwise the
worker exits. `ok` is the protocol's admission test. -/
def consumeAt (s : State) (i : Nat) (w : Worker) (ok : Prop) [Decidable ok] : State :=
  if ok then { setWorker s i { w with consumed := true } with manifest := { s.manifest with phase := .started } }
  else setWorker s i { w with alive := false }

def step (p : Protocol) (s : State) : Step → State
  | .reserve b =>
    match p with
    | .fixed => if anyLive s s.nextLaunch = true then s else reserveAt s b
    | .current => reserveAt s b
  | .launch i =>
    match s.launches i, s.workers i with
    | some (t, b), none =>
      match p with
      | .fixed => setWorker s i { token := t, bundle := b, consumed := false, alive := true }
      -- The current launch keeps its bundle but rereads the manifest's newest token.
      | .current => setWorker s i { token := s.manifest.run, bundle := b, consumed := false, alive := true }
    | _, _ => s
  | .consume i =>
    match s.workers i with
    | some w =>
      match p with
      | .fixed => consumeAt s i w (w.alive = true ∧ w.consumed = false ∧ w.token = s.manifest.run ∧
          s.manifest.phase = .reserved ∧ w.bundle = s.manifest.bundle)
      | .current => consumeAt s i w (w.alive = true ∧ w.consumed = false ∧ w.token = s.manifest.run ∧
          s.manifest.phase = .reserved)
    | none => s
  | .stop i =>
    match s.workers i with
    | some w =>
      let s' := setWorker s i { w with alive := false }
      if w.consumed = true ∧ w.alive = true ∧ w.token = s.manifest.run then
        { s' with manifest := { s.manifest with phase := .ended } }
      else s'
    | none => s

def run (p : Protocol) (s : State) (steps : List Step) : State := steps.foldl (step p) s

def fresh : State :=
  { manifest := { run := 0, bundle := 0, phase := .ended }, nextRun := 1,
    launches := fun _ => none, nextLaunch := 0, workers := fun _ => none }

/-- What a live consumed worker presents, against the manifest. -/
def bound (s : State) (i : Nat) : Bool :=
  match s.workers i with
  | some w => !(w.consumed && w.alive) ||
      (w.token == s.manifest.run && w.bundle == s.manifest.bundle && s.manifest.phase == .started)
  | none => true

/-! ## The two traces -/

/-- Resume A reserves bundle 10, its launch is delayed, a re-pin B reserves bundle 20, then A's
launch starts and consumes. -/
def delayedLaunch : List Step := [.reserve 10, .reserve 20, .launch 0, .consume 0]

theorem current_launch_takes_other_token :
    let s := run .current fresh delayedLaunch
    (s.workers 0).map (·.consumed) = some true ∧ (s.workers 0).map (·.bundle) = some 10 ∧
      s.manifest.bundle = 20 := by decide

theorem fixed_launch_keeps_own_token :
    let s := run .fixed fresh delayedLaunch
    (s.workers 0).map (·.consumed) = some false ∧ (s.workers 0).map (·.alive) = some false := by
  decide

/-- A run starts and consumes; then a second resume, whose liveness check was stale, reserves. -/
def staleSecondResume : List Step := [.reserve 10, .launch 0, .consume 0, .reserve 10]

theorem current_resume_revokes_live_worker :
    let s := run .current fresh staleSecondResume
    (s.workers 0).map (fun w => w.consumed && w.alive) = some true ∧
      (s.workers 0).map (·.token) ≠ some s.manifest.run := by decide

theorem fixed_resume_spares_live_worker :
    let s := run .fixed fresh staleSecondResume
    (s.workers 0).map (·.token) = some s.manifest.run ∧ s.manifest.phase = .started := by decide

/-! ## The fixed protocol binds every live authority -/

/-- Workers exist only for launches made; descriptors carry fresh tokens; a live consumed worker
holds the manifest's token and bundle in phase started, and is the only one. -/
def Inv (s : State) : Prop :=
  (∀ i, s.nextLaunch ≤ i → s.workers i = none ∧ s.launches i = none) ∧
  (∀ i t b, s.launches i = some (t, b) → t < s.nextRun) ∧
  s.manifest.run < s.nextRun ∧
  (∀ i w, s.workers i = some w → w.consumed = true → w.alive = true →
    w.token = s.manifest.run ∧ w.bundle = s.manifest.bundle ∧ s.manifest.phase = .started) ∧
  (∀ i j wi wj, s.workers i = some wi → s.workers j = some wj →
    wi.consumed = true → wi.alive = true → wj.consumed = true → wj.alive = true → i = j)

theorem anyLive_false (s : State) (h1 : ∀ i, s.nextLaunch ≤ i → s.workers i = none)
    (h : anyLive s s.nextLaunch = false) :
    ∀ i w, s.workers i = some w → w.consumed = true → w.alive = true → False := by
  intro i w hw hc ha
  by_cases hi : i < s.nextLaunch
  · unfold anyLive at h
    rw [List.any_eq_false] at h
    have := h i (List.mem_range.2 hi)
    simp [hw, hc, ha] at this
  · have := h1 i (by omega)
    rw [this] at hw; cases hw

theorem fresh_inv : Inv fresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [fresh]

theorem fixed_preserves_inv (s : State) (t : Step) (h : Inv s) : Inv (step .fixed s t) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases t with
  | reserve b =>
    simp only [step]
    by_cases hl : anyLive s s.nextLaunch = true
    · rw [if_pos hl]; exact ⟨h1, h2, h3, h4, h5⟩
    · rw [if_neg hl]
      have hnone := anyLive_false s (fun i hi => (h1 i hi).1) (by simpa using hl)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have := h1 i (by simp [reserveAt] at hi; omega)
        have hne : i ≠ s.nextLaunch := by simp [reserveAt] at hi; omega
        exact ⟨this.1, by simp [reserveAt, hne, this.2]⟩
      · intro i t' b' hd
        by_cases hi : i = s.nextLaunch
        · simp [reserveAt, hi] at hd; simp [reserveAt]; omega
        · simp [reserveAt, hi] at hd; have := h2 i t' b' hd; simp [reserveAt]; omega
      · simp [reserveAt]
      · intro i w hw hc ha; exact absurd (hnone i w hw hc ha) id
      · intro i j wi wj hi _ hci hai _ _; exact absurd (hnone i wi hi hci hai) id
  | launch i =>
    simp only [step]
    cases hd : s.launches i with
    | none => simp only; exact ⟨h1, h2, h3, h4, h5⟩
    | some d =>
      obtain ⟨t', b'⟩ := d
      cases hw : s.workers i with
      | some _ => simp only; exact ⟨h1, h2, h3, h4, h5⟩
      | none =>
        simp only [setWorker]
        have hi : i < s.nextLaunch := by
          apply Nat.lt_of_not_le; intro hc; have := (h1 i hc).2; rw [this] at hd; cases hd
        refine ⟨?_, h2, h3, ?_, ?_⟩
        · intro j hj
          have hj' : s.nextLaunch ≤ j := hj
          have := h1 j hj'
          have hne : j ≠ i := by omega
          simp [hne, this.1, this.2]
        · intro j w hj hc ha
          by_cases hji : j = i
          · subst hji; simp at hj; subst hj; simp at hc
          · simp [hji] at hj; exact h4 j w hj hc ha
        · intro j k wj wk hj hk hcj haj hck hak
          by_cases hji : j = i
          · subst hji; simp at hj; subst hj; simp at hcj
          · by_cases hki : k = i
            · subst hki; simp at hk; subst hk; simp at hck
            · simp [hji] at hj; simp [hki] at hk; exact h5 j k wj wk hj hk hcj haj hck hak
  | consume i =>
    simp only [step]
    cases hw : s.workers i with
    | none => exact ⟨h1, h2, h3, h4, h5⟩
    | some w =>
      simp only [consumeAt]
      by_cases hc : w.alive = true ∧ w.consumed = false ∧ w.token = s.manifest.run ∧
          s.manifest.phase = .reserved ∧ w.bundle = s.manifest.bundle
      · rw [if_pos hc]
        obtain ⟨_, _, htok, hph, hb⟩ := hc
        -- No other worker is live and consumed: that would put the manifest in phase started.
        have hother : ∀ j wj, s.workers j = some wj → wj.consumed = true → wj.alive = true → False :=
          fun j wj hj hcj haj => by have := (h4 j wj hj hcj haj).2.2; rw [hph] at this; cases this
        refine ⟨?_, h2, h3, ?_, ?_⟩
        · intro j hj
          have := h1 j hj
          have hne : j ≠ i := by intro e; subst e; rw [this.1] at hw; cases hw
          simp [setWorker, hne, this.1, this.2]
        · intro j wj hj hcj haj
          by_cases hji : j = i
          · subst hji; simp [setWorker] at hj; subst hj; exact ⟨htok, hb, rfl⟩
          · simp [setWorker, hji] at hj; exact absurd (hother j wj hj hcj haj) id
        · intro j k wj wk hj hk hcj haj hck hak
          by_cases hji : j = i
          · by_cases hki : k = i
            · rw [hji, hki]
            · simp [setWorker, hki] at hk; exact absurd (hother k wk hk hck hak) id
          · simp [setWorker, hji] at hj; exact absurd (hother j wj hj hcj haj) id
      · rw [if_neg hc]
        simp only [setWorker]
        refine ⟨?_, h2, h3, ?_, ?_⟩
        · intro j hj
          have := h1 j hj
          have hne : j ≠ i := by intro e; subst e; rw [this.1] at hw; cases hw
          simp [hne, this.1, this.2]
        · intro j wj hj hcj haj
          by_cases hji : j = i
          · subst hji; simp at hj; subst hj; simp at haj
          · simp [hji] at hj; exact h4 j wj hj hcj haj
        · intro j k wj wk hj hk hcj haj hck hak
          by_cases hji : j = i
          · subst hji; simp at hj; subst hj; simp at haj
          · by_cases hki : k = i
            · subst hki; simp at hk; subst hk; simp at hak
            · simp [hji] at hj; simp [hki] at hk; exact h5 j k wj wk hj hk hcj haj hck hak
  | stop i =>
    simp only [step]
    cases hw : s.workers i with
    | none => exact ⟨h1, h2, h3, h4, h5⟩
    | some w =>
      simp only
      have base1 : ∀ j, s.nextLaunch ≤ j →
          (setWorker s i { w with alive := false }).workers j = none ∧ s.launches j = none := by
        intro j hj
        have := h1 j hj
        have hne : j ≠ i := by intro e; subst e; rw [this.1] at hw; cases hw
        simp [setWorker, hne, this.1, this.2]
      have live : ∀ j wj, (setWorker s i { w with alive := false }).workers j = some wj →
          wj.consumed = true → wj.alive = true → j ≠ i ∧ s.workers j = some wj := by
        intro j wj hj hcj haj
        by_cases hji : j = i
        · subst hji; simp [setWorker] at hj; subst hj; simp at haj
        · simp [setWorker, hji] at hj; exact ⟨hji, hj⟩
      by_cases hend : w.consumed = true ∧ w.alive = true ∧ w.token = s.manifest.run
      · rw [if_pos hend]
        -- worker i was the one live consumed worker; once it stops there are none
        refine ⟨base1, h2, h3, ?_, ?_⟩
        · intro j wj hj hcj haj
          obtain ⟨hne, hj'⟩ := live j wj hj hcj haj
          exact absurd (h5 j i wj w hj' hw hcj haj hend.1 hend.2.1) hne
        · intro j k wj wk hj hk hcj haj hck hak
          obtain ⟨hne, hj'⟩ := live j wj hj hcj haj
          exact absurd (h5 j i wj w hj' hw hcj haj hend.1 hend.2.1) hne
      · rw [if_neg hend]
        refine ⟨base1, h2, h3, ?_, ?_⟩
        · intro j wj hj hcj haj
          obtain ⟨_, hj'⟩ := live j wj hj hcj haj
          exact h4 j wj hj' hcj haj
        · intro j k wj wk hj hk hcj haj hck hak
          obtain ⟨_, hj'⟩ := live j wj hj hcj haj
          obtain ⟨_, hk'⟩ := live k wk hk hck hak
          exact h5 j k wj wk hj' hk' hcj haj hck hak

theorem fixed_run_inv (s : State) (steps : List Step) (h : Inv s) : Inv (run .fixed s steps) := by
  unfold run
  induction steps generalizing s with
  | nil => exact h
  | cons t rest ih => exact ih (step .fixed s t) (fixed_preserves_inv s t h)

/-- Every live worker that consumed holds the manifest's token and runs the manifest's bundle. -/
theorem fixed_live_authority_is_bound (steps : List Step) (i : Nat) (w : Worker)
    (hw : (run .fixed fresh steps).workers i = some w) (hc : w.consumed = true)
    (ha : w.alive = true) :
    w.token = (run .fixed fresh steps).manifest.run ∧
      w.bundle = (run .fixed fresh steps).manifest.bundle :=
  let h := ((fixed_run_inv fresh steps fresh_inv).2.2.2.1 i w hw hc ha)
  ⟨h.1, h.2.1⟩

end PettaClaw.CodingSessionLaunch

#print axioms PettaClaw.CodingSessionLaunch.current_launch_takes_other_token
#print axioms PettaClaw.CodingSessionLaunch.fixed_launch_keeps_own_token
#print axioms PettaClaw.CodingSessionLaunch.current_resume_revokes_live_worker
#print axioms PettaClaw.CodingSessionLaunch.fixed_resume_spares_live_worker
#print axioms PettaClaw.CodingSessionLaunch.fixed_preserves_inv
#print axioms PettaClaw.CodingSessionLaunch.fixed_live_authority_is_bound
