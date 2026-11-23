/-
  UpdateRollbackSafety.lean — Abstract two-slot monotonic trial/rollback protocol.

  Models two complementary boot slots, committed versus staged versions, trial state,
  and a typed boot-target choice (`primary | fallback`) with zero bootloader-specific
  entry indices, zero sentinels, or hardware register constants.

  Note on refinement boundary: concrete implementations additionally owe disjoint
  storage extents, verified readback before metadata commit, and durable publication
  of the boot descriptor.
-/
namespace Mettapedia.Machines.Kernel.UpdateRollbackSafety

/-- Two complementary boot slots. -/
inductive Slot where
  | a
  | b
  deriving DecidableEq, Repr

/-- Inactive counterpart of a slot. -/
def Slot.other : Slot → Slot
  | .a => .b
  | .b => .a

theorem slot_other_ne (s : Slot) : s.other ≠ s := by
  cases s <;> decide

theorem slot_other_involutive (s : Slot) : s.other.other = s := by
  cases s <;> rfl

/-- Trial lifecycle for a staged candidate image. -/
inductive TrialState where
  | idle
  | pending
  | started
  | failed
  deriving DecidableEq, Repr

/-- Typed next-boot selection between the primary (active/trial) slot and fallback slot. -/
inductive BootChoice where
  | primary
  | fallback
  deriving DecidableEq, Repr

/-- Abstract A/B update state separating committed image from staged candidate. -/
structure UpdateState where
  committedSlot    : Slot
  committedVersion : Nat
  stagedSlot       : Slot
  stagedVersion    : Nat
  trial            : TrialState
  deriving DecidableEq, Repr

/-- Boot target selected on next reboot. -/
def bootChoice (st : UpdateState) : BootChoice :=
  match st.trial with
  | .started | .failed => .fallback
  | .idle | .pending   => .primary

/-- Eligibility predicate for staging `newVersion` onto `running.other`. -/
def canStage (st : UpdateState) (running : Slot) (newVersion : Nat) : Bool :=
  let dst := running.other
  decide (newVersion > st.committedVersion) &&
  !(decide (st.trial = .pending) && decide (st.stagedSlot = dst))

/-- Stage a strictly newer candidate onto the inactive slot without overwriting `running`. -/
def stage (st : UpdateState) (running : Slot) (newVersion : Nat) : Option (Slot × UpdateState) :=
  if canStage st running newVersion then
    let dst := running.other
    some (dst, { st with stagedSlot := dst, stagedVersion := newVersion, trial := .pending })
  else
    none

/-- Boot-start transition when `booted` enters execution. -/
def onBootStart (st : UpdateState) (booted : Slot) : Option UpdateState :=
  match st.trial with
  | .pending =>
      if booted = st.stagedSlot then some { st with trial := .started }
      else some { st with trial := .failed }
  | .started =>
      if booted ≠ st.stagedSlot then some { st with trial := .failed }
      else none
  | _ => none

/-- Health confirmation reported by `booted`: promotes only when `booted` is the staged trial slot. -/
def onHealthy (st : UpdateState) (booted : Slot) : Option UpdateState :=
  match st.trial with
  | .pending | .started =>
      if booted = st.stagedSlot then
        some { st with
          committedSlot    := st.stagedSlot,
          committedVersion := max st.committedVersion st.stagedVersion,
          trial            := .idle }
      else none
  | _ => none

/-- Protocol events for trace-level monotonicity proofs. -/
inductive UpdateEvent where
  | stage (running : Slot) (newVersion : Nat)
  | bootStart (booted : Slot)
  | healthy (booted : Slot)
  deriving DecidableEq, Repr

/-- Single-step state transition (rejected events leave state unchanged). -/
def step (st : UpdateState) : UpdateEvent → UpdateState
  | .stage running v =>
      match stage st running v with
      | some (_, st') => st'
      | none          => st
  | .bootStart booted => (onBootStart st booted).getD st
  | .healthy booted   => (onHealthy st booted).getD st

/-- Execute a finite sequence of update protocol events. -/
def runTrace (st : UpdateState) (evs : List UpdateEvent) : UpdateState :=
  evs.foldl step st

theorem stage_selects_inactive_slot (st : UpdateState) (running : Slot) (v : Nat)
    (dst : Slot) (next : UpdateState)
    (h : stage st running v = some (dst, next)) :
    dst ≠ running ∧ dst = running.other := by
  unfold stage at h
  split at h
  · injection h with hpair
    have hdst : dst = running.other := (Prod.mk.inj hpair).1.symm
    exact ⟨hdst ▸ slot_other_ne running, hdst⟩
  · contradiction

theorem stage_rejects_downgrade (st : UpdateState) (running : Slot) (v : Nat)
    (hle : v ≤ st.committedVersion) :
    stage st running v = none := by
  unfold stage canStage
  have hnot : ¬(v > st.committedVersion) := by omega
  simp [hnot]

theorem stage_rejects_overwrite_pending (st : UpdateState) (running : Slot) (v : Nat)
    (hp : st.trial = .pending) (hc : st.stagedSlot = running.other) :
    stage st running v = none := by
  unfold stage canStage
  simp [hp, hc]

theorem boot_start_arms_fallback (st next : UpdateState)
    (hp : st.trial = .pending)
    (hstart : onBootStart st st.stagedSlot = some next) :
    next.trial = .started ∧ bootChoice next = .fallback := by
  unfold onBootStart at hstart
  rw [hp] at hstart
  simp at hstart
  subst hstart
  exact ⟨rfl, rfl⟩

theorem fallback_boot_marks_failed_and_keeps_fallback (st next : UpdateState) (booted : Slot)
    (hs : st.trial = .started) (hne : booted ≠ st.stagedSlot)
    (hstart : onBootStart st booted = some next) :
    next.trial = .failed ∧ bootChoice next = .fallback := by
  unfold onBootStart at hstart
  rw [hs] at hstart
  simp [hne] at hstart
  subst hstart
  exact ⟨rfl, rfl⟩

theorem healthy_refuses_wrong_slot (st : UpdateState) (booted : Slot)
    (hne : booted ≠ st.stagedSlot) :
    onHealthy st booted = none := by
  unfold onHealthy
  cases st.trial <;> simp [hne]

theorem healthy_promotes_only_staged_slot (st next : UpdateState) (booted : Slot)
    (h : onHealthy st booted = some next) :
    booted = st.stagedSlot ∧
    next.committedSlot = st.stagedSlot ∧
    next.committedVersion = max st.committedVersion st.stagedVersion ∧
    next.trial = .idle ∧
    bootChoice next = .primary := by
  unfold onHealthy at h
  cases ht : st.trial <;> rw [ht] at h <;> dsimp only at h
  · contradiction
  · by_cases hbc : booted = st.stagedSlot
    · simp [hbc] at h; subst h; exact ⟨hbc, rfl, rfl, rfl, rfl⟩
    · simp [hbc] at h
  · by_cases hbc : booted = st.stagedSlot
    · simp [hbc] at h; subst h; exact ⟨hbc, rfl, rfl, rfl, rfl⟩
    · simp [hbc] at h
  · contradiction

/-- Single-step monotonicity of `committedVersion`. -/
theorem step_committedVersion_monotonic (st : UpdateState) (ev : UpdateEvent) :
    st.committedVersion ≤ (step st ev).committedVersion := by
  cases ev with
  | stage running v =>
      by_cases hc : canStage st running v = true <;> simp [step, stage, hc]
  | bootStart booted =>
      simp only [step, onBootStart]
      cases st.trial
      · exact Nat.le_refl _
      · by_cases h : booted = st.stagedSlot <;> simp [h]
      · by_cases h : booted = st.stagedSlot <;> simp [h]
      · exact Nat.le_refl _
  | healthy booted =>
      simp only [step, onHealthy]
      cases st.trial
      · exact Nat.le_refl _
      · by_cases h : booted = st.stagedSlot <;> simp [h, Nat.le_max_left]
      · by_cases h : booted = st.stagedSlot <;> simp [h, Nat.le_max_left]
      · exact Nat.le_refl _

/-- Trace-level monotonicity: across any finite trace of stage/boot/health events,
    the committed version never decreases. -/
theorem trace_committedVersion_monotonic (evs : List UpdateEvent) :
    ∀ st : UpdateState, st.committedVersion ≤ (runTrace st evs).committedVersion := by
  induction evs with
  | nil =>
      intro st
      exact Nat.le_refl _
  | cons ev rest ih =>
      intro st
      exact Nat.le_trans (step_committedVersion_monotonic st ev) (ih (step st ev))

end Mettapedia.Machines.Kernel.UpdateRollbackSafety
