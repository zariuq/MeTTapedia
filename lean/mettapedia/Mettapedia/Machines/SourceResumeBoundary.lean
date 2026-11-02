import Mettapedia.Machines.SourceContextAdmission
import Mettapedia.Machines.ConstraintPropagation

/-!
# Guarded caller segments and the ordinary scheduling boundary

A segment repeatedly executes the maintained machine's word, checking the
current retained context before each word. On refusal it transfers the exact
resident state to ordinary execution. The proof compares a bounded direct
prefix followed by the ordinary suffix with an independently bounded ordinary
run, including its actual count, source ledger and pending publications.

The context guard is independent of available source credit. Constraint
owners, dormant watches, queued wakes and table work retain the ordinary
boundary. A consumed queue does not block later admission. The service control
uses the maintained chronological binding/wakeup construction; it demonstrates
why a pending wake may change a later condition.

These are laws for segment admission and composition. Native extraction of
the context, each worker's word refinement, solver synchronization and C memory
safety retain their implementation obligations. The count below is a logical
machine-word count, not the cost of a native physical step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.SourceResumeBoundary

open SourceContextAdmission

variable {Goal Term : Type}

def admitted (context : RetainedContext Goal) (tableEntries : Nat) : Bool :=
  !nativeBusy context && decide (tableEntries = 0)

theorem admission_refines (context : RetainedContext Goal) (tableEntries : Nat) :
    admitted context tableEntries = (sourceAllows context && decide (tableEntries = 0)) := by
  simp only [admitted, context_refines]

/-- Inspect the live context again after every successful word. -/
def runPrefix (core : MachineCore Term) (ready : core.State → Bool) :
    Nat → core.State → core.State × Nat
  | 0, state => (state, 0)
  | limit + 1, state =>
      if ready state then
        match core.step state with
        | none => (state, 0)
        | some next =>
            let suffix := runPrefix core ready limit next
            (suffix.1, suffix.2 + 1)
      else (state, 0)

theorem prefix_used_le (core : MachineCore Term) (ready : core.State → Bool)
    (limit : Nat) (state : core.State) : (runPrefix core ready limit state).2 ≤ limit := by
  induction limit generalizing state with
  | zero => simp [runPrefix]
  | succ limit ih =>
      by_cases allowed : ready state = true
      · cases advanced : core.step state with
        | none => simp [runPrefix, allowed, advanced]
        | some next => simpa [runPrefix, allowed, advanced] using Nat.add_le_add_right (ih next) 1
      · simp [runPrefix, allowed]

/-- Replaying exactly the direct prefix's count yields its full residual.
This does not assume that a refused endpoint is a final state. -/
theorem prefix_replays (core : MachineCore Term) (ready : core.State → Bool)
    (limit : Nat) (state : core.State) :
    core.runSlice (runPrefix core ready limit state).2 state = runPrefix core ready limit state := by
  induction limit generalizing state with
  | zero => rfl
  | succ limit ih =>
      by_cases allowed : ready state = true
      · cases advanced : core.step state with
        | none => simp [runPrefix, allowed, advanced, MachineCore.runSlice]
        | some next =>
            simp only [runPrefix, allowed, ↓reduceIte, advanced, MachineCore.runSlice]
            rw [ih]
      · simp [runPrefix, allowed, MachineCore.runSlice]

theorem refused_prefix_keeps_state (core : MachineCore Term) (ready : core.State → Bool)
    (limit : Nat) (state : core.State) (refused : ready state = false) :
    runPrefix core ready limit state = (state, 0) := by
  cases limit <;> simp [runPrefix, refused]

/-- A short prefix stops because the current context refused or the
maintained machine has no successor, not because its caller disappeared. -/
theorem prefix_exit_reason (core : MachineCore Term) (ready : core.State → Bool)
    (limit : Nat) (state : core.State)
    (short : (runPrefix core ready limit state).2 < limit) :
    ready (runPrefix core ready limit state).1 = false ∨
      core.step (runPrefix core ready limit state).1 = none := by
  induction limit generalizing state with
  | zero => simp [runPrefix] at short
  | succ limit ih =>
      by_cases allowed : ready state = true
      · cases advanced : core.step state with
        | none => simp [runPrefix, allowed, advanced]
        | some next =>
            have shorter : (runPrefix core ready limit next).2 < limit := by
              simpa [runPrefix, allowed, advanced] using short
            simpa [runPrefix, allowed, advanced] using ih next shorter
      · have refused : ready state = false := Bool.eq_false_iff.mpr allowed
        simp [runPrefix, refused]

/-- Ordinary execution consumes the remaining logical allowance from the
actual endpoint; it never reconstructs the segment's original source call. -/
def joined (core : MachineCore Term) (ready : core.State → Bool)
    (segmentLimit allowance : Nat) (state : core.State) : core.State × Nat :=
  let direct := runPrefix core ready (min segmentLimit allowance) state
  let ordinary := core.runSlice (allowance - direct.2) direct.1
  (ordinary.1, direct.2 + ordinary.2)

theorem joined_exact (core : MachineCore Term) (ready : core.State → Bool)
    (segmentLimit allowance : Nat) (state : core.State) :
    joined core ready segmentLimit allowance state = core.runSlice allowance state := by
  let direct := runPrefix core ready (min segmentLimit allowance) state
  have bounded : direct.2 ≤ allowance :=
    (prefix_used_le core ready (min segmentLimit allowance) state).trans (Nat.min_le_right _ _)
  have replay : core.runSlice direct.2 state = direct :=
    prefix_replays core ready (min segmentLimit allowance) state
  have split := core.runSlice_add direct.2 (allowance - direct.2) state
  rw [show direct.2 + (allowance - direct.2) = allowance by omega, replay] at split
  exact split.symm

theorem joined_split (core : MachineCore Term) (ready : core.State → Bool)
    (segmentLimit first later : Nat) (state : core.State) :
    joined core ready segmentLimit (first + later) state =
      let earlier := joined core ready segmentLimit first state
      let suffix := joined core ready segmentLimit later earlier.1
      (suffix.1, earlier.2 + suffix.2) := by
  simp only [joined_exact]
  exact core.runSlice_add first later state

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

/-- The guarded prefix/suffix composition joins the existing source-price
and contextual execution refinement, including pending workers and frames. -/
theorem contextual_slice_refines
    (sem : SourceWordAdmission.Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum segmentLimit allowance : Nat) (physicalLimit : Option Nat)
    (schedule : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker →
      RetainedContext Goal × SourceStepSelection.Snapshot)
    (tableEntries : SourceWordAdmission.Kernel Value Call Effect Fault Delay Suspension Context World Worker → Nat)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    let result := joined (nativeCore sem maximum physicalLimit schedule)
      (fun current => admitted (schedule current.meter.state).1 (tableEntries current.meter.state))
      segmentLimit allowance state
    (ContextualSourceAdmission.decode physicalLimit result.1, result.2) =
      (referenceCore sem schedule).runSlice allowance
        (ContextualSourceAdmission.decode physicalLimit state) := by
  dsimp only
  rw [joined_exact]
  exact slice_refines sem maximum allowance physicalLimit schedule state inRange

namespace Controls

theorem retained_owner_refuses : admitted (⟨true, [], [], 0⟩ : RetainedContext Nat) 0 = false := by
  decide

theorem dormant_watch_refuses : admitted (⟨false, [7], [], 0⟩ : RetainedContext Nat) 0 = false := by
  decide

theorem queued_wake_refuses : admitted (⟨false, [], [7], 0⟩ : RetainedContext Nat) 0 = false := by
  decide

theorem consumed_queue_readmits : admitted (⟨false, [], [7], 1⟩ : RetainedContext Nat) 0 = true := by
  decide

theorem table_work_refuses : admitted (⟨false, [], [], 0⟩ : RetainedContext Nat) 1 = false := by
  decide

open ConstraintPropagation

def emptyService : Service Nat Nat Nat := ⟨⟨fun _ => none, fun _ => [], []⟩, []⟩

def boundTrigger : Service Nat Nat Nat := (emptyService.suspend 0 1).bind 0 7

def condition (service : Service Nat Nat Nat) : Bool :=
  service.state.value 1 == some 1

/-- Consume the oldest wake before the condition, retaining the remaining
queue and the binding service's ordinary chronological updates. -/
def afterWake (service : Service Nat Nat Nat) : Service Nat Nat Nat :=
  match service.state.woken with
  | [] => service
  | goal :: later => (service.setWoken later).bind goal 1

theorem binding_posts_real_wake : boundTrigger.state.woken = [1] := by
  decide

theorem skipped_wake_changes_condition :
    condition boundTrigger = false ∧ condition (afterWake boundTrigger) = true := by
  decide

/-- Keeping only the first readiness observation is invalid when a word
creates retained work. The next iteration must inspect the updated state. -/
abbrev controlCore : MachineCore Nat where
  State := Nat
  load := id
  step := fun state => some (state + 1)

theorem changed_context_stops_direct_prefix :
    runPrefix controlCore (fun state => state < 1) 16 0 = (1, 1) ∧
      controlCore.runSlice 16 0 = (16, 16) := by
  decide

theorem refused_context_still_continues_ordinary :
    joined controlCore (fun state => state < 1) 16 3 0 = (3, 3) := by
  decide

end Controls
end Mettapedia.Machines.SourceResumeBoundary
