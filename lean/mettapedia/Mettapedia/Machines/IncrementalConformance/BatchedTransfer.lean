import Mettapedia.Machines.IncrementalConformance.TransferAccounting

/-!
# Bounded conversion scratch for ordered batched transfer

This module reuses `TransferAccounting.ChunkReceiver`: the receiver owns the
records copied by its synchronous `chunkStep`. A pending reverse list represents
the conversion region. A row is converted and charged before the threshold is
checked; a completed callback then releases the whole pending region.

The batched runner and an all-at-once runner have different allocation schedules
but the same ordered owned observation and visit count. The actual peak counter
includes the row crossing the threshold. The bound is threshold plus maximum
single-row charge, independent of the total input size.

The byte charge must include all storage allocated in this conversion region,
including row metadata and padding. This does not bound the persistent receiver,
its indexes, the SWI loader, callback scratch, allocator fragmentation or RSS.
Synchronous ownership transfer is represented by the existing copying receiver;
a native callback must finish owning its accepted copies before region reset.
A count threshold is not a byte threshold; its native resource refinement needs
an additional row-size bound or a byte-based flush trigger.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.BatchedTransfer

open TransferAccounting

variable {Record : Type*}

structure State (Record : Type*) where
  receiver : ChunkReceiver Record
  pending : List Record
  scratch : Nat
  peak : Nat
  deriving DecidableEq, Repr

def start (receiver : ChunkReceiver Record) : State Record :=
  ⟨receiver, [], 0, 0⟩

/-- The ownership transition copies the pending ordered chunk before resetting
scratch. Empty chunks are handled by the established receiver convention. -/
def flush (state : State Record) : State Record :=
  { state with
    receiver := chunkStep state.receiver state.pending.reverse
    pending := []
    scratch := 0 }

/-- Count the converted crossing row before deciding to flush. -/
def allocate (bytes : Record → Nat) (state : State Record) (row : Record) : State Record :=
  let charged := state.scratch + bytes row
  { state with
    pending := row :: state.pending
    scratch := charged
    peak := max state.peak charged }

def step (bytes : Record → Nat) (threshold : Nat) (state : State Record)
    (row : Record) : State Record :=
  let added := allocate bytes state row
  if threshold ≤ added.scratch then flush added else added

def run (bytes : Record → Nat) (threshold : Nat) : State Record → List Record → State Record
  | state, [] => state
  | state, row :: rest => run bytes threshold (step bytes threshold state row) rest

/-- The reference retains all converted rows until one final receiver callback. -/
def bulkRun (bytes : Record → Nat) : State Record → List Record → State Record
  | state, [] => state
  | state, row :: rest => bulkRun bytes (allocate bytes state row) rest

def observation (state : State Record) : List Record :=
  chunkObservation state.receiver ++ state.pending.reverse

def visits (state : State Record) : Nat :=
  state.receiver.visits + state.pending.length

def regionBytes (bytes : Record → Nat) (rows : List Record) : Nat :=
  (rows.map bytes).sum

/-- The counter is derived from the pending converted rows. -/
def Charged (bytes : Record → Nat) (state : State Record) : Prop :=
  state.scratch = regionBytes bytes state.pending

/-- A zero threshold has no settled debt; a positive threshold has strictly
less than one threshold of settled conversion scratch. -/
def Below (threshold : Nat) (state : State Record) : Prop :=
  if threshold = 0 then state.scratch = 0 else state.scratch < threshold

@[simp] theorem start_observation (receiver : ChunkReceiver Record) :
    observation (start receiver) = chunkObservation receiver := by simp [observation, start]

@[simp] theorem flush_observation (state : State Record) :
    observation (flush state) = observation state := by
  simp [observation, flush, chunkStep_observation]

@[simp] theorem allocate_observation (bytes : Record → Nat) (state : State Record)
    (row : Record) :
    observation (allocate bytes state row) = observation state ++ [row] := by
  simp [observation, allocate, List.append_assoc]

@[simp] theorem step_observation (bytes : Record → Nat) (threshold : Nat)
    (state : State Record) (row : Record) :
    observation (step bytes threshold state row) = observation state ++ [row] := by
  simp only [step]
  split_ifs <;> simp

@[simp] theorem flush_visits (state : State Record) :
    visits (flush state) = visits state := by
  simp [visits, flush, chunkStep_visits]

@[simp] theorem allocate_visits (bytes : Record → Nat) (state : State Record)
    (row : Record) : visits (allocate bytes state row) = visits state + 1 := by
  simp [visits, allocate, Nat.add_assoc]

@[simp] theorem step_visits (bytes : Record → Nat) (threshold : Nat)
    (state : State Record) (row : Record) :
    visits (step bytes threshold state row) = visits state + 1 := by
  simp only [step]
  split_ifs <;> simp

/-- Observation agreement is proved for every processed prefix, including a
partly filled conversion region. -/
theorem run_observation (bytes : Record → Nat) (threshold : Nat)
    (state : State Record) (rows : List Record) :
    observation (run bytes threshold state rows) = observation state ++ rows := by
  induction rows generalizing state with
  | nil => simp [run]
  | cons row rest ih => simp [run, ih, List.append_assoc]

theorem bulkRun_observation (bytes : Record → Nat) (state : State Record)
    (rows : List Record) :
    observation (bulkRun bytes state rows) = observation state ++ rows := by
  induction rows generalizing state with
  | nil => simp [bulkRun]
  | cons row rest ih => simp [bulkRun, ih, List.append_assoc]

theorem run_visits (bytes : Record → Nat) (threshold : Nat)
    (state : State Record) (rows : List Record) :
    visits (run bytes threshold state rows) = visits state + rows.length := by
  induction rows generalizing state with
  | nil => simp [run]
  | cons row rest ih => simp [run, ih, Nat.add_assoc, Nat.add_comm]

theorem bulkRun_visits (bytes : Record → Nat) (state : State Record)
    (rows : List Record) :
    visits (bulkRun bytes state rows) = visits state + rows.length := by
  induction rows generalizing state with
  | nil => simp [bulkRun]
  | cons row rest ih => simp [bulkRun, ih, Nat.add_assoc, Nat.add_comm]

/-- Completed receivers agree exactly, including duplicates and ordering.
Allocation schedules differ and are not identified by this observation. -/
theorem batched_equals_bulk (bytes : Record → Nat) (threshold : Nat)
    (receiver : ChunkReceiver Record) (rows : List Record) :
    chunkObservation (flush (run bytes threshold (start receiver) rows)).receiver =
      chunkObservation (flush (bulkRun bytes (start receiver) rows)).receiver ∧
    (flush (run bytes threshold (start receiver) rows)).receiver.visits =
      (flush (bulkRun bytes (start receiver) rows)).receiver.visits := by
  have leftObs := run_observation bytes threshold (start receiver) rows
  have rightObs := bulkRun_observation bytes (start receiver) rows
  have leftWork := run_visits bytes threshold (start receiver) rows
  have rightWork := bulkRun_visits bytes (start receiver) rows
  constructor
  · simpa [observation, flush, chunkStep_observation] using leftObs.trans rightObs.symm
  · simpa [visits, flush, chunkStep_visits] using leftWork.trans rightWork.symm

@[simp] theorem start_charged (bytes : Record → Nat) (receiver : ChunkReceiver Record) :
    Charged bytes (start receiver) := by simp [Charged, start, regionBytes]

@[simp] theorem flush_charged (bytes : Record → Nat) (state : State Record) :
    Charged bytes (flush state) := by simp [Charged, flush, regionBytes]

theorem allocate_charged (bytes : Record → Nat) {state : State Record}
    (charged : Charged bytes state) (row : Record) :
    Charged bytes (allocate bytes state row) := by
  simp only [Charged, allocate, regionBytes, List.map_cons, List.sum_cons] at *
  omega

theorem step_charged (bytes : Record → Nat) (threshold : Nat)
    {state : State Record} (charged : Charged bytes state) (row : Record) :
    Charged bytes (step bytes threshold state row) := by
  simp only [step]
  split_ifs
  · exact flush_charged _ _
  · exact allocate_charged bytes charged row

@[simp] theorem start_below (threshold : Nat) (receiver : ChunkReceiver Record) :
    Below threshold (start receiver) := by
  unfold Below
  split_ifs
  · rfl
  · change 0 < threshold
    omega

@[simp] theorem flush_below (threshold : Nat) (state : State Record) :
    Below threshold (flush state) := by
  unfold Below
  split_ifs
  · rfl
  · change 0 < threshold
    omega

theorem step_below (bytes : Record → Nat) (threshold : Nat)
    (state : State Record) (row : Record) :
    Below threshold (step bytes threshold state row) := by
  simp only [step]
  split_ifs with reached
  · exact flush_below _ _
  · have positive : threshold ≠ 0 := by
      intro zero
      subst threshold
      simp at reached
    simp only [Below, if_neg positive]
    omega

/-- Includes the temporary allocation before the callback resets the region.
The result is derived from the threshold test and the one-row byte bound. -/
theorem allocate_peak_bound (bytes : Record → Nat) (threshold maxRow : Nat)
    {state : State Record} (below : Below threshold state)
    (peak : state.peak ≤ threshold + maxRow) (row : Record)
    (rowBound : bytes row ≤ maxRow) :
    (allocate bytes state row).peak ≤ threshold + maxRow := by
  unfold Below at below
  have scratch : state.scratch ≤ threshold := by split_ifs at below <;> omega
  simp only [allocate, max_le_iff]
  constructor
  · exact peak
  · omega

theorem step_peak_bound (bytes : Record → Nat) (threshold maxRow : Nat)
    {state : State Record} (below : Below threshold state)
    (peak : state.peak ≤ threshold + maxRow) (row : Record)
    (rowBound : bytes row ≤ maxRow) :
    (step bytes threshold state row).peak ≤ threshold + maxRow := by
  simp only [step]
  split_ifs
  · exact allocate_peak_bound bytes threshold maxRow below peak row rowBound
  · exact allocate_peak_bound bytes threshold maxRow below peak row rowBound

/-- The bound holds for every finite prefix regardless of total input size. -/
theorem run_peak_bound (bytes : Record → Nat) (threshold maxRow : Nat)
    {state : State Record} (below : Below threshold state)
    (peak : state.peak ≤ threshold + maxRow) (rows : List Record)
    (rowBounds : ∀ row ∈ rows, bytes row ≤ maxRow) :
    (run bytes threshold state rows).peak ≤ threshold + maxRow := by
  induction rows generalizing state with
  | nil => exact peak
  | cons row rest ih =>
      apply ih (step_below bytes threshold state row)
      · exact step_peak_bound bytes threshold maxRow below peak row (rowBounds row (by simp))
      · intro other member
        exact rowBounds other (by simp [member])

/-- Finished batch conversion retains no scratch. Its owned receiver can still
be large; that storage is deliberately not charged as conversion scratch. -/
theorem finished_scratch_bound (bytes : Record → Nat) (threshold maxRow : Nat)
    (receiver : ChunkReceiver Record) (rows : List Record)
    (rowBounds : ∀ row ∈ rows, bytes row ≤ maxRow) :
    (flush (run bytes threshold (start receiver) rows)).scratch = 0 ∧
      (flush (run bytes threshold (start receiver) rows)).peak ≤ threshold + maxRow := by
  exact ⟨rfl, run_peak_bound bytes threshold maxRow (start_below _ _) (by simp [start])
    rows rowBounds⟩

/-- The bulk conversion region keeps the sum of all row charges until its
single callback. This is independent of the batched peak invariant. -/
theorem bulkRun_scratch (bytes : Record → Nat) (state : State Record) (rows : List Record) :
    (bulkRun bytes state rows).scratch = state.scratch + regionBytes bytes rows := by
  induction rows generalizing state with
  | nil => simp [bulkRun, regionBytes]
  | cons row rest ih => simp [bulkRun, ih, allocate, regionBytes, Nat.add_assoc]

theorem bulkRun_peak (bytes : Record → Nat) (state : State Record)
    (scratchBelowPeak : state.scratch ≤ state.peak) (rows : List Record) :
    (bulkRun bytes state rows).peak = max state.peak (state.scratch + regionBytes bytes rows) := by
  induction rows generalizing state with
  | nil =>
      simpa only [bulkRun, regionBytes, List.map_nil, List.sum_nil, Nat.add_zero]
        using (max_eq_left scratchBelowPeak).symm
  | cons row rest ih =>
      rw [bulkRun, ih (allocate bytes state row) (Nat.le_max_right _ _)]
      simp only [allocate, regionBytes, List.map_cons, List.sum_cons, Nat.add_assoc]
      rw [max_assoc]
      have bound : state.scratch + bytes row ≤
          state.scratch + (bytes row + (rest.map bytes).sum) := by omega
      rw [max_eq_right bound]

/-- Independent reference peak: all rows remain converted until the callback. -/
theorem bulk_peak_exact (bytes : Record → Nat) (receiver : ChunkReceiver Record)
    (rows : List Record) :
    (flush (bulkRun bytes (start receiver) rows)).peak = regionBytes bytes rows := by
  rw [show (flush (bulkRun bytes (start receiver) rows)).peak =
      (bulkRun bytes (start receiver) rows).peak from rfl]
  rw [bulkRun_peak bytes (start receiver) (by simp [start]) rows]
  simp [start]

/-- A count cap may force an earlier synchronous ownership transfer. It does
not replace the byte trigger and cannot increase conversion scratch. -/
def cappedStep (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (row : Record) : State Record :=
  let settled := step bytes threshold state row
  if cap ≤ settled.pending.length then flush settled else settled

def cappedRun (bytes : Record → Nat) (threshold cap : Nat) :
    State Record → List Record → State Record
  | state, [] => state
  | state, row :: rest => cappedRun bytes threshold cap
      (cappedStep bytes threshold cap state row) rest

@[simp] theorem cappedStep_observation (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (row : Record) :
    observation (cappedStep bytes threshold cap state row) = observation state ++ [row] := by
  simp only [cappedStep]
  split_ifs <;> simp

@[simp] theorem cappedStep_visits (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (row : Record) :
    visits (cappedStep bytes threshold cap state row) = visits state + 1 := by
  simp only [cappedStep]
  split_ifs <;> simp

@[simp] theorem cappedStep_peak (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (row : Record) :
    (cappedStep bytes threshold cap state row).peak = (step bytes threshold state row).peak := by
  simp only [cappedStep]
  split_ifs <;> rfl

theorem cappedStep_below (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (row : Record) :
    Below threshold (cappedStep bytes threshold cap state row) := by
  simp only [cappedStep]
  split_ifs
  · exact flush_below _ _
  · exact step_below _ _ _ _

theorem cappedRun_observation (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (rows : List Record) :
    observation (cappedRun bytes threshold cap state rows) = observation state ++ rows := by
  induction rows generalizing state with
  | nil => simp [cappedRun]
  | cons row rest ih => simp [cappedRun, ih, List.append_assoc]

theorem cappedRun_visits (bytes : Record → Nat) (threshold cap : Nat)
    (state : State Record) (rows : List Record) :
    visits (cappedRun bytes threshold cap state rows) = visits state + rows.length := by
  induction rows generalizing state with
  | nil => simp [cappedRun]
  | cons row rest ih => simp [cappedRun, ih, Nat.add_assoc, Nat.add_comm]

/-- Earlier count-triggered callbacks preserve the byte peak invariant. -/
theorem cappedRun_peak_bound (bytes : Record → Nat) (threshold cap maxRow : Nat)
    {state : State Record} (below : Below threshold state)
    (peak : state.peak ≤ threshold + maxRow) (rows : List Record)
    (rowBounds : ∀ row ∈ rows, bytes row ≤ maxRow) :
    (cappedRun bytes threshold cap state rows).peak ≤ threshold + maxRow := by
  induction rows generalizing state with
  | nil => exact peak
  | cons row rest ih =>
      apply ih (cappedStep_below bytes threshold cap state row)
      · rw [cappedStep_peak]
        exact step_peak_bound bytes threshold maxRow below peak row (rowBounds row (by simp))
      · intro other member
        exact rowBounds other (by simp [member])

theorem cappedStep_charged (bytes : Record → Nat) (threshold cap : Nat)
    {state : State Record} (charged : Charged bytes state) (row : Record) :
    Charged bytes (cappedStep bytes threshold cap state row) := by
  simp only [cappedStep]
  split_ifs
  · exact flush_charged _ _
  · exact step_charged _ _ charged _

/-- Byte accounting remains tied to the pending row charges through arbitrary
count/byte-triggered flushes, not just to an isolated peak-counter inequality. -/
theorem cappedRun_charged (bytes : Record → Nat) (threshold cap : Nat)
    {state : State Record} (charged : Charged bytes state) (rows : List Record) :
    Charged bytes (cappedRun bytes threshold cap state rows) := by
  induction rows generalizing state with
  | nil => exact charged
  | cons row rest ih => exact ih (cappedStep_charged bytes threshold cap charged row)

/-- The count cap separately bounds outstanding converted row metadata. -/
theorem cappedStep_pending_lt (bytes : Record → Nat) (threshold cap : Nat)
    (positive : 0 < cap) (state : State Record) (row : Record) :
    (cappedStep bytes threshold cap state row).pending.length < cap := by
  simp only [cappedStep]
  split_ifs with full
  · simpa [flush] using positive
  · omega

theorem cappedRun_pending_lt (bytes : Record → Nat) (threshold cap : Nat)
    (positive : 0 < cap) {state : State Record} (below : state.pending.length < cap)
    (rows : List Record) :
    (cappedRun bytes threshold cap state rows).pending.length < cap := by
  induction rows generalizing state with
  | nil => exact below
  | cons row rest ih => exact ih (cappedStep_pending_lt bytes threshold cap positive state row)

/-- The crossing row fits in the next count slot before the callback. -/
theorem crossing_count_le (bytes : Record → Nat) (cap : Nat)
    (state : State Record) (row : Record) (below : state.pending.length < cap) :
    (allocate bytes state row).pending.length ≤ cap := by
  simp only [allocate, List.length_cons]
  omega

/-- Both successful import schedules preserve the same copied occurrences;
count and byte triggers affect only callback boundaries and scratch retention. -/
theorem capped_equals_bulk (bytes : Record → Nat) (threshold cap : Nat)
    (receiver : ChunkReceiver Record) (rows : List Record) :
    chunkObservation (flush (cappedRun bytes threshold cap (start receiver) rows)).receiver =
      chunkObservation (flush (bulkRun bytes (start receiver) rows)).receiver ∧
    (flush (cappedRun bytes threshold cap (start receiver) rows)).receiver.visits =
      (flush (bulkRun bytes (start receiver) rows)).receiver.visits := by
  have leftObs := cappedRun_observation bytes threshold cap (start receiver) rows
  have rightObs := bulkRun_observation bytes (start receiver) rows
  have leftWork := cappedRun_visits bytes threshold cap (start receiver) rows
  have rightWork := bulkRun_visits bytes (start receiver) rows
  constructor
  · simpa [observation, flush, chunkStep_observation] using leftObs.trans rightObs.symm
  · simpa [visits, flush, chunkStep_visits] using leftWork.trans rightWork.symm

def maxRowCharge (bytes : Record → Nat) : List Record → Nat
  | [] => 0
  | row :: rest => max (bytes row) (maxRowCharge bytes rest)

theorem rowCharge_le_max (bytes : Record → Nat) (row : Record) (rows : List Record)
    (member : row ∈ rows) : bytes row ≤ maxRowCharge bytes rows := by
  induction rows with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst row
        exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

/-- The threshold-plus-one-row bound uses the actual largest row in the input;
no caller-supplied bound on the desired peak is required. -/
theorem completed_peak_le_threshold_plus_maxRow (bytes : Record → Nat)
    (threshold cap : Nat) (receiver : ChunkReceiver Record) (rows : List Record) :
    (flush (cappedRun bytes threshold cap (start receiver) rows)).peak ≤
      threshold + maxRowCharge bytes rows := by
  exact cappedRun_peak_bound bytes threshold cap (maxRowCharge bytes rows)
    (start_below _ _) (by simp [start]) rows (fun row member => rowCharge_le_max bytes row rows member)

namespace Controls

def byteSize (row : Nat) : Nat := row

theorem duplicates_and_order_survive_region_resets :
    chunkObservation (flush (run byteSize 10 (start ⟨[], 0⟩) [7, 7, 2, 9])).receiver =
      [7, 7, 2, 9] ∧
      (flush (run byteSize 10 (start ⟨[], 0⟩) [7, 7, 2, 9])).receiver.visits = 4 := by decide

theorem crossing_row_is_in_the_peak :
    (flush (run byteSize 10 (start ⟨[], 0⟩) [9, 9])).scratch = 0 ∧
      (flush (run byteSize 10 (start ⟨[], 0⟩) [9, 9])).peak = 18 ∧
      10 < (flush (run byteSize 10 (start ⟨[], 0⟩) [9, 9])).peak := by decide

theorem one_oversized_row_remains_visible :
    (flush (run byteSize 10 (start ⟨[], 0⟩) [100])).peak = 100 ∧
      chunkObservation (flush (run byteSize 10 (start ⟨[], 0⟩) [100])).receiver = [100] := by decide

theorem allocation_schedules_have_different_peaks :
    (flush (run byteSize 10 (start ⟨[], 0⟩) [6, 6, 6, 6, 6])).peak = 12 ∧
      (flush (bulkRun byteSize (start ⟨[], 0⟩) [6, 6, 6, 6, 6])).peak = 30 := by decide

/-- Resetting before the ownership transfer discards pending records. -/
theorem premature_region_reset_loses_rows :
    let staged := allocate byteSize (start (⟨[], 0⟩ : ChunkReceiver Nat)) 7
    observation { staged with pending := [], scratch := 0 } ≠ observation (flush staged) := by decide

/-- A row-count trigger without a size bound cannot give a fixed byte limit. -/
theorem a_single_row_has_unbounded_byte_charge (claimed : Nat) :
    claimed < (allocate byteSize (start (⟨[], 0⟩ : ChunkReceiver Nat)) (claimed + 1)).peak := by
  simp [allocate, start, byteSize]

/-- Zero-sized payloads still hit the independent row cap; native charges must
also include any conversion-region headers to use the byte theorem faithfully. -/
theorem count_cap_prevents_unbounded_pending_metadata :
    (cappedRun (fun _ : Nat => 0) 10 2 (start ⟨[], 0⟩) [7, 7, 7, 7, 7]).pending = [7] ∧
      observation (cappedRun (fun _ : Nat => 0) 10 2 (start ⟨[], 0⟩) [7, 7, 7, 7, 7]) =
        [7, 7, 7, 7, 7] := by decide

end Controls
end Mettapedia.Machines.IncrementalConformance.BatchedTransfer
