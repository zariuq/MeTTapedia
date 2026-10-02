import Mathlib.Data.List.Flatten
import Mathlib.Tactic

/-!
# Repeated snapshots versus incremental transfer

Two executable transports maintain an append-only ordered sequence of records.
The snapshot transport copies the entire updated sequence on every request;
the delta transport copies only the new records, then appends them at the
receiver. Every intermediate receiver state agrees, including duplicates.

Counters are incremented by the recursive record-copy loop. They do not count
solver propagation, list-append implementation, indexing, allocation, payload
serialization, or branch snapshots. This is a transport component, not a
permission to replay arbitrary attributed-variable hooks or effectful goals.
The caller must establish that a logical record is an admissible incremental
update and that its receiving state remains alive and correctly owned.

For singleton updates the snapshot loop copies a triangular number of records;
the delta loop copies one per update. This isolates the avoidable transport
term without claiming linear complexity for constraint solving.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.TransferAccounting

variable {Record : Type*}

/-- One counted visit and output cell for each copied record. -/
def transfer : List Record → List Record × Nat
  | [] => ([], 0)
  | x :: xs =>
      let tail := transfer xs
      (x :: tail.1, tail.2 + 1)

@[simp] theorem transfer_records (xs : List Record) : (transfer xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [transfer, ih]

@[simp] theorem transfer_visits (xs : List Record) : (transfer xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [transfer, ih]

structure Receiver (Record : Type*) where
  records : List Record
  visits : Nat
  deriving DecidableEq, Repr

def snapshotStep (s : Receiver Record) (new : List Record) : Receiver Record :=
  let copied := transfer (s.records ++ new)
  ⟨copied.1, s.visits + copied.2⟩

def deltaStep (s : Receiver Record) (new : List Record) : Receiver Record :=
  let copied := transfer new
  ⟨s.records ++ copied.1, s.visits + copied.2⟩

def run (step : Receiver Record → List Record → Receiver Record) :
    Receiver Record → List (List Record) → Receiver Record
  | s, [] => s
  | s, chunk :: chunks => run step (step s chunk) chunks

@[simp] theorem snapshotStep_records (s : Receiver Record) (new : List Record) :
    (snapshotStep s new).records = s.records ++ new := by
  simp [snapshotStep]

@[simp] theorem deltaStep_records (s : Receiver Record) (new : List Record) :
    (deltaStep s new).records = s.records ++ new := by
  simp [deltaStep]

theorem snapshot_records (s : Receiver Record) (chunks : List (List Record)) :
    (run snapshotStep s chunks).records = s.records ++ chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp [run]
  | cons chunk chunks ih => simp [run, ih, List.append_assoc]

theorem delta_records (s : Receiver Record) (chunks : List (List Record)) :
    (run deltaStep s chunks).records = s.records ++ chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp [run]
  | cons chunk chunks ih => simp [run, ih, List.append_assoc]

/-- Equality is of ordered records, stronger than bag equality; multiplicity
is retained. Taking a prefix proves agreement at every request boundary. -/
theorem receivers_agree (s : Receiver Record) (chunks : List (List Record)) :
    (run snapshotStep s chunks).records = (run deltaStep s chunks).records := by
  rw [snapshot_records, delta_records]

theorem every_prefix_agrees (s : Receiver Record) (chunks : List (List Record))
    (n : Nat) :
    (run snapshotStep s (chunks.take n)).records =
      (run deltaStep s (chunks.take n)).records := receivers_agree _ _

/-- Independent arithmetic accounting of complete prefix sizes. -/
def prefixVolume : Nat → List (List Record) → Nat
  | _, [] => 0
  | resident, chunk :: chunks =>
      resident + chunk.length + prefixVolume (resident + chunk.length) chunks

/-- Old records retransmitted on successive requests. -/
def repeatedVolume : Nat → List (List Record) → Nat
  | _, [] => 0
  | resident, chunk :: chunks =>
      resident + repeatedVolume (resident + chunk.length) chunks

theorem snapshot_visits (s : Receiver Record) (chunks : List (List Record)) :
    (run snapshotStep s chunks).visits = s.visits + prefixVolume s.records.length chunks := by
  induction chunks generalizing s with
  | nil => simp [run, prefixVolume]
  | cons chunk chunks ih =>
      simp [run, ih, snapshotStep, prefixVolume, Nat.add_assoc]

theorem delta_visits (s : Receiver Record) (chunks : List (List Record)) :
    (run deltaStep s chunks).visits = s.visits + chunks.flatten.length := by
  induction chunks generalizing s with
  | nil => simp [run]
  | cons chunk chunks ih => simp [run, ih, deltaStep, Nat.add_assoc]

theorem prefixVolume_decomposition (resident : Nat) (chunks : List (List Record)) :
    prefixVolume resident chunks = chunks.flatten.length + repeatedVolume resident chunks := by
  induction chunks generalizing resident with
  | nil => simp [prefixVolume, repeatedVolume]
  | cons chunk chunks ih =>
      simp only [prefixVolume, repeatedVolume, List.flatten_cons, List.length_append, ih]
      omega

/-- The saving is precisely the repeated old-record visits in this meter. -/
theorem exact_transport_saving (s : Receiver Record) (chunks : List (List Record)) :
    (run snapshotStep s chunks).visits =
      (run deltaStep s chunks).visits + repeatedVolume s.records.length chunks := by
  rw [snapshot_visits, delta_visits, prefixVolume_decomposition]
  omega

theorem delta_no_more_visits (s : Receiver Record) (chunks : List (List Record)) :
    (run deltaStep s chunks).visits ≤ (run snapshotStep s chunks).visits := by
  rw [exact_transport_saving]
  omega

def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + n + 1

theorem twice_triangular (n : Nat) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => simp [triangular]
  | succ n ih => simp only [triangular]; nlinarith

theorem singleton_prefixVolume (resident : Nat) (records : List Record) :
    prefixVolume resident (records.map (fun x => [x])) =
      records.length * resident + triangular records.length := by
  induction records generalizing resident with
  | nil => simp [prefixVolume, triangular]
  | cons x xs ih =>
      simp only [List.map_cons, prefixVolume, List.length_cons,
        List.length_nil, ih, triangular]
      ring

theorem flatten_singletons (records : List Record) :
    (records.map (fun x => [x])).flatten = records := by
  induction records with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem singleton_delta_visits (records : List Record) :
    (run deltaStep ⟨[], 0⟩ (records.map (fun x => [x]))).visits = records.length := by
  rw [delta_visits, flatten_singletons]
  exact Nat.zero_add _

theorem singleton_snapshot_visits (records : List Record) :
    2 * (run snapshotStep ⟨[], 0⟩ (records.map (fun x => [x]))).visits =
      records.length * (records.length + 1) := by
  rw [snapshot_visits, singleton_prefixVolume]
  simpa using twice_triangular records.length

/-! ## A receiver that does not append by traversing the old record list

The flat receiver above specifies the update observation. This representation
keeps reverse-ordered chunks, so each nonempty update adds just one chunk header
besides its transferred records. Flattening is an explicit observation, not an
operation performed by `chunkStep`. Repeated full observations still cost work.
-/

structure ChunkReceiver (Record : Type*) where
  chunks : List (List Record)
  visits : Nat
  deriving DecidableEq, Repr

def chunkObservation (s : ChunkReceiver Record) : List Record :=
  s.chunks.reverse.flatten

def chunkStep (s : ChunkReceiver Record) (new : List Record) : ChunkReceiver Record :=
  match new with
  | [] => s
  | x :: xs =>
      let copied := transfer (x :: xs)
      ⟨copied.1 :: s.chunks, s.visits + copied.2⟩

theorem chunkStep_observation (s : ChunkReceiver Record) (new : List Record) :
    chunkObservation (chunkStep s new) = chunkObservation s ++ new := by
  cases new with
  | nil => simp [chunkStep]
  | cons x xs => simp [chunkStep, chunkObservation]

theorem chunkStep_visits (s : ChunkReceiver Record) (new : List Record) :
    (chunkStep s new).visits = s.visits + new.length := by
  cases new with
  | nil => simp [chunkStep]
  | cons x xs => simp [chunkStep]

/-- Empty requests retain no new chunk header. -/
theorem chunkStep_headers (s : ChunkReceiver Record) (new : List Record) :
    (chunkStep s new).chunks.length = s.chunks.length + if new.isEmpty then 0 else 1 := by
  cases new <;> simp [chunkStep]

def chunkRun : ChunkReceiver Record → List (List Record) → ChunkReceiver Record
  | s, [] => s
  | s, chunk :: chunks => chunkRun (chunkStep s chunk) chunks

theorem chunkRun_observation (s : ChunkReceiver Record) (chunks : List (List Record)) :
    chunkObservation (chunkRun s chunks) = chunkObservation s ++ chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp [chunkRun]
  | cons chunk chunks ih =>
      simp [chunkRun, ih, chunkStep_observation, List.append_assoc]

theorem chunkRun_visits (s : ChunkReceiver Record) (chunks : List (List Record)) :
    (chunkRun s chunks).visits = s.visits + chunks.flatten.length := by
  induction chunks generalizing s with
  | nil => simp [chunkRun]
  | cons chunk chunks ih => simp [chunkRun, ih, chunkStep_visits, Nat.add_assoc]

/-- Representation correspondence is proved for all batches, not by making
the chunk receiver a synonym for the flat receiver. -/
theorem chunkRun_realizes_delta (s : Receiver Record) (chunks : List (List Record)) :
    chunkObservation (chunkRun ⟨[s.records], s.visits⟩ chunks) =
      (run deltaStep s chunks).records ∧
    (chunkRun ⟨[s.records], s.visits⟩ chunks).visits =
      (run deltaStep s chunks).visits := by
  rw [chunkRun_observation, delta_records, chunkRun_visits, delta_visits]
  simp [chunkObservation]

namespace Controls

theorem duplicate_records_survive :
    (run deltaStep ⟨[], 0⟩ ([[7], [7]] : List (List Nat))).records = [7, 7] := by
  decide

theorem three_updates_transfer_six_or_three :
    (run snapshotStep ⟨[], 0⟩ ([[1], [2], [3]] : List (List Nat))).visits = 6 ∧
    (run deltaStep ⟨[], 0⟩ ([[1], [2], [3]] : List (List Nat))).visits = 3 := by
  decide

/-- Dropping the receiver between requests destroys the incremental invariant. -/
theorem reset_receiver_loses_prior_records :
    (deltaStep (deltaStep ⟨[], 0⟩ [1]) [2]).records ≠
      (deltaStep ⟨[], 0⟩ ([2] : List Nat)).records := by
  decide

/-- Delta transfer needs an actual update algebra: deleting a record is not
implemented by appending the desired replacement snapshot. -/
theorem replacement_is_not_append :
    (snapshotStep ⟨[], 0⟩ ([2] : List Nat)).records ≠
      (deltaStep ⟨[1], 0⟩ [2]).records := by
  decide

theorem empty_delta_does_not_retain_headers :
    (chunkRun ⟨[], 0⟩ ([[], [], []] : List (List Nat))).chunks = [] := by
  decide

theorem chunks_preserve_order_and_duplicates :
    chunkObservation (chunkRun ⟨[], 0⟩ ([[7], [8, 7]] : List (List Nat))) = [7, 8, 7] := by
  decide

end Controls
end Mettapedia.Machines.IncrementalConformance.TransferAccounting
