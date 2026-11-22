import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Disposal through allocated chunk owners

The source scans a fixed directory and frees each occupied slot. The target
registers a newly allocated owner while installing its first directory slot,
then disposes through that ownership list. Chunk IDs represent allocations,
not source variable identities. Existing directory lookups are unchanged.

The invariant relates the complete occupied directory to a duplicate-free
owner list. Installation preserves it even at sparse indices. Checked release
rejects missing or repeated owners, so the refinement does not silently make
double release idempotent. The dense symbol directory separately uses the
exclusive published extent to include its last partial chunk.

The model assumes serialized installation and quiescent disposal, as required
by the native writer mutex and lifetime contract. C allocation layout, atomic
publication, absence of concurrent disposal and pointer validity retain their
native qualification obligations; this is not formal verification of C.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.InternChunkOwnership

abbrev Chunk := Nat

def occupied (directory : List (Option Chunk)) : List Chunk := directory.filterMap id

/-- A successful allocation may occupy only an empty slot. -/
def install : Nat → Chunk → List (Option Chunk) → Option (List (Option Chunk))
  | 0, chunk, none :: rest => some (some chunk :: rest)
  | index + 1, chunk, first :: rest =>
      (install index chunk rest).map (first :: ·)
  | _, _, _ => none

theorem install_length (index : Nat) (chunk : Chunk) (before after : List (Option Chunk))
    (made : install index chunk before = some after) : after.length = before.length := by
  induction before generalizing index after with
  | nil => simp [install] at made
  | cons first rest ih =>
      cases index with
      | zero =>
          cases first with
          | none =>
              have same : some chunk :: rest = after := by simpa [install] using made
              simpa using congrArg List.length same.symm
          | some old => simp [install] at made
      | succ index =>
          cases tail : install index chunk rest with
          | none => simp [install, tail] at made
          | some next =>
              have same : first :: next = after := by simpa [install, tail] using made
              subst after
              simpa using congrArg Nat.succ (ih index next tail)

theorem install_occupied (index : Nat) (chunk : Chunk) (before after : List (Option Chunk))
    (made : install index chunk before = some after) :
    (occupied after).Perm (chunk :: occupied before) := by
  induction before generalizing index after with
  | nil => simp [install] at made
  | cons first rest ih =>
      cases index with
      | zero =>
          cases first with
          | none =>
              have same : some chunk :: rest = after := by simpa [install] using made
              subst after
              exact List.Perm.refl _
          | some old => simp [install] at made
      | succ index =>
          cases tail : install index chunk rest with
          | none => simp [install, tail] at made
          | some next =>
              have same : first :: next = after := by simpa [install, tail] using made
              subst after
              cases first with
              | none => simpa [occupied] using ih index next tail
              | some old =>
                  exact (List.Perm.cons old (ih index next tail)).trans (List.Perm.swap _ _ _)

structure State where
  directory : List (Option Chunk)
  owners : List Chunk
  deriving DecidableEq

def State.Valid (state : State) : Prop :=
  state.owners.Nodup ∧ state.owners.Perm (occupied state.directory)

def initial (capacity : Nat) : State := ⟨List.replicate capacity none, []⟩

theorem initial_valid (capacity : Nat) : (initial capacity).Valid := by
  simp [initial, State.Valid, occupied]

/-- The owner is retained before the installed directory is published. -/
def register (state : State) (index : Nat) (chunk : Chunk) : Option State :=
  (install index chunk state.directory).map fun directory => ⟨directory, chunk :: state.owners⟩

theorem register_valid (before after : State) (index : Nat) (chunk : Chunk)
    (valid : before.Valid) (fresh : chunk ∉ before.owners)
    (made : register before index chunk = some after) : after.Valid := by
  unfold register at made
  obtain ⟨directory, installed, same⟩ := Option.map_eq_some_iff.mp made
  subst after
  refine ⟨List.nodup_cons.mpr ⟨fresh, valid.1⟩, ?_⟩
  exact (List.Perm.cons chunk valid.2).trans (install_occupied index chunk _ _ installed).symm

/-- Releasing a dead allocation is refused, including a repeated owner. -/
def release (live : Finset Chunk) : List Chunk → Option (Finset Chunk)
  | [] => some live
  | chunk :: later => if chunk ∈ live then release (live.erase chunk) later else none

/-- Independent reference: scan every directory slot, including empty ones. -/
def sweep (live : Finset Chunk) : List (Option Chunk) → Option (Finset Chunk)
  | [] => some live
  | none :: later => sweep live later
  | some chunk :: later =>
      if chunk ∈ live then sweep (live.erase chunk) later else none

theorem sweep_occupied (directory : List (Option Chunk)) (live : Finset Chunk) :
    sweep live directory = release live (occupied directory) := by
  induction directory generalizing live with
  | nil => rfl
  | cons first rest ih =>
      cases first <;> simp [sweep, occupied, release, ih]

theorem release_spec (owners : List Chunk) (unique : owners.Nodup) (live : Finset Chunk) :
    release live owners =
      if ∀ chunk ∈ owners, chunk ∈ live then some (live \ owners.toFinset) else none := by
  induction owners generalizing live with
  | nil => simp [release]
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp unique
      rw [release]
      by_cases alive : first ∈ live
      · rw [if_pos alive, ih distinct.2]
        have remaining : (∀ chunk ∈ rest, chunk ∈ live.erase first) ↔
            (∀ chunk ∈ rest, chunk ∈ live) := by
          constructor
          · intro all chunk present
            exact Finset.mem_of_mem_erase (all chunk present)
          · intro all chunk present
            exact Finset.mem_erase.mpr ⟨by intro same; subst chunk; exact distinct.1 present,
              all chunk present⟩
        have difference : live.erase first \ rest.toFinset = live \ (first :: rest).toFinset := by
          ext chunk
          simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert]
          tauto
        simp only [remaining, difference, List.mem_cons, forall_eq_or_imp, alive, true_and]
      · simp [alive]

theorem disposal_refines (state : State) (valid : state.Valid) (live : Finset Chunk) :
    release live state.owners = sweep live state.directory := by
  rw [sweep_occupied, release_spec _ valid.1, release_spec _ (valid.2.nodup_iff.mp valid.1)]
  have sets : state.owners.toFinset = (occupied state.directory).toFinset :=
    List.toFinset_eq_of_perm _ _ valid.2
  have same : (∀ chunk ∈ state.owners, chunk ∈ live) ↔
      (∀ chunk ∈ occupied state.directory, chunk ∈ live) := by
    constructor <;> intro all chunk present
    · exact all chunk ((valid.2.mem_iff).mpr present)
    · exact all chunk ((valid.2.mem_iff).mp present)
  simp only [same, sets]

theorem disposal_retires_all (state : State) (valid : state.Valid) :
    release state.owners.toFinset state.owners = some ∅ := by
  rw [release_spec _ valid.1]
  simp

theorem owner_count_bounded (state : State) (valid : state.Valid) :
    state.owners.length ≤ state.directory.length := by
  rw [valid.2.length_eq]
  exact List.length_filterMap_le _ _

/-! ## A used count does not identify the occupied slots -/

/-- The reader stops after finding the advertised number of owners. The
second component counts *slots inspected*, including empty slots. -/
def scanCounted : List (Option Chunk) → Nat → List Chunk × Nat
  | [], _ => ([], 0)
  | _ :: _, 0 => ([], 0)
  | none :: rest, remaining + 1 =>
      let next := scanCounted rest (remaining + 1)
      (next.1, next.2 + 1)
  | some chunk :: rest, remaining + 1 =>
      let next := scanCounted rest remaining
      (chunk :: next.1, next.2 + 1)

theorem scanCounted_complete (directory : List (Option Chunk)) (count : Nat)
    (enough : (occupied directory).length ≤ count) :
    (scanCounted directory count).1 = occupied directory := by
  induction directory generalizing count with
  | nil => rfl
  | cons slot rest ih =>
      cases count with
      | zero =>
          have empty : occupied (slot :: rest) = [] :=
            List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
          exact empty.symm
      | succ count =>
          cases slot with
          | none =>
              exact ih _ (by simpa [occupied] using enough)
          | some chunk =>
              have bound : (occupied rest).length ≤ count := by
                simpa [occupied, Nat.succ_le_succ_iff] using enough
              simp [scanCounted, occupied, ih _ bound]

theorem scanCounted_release_refines (directory : List (Option Chunk)) (live : Finset Chunk) :
    release live (scanCounted directory (occupied directory).length).1 =
      sweep live directory := by
  rw [scanCounted_complete directory _ le_rfl, sweep_occupied]

/-- Even with an exact used count of one, finding a last-slot owner takes
as many slot reads as a capacity scan. -/
theorem counted_scan_sparse_last (emptySlots : Nat) (owner : Chunk) :
    scanCounted (List.replicate emptySlots none ++ [some owner]) 1 =
      ([owner], emptySlots + 1) := by
  induction emptySlots with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, scanCounted, ih, Nat.add_assoc]

/-- With individual release as the primitive, a successful disposal must
issue one release per live owner. This does not assume a particular order,
nor apply to payloads that can be bulk-freed without individual release. -/
theorem complete_release_work (live : Finset Chunk) (owners : List Chunk)
    (done : release live owners = some ∅) : owners.length = live.card := by
  induction owners generalizing live with
  | nil =>
      have empty : live = ∅ := by simpa [release] using done
      simp [empty]
  | cons owner rest ih =>
      by_cases mem : owner ∈ live
      · have tail : release (live.erase owner) rest = some ∅ := by
          simpa [release, mem] using done
        have actual := ih _ tail
        rw [Finset.card_erase_of_mem mem] at actual
        simp only [List.length_cons]
        have positive : 0 < live.card := Finset.card_pos.mpr ⟨owner, mem⟩
        omega
      · simp [release, mem] at done

theorem registered_owners_attain_release_bound (state : State) (valid : state.Valid) :
    state.owners.length = state.owners.toFinset.card :=
  complete_release_work _ _ (disposal_retires_all state valid)

/-- Exclusive entry extent, including the reserved zero slot. -/
def denseChunks (extent : Nat) : Nat := if extent = 0 then 0 else (extent - 1) / 16384 + 1

theorem dense_chunk_coverage (extent chunk : Nat) :
    chunk < denseChunks extent ↔ chunk * 16384 < extent := by
  unfold denseChunks
  split <;> omega

theorem dense_chunks_in_word_range (extent : Nat) (bounded : extent < 2^32) :
    denseChunks extent ≤ 262144 := by
  unfold denseChunks
  split <;> omega

/-- A published exclusive extent cannot wrap when allocating a new symbol. -/
def nativeNext (extent : Nat) : Option Nat :=
  if extent = 4294967295 then none else some (extent + 1)

def referenceNext (extent : Nat) : Option Nat :=
  if extent + 1 < 2^32 then some (extent + 1) else none

theorem exclusive_extent_refines (extent : Nat) (bounded : extent < 2^32) :
    nativeNext extent = referenceNext extent := by
  by_cases last : extent = 4294967295
  · simp [nativeNext, referenceNext, last]
  · have room : extent + 1 < 2^32 := by omega
    unfold nativeNext referenceNext
    rw [if_neg last, if_pos room]

theorem published_extent_stays_bounded (extent next : Nat) (bounded : extent < 2^32)
    (advanced : nativeNext extent = some next) : 0 < next ∧ next < 2^32 := by
  rw [exclusive_extent_refines extent bounded] at advanced
  unfold referenceNext at advanced
  split at advanced
  · simp only [Option.some.injEq] at advanced
    omega
  · simp at advanced

namespace Controls

def sparse : State := ⟨[some 11, none, none, some 29], [29, 11]⟩

theorem sparse_valid : sparse.Valid := by
  refine ⟨by decide, ?_⟩
  exact List.Perm.swap _ _ _

theorem sparse_register_keeps_older_owner :
    register ⟨[none, none, none, none], []⟩ 3 29 =
      some ⟨[none, none, none, some 29], [29]⟩ := by decide

theorem sparse_disposal_is_complete : release {11, 29} sparse.owners = some ∅ := by decide

theorem dropped_owner_leaks : release {11, 29} [11] = some {29} := by decide

theorem repeated_owner_refuses : release {11, 29} [29, 11, 29] = none := by decide

theorem last_partial_chunk_is_included :
    denseChunks 16384 = 1 ∧ denseChunks 16385 = 2 ∧ denseChunks 1 = 1 := by decide

theorem exhausted_extent_refuses_new_entry :
    nativeNext 4294967295 = none ∧ (4294967295 + 1) % 2^32 = 0 := by decide

end Controls
end Mettapedia.Machines.InternChunkOwnership
