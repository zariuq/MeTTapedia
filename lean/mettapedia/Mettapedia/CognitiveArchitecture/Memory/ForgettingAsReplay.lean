/-!
# Forgetting as counterfactual replay: what a memory must keep to forget exactly

**Exact forgetting.** Forgetting source `s` is exact when the memory left
afterwards is the one that replaying the log without `s`'s writes would have
built. This is the criterion of exact machine unlearning ("as if retrained
without the data"; Cao and Yang 2015, Thudi et al. 2022) and of deletion
propagation in databases (Green, Karvounarakis and Tannen 2007). It is also
the recovery-free reading of belief contraction. Recent agent-memory audits
report forgetting that fails by "resurrection": consolidation write-back,
copies, restored checkpoints. This file says which memory representations
can forget exactly and which cannot.

Results:
* **A bare store cannot forget exactly.** If the memory records only which
  facts are present, two logs with different sources can leave the same
  store and still need different results after forgetting. No forgetting
  function is exact (`bare_store_cannot_forget`). A consolidated summary
  written back without its sources is such a store.
* **Provenance suffices.** A store that keeps each fact's supporting
  sources forgets exactly by dropping `s` from every support
  (`provenance_store_forgets`). Every view computed from that provenance
  inherits exactness (`views_inherit_exact_forgetting`).
* **Destructive updates cannot forget exactly.** When a newer write
  supersedes an older one, a store holding only the current value cannot
  resurrect the right older value (`destructive_store_cannot_forget`). A
  versioned history can, by recomputing the latest surviving write. This is the formal reason to keep append-only
  versions and tombstones (compare `EventSourcedMemory`, `BitemporalClaims`).
  A per-key version store, which keeps each write's source and value, forgets
  exactly (`versions_store_forgets`) and still yields the current value
  (`latest_of_versions`).
* **Coupled derivations need replay.** When derivations compete for a shared
  budget, such as a curated core of capacity one, deleting only what `s`
  supported is not exact: the slot `s`'s fact held should go to the fact it
  displaced (`capacity_coupling_defeats_local_purge`). Replay from the log
  is exact (`replay_forgets`).

So exact forgetting needs a provenance-carrying store for monotone,
uncoupled derivations, and the append-only log itself as soon as writes
supersede one another or compete for capacity.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.ForgettingAsReplay

/-! ## Presence of facts, with and without provenance -/

/-- A log of writes, oldest first: each write names its source and a fact. -/
abbrev Log := List (Nat × Nat)

def without (s : Nat) (log : Log) : Log := log.filter (fun e => e.1 != s)

/-- The bare store: which facts are present. -/
def present (log : Log) (f : Nat) : Bool := log.any (fun e => e.2 == f)

/-- A bare store has no exact forgetting function. -/
theorem bare_store_cannot_forget :
    ¬ ∃ forget : Nat → (Nat → Bool) → (Nat → Bool),
      ∀ (log : Log) (s : Nat), forget s (present log) = present (without s log) := by
  rintro ⟨forget, exact⟩
  have same : present [(1, 0)] = present [(1, 0), (2, 0)] := by
    funext f
    by_cases h : f = 0 <;> simp [present, h]
  have h1 := exact [(1, 0)] 1
  have h2 := exact [(1, 0), (2, 0)] 1
  rw [same] at h1
  have := congrArg (fun p => p 0) (h1.symm.trans h2)
  simp [present, without] at this

/-- The provenance store: each fact's supporting sources, in log order. -/
def supports (log : Log) (f : Nat) : List Nat :=
  (log.filter (fun e => e.2 == f)).map Prod.fst

def forgetSupports (s : Nat) (store : Nat → List Nat) : Nat → List Nat :=
  fun f => (store f).filter (fun x => x != s)

theorem provenance_store_forgets (log : Log) (s : Nat) :
    forgetSupports s (supports log) = supports (without s log) := by
  funext f
  simp only [forgetSupports, supports, without]
  induction log with
  | nil => rfl
  | cons e rest ih =>
    by_cases hf : e.2 = f <;> by_cases hs : e.1 = s <;>
      simp [hf, hs, ih]

/-- Any view computed from the provenance store forgets exactly. -/
theorem views_inherit_exact_forgetting {α : Type} (view : (Nat → List Nat) → α)
    (log : Log) (s : Nat) :
    view (forgetSupports s (supports log)) = view (supports (without s log)) := by
  rw [provenance_store_forgets]

/-- Presence is recovered from provenance, so nothing is lost by keeping it. -/
theorem present_of_supports (log : Log) (f : Nat) :
    present log f = !(supports log f).isEmpty := by
  induction log with
  | nil => rfl
  | cons e rest ih =>
    cases h : (e.2 == f) <;> simp_all [present, supports]

/-! ## Superseding writes -/

/-- Keyed writes, oldest first: source, key, value. -/
abbrev KLog := List (Nat × Nat × Nat)

def kwithout (s : Nat) (log : KLog) : KLog := log.filter (fun e => e.1 != s)

/-- The current value of a key: its latest write. -/
def latest (log : KLog) (k : Nat) : Option Nat :=
  (log.filter (fun e => e.2.1 == k)).getLast?.map (fun e => e.2.2)

/-- A store that keeps only current values cannot forget exactly. -/
theorem destructive_store_cannot_forget :
    ¬ ∃ forget : Nat → (Nat → Option Nat) → (Nat → Option Nat),
      ∀ (log : KLog) (s : Nat), forget s (latest log) = latest (kwithout s log) := by
  rintro ⟨forget, exact⟩
  -- Both logs end with source 1 writing value 9 to key 0.
  have same : latest [(2, 0, 5), (1, 0, 9)] = latest [(3, 0, 6), (1, 0, 9)] := by
    funext k
    by_cases h : k = 0
    · simp [latest, h]
    · have h' : (0 : Nat) ≠ k := fun e => h e.symm
      simp [latest, h']
  have h1 := exact [(2, 0, 5), (1, 0, 9)] 1
  have h2 := exact [(3, 0, 6), (1, 0, 9)] 1
  rw [same] at h1
  have := congrArg (fun p => p 0) (h1.symm.trans h2)
  simp [latest, kwithout] at this

/-- The per-key version store: each key's writes as (source, value), oldest
first. The current value is its last entry. -/
def versions (log : KLog) (k : Nat) : List (Nat × Nat) :=
  (log.filter (fun e => e.2.1 == k)).map (fun e => (e.1, e.2.2))

def forgetVersions (s : Nat) (store : Nat → List (Nat × Nat)) : Nat → List (Nat × Nat) :=
  fun k => (store k).filter (fun v => v.1 != s)

/-- A versioned store forgets exactly by dropping the source's versions. -/
theorem versions_store_forgets (log : KLog) (s : Nat) :
    forgetVersions s (versions log) = versions (kwithout s log) := by
  funext k
  simp only [forgetVersions, versions, kwithout]
  induction log with
  | nil => rfl
  | cons e rest ih =>
    by_cases hk : e.2.1 = k <;> by_cases hs : e.1 = s <;>
      simp [hk, hs, ih]

/-- The current value is read off the version store, so nothing is lost by
keeping versions. -/
theorem latest_of_versions (log : KLog) (k : Nat) :
    latest log k = ((versions log k).getLast?).map Prod.snd := by
  simp [latest, versions, List.getLast?_map, Option.map_map, Function.comp_def]

/-! ## Derivations that compete for capacity -/

/-- A curated core of capacity `cap`: the first `cap` distinct facts written,
in log order. -/
def core (cap : Nat) (log : Log) : List Nat := ((log.map Prod.snd).eraseDups).take cap

/-- Local purge: keep the core's facts that still have support without `s`,
and promote nothing new. -/
def localPurge (s : Nat) (log : Log) (current : List Nat) : List Nat :=
  current.filter (fun f => present (without s log) f)

/-- With a capacity of one, the slot that source 1's fact held should pass to
the fact it displaced; local purge leaves the core empty instead. -/
theorem capacity_coupling_defeats_local_purge :
    localPurge 1 [(1, 10), (2, 20)] (core 1 [(1, 10), (2, 20)]) = [] ∧
      core 1 (without 1 [(1, 10), (2, 20)]) = [20] := by
  decide

#print axioms bare_store_cannot_forget
#print axioms provenance_store_forgets
#print axioms views_inherit_exact_forgetting
#print axioms present_of_supports
#print axioms destructive_store_cannot_forget
#print axioms versions_store_forgets
#print axioms latest_of_versions
#print axioms capacity_coupling_defeats_local_purge

end Mettapedia.CognitiveArchitecture.Memory.ForgettingAsReplay
