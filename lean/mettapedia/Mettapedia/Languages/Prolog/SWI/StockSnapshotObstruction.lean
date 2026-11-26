import Mettapedia.Machines.ReadOnlyQuery

/-!
# Entry observations for a lazy conjunctive read

A suspended join has a fixed sequence of remaining left keys. Each right key
has one independently chosen Boolean payload at entry. The join emits a key
when its payload is true. A consumer can clear the right relation after the
first answer, leaving the same live state for all entry payloads.

Preparation can adapt its indexed reads and save arbitrary state. A read
represents access to the entry payload, including access preserved by an
already-entered lookup. On resumption the matcher has that saved observation
and can consult the live relation. An independently retained historical view
or a writer's record of the old rows would add information to this interface.

Even for this family of joins, every future key must be covered by the entry
observations. The bound counts keys whose entry values must be accessible.
A shared snapshot handle can make many keys accessible without copying them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Prolog.SWI.StockSnapshotObstruction

open Mettapedia.Machines.ReadOnlyQuery

universe u v

variable {Key : Type u} {Saved : Type v}

/-- The ordered suffix when every indexed lookup uses the entry view. -/
def answersAt (keys : List Key) (entry : Key → Bool) : List Key :=
  keys.filter entry

private def flipAt [DecidableEq Key] (entry : Key → Bool) (key : Key) : Key → Bool :=
  fun other => if other = key then !entry other else entry other

private theorem observation_eq_of_unread [DecidableEq Key]
    (prepare : Program Key Bool Saved) (entry : Key → Bool) (key : Key)
    (unread : key ∉ (run entry prepare).reads.map Prod.fst) :
    run entry prepare = run (flipAt entry key) prepare := by
  symm
  apply run_eq_of_agrees
  intro read member
  have different : read.1 ≠ key := by
    intro same
    exact unread (List.mem_map.mpr ⟨read, member, same⟩)
  simpa [flipAt, different] using run_agrees entry prepare read member

private theorem answers_ne_of_flip [DecidableEq Key]
    (keys : List Key) (entry : Key → Bool) (key : Key) (needed : key ∈ keys) :
    answersAt keys entry ≠ answersAt keys (flipAt entry key) := by
  intro same
  have membership := congrArg (fun xs : List Key => key ∈ xs) same
  cases value : entry key <;> simp [answersAt, needed, flipAt, value] at membership

/-- Two entry worlds can give the same saved observation and require
different suffixes. Clearing the right relation then erases the remaining
distinction from the live state. -/
theorem unread_key_obstruction [DecidableEq Key]
    (keys : List Key) (prepare : Program Key Bool Saved) (entry : Key → Bool) (key : Key)
    (needed : key ∈ keys) (unread : key ∉ (run entry prepare).reads.map Prod.fst) :
    ∃ rival, run entry prepare = run rival prepare ∧
      answersAt keys entry ≠ answersAt keys rival :=
  ⟨flipAt entry key, observation_eq_of_unread prepare entry key unread,
    answers_ne_of_flip keys entry key needed⟩

/-- After the consumer clears the right relation, every entry assignment
still requires its own snapshot answer. -/
def CorrectAfterClear (keys : List Key) (prepare : Program Key Bool Saved)
    (resume : Observation Key Bool Saved → (Key → Option Bool) → List Key) : Prop :=
  ∀ entry, resume (run entry prepare) (fun _ => none) = answersAt keys entry

theorem every_future_key_is_observed [DecidableEq Key]
    (keys : List Key) (prepare : Program Key Bool Saved)
    (resume : Observation Key Bool Saved → (Key → Option Bool) → List Key)
    (correct : CorrectAfterClear keys prepare resume) (entry : Key → Bool) :
    keys ⊆ (run entry prepare).reads.map Prod.fst := by
  intro key needed
  by_cases observed : key ∈ (run entry prepare).reads.map Prod.fst
  · exact observed
  · obtain ⟨rival, same, different⟩ := unread_key_obstruction keys prepare entry key needed observed
    have agreed := congrArg (fun saved => resume saved (fun _ => none)) same
    exact False.elim (different ((correct entry).symm.trans (agreed.trans (correct rival))))

/-- The obligation holds for each entry, including an execution whose consumer
cuts immediately. Preparation occurs before the consumer makes that choice. -/
theorem entry_read_lower_bound [DecidableEq Key]
    (keys : List Key) (distinct : keys.Nodup) (prepare : Program Key Bool Saved)
    (resume : Observation Key Bool Saved → (Key → Option Bool) → List Key)
    (correct : CorrectAfterClear keys prepare resume) (entry : Key → Bool) :
    keys.length ≤ (run entry prepare).reads.length := by
  simpa only [List.length_map] using distinct.length_le_of_subset
    (every_future_key_is_observed keys prepare resume correct entry)

/-- An arbitrarily long join suffix rules out a fixed budget of entry
lookups for a matcher using only saved observations and live reads. -/
theorem no_fixed_read_budget (budget : Nat) (prepare : Program Nat Bool Saved)
    (resume : Observation Nat Bool Saved → (Nat → Option Bool) → List Nat)
    (correct : CorrectAfterClear (List.range (budget + 1)) prepare resume)
    (entry : Nat → Bool) :
    budget < (run entry prepare).reads.length := by
  have lower := entry_read_lower_bound (List.range (budget + 1)) List.nodup_range
    prepare resume correct entry
  rw [List.length_range] at lower
  exact Nat.lt_of_succ_le lower

/-- A retained cursor that can only read a prefix in storage order must
advance to the requested key. In this use, the observations include any
steps taken after the first yield and before the requested answer. -/
theorem sequential_cursor_lower_bound (key : Nat) (prepare : Program Nat Bool Saved)
    (resume : Observation Nat Bool Saved → (Nat → Option Bool) → List Nat)
    (correct : CorrectAfterClear [key] prepare resume) (entry : Nat → Bool)
    (inRange : (run entry prepare).reads.map Prod.fst ⊆
      List.range (run entry prepare).reads.length) :
    key < (run entry prepare).reads.length :=
  List.mem_range.mp (inRange (every_future_key_is_observed [key] prepare resume correct entry
    (List.mem_singleton_self key)))

/-- Collecting the entry observations attains the bound when the keys are
distinct. The order remains the order of the join's left keys. -/
def captureSuffix (keys : List Key) : Program Key Bool (List Key) :=
  match keys with
  | [] => .pure []
  | key :: rest =>
    .read key fun present =>
      bind (captureSuffix rest) fun tail =>
        .pure (if present then key :: tail else tail)

theorem capture_suffix_exact (keys : List Key) (entry : Key → Bool) :
    run entry (captureSuffix keys) = ⟨answersAt keys entry, samples entry keys⟩ := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    cases value : entry key <;>
      simp [captureSuffix, run, run_bind, ih, answersAt, samples, value]

theorem capture_suffix_correct (keys : List Key) :
    CorrectAfterClear keys (captureSuffix keys) (fun observed _ => observed.answer) := by
  intro entry
  exact congrArg Observation.answer (capture_suffix_exact keys entry)

end Mettapedia.Languages.Prolog.SWI.StockSnapshotObstruction
