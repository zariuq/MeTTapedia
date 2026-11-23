import Mettapedia.Machines.DeferredLocalUpdate
import Mathlib.Data.Finset.Basic

/-!
# Process history and cell ownership give different information

A sticky process flag records that launch has happened; it is not a count
of current workers. An initially certified caller remains alone throughout
a window when it neither launches nor exits, because launching requires a
live parent. Even a sticky flag cannot survive a thread-creating call by
the caller inside that window.

A private cell can remain a local update target after global certification
has been lost. The second model lets participants write only where they
have authority, and makes exposure an explicit event. This explains which
windows can ignore other participants' writes. It does not implement a
reference count, memory ordering, pointer lifetime, or foreign access.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MonotoneSingleThreadLatch

section Process

variable {Actor : Type*} [DecidableEq Actor]

@[ext] structure Process (Actor : Type*) where
  running : Finset Actor
  launched : Bool
  deriving DecidableEq

def initial (caller : Actor) : Process Actor := ⟨{caller}, false⟩

inductive Event (Actor : Type*) where
  | launch (parent child : Actor)
  | exit (actor : Actor)

def step (process : Process Actor) : Event Actor → Process Actor
  | .launch parent child =>
      if parent ∈ process.running then ⟨insert child process.running, true⟩ else process
  | .exit actor => { process with running := process.running.erase actor }

def history (process : Process Actor) : List (Event Actor) → Process Actor
  | [] => process
  | event :: rest => history (step process event) rest

theorem sticky (process : Process Actor) (events : List (Event Actor))
    (launched : process.launched = true) : (history process events).launched = true := by
  induction events generalizing process with
  | nil => exact launched
  | cons event rest ih =>
      apply ih
      cases event with
      | launch parent child => by_cases live : parent ∈ process.running <;> simp [step, live, launched]
      | exit actor => exact launched

private theorem certified_subset (origin : Actor) (process : Process Actor) (events : List (Event Actor))
    (valid : process.launched = false → process.running ⊆ {origin}) :
    (history process events).launched = false → (history process events).running ⊆ {origin} := by
  induction events generalizing process with
  | nil => exact valid
  | cons event rest ih =>
      apply ih
      cases event with
      | launch parent child =>
          by_cases live : parent ∈ process.running
          · simp [step, live]
          · simpa [step, live] using valid
      | exit actor =>
          intro flag
          exact Finset.erase_subset _ _ |>.trans (valid flag)

/-- At the sample, a live caller seeing the initial flag is the sole
participant. Merely rejoining the last worker cannot restore that flag. -/
theorem seeing_unlaunched_means_solo (origin caller : Actor) (events : List (Event Actor))
    (certified : (history (initial origin) events).launched = false)
    (present : caller ∈ (history (initial origin) events).running) :
    history (initial origin) events = initial caller := by
  have inside := certified_subset origin (initial origin) events (fun _ => le_rfl) certified
  have equal : caller = origin := Finset.mem_singleton.mp (inside present)
  subst origin
  apply Process.ext
  · exact Finset.Subset.antisymm inside (Finset.singleton_subset_iff.mpr present)
  · exact certified

def outsideCaller (caller : Actor) : Event Actor → Prop
  | .launch parent _ => parent ≠ caller
  | .exit actor => actor ≠ caller

private theorem solo_window (caller : Actor) (events : List (Event Actor))
    (outside : ∀ event ∈ events, outsideCaller caller event) :
    history (initial caller) events = initial caller := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      have all := ih (fun later yes => outside later (List.mem_cons_of_mem _ yes))
      have now := outside event (by simp)
      have same : step (initial caller) event = initial caller := by
        cases event with
        | launch parent child => simp [initial, step, outsideCaller] at now ⊢; simp [now]
        | exit actor => simp [initial, step, outsideCaller] at now ⊢; simp [now]
      rw [history, same, all]

theorem unlaunched_survives_no_reentry_window (origin caller : Actor)
    (past window : List (Event Actor))
    (certified : (history (initial origin) past).launched = false)
    (present : caller ∈ (history (initial origin) past).running)
    (outside : ∀ event ∈ window, outsideCaller caller event) :
    history (history (initial origin) past) window = initial caller := by
  rw [seeing_unlaunched_means_solo origin caller past certified present]
  exact solo_window caller window outside

namespace Controls

theorem a_rejoined_worker_leaves_the_latch_set :
    history (initial false) [.launch false true, .exit true] = ⟨{false}, true⟩ := by decide

/-- Monotonicity does not justify saving a boolean across an operation
that can create a thread. The first thread may create its own interference. -/
theorem reentrant_launch_invalidates_prior_observation :
    (initial false).launched = false ∧
      (history (initial false) [.launch false true]).running.card = 2 := by decide

end Controls
end Process

section LocalCell

open DeferredLocalUpdate (Write actionsAt overwrite perform replay disjoint_edits_need_no_exclusion)

variable {Actor Slot Value : Type*} [DecidableEq Actor] [DecidableEq Slot]

abbrev Authorities (Actor Slot : Type*) := Actor → Finset Slot

def Private (rights : Authorities Actor Slot) (owner : Actor) (slot : Slot) : Prop :=
  ∀ actor, slot ∈ rights actor → actor = owner

inductive Edit (Actor Slot Value : Type*) where
  | expose (source recipient : Actor) (slot : Slot)
  | write (actor : Actor) (slot : Slot) (update : Value → Value)

def dispatch (rights : Authorities Actor Slot) :
    Edit Actor Slot Value → Authorities Actor Slot × Option (Write Slot Value)
  | .expose source recipient key =>
      if key ∈ rights source then
        (Function.update rights recipient (insert key (rights recipient)), none)
      else (rights, none)
  | .write actor key update =>
      (rights, if key ∈ rights actor then some (key, update) else none)

def staysLocal (owner : Actor) (slot : Slot) : Edit Actor Slot Value → Prop
  | .expose source recipient key => key = slot → source = owner → recipient = owner
  | .write actor key _ => key = slot → actor ≠ owner

private theorem dispatch_private (rights : Authorities Actor Slot) (owner : Actor) (slot : Slot)
    (op : Edit Actor Slot Value) (isolated : Private rights owner slot)
    (quiet : staysLocal owner slot op) :
    Private (dispatch rights op).1 owner slot ∧
      actionsAt slot (dispatch rights op).2.toList = [] := by
  cases op with
  | expose source recipient key =>
      by_cases holds : key ∈ rights source
      · rw [dispatch, if_pos holds]
        refine ⟨?_, rfl⟩
        intro actor received
        by_cases it : actor = recipient
        · subst actor
          simp only [Function.update_self, Finset.mem_insert] at received
          rcases received with same | old
          · subst key
            exact quiet rfl (isolated source holds)
          · exact isolated recipient old
        · exact isolated actor (by simpa only [Function.update_of_ne it] using received)
      · simpa [dispatch, holds, actionsAt] using isolated
  | write actor key update =>
      refine ⟨isolated, ?_⟩
      by_cases holds : key ∈ rights actor
      · have different : key ≠ slot := by
          rintro rfl
          exact quiet rfl (isolated actor holds)
        simp [dispatch, holds, actionsAt, different]
      · simp [dispatch, holds, actionsAt]

def edits (rights : Authorities Actor Slot) :
    List (Edit Actor Slot Value) → Authorities Actor Slot × List (Write Slot Value)
  | [] => (rights, [])
  | op :: rest =>
      let first := dispatch rights op
      let later := edits first.1 rest
      (later.1, first.2.toList ++ later.2)

/-- A fresh unexposed cell's update does not depend on other participants'
edits, regardless of whether the process-wide fast path has been lost. -/
theorem private_edits_have_empty_projection (rights : Authorities Actor Slot)
    (owner : Actor) (slot : Slot) (window : List (Edit Actor Slot Value))
    (initially : Private rights owner slot)
    (localWindow : ∀ event ∈ window, staysLocal owner slot event) :
    Private (edits rights window).1 owner slot ∧ actionsAt slot (edits rights window).2 = [] := by
  induction window generalizing rights with
  | nil => exact ⟨initially, rfl⟩
  | cons op rest ih =>
      have early := dispatch_private rights owner slot op initially (localWindow op (by simp))
      have later := ih _ early.1 (fun op yes => localWindow op (List.mem_cons_of_mem _ yes))
      refine ⟨later.1, ?_⟩
      simp only [edits, actionsAt, List.filterMap_append]
      unfold actionsAt at early later
      rw [early.2, later.2, List.nil_append]

theorem private_overwrite_matches_current (rights : Authorities Actor Slot)
    (owner : Actor) (slot : Slot) (window : List (Edit Actor Slot Value))
    (initially : Private rights owner slot)
    (localWindow : ∀ event ∈ window, staysLocal owner slot event)
    (before : Slot → Value) (update : Value → Value) :
    overwrite before slot update (edits rights window).2 =
      perform (replay before (edits rights window).2) (slot, update) :=
  disjoint_edits_need_no_exclusion before slot update _
    (private_edits_have_empty_projection rights owner slot window initially localWindow).2

namespace Controls

def rights (actor : Bool) : Finset Bool := {actor}

def elsewhere : List (Edit Bool Bool Nat) := [.write true true (· + 1)]

theorem local_update_survives_parallel_activity :
    (history (initial false) [.launch false true]).launched = true ∧
    overwrite (fun _ => 0) false (· + 1) (edits rights elsewhere).2 =
      perform (replay (fun _ => 0) (edits rights elsewhere).2) (false, (· + 1)) := by
  refine ⟨by decide, private_overwrite_matches_current rights false false elsewhere ?_ ?_ _ _⟩
  · intro actor holds
    simpa [rights, eq_comm] using holds
  · intro op occurs
    simp only [elsewhere, List.mem_singleton] at occurs
    subst op
    simp [staysLocal]

theorem publication_allows_an_intervening_write :
    overwrite (fun _ => 0) false (· + 1)
      (edits rights ([.expose false true false, .write true false (· + 1)] :
        List (Edit Bool Bool Nat))).2 false = 1 ∧
    perform (replay (fun _ => 0)
      (edits rights ([.expose false true false, .write true false (· + 1)] :
        List (Edit Bool Bool Nat))).2) (false, (· + 1)) false = 2 := by decide

end Controls
end LocalCell
end Mettapedia.Machines.MonotoneSingleThreadLatch
