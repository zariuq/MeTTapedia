import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns
import Mettapedia.Machines.ReadyQueue

/-!
# Parked `await` and `whenever`: the wait index, and the fairness each guard needs

A reactive firing **parks** until its guard holds: `await X` fires once, `whenever X` fires on
each enabling. A runtime does not re-match every parked firing after every commit. It keeps a
**wait index**: a parked firing is *awake* (it will be re-matched) or *asleep* (its last re-match
found no row), and a commit wakes the parked firings that the index associates with it. This module
gives that runtime a semantics over the commits of `Commits` and proves what keeps happening.

## The reactive system (`reactive`)

A parked firing (`Parked`) has the ground rows its guard can fire, the region its guard reads (its
key in the index), and whether it is persistent. Its **guard** holds when some row is fireable: the
row's takes and keeps are present, nothing is both, its predicate queries hold (`Matches`), and its
fresh identities are unborn. The steps are an outside commit (`env`), running an awake parked firing
with one of its fireable rows (`run`), putting an awake firing to sleep when its guard fails
(`sleep`), and the idle step. A commit wakes the parked firings that the index selects for it.

## The wait index loses no wakeup

* An index **loses no wakeup** for a parked firing (`NoLostWakeup`) when every commit that turns its
  guard from false to true is one the index wakes it for.
* **The region index loses no wakeup** (`regionIndex_noLostWakeup`): wake a firing for every commit
  that writes into its region, provided its rows live in its region (`InRegion`). This is K's
  `woken_requires_write` applied to the guard.
* **The kind index loses no wakeup** (`kindIndex_noLostWakeup`): a firing whose rows query nothing
  is woken only by makes in its region (`positive_woken_by_make`); others by any write.
* **Invariant** (`WakeInv`, `wakeInv_next`, `Run.wakeInv`): with an index that loses no wakeup,
  every parked firing whose guard holds is awake, in every reachable state.

## What keeps happening

* **Strong fairness wakes and fires every parked `await` whose guard holds infinitely often**
  (`await_fires`), and fires a `whenever` infinitely often (`whenever_fires_often`). The fairness is
  that of the scheduler's choice among awake firings (the task `runTask p`).
* **Weak fairness suffices for a stable guard** (`await_fires_of_stable`): once the guard holds it
  keeps holding until the firing runs. A row without predicate queries stays fireable across any
  commit that does not take what it uses or claim its fresh identities (`fireable_after_commit`),
  so a guard without competitors (the only receiver on a private channel, a reader of facts nobody
  takes) needs only weak fairness (`await_fires_of_sole_consumer`).
* Strong fairness is implementable: the aging scheduler of `FairRuns` gives a strongly fair run of
  every reactive system with finitely many parked firings (`exists_stronglyFair_reactive_run`).

## Controls

* `Controls.flicker_weaklyFair`, `Controls.flicker_await_never_fires`: an `await` that takes a
  token competes with a `whenever` that holds and releases it. The run in which the whenever toggles
  forever is weakly fair for both and never fires the await, whose guard holds at every other
  step: **weak fairness is not enough for a guard that flickers.**
* `Controls.flicker_stronglyFair_fires`: in every strongly fair run of the same system the await
  fires.
* `Controls.makesIndex_loses_wakeup`: an index that wakes a firing only for makes in its region is
  wrong for an absence guard. "Add an output unless locked" sleeps while the lock is present; the
  lock is taken; the index does not wake it; its guard then holds forever, and it never runs in a run
  that is strongly fair, because it is never awake. With the region index the same commit wakes it
  (`Controls.regionIndex_wakes`).
* `ParkingHandshake` splits registration, recheck, notification and conditional parking into
  explicit cell operations. A delivered notice cannot be overwritten by a later stale park;
  failed queue admission retains it, and generation checks reject late actions after reuse.
  The source-to-notification and queue-progress links remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Rows and guards -/

/-- What a row needs from the store: its takes and keeps present, nothing both, its predicate
queries holding. Freshness is the allocator's and is checked against the identities ever born. -/
structure Matches (label : O → R) (store : Finset O) (c : Commit O R) : Prop where
  taken_subset : c.taken ⊆ store
  kept_subset : c.kept ⊆ store
  apart : Disjoint c.taken c.kept
  queries_hold : ∀ read ∈ c.queries, read.Holds label store

/-- A row is fireable: it matches and its fresh identities are unborn. -/
abbrev Fireable (label : O → R) (store born : Finset O) (c : Commit O R) : Prop :=
  Matches label store c ∧ Disjoint c.made born

omit [DecidableEq O] in
/-- A fireable row is an enabled commit, when every live occurrence is born. -/
theorem Fireable.enabled {label : O → R} {store born : Finset O} {c : Commit O R}
    (fireable : Fireable label store born c) (sub : store ⊆ born) : Enabled label store c where
  taken_subset := fireable.1.taken_subset
  kept_subset := fireable.1.kept_subset
  apart := fireable.1.apart
  fresh := Finset.disjoint_of_subset_right sub fireable.2
  queries_hold := fireable.1.queries_hold

/-- A parked firing: the rows its guard can fire, the region its guard reads, and whether it is
persistent (`whenever`) or fires once (`await`). -/
structure Parked (O : Type u) (R : Type v) where
  rows : Set (Commit O R)
  region : R → Bool
  persistent : Bool

/-- The guard of a parked firing holds: some row is fireable. -/
abbrev Guard (label : O → R) (p : Parked O R) (store born : Finset O) : Prop :=
  ∃ c ∈ p.rows, Fireable label store born c

/-- The rows of a parked firing live in its region: what they take and keep, and the regions of
their predicate queries. -/
def InRegion (label : O → R) (p : Parked O R) : Prop :=
  ∀ c ∈ p.rows, (∀ o ∈ c.taken ∪ c.kept, p.region (label o) = true) ∧
    ∀ read ∈ c.queries, ∀ r, read.region r = true → p.region r = true

/-- The rows of a parked firing have no predicate queries. -/
def PositiveRows (p : Parked O R) : Prop := ∀ c ∈ p.rows, c.queries = []

/-- A row in a region matches a store exactly when it matches the store's part in the region. -/
theorem matches_regionOf_iff {label : O → R} {store : Finset O} {region : R → Bool}
    {c : Commit O R} (uses : ∀ o ∈ c.taken ∪ c.kept, region (label o) = true)
    (reads : ∀ read ∈ c.queries, ∀ r, read.region r = true → region r = true) :
    Matches label store c ↔ Matches label (regionOf label store region) c := by
  have subsetIff : ∀ X : Finset O, (∀ o ∈ X, region (label o) = true) →
      (X ⊆ store ↔ X ⊆ regionOf label store region) := by
    intro X inside
    constructor
    · intro sub o member
      exact mem_regionOf.mpr ⟨sub member, inside o member⟩
    · intro sub o member
      exact (mem_regionOf.mp (sub member)).1
  have readIff : ∀ read ∈ c.queries,
      regionOf label (regionOf label store region) read.region = regionOf label store read.region := by
    intro read member
    ext o
    simp only [mem_regionOf]
    constructor
    · rintro ⟨⟨inStore, _⟩, inRead⟩
      exact ⟨inStore, inRead⟩
    · rintro ⟨inStore, inRead⟩
      exact ⟨⟨inStore, reads read member _ inRead⟩, inRead⟩
  have takenInside : ∀ o ∈ c.taken, region (label o) = true :=
    fun o member => uses o (Finset.mem_union_left _ member)
  have keptInside : ∀ o ∈ c.kept, region (label o) = true :=
    fun o member => uses o (Finset.mem_union_right _ member)
  constructor
  · intro m
    refine ⟨(subsetIff _ takenInside).1 m.taken_subset, (subsetIff _ keptInside).1 m.kept_subset,
      m.apart, fun read member => ?_⟩
    unfold PredicateQuery.Holds
    rw [readIff read member]
    exact m.queries_hold read member
  · intro m
    refine ⟨(subsetIff _ takenInside).2 m.taken_subset, (subsetIff _ keptInside).2 m.kept_subset,
      m.apart, fun read member => ?_⟩
    have := m.queries_hold read member
    unfold PredicateQuery.Holds at this ⊢
    rwa [readIff read member] at this

/-- **A row without predicate queries stays fireable** across a commit that takes nothing it uses
and claims none of its fresh identities. -/
theorem fireable_after_commit {label : O → R} {store born : Finset O} {c d : Commit O R}
    (fireable : Fireable label store born c) (positive : c.queries = [])
    (untouched : Disjoint d.taken (c.taken ∪ c.kept)) (ownIds : Disjoint d.made c.made) :
    Fireable label (fire store d) (born ∪ d.made) c := by
  have survives : ∀ o ∈ c.taken ∪ c.kept, o ∈ store → o ∈ fire store d := fun o used inStore =>
    mem_fire.mpr (Or.inl ⟨inStore, fun taken => Finset.disjoint_left.mp untouched taken used⟩)
  refine ⟨⟨fun o taken => survives o (Finset.mem_union_left _ taken) (fireable.1.taken_subset taken),
      fun o kept => survives o (Finset.mem_union_right _ kept) (fireable.1.kept_subset kept),
      fireable.1.apart, by simp [positive]⟩, ?_⟩
  exact Finset.disjoint_union_right.mpr ⟨fireable.2, ownIds.symm⟩

/-! ## Wait indexes -/

/-- An index **loses no wakeup** for a parked firing: every commit that turns its guard from false to
true is one the index wakes it for. -/
def NoLostWakeup (label : O → R) (index : Parked O R → Commit O R → Prop) (p : Parked O R) : Prop :=
  ∀ (store born : Finset O) (d : Commit O R), store ⊆ born → Enabled label store d →
    Disjoint d.made born → ¬ Guard label p store born →
      Guard label p (fire store d) (born ∪ d.made) → index p d

/-- The region index: wake a firing for every commit that writes into its region (`Writes`). -/
def regionIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  Writes label d p.region

/-- The kind index: a firing whose rows have no predicate queries is woken by makes in its region;
any
other by any write in its region. -/
def kindIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  (PositiveRows p ∧ ∃ o ∈ d.made, p.region (label o) = true) ∨
    (¬ PositiveRows p ∧ regionIndex label p d)

/-- The makes index: wake a firing only for makes in its region. Right for positive guards, wrong
for absence guards (`Controls.makesIndex_loses_wakeup`). -/
def makesIndex (label : O → R) (p : Parked O R) (d : Commit O R) : Prop :=
  ∃ o ∈ d.made, p.region (label o) = true

/-- The test a guard applies to the part of the store in its region, with fixed born identities. -/
def regionTest (label : O → R) (p : Parked O R) (born : Finset O) (X : Finset O) : Prop :=
  ∃ c ∈ p.rows, Matches label X c ∧ Disjoint c.made born

theorem regionTest_iff_guard {label : O → R} {p : Parked O R} (inRegion : InRegion label p)
    {store born : Finset O} :
    regionTest label p born (regionOf label store p.region) ↔ Guard label p store born := by
  constructor
  · rintro ⟨c, row, m, fresh⟩
    exact ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).2 m, fresh⟩
  · rintro ⟨c, row, m, fresh⟩
    exact ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).1 m, fresh⟩

theorem not_regionTest_of_not_guard {label : O → R} {p : Parked O R} (inRegion : InRegion label p)
    {store born : Finset O} {extra : Finset O} (before : ¬ Guard label p store born) :
    ¬ regionTest label p (born ∪ extra) (regionOf label store p.region) := by
  rintro ⟨c, row, m, fresh⟩
  exact before ⟨c, row, (matches_regionOf_iff (inRegion c row).1 (inRegion c row).2).2 m,
    Finset.disjoint_of_subset_right Finset.subset_union_left fresh⟩

/-- **The region index loses no wakeup.** -/
theorem regionIndex_noLostWakeup {label : O → R} {p : Parked O R} (inRegion : InRegion label p) :
    NoLostWakeup label (regionIndex label) p := by
  intro store born d _ _ _ before after
  exact woken_requires_write (test := regionTest label p (born ∪ d.made))
    (not_regionTest_of_not_guard inRegion before) ((regionTest_iff_guard inRegion).2 after)

/-- **The kind index loses no wakeup.** -/
theorem kindIndex_noLostWakeup {label : O → R} {p : Parked O R} (inRegion : InRegion label p) :
    NoLostWakeup label (kindIndex label) p := by
  intro store born d sub enabled fresh before after
  by_cases positive : PositiveRows p
  · refine Or.inl ⟨positive, positive_woken_by_make (test := regionTest label p (born ∪ d.made)) ?_
      (not_regionTest_of_not_guard inRegion before) ((regionTest_iff_guard inRegion).2 after)⟩
    rintro small large le ⟨c, row, m, freshC⟩
    exact ⟨c, row, ⟨m.taken_subset.trans le, m.kept_subset.trans le, m.apart,
      by simp [positive c row]⟩, freshC⟩
  · exact Or.inr ⟨positive, regionIndex_noLostWakeup inRegion store born d sub enabled fresh before after⟩

/-! ## The reactive system -/

/-- The runtime state: the store, every identity ever born, the parked firings, the awake ones. -/
structure RState (O : Type u) (P : Type w) where
  store : Finset O
  born : Finset O
  parked : Set P
  awake : Set P

/-- A step: an outside commit, running a parked firing with one of its rows, putting a firing to
sleep, or idling. -/
inductive RLabel (O : Type u) (R : Type v) (P : Type w) where
  | env (d : Commit O R)
  | run (p : P) (c : Commit O R)
  | sleep (p : P)
  | idle

variable {P : Type w}

section System

variable (label : O → R) (proc : P → Parked O R) (index : Parked O R → Commit O R → Prop)
  (envOK : Commit O R → Prop)

/-- The parked firings a commit wakes. -/
def woken (σ : RState O P) (d : Commit O R) : Set P := {q | q ∈ σ.parked ∧ index (proc q) d}

/-- When a step may happen. -/
def rAllowed (σ : RState O P) : RLabel O R P → Prop
  | .env d => envOK d ∧ Enabled label σ.store d ∧ Disjoint d.made σ.born
  | .run p c => p ∈ σ.parked ∧ p ∈ σ.awake ∧ c ∈ (proc p).rows ∧ Fireable label σ.store σ.born c
  | .sleep p => p ∈ σ.awake ∧ ¬ Guard label (proc p) σ.store σ.born
  | .idle => True

/-- What a step does. -/
def rNext (σ : RState O P) : RLabel O R P → RState O P
  | .env d => ⟨fire σ.store d, σ.born ∪ d.made, σ.parked, σ.awake ∪ woken proc index σ d⟩
  | .run p c => ⟨fire σ.store c, σ.born ∪ c.made,
      if (proc p).persistent then σ.parked else σ.parked \ {p},
      if (proc p).persistent then σ.awake ∪ woken proc index σ c
      else (σ.awake ∪ woken proc index σ c) \ {p}⟩
  | .sleep p => ⟨σ.store, σ.born, σ.parked, σ.awake \ {p}⟩
  | .idle => σ

/-- The reactive system. -/
def reactive : LTS (RState O P) (RLabel O R P) := ⟨rAllowed label proc envOK, rNext proc index⟩

@[simp] theorem reactive_next : (reactive label proc index envOK).next = rNext proc index := rfl

@[simp] theorem reactive_allowed :
    (reactive label proc index envOK).Allowed = rAllowed label proc envOK := rfl

/-- The task "run parked firing `p`". -/
def runTask (p : P) : RLabel O R P → Prop
  | .run q _ => q = p
  | _ => False

/-- The invariant of the wait index: every live occurrence is born, and every parked firing whose
guard holds is awake. -/
structure WakeInv (σ : RState O P) : Prop where
  store_born : σ.store ⊆ σ.born
  awake_of_guard : ∀ q ∈ σ.parked, Guard label (proc q) σ.store σ.born → q ∈ σ.awake

end System

section Invariant

variable {label : O → R} {proc : P → Parked O R} {index : Parked O R → Commit O R → Prop}
  {envOK : Commit O R → Prop}

theorem fire_subset_born {store born : Finset O} {d : Commit O R} (sub : store ⊆ born) :
    fire store d ⊆ born ∪ d.made := by
  intro o member
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact Finset.mem_union_left _ (sub inStore)
  · exact Finset.mem_union_right _ made

/-- After a commit, a parked firing whose guard holds was awake or is woken. -/
theorem awake_after_commit (adequate : ∀ q, NoLostWakeup label index (proc q)) {σ : RState O P}
    (inv : WakeInv label proc σ) {d : Commit O R} (enabled : Enabled label σ.store d)
    (fresh : Disjoint d.made σ.born) {q : P} (parked : q ∈ σ.parked)
    (after : Guard label (proc q) (fire σ.store d) (σ.born ∪ d.made)) :
    q ∈ σ.awake ∪ woken proc index σ d := by
  by_cases before : Guard label (proc q) σ.store σ.born
  · exact Or.inl (inv.awake_of_guard q parked before)
  · exact Or.inr ⟨parked, adequate q σ.store σ.born d inv.store_born enabled fresh before after⟩

/-- **Every step keeps the wait-index invariant**, for an index that loses no wakeup. -/
theorem wakeInv_next (adequate : ∀ q, NoLostWakeup label index (proc q)) {σ : RState O P}
    (inv : WakeInv label proc σ) {a : RLabel O R P} (allowed : rAllowed label proc envOK σ a) :
    WakeInv label proc (rNext proc index σ a) := by
  cases a with
  | env d =>
      obtain ⟨_, enabled, fresh⟩ := allowed
      exact ⟨fire_subset_born inv.store_born,
        fun q parked after => awake_after_commit adequate inv enabled fresh parked after⟩
  | run p c =>
      obtain ⟨_, _, _, fireable⟩ := allowed
      have enabled := fireable.enabled inv.store_born
      refine ⟨fire_subset_born inv.store_born, fun q parked after => ?_⟩
      simp only [rNext] at parked after ⊢
      cases persistent : (proc p).persistent
      · simp only [persistent, Bool.false_eq_true, if_false] at parked ⊢
        obtain ⟨parkedOld, notP⟩ := parked
        exact ⟨awake_after_commit adequate inv enabled fireable.2 parkedOld after, notP⟩
      · simp only [persistent, if_true] at parked ⊢
        exact awake_after_commit adequate inv enabled fireable.2 parked after
  | sleep p =>
      obtain ⟨_, noGuard⟩ := allowed
      refine ⟨inv.store_born, fun q parked guard => ⟨inv.awake_of_guard q parked guard, ?_⟩⟩
      rintro rfl
      exact noGuard guard
  | idle => exact inv

/-- **The invariant holds along every run that starts in it.** -/
theorem Run.wakeInv (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) :
    ∀ n, WakeInv label proc (r.state n) := by
  intro n
  induction n with
  | zero => exact init
  | succ n ih =>
      rw [r.step n]
      exact wakeInv_next adequate ih (r.allowed n)

/-- A parked firing stays parked unless it runs. -/
theorem parked_next {σ : RState O P} {a : RLabel O R P} {p : P} (parked : p ∈ σ.parked)
    (notRun : ¬ runTask p a) : p ∈ (rNext proc index σ a).parked := by
  cases a with
  | env d => exact parked
  | run q c =>
      have different : q ≠ p := notRun
      simp only [rNext]
      split_ifs
      · exact parked
      · exact ⟨parked, fun same => different (Set.mem_singleton_iff.mp same).symm⟩
  | sleep q => exact parked
  | idle => exact parked

/-- A persistent firing stays parked. -/
theorem parked_next_of_persistent {σ : RState O P} {a : RLabel O R P} {p : P}
    (persistent : (proc p).persistent = true) (parked : p ∈ σ.parked) :
    p ∈ (rNext proc index σ a).parked := by
  by_cases runs : runTask p a
  · cases a with
    | run q c =>
        have same : q = p := runs
        subst same
        simp only [rNext, persistent, if_true]
        exact parked
    | env d => exact absurd runs id
    | sleep q => exact absurd runs id
    | idle => exact absurd runs id
  · exact parked_next parked runs

/-- A parked firing that never runs stays parked forever. -/
theorem Run.parked_forever (r : Run (reactive label proc index envOK)) {p : P} {N : ℕ}
    (parked : p ∈ (r.state N).parked) (never : ∀ n ≥ N, ¬ runTask p (r.label n)) :
    ∀ n ≥ N, p ∈ (r.state n).parked := by
  intro n le
  induction n, le using Nat.le_induction with
  | base => exact parked
  | succ n le ih =>
      rw [r.step n]
      exact parked_next ih (never n le)

/-- A parked firing whose guard holds, under the invariant, can run. -/
theorem runTask_enabled {σ : RState O P} (inv : WakeInv label proc σ) {p : P}
    (parked : p ∈ σ.parked) (guard : Guard label (proc p) σ.store σ.born) :
    (reactive label proc index envOK).TaskEnabled (runTask p) σ := by
  obtain ⟨c, row, fireable⟩ := guard
  exact ⟨.run p c, rfl, parked, inv.awake_of_guard p parked ⟨c, row, fireable⟩, row, fireable⟩

end Invariant

/-! ## What keeps happening -/

section Liveness

variable {label : O → R} {proc : P → Parked O R} {index : Parked O R → Commit O R → Prop}
  {envOK : Commit O R → Prop}

/-- **Strong fairness wakes and fires every parked `await` whose guard holds infinitely often.** -/
theorem await_fires (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    (parked : p ∈ (r.state 0).parked) (fair : r.StronglyFair (runTask p))
    (often : InfinitelyOften fun n => Guard label (proc p) (r.state n).store (r.state n).born) :
    ∃ n, runTask p (r.label n) := by
  by_contra never
  push Not at never
  have stays := Run.parked_forever r parked fun n _ => never n
  have enabledOften : InfinitelyOften fun n =>
      (reactive label proc index envOK).TaskEnabled (runTask p) (r.state n) := by
    intro N
    obtain ⟨n, le, guard⟩ := often N
    exact ⟨n, le, runTask_enabled (Run.wakeInv adequate r init n) (stays n (Nat.zero_le n)) guard⟩
  obtain ⟨n, _, fires⟩ := fair enabledOften 0
  exact never n fires

/-- **Strong fairness fires a parked `whenever` infinitely often when its guard holds infinitely
often.** -/
theorem whenever_fires_often (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    (persistent : (proc p).persistent = true) (parked : p ∈ (r.state 0).parked)
    (fair : r.StronglyFair (runTask p))
    (often : InfinitelyOften fun n => Guard label (proc p) (r.state n).store (r.state n).born) :
    InfinitelyOften fun n => runTask p (r.label n) := by
  have stays : ∀ n, p ∈ (r.state n).parked := by
    intro n
    induction n with
    | zero => exact parked
    | succ n ih => rw [r.step n]; exact parked_next_of_persistent persistent ih
  apply fair
  intro N
  obtain ⟨n, le, guard⟩ := often N
  exact ⟨n, le, runTask_enabled (Run.wakeInv adequate r init n) (stays n) guard⟩

/-- **Weak fairness suffices for a stable guard**: a guard that holds at `N` and keeps holding until
the firing runs. -/
theorem await_fires_of_stable (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    {N : ℕ} (parked : p ∈ (r.state N).parked) (fair : r.WeaklyFair (runTask p))
    (holds : Guard label (proc p) (r.state N).store (r.state N).born)
    (stable : ∀ n ≥ N, Guard label (proc p) (r.state n).store (r.state n).born →
      ¬ runTask p (r.label n) → Guard label (proc p) (r.state (n + 1)).store (r.state (n + 1)).born) :
    ∃ n ≥ N, runTask p (r.label n) := by
  apply fair.fires N
  intro n le notYet
  have both : Guard label (proc p) (r.state n).store (r.state n).born ∧ p ∈ (r.state n).parked := by
    induction n, le using Nat.le_induction with
    | base => exact ⟨holds, parked⟩
    | succ n le ih =>
        have before := ih fun m lo hi => notYet m lo (by omega)
        have notRun := notYet n le (Nat.lt_succ_self n)
        refine ⟨stable n le before.1 notRun, ?_⟩
        rw [r.step n]
        exact parked_next before.2 notRun
  exact runTask_enabled (Run.wakeInv adequate r init n) both.2 both.1

/-- The commit a step performs, if any. -/
def performed : RLabel O R P → Option (Commit O R)
  | .env d => some d
  | .run _ c => some c
  | _ => none

/-- **A guard without competitors needs only weak fairness.** A row of a parked `await` that has no
predicate queries is fireable at `N`, and until the firing runs no step takes what the row uses
or claims its fresh identities; then the firing runs. -/
theorem await_fires_of_sole_consumer (adequate : ∀ q, NoLostWakeup label index (proc q))
    (r : Run (reactive label proc index envOK)) (init : WakeInv label proc (r.state 0)) {p : P}
    {N : ℕ} (parked : p ∈ (r.state N).parked) (fair : r.WeaklyFair (runTask p)) {c : Commit O R}
    (row : c ∈ (proc p).rows) (positive : c.queries = [])
    (fireable : Fireable label (r.state N).store (r.state N).born c)
    (noCompetition : ∀ n ≥ N, ¬ runTask p (r.label n) → ∀ d, performed (r.label n) = some d →
      Disjoint d.taken (c.taken ∪ c.kept) ∧ Disjoint d.made c.made) :
    ∃ n ≥ N, runTask p (r.label n) := by
  have stays : ∀ n ≥ N, (∀ m, N ≤ m → m < n → ¬ runTask p (r.label m)) →
      Fireable label (r.state n).store (r.state n).born c := by
    intro n le
    induction n, le using Nat.le_induction with
    | base => exact fun _ => fireable
    | succ n le ih =>
        intro notYet
        have before := ih fun m lo hi => notYet m lo (by omega)
        have notRun := notYet n le (Nat.lt_succ_self n)
        rw [r.step n]
        cases labelIs : r.label n with
        | env d =>
            obtain ⟨untouched, ownIds⟩ := noCompetition n le notRun d (by rw [labelIs]; rfl)
            exact fireable_after_commit before positive untouched ownIds
        | run q d =>
            obtain ⟨untouched, ownIds⟩ := noCompetition n le notRun d (by rw [labelIs]; rfl)
            exact fireable_after_commit before positive untouched ownIds
        | sleep q => exact before
        | idle => exact before
  have parkedUntil : ∀ n ≥ N, (∀ m, N ≤ m → m < n → ¬ runTask p (r.label m)) →
      p ∈ (r.state n).parked := by
    intro n le
    induction n, le using Nat.le_induction with
    | base => exact fun _ => parked
    | succ n le ih =>
        intro notYet
        rw [r.step n]
        exact parked_next (ih fun m lo hi => notYet m lo (by omega)) (notYet n le (Nat.lt_succ_self n))
  apply fair.fires N
  intro n le notYet
  exact runTask_enabled (Run.wakeInv adequate r init n) (parkedUntil n le notYet)
    ⟨c, row, stays n le notYet⟩

omit [DecidableEq O] in
/-- The reactive system never blocks: the idle step is always allowed. -/
theorem reactive_nonBlocking [DecidableEq O] (label : O → R) (proc : P → Parked O R)
    (index : Parked O R → Commit O R → Prop) (envOK : Commit O R → Prop) :
    (reactive label proc index envOK).NonBlocking :=
  fun _ => ⟨.idle, trivial⟩

/-- **Strong fairness is implementable**: with finitely many parked firings, the aging scheduler
gives a run that is strongly fair for running every one of them. -/
theorem exists_stronglyFair_reactive_run [Fintype P] [DecidableEq P] (label : O → R)
    (proc : P → Parked O R) (index : Parked O R → Commit O R → Prop) (envOK : Commit O R → Prop)
    (σ : RState O P) :
    ∃ r : Run (reactive label proc index envOK), r.state 0 = σ ∧ ∀ p, r.StronglyFair (runTask p) :=
  exists_stronglyFair_run (fun p => runTask p) (reactive_nonBlocking label proc index envOK) σ

end Liveness

/-! ## Controls -/

namespace Controls

/-! ### A flickering guard: a token held and released -/

/-- Where a token occurrence is: free or held. -/
inductive Spot where
  | free
  | held
  deriving DecidableEq

/-- Even identities are free tokens, odd ones held tokens. -/
def spot (o : ℕ) : Spot := if o % 2 = 0 then .free else .held

/-- The free region. -/
def isFree : Spot → Bool
  | .free => true
  | .held => false

/-- The toggler's step at identity `k`: take it and make the next identity. -/
def toggle (k : ℕ) : Commit ℕ Spot := ⟨{k}, ∅, {k + 1}, []⟩

/-- The await's row at a free token `2k`: take it. -/
def grab (k : ℕ) : Commit ℕ Spot := ⟨{2 * k}, ∅, ∅, []⟩

/-- `true` is the await that takes a free token; `false` is the whenever that holds and releases
the token. -/
def flickerProc : Bool → Parked ℕ Spot
  | true => ⟨{c | ∃ k, c = grab k}, isFree, false⟩
  | false => ⟨{c | ∃ k, c = toggle k}, fun _ => true, true⟩

/-- The flicker system, with the region index and no outside commits. -/
abbrev flickerSystem := reactive spot flickerProc (regionIndex spot) (fun _ => False)

/-- The start: token `0` free, both firings parked and awake. -/
def flickerStart : RState ℕ Bool := ⟨{0}, {0}, Set.univ, Set.univ⟩

theorem flicker_inRegion (p : Bool) : InRegion spot (flickerProc p) := by
  cases p
  · rintro c ⟨k, rfl⟩
    exact ⟨fun _ _ => rfl, by simp [toggle]⟩
  · rintro c ⟨k, rfl⟩
    refine ⟨fun o member => ?_, by simp [grab]⟩
    simp only [grab, Finset.union_empty, Finset.mem_singleton] at member
    subst member
    simp [flickerProc, spot, isFree]

theorem flicker_adequate (p : Bool) : NoLostWakeup spot (regionIndex spot) (flickerProc p) :=
  regionIndex_noLostWakeup (flicker_inRegion p)

theorem flickerStart_inv : WakeInv spot flickerProc flickerStart :=
  ⟨le_rfl, fun _ _ _ => Set.mem_univ _⟩

/-- The await's guard holds at a single token exactly when the token is free. -/
theorem await_guard_iff {m : ℕ} {born : Finset ℕ} :
    Guard spot (flickerProc true) {m} born ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨c, ⟨k, rfl⟩, m', _⟩
    have := m'.taken_subset (Finset.mem_singleton_self (2 * k))
    simp only [Finset.mem_singleton] at this
    omega
  · intro even
    refine ⟨grab (m / 2), ⟨m / 2, rfl⟩, ⟨?_, by simp [grab], by simp [grab], by simp [grab]⟩,
      by simp [grab]⟩
    intro o member
    simp only [grab, Finset.mem_singleton] at member ⊢
    omega

/-- The run in which the whenever toggles forever. -/
def flickerRun : Run flickerSystem where
  state n := ⟨{n}, Finset.range (n + 1), Set.univ, Set.univ⟩
  label n := .run false (toggle n)
  allowed n := by
    refine ⟨Set.mem_univ _, Set.mem_univ _, ⟨n, rfl⟩, ⟨?_, by simp [toggle], by simp [toggle],
      by simp [toggle]⟩, by simp [toggle]⟩
    simp [toggle]
  step n := by
    have store : fire ({n} : Finset ℕ) (toggle n) = {n + 1} := by ext o; simp [toggle, mem_fire]
    have born : Finset.range (n + 1) ∪ (toggle n).made = Finset.range (n + 1 + 1) := by
      ext o; simp [toggle, Finset.mem_range]; omega
    show (⟨{n + 1}, Finset.range (n + 1 + 1), Set.univ, Set.univ⟩ : RState ℕ Bool) =
      ⟨fire {n} (toggle n), Finset.range (n + 1) ∪ (toggle n).made, Set.univ,
        Set.univ ∪ woken flickerProc (regionIndex spot) ⟨{n}, Finset.range (n + 1), Set.univ, Set.univ⟩
          (toggle n)⟩
    rw [store, born, Set.univ_union]

theorem flickerRun_enabled_iff (n : ℕ) :
    flickerSystem.TaskEnabled (runTask true) (flickerRun.state n) ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨a, inTask, allowed⟩
    cases a with
    | run q c =>
        have same : q = true := inTask
        subst same
        obtain ⟨_, _, row, fireable⟩ := allowed
        exact await_guard_iff.1 ⟨c, row, fireable⟩
    | env d => exact absurd inTask id
    | sleep q => exact absurd inTask id
    | idle => exact absurd inTask id
  · intro even
    exact runTask_enabled (index := regionIndex spot) (envOK := fun _ => False)
      ⟨fun o member => by
        change o ∈ ({n} : Finset ℕ) at member
        change o ∈ Finset.range (n + 1)
        simp only [Finset.mem_singleton] at member
        simp [member], fun _ _ _ => Set.mem_univ _⟩
      (Set.mem_univ _)
      (await_guard_iff.2 even)

/-- In the toggling run the await never runs. -/
theorem flicker_await_never_fires : ∀ n, ¬ runTask true (flickerRun.label n) :=
  fun _ same => Bool.false_ne_true same

/-- **The toggling run is weakly fair for both firings**, and the await's guard holds at every
other step. -/
theorem flicker_weaklyFair :
    (∀ p, flickerRun.WeaklyFair (runTask p)) ∧
      InfinitelyOften fun n => Guard spot (flickerProc true) (flickerRun.state n).store
        (flickerRun.state n).born := by
  refine ⟨fun p => ?_, fun N => ⟨2 * N, by omega, await_guard_iff.2 (by omega)⟩⟩
  cases p
  · intro _ N
    exact ⟨N, le_rfl, rfl⟩
  · rintro ⟨N, always⟩
    have := (flickerRun_enabled_iff (2 * N + 1)).1 (always _ (by omega))
    omega

/-- The toggling run is not strongly fair for the await. -/
theorem flicker_not_stronglyFair : ¬ flickerRun.StronglyFair (runTask true) := by
  intro fair
  obtain ⟨n, _, fires⟩ := fair (fun N => ⟨2 * N, by omega, (flickerRun_enabled_iff _).2 (by omega)⟩) 0
  exact flicker_await_never_fires n fires

/-- While the await has not run, the store is one token and the born identities are those up to
it. -/
theorem flicker_shape (r : Run flickerSystem) (start : r.state 0 = flickerStart)
    (never : ∀ n, ¬ runTask true (r.label n)) :
    ∀ n, ∃ m, (r.state n).store = {m} ∧ (r.state n).born = Finset.range (m + 1) ∧
      (r.state n).parked = Set.univ := by
  intro n
  induction n with
  | zero => exact ⟨0, by rw [start]; rfl, by rw [start]; rfl, by rw [start]; rfl⟩
  | succ n ih =>
      obtain ⟨m, store, born, parked⟩ := ih
      have allowed := r.allowed n
      rw [r.step n]
      cases labelIs : r.label n with
      | env d =>
          rw [labelIs] at allowed
          exact absurd allowed.1 id
      | run q c =>
          cases q with
          | true => exact absurd (by rw [labelIs]; rfl : runTask true (r.label n)) (never n)
          | false =>
              rw [labelIs] at allowed
              obtain ⟨_, _, ⟨k, rfl⟩, fireable, _⟩ := allowed
              have kIs : k = m := by
                have := fireable.taken_subset (Finset.mem_singleton_self k)
                simpa [toggle, store] using this
              subst kIs
              refine ⟨k + 1, ?_, ?_, ?_⟩
              · simp only [reactive_next, rNext, store]; ext o; simp [toggle, mem_fire]
              · simp only [reactive_next, rNext, born]; ext o; simp [toggle, Finset.mem_range]; omega
              · simp only [reactive_next, rNext, flickerProc, if_true]; exact parked
      | sleep q => exact ⟨m, store, born, parked⟩
      | idle => exact ⟨m, store, born, parked⟩

/-- **In every strongly fair run of the flicker system the await runs.** -/
theorem flicker_stronglyFair_fires (r : Run flickerSystem) (start : r.state 0 = flickerStart)
    (fair : ∀ p, r.StronglyFair (runTask p)) : ∃ n, runTask true (r.label n) := by
  by_contra never
  push Not at never
  have shape := flicker_shape r start never
  have inv := Run.wakeInv flicker_adequate r (start ▸ flickerStart_inv)
  -- the whenever can always run
  have togglerEnabled : ∀ n, flickerSystem.TaskEnabled (runTask false) (r.state n) := by
    intro n
    obtain ⟨m, store, born, parked⟩ := shape n
    refine runTask_enabled (inv n) (by rw [parked]; trivial) ⟨toggle m, ⟨m, rfl⟩, ⟨?_, by simp [toggle],
      by simp [toggle], by simp [toggle]⟩, ?_⟩
    · rw [store]; simp [toggle]
    · rw [born]; simp [toggle]
  -- the await's guard holds infinitely often
  have often : InfinitelyOften fun n => Guard spot (flickerProc true) (r.state n).store (r.state n).born := by
    by_contra notOften
    obtain ⟨N, never'⟩ := not_infinitelyOften_iff.mp notOften
    obtain ⟨n, le, fires⟩ := (fair false).weaklyFair ⟨0, fun n _ => togglerEnabled n⟩ N
    obtain ⟨m, store, _, _⟩ := shape n
    have odd : m % 2 = 1 := by
      have : ¬ Guard spot (flickerProc true) (r.state n).store (r.state n).born := never' n le
      rw [store, await_guard_iff] at this
      omega
    obtain ⟨m', store', _, _⟩ := shape (n + 1)
    have next : m' = m + 1 := by
      have allowed := r.allowed n
      have stepEq := r.step n
      cases labelIs : r.label n with
      | run q c =>
          have qIs : q = false := by rw [labelIs] at fires; exact fires
          subst qIs
          rw [labelIs] at allowed stepEq
          obtain ⟨_, _, ⟨k, rfl⟩, fireable, _⟩ := allowed
          have kIs : k = m := by
            have := fireable.taken_subset (Finset.mem_singleton_self k)
            simpa [toggle, store] using this
          subst kIs
          have : (r.state (n + 1)).store = {k + 1} := by
            rw [stepEq]; simp only [reactive_next, rNext, store]; ext o; simp [toggle, mem_fire]
          rw [store'] at this
          exact Finset.singleton_injective this
      | env d => rw [labelIs] at fires; exact absurd fires id
      | sleep q => rw [labelIs] at fires; exact absurd fires id
      | idle => rw [labelIs] at fires; exact absurd fires id
    have : ¬ Guard spot (flickerProc true) (r.state (n + 1)).store (r.state (n + 1)).born :=
      never' (n + 1) (by omega)
    rw [store', await_guard_iff] at this
    omega
  obtain ⟨n, fires⟩ := await_fires flicker_adequate r (start ▸ flickerStart_inv)
    (by rw [start]; trivial) (fair true) often
  exact never n fires

/-! ### A lost wakeup: an absence guard keyed on makes -/

section LostWakeup

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- "Add an output unless locked", parked. -/
def unlessLockedProc : Unit → Parked ℕ Atom := fun _ => ⟨{unlessLocked}, isLock, false⟩

/-- The only outside commit: take the lock. -/
def onlyUnlock (d : Commit ℕ Atom) : Prop := d = lockTaker

/-- The start: the lock present, the firing parked and awake. -/
def lockedStart : RState ℕ Unit := ⟨{1}, {1}, Set.univ, Set.univ⟩

/-- After the firing sleeps. -/
def asleep : RState ℕ Unit := ⟨{1}, {1}, Set.univ, Set.univ \ {()}⟩

/-- After the lock is taken, under the makes index. -/
def unlocked : RState ℕ Unit := rNext unlessLockedProc (makesIndex label) asleep (.env lockTaker)

/-- The system with the makes index. -/
abbrev makesSystem := reactive label unlessLockedProc (makesIndex label) onlyUnlock

theorem not_guard_locked : ¬ Guard label (unlessLockedProc ()) {1} {1} := by
  rintro ⟨c, row, m, _⟩
  have same : c = unlessLocked := row
  subst same
  have := m.queries_hold ⟨isLock, ∅⟩ (by simp [unlessLocked])
  revert this
  decide

theorem lockTaker_enabled_locked : Enabled label {1} lockTaker :=
  ⟨by decide, by decide, by decide, by decide, by simp [lockTaker]⟩

/-- Once the lock is taken, the guard holds. -/
theorem guard_unlocked : Guard label (unlessLockedProc ()) (fire {1} lockTaker) ({1} ∪ lockTaker.made) :=
  ⟨unlessLocked, rfl, ⟨by simp [unlessLocked], by simp [unlessLocked], by simp [unlessLocked],
    by simp only [unlessLocked, List.mem_singleton, forall_eq]; decide⟩, by decide⟩

theorem unlocked_asleep : () ∉ unlocked.awake := by
  rintro (⟨_, notMem⟩ | ⟨_, o, made, inRegion⟩)
  · exact notMem rfl
  · simp only [lockTaker, Finset.mem_singleton] at made
    subst made
    revert inRegion
    decide

/-- Sleep, take the lock, then idle forever. -/
def lostRun : Run makesSystem where
  state n := match n with
    | 0 => lockedStart
    | 1 => asleep
    | _ + 2 => unlocked
  label n := match n with
    | 0 => .sleep ()
    | 1 => .env lockTaker
    | _ + 2 => .idle
  allowed n := match n with
    | 0 => ⟨Set.mem_univ _, not_guard_locked⟩
    | 1 => ⟨rfl, lockTaker_enabled_locked, by decide⟩
    | _ + 2 => trivial
  step n := match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem lostRun_never_enabled (n : ℕ) : ¬ makesSystem.TaskEnabled (runTask ()) (lostRun.state n) := by
  rintro ⟨a, inTask, allowed⟩
  cases a with
  | run q c =>
      obtain ⟨_, awake, row, fireable⟩ := allowed
      match n with
      | 0 => exact not_guard_locked ⟨c, row, fireable⟩
      | 1 => exact awake.2 rfl
      | _ + 2 => exact unlocked_asleep awake
  | env d => exact absurd inTask id
  | sleep q => exact absurd inTask id
  | idle => exact absurd inTask id

/-- **The makes index loses the wakeup of an absence guard.** After the lock is taken the guard
holds forever, the run is strongly fair for the firing, and the firing never runs; the makes index
fails `NoLostWakeup` for it. -/
theorem makesIndex_loses_wakeup :
    (∀ n ≥ 2, Guard label (unlessLockedProc ()) (lostRun.state n).store (lostRun.state n).born) ∧
      (∀ n, ¬ runTask () (lostRun.label n)) ∧ lostRun.StronglyFair (runTask ()) ∧
      ¬ NoLostWakeup label (makesIndex label) (unlessLockedProc ()) := by
  refine ⟨fun n le => ?_, fun n => ?_, fun often => ?_, fun adequate => ?_⟩
  · match n, le with
    | _ + 2, _ => exact guard_unlocked
  · match n with
    | 0 => exact id
    | 1 => exact id
    | _ + 2 => exact id
  · obtain ⟨n, _, enabled⟩ := often 0
    exact absurd enabled (lostRun_never_enabled n)
  · obtain ⟨o, made, inRegion⟩ := adequate {1} {1} lockTaker le_rfl lockTaker_enabled_locked
      (by decide) not_guard_locked guard_unlocked
    simp only [lockTaker, Finset.mem_singleton] at made
    subst made
    revert inRegion
    decide

/-- **The region index wakes it**: the same commit, taking the lock, wakes the firing. -/
theorem regionIndex_wakes :
    () ∈ (rNext unlessLockedProc (regionIndex label) asleep (.env lockTaker)).awake :=
  Or.inr ⟨Set.mem_univ _, 1, by simp [lockTaker], rfl⟩

/-- A stale guard check cannot justify parking after an intervening commit,
    even with the region index. Rechecking rejects the sleep; applying that
    unallowed sleep anyway leaves an enabled firing asleep and breaks the
    wake invariant. This is a model control, not an implementation of the
    registration/parking protocol. -/
theorem stale_check_after_unlock_loses_wakeup :
    let after := rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)
    let slept := rNext unlessLockedProc (regionIndex label) after (.sleep ())
    rAllowed label unlessLockedProc onlyUnlock lockedStart (.sleep ()) ∧
      rAllowed label unlessLockedProc onlyUnlock lockedStart (.env lockTaker) ∧
      ¬ rAllowed label unlessLockedProc onlyUnlock after (.sleep ()) ∧
      Guard label (unlessLockedProc ()) slept.store slept.born ∧
      () ∉ slept.awake ∧ ¬ WakeInv label unlessLockedProc slept := by
  dsimp only
  have before : rAllowed label unlessLockedProc onlyUnlock lockedStart (.sleep ()) :=
    ⟨Set.mem_univ _, not_guard_locked⟩
  have committed : rAllowed label unlessLockedProc onlyUnlock lockedStart (.env lockTaker) :=
    ⟨rfl, lockTaker_enabled_locked, by decide⟩
  have ready : Guard label (unlessLockedProc ())
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)).store
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)).born := by
    simpa [rNext, lockedStart] using guard_unlocked
  have rejected : ¬ rAllowed label unlessLockedProc onlyUnlock
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ()) :=
    fun h => h.2 ready
  have stillReady : Guard label (unlessLockedProc ())
      (rNext unlessLockedProc (regionIndex label)
        (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).store
      (rNext unlessLockedProc (regionIndex label)
        (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).born := by
    simpa [rNext] using ready
  have asleep : () ∉ (rNext unlessLockedProc (regionIndex label)
      (rNext unlessLockedProc (regionIndex label) lockedStart (.env lockTaker)) (.sleep ())).awake := by
    simp [rNext]
  refine ⟨before, committed, rejected, stillReady, asleep, ?_⟩
  intro inv
  apply asleep
  apply inv.awake_of_guard ()
  · simp [rNext, lockedStart]
  · exact stillReady

end LostWakeup

/-! ### Matching, fireable rows, regions, positive rows -/

/-- **Matches, positive**: grabbing occurrence `0` matches the store `{0}`. -/
theorem grab_matches : Matches spot {0} (grab 0) :=
  ⟨by decide, by decide, by decide, by simp [grab]⟩

/-- **Matches, negative**: it does not match the empty store. -/
theorem grab_not_matches_empty : ¬ Matches spot ∅ (grab 0) := fun matched =>
  absurd matched.taken_subset (by decide)

/-- **Fireable, negative**: toggling `0` matches `{0}`, but its fresh identity `1` is already
born. (The flicker runs fire positive instances.) -/
theorem toggle_reborn_not_fireable : ¬ Fireable spot {0} {0, 1} (toggle 0) := fun fireable =>
  absurd fireable.2 (by decide)

/-- **Positive rows, positive**: no row of either flicker firing has a predicate query. -/
theorem flicker_positiveRows (p : Bool) : PositiveRows (flickerProc p) := by
  intro c member
  cases p
  · obtain ⟨k, rfl⟩ := member; rfl
  · obtain ⟨k, rfl⟩ := member; rfl

/-- A parked firing whose one row queries the free region. -/
def queryingProc : Parked ℕ Spot := ⟨{⟨∅, ∅, ∅, [⟨isFree, ∅⟩]⟩}, isFree, false⟩

/-- **Positive rows, negative**: its row has a predicate query. -/
theorem queryingProc_not_positive : ¬ PositiveRows queryingProc := fun positive => by
  have := positive _ (Set.mem_singleton _)
  simp at this

/-- A parked firing whose region is the free spots but whose row takes the held spot `1`. -/
def outsideProc : Parked ℕ Spot := ⟨{⟨{1}, ∅, ∅, []⟩}, isFree, false⟩

/-- **In region, negative**: its row takes outside its region. (`flicker_inRegion` is the
positive control.) -/
theorem outsideProc_not_inRegion : ¬ InRegion spot outsideProc := fun inRegion => by
  have := (inRegion _ (Set.mem_singleton _)).1 1 (by simp)
  revert this
  decide

end Controls

/-! ## Split-phase notification and conditional parking

A registration owns one generation of a waiter cell. Rechecking and parking
are separate operations. A notification changes the phase used by the final
conditional park, so an earlier failed check cannot overwrite that notice.
Cancelled or consumer-claimed generations may be registered again; late actions
carry their old generation and are ignored. Claiming a queued wake transfers
its obligation to the consumer; it does not assert that a source row fired.
Queue refusal retains the runnable obligation. A new registration requires a
new source read before rechecking, including after notifications coalesced in
the previous queued generation.

These transitions model individual atomic cell operations and a queue-admission
result. They do not assume that a source mutation already delivered its notice:
the publication-to-notification link, storage lifetime and actual queue protocol
remain obligations. In particular, the guard result passed to `recheck` must
come from a source query; this model proves the handshake, not that query.
-/

namespace ParkingHandshake

inductive Phase where
  | idle | checking | armed | asleep | runnable | queued | claimed | cancelled
  deriving DecidableEq, Repr

structure Cell where
  generation : Nat
  phase : Phase
  deriving DecidableEq, Repr

inductive Action where
  | register
  | recheck (generation : Nat) (ready : Bool)
  | notify (generation : Nat)
  | park (generation : Nat)
  | enqueue (generation : Nat) (accepted : Bool)
  | retryAdmission (generation : Nat)
  | claim (generation : Nat)
  | cancel (generation : Nat)
  deriving DecidableEq, Repr

/-- All actions except registration target an exact registration generation. -/
def Action.generation : Action → Option Nat
  | .register => none
  | .recheck g _ | .notify g | .park g | .enqueue g _ | .retryAdmission g | .claim g | .cancel g => some g

/-- Notification, recheck and park compare the phase in the same atomic
cell. Queue admission is represented by its actual accepted/refused result. -/
def step (cell : Cell) : Action → Cell
  | .register =>
      if cell.phase = .idle ∨ cell.phase = .claimed ∨ cell.phase = .cancelled then
        ⟨cell.generation + 1, .checking⟩ else cell
  | .recheck generation ready =>
      if generation = cell.generation ∧ cell.phase = .checking then
        {cell with phase := if ready then .runnable else .armed} else cell
  | .notify generation =>
      if generation = cell.generation ∧ cell.phase ≠ .idle ∧ cell.phase ≠ .cancelled ∧
          cell.phase ≠ .queued ∧ cell.phase ≠ .claimed then
        {cell with phase := .runnable} else cell
  | .park generation =>
      if generation = cell.generation ∧ cell.phase = .armed then
        {cell with phase := .asleep} else cell
  | .enqueue generation accepted =>
      if generation = cell.generation ∧ cell.phase = .runnable ∧ accepted = true then
        {cell with phase := .queued} else cell
  | .retryAdmission generation =>
      if generation = cell.generation ∧ cell.phase = .queued then
        {cell with phase := .runnable} else cell
  | .claim generation =>
      if generation = cell.generation ∧ cell.phase = .queued then
        {cell with phase := .claimed} else cell
  | .cancel generation =>
      if generation = cell.generation ∧ cell.phase ≠ .claimed then
        {cell with phase := .cancelled} else cell

def execute (cell : Cell) (actions : List Action) : Cell := actions.foldl step cell

/-- A delivered notice remains runnable/queued, has passed to a consumer, is
explicitly cancelled, or belongs to a retired generation. Claim and cancel
are distinct outcomes; neither asserts that a guarded source row fired. -/
def Covered (generation : Nat) (cell : Cell) : Prop :=
  generation < cell.generation ∨
    (generation = cell.generation ∧
      (cell.phase = .runnable ∨ cell.phase = .queued ∨ cell.phase = .claimed ∨ cell.phase = .cancelled))

theorem generation_mono (cell : Cell) (action : Action) :
    cell.generation ≤ (step cell action).generation := by
  cases action <;> simp only [step] <;> split <;> simp

theorem stale_action_ignored (cell : Cell) (action : Action) (generation : Nat)
    (target : action.generation = some generation) (stale : generation ≠ cell.generation) :
    step cell action = cell := by
  cases action <;> simp only [Action.generation, Option.some.injEq, reduceCtorEq] at target
  all_goals subst generation; simp [step, stale]

/-- A successful notification establishes the obligation before any later
park attempt. Already queued work keeps its original queue admission. -/
theorem notify_covered (cell : Cell)
    (active : cell.phase ≠ .idle ∧ cell.phase ≠ .cancelled) :
    Covered cell.generation (step cell (.notify cell.generation)) := by
  rcases cell with ⟨generation, phase⟩
  cases phase <;> simp_all [step, Covered]

/-- Every subsequent protocol operation preserves the delivered notice or
records its explicit disposition. Registration cannot reset an active cell. -/
theorem covered_step {generation : Nat} {cell : Cell} (covered : Covered generation cell)
    (action : Action) : Covered generation (step cell action) := by
  rcases covered with old | ⟨same, phase⟩
  · exact Or.inl (lt_of_lt_of_le old (generation_mono cell action))
  · subst generation
    rcases cell with ⟨generation, status⟩
    rcases phase with rfl | rfl | rfl | rfl
    all_goals cases action <;> simp [step, Covered]
    all_goals split <;> simp_all

theorem covered_execute {generation : Nat} {cell : Cell} (covered : Covered generation cell)
    (actions : List Action) : Covered generation (execute cell actions) := by
  induction actions generalizing cell with
  | nil => exact covered
  | cons action rest ih => exact ih (covered_step covered action)

/-- In the same registration, no suffix of late checks, failed enqueues,
notifications or park attempts can overwrite a delivered wake with sleep. -/
theorem notified_never_sleeps (cell : Cell) (actions : List Action)
    (active : cell.phase ≠ .idle ∧ cell.phase ≠ .cancelled)
    (same : (execute (step cell (.notify cell.generation)) actions).generation = cell.generation) :
    (execute (step cell (.notify cell.generation)) actions).phase ≠ .asleep := by
  have covered := covered_execute (notify_covered cell active) actions
  rcases covered with older | ⟨_, phase⟩
  · omega
  · rcases phase with ready | queued | claimed | cancelled
    · intro asleep; cases ready.symm.trans asleep
    · intro asleep; cases queued.symm.trans asleep
    · intro asleep; cases claimed.symm.trans asleep
    · intro asleep; cases cancelled.symm.trans asleep

theorem enqueue_refusal_retains_cell (cell : Cell) (generation : Nat) :
    step cell (.enqueue generation false) = cell := by simp [step]

theorem enqueue_ready (generation : Nat) :
    step ⟨generation, .runnable⟩ (.enqueue generation true) = ⟨generation, .queued⟩ := by
  simp [step]

/-- An accepted handoff of a runnable waiter is not inserted a second time. -/
theorem queued_is_not_reenqueued (generation : Nat) (accepted : Bool) :
    step ⟨generation, .queued⟩ (.enqueue generation accepted) = ⟨generation, .queued⟩ := by
  simp [step]

/-- Dequeuing transfers the runnable obligation, with a distinct result from
cancelling an unclaimed wake. No source execution is hidden in this step. -/
theorem claim_differs_from_cancellation (generation : Nat) :
    step ⟨generation, .queued⟩ (.claim generation) = ⟨generation, .claimed⟩ ∧
      step ⟨generation, .queued⟩ (.cancel generation) = ⟨generation, .cancelled⟩ := by
  simp [step]

/-- Registering again after a consumer claim allocates a new identity for
the new check; delayed actions still target the retired generation. -/
theorem rearm_after_claim (generation : Nat) :
    step (step ⟨generation, .queued⟩ (.claim generation)) .register =
      ⟨generation + 1, .checking⟩ := by simp [step]

/-- Retaining a notice alone cannot ensure service: arbitrarily many queue
refusals leave the identical runnable obligation. Progress needs a separate
capacity/admission and scheduling argument. -/
theorem repeated_queue_refusal (cell : Cell) (generation count : Nat) :
    execute cell (List.replicate count (.enqueue generation false)) = cell := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, execute, List.foldl_cons, enqueue_refusal_retains_cell]
        using ih

namespace Controls

def initial : Cell := ⟨0, .idle⟩

/-- A quiet registered waiter can park, then a later notice makes it runnable. -/
theorem normal_wait_and_later_notice :
    execute initial [.register, .recheck 1 false, .park 1] = ⟨1, .asleep⟩ ∧
      execute initial [.register, .recheck 1 false, .park 1, .notify 1] = ⟨1, .runnable⟩ := by
  decide

/-- Both notification windows are covered: before the failed recheck and
between the failed recheck and final conditional park. -/
theorem notice_wins_both_windows :
    execute initial [.register, .notify 1, .recheck 1 false, .park 1] = ⟨1, .runnable⟩ ∧
      execute initial [.register, .recheck 1 false, .notify 1, .park 1] = ⟨1, .runnable⟩ := by
  decide

/-- The naïve final store really loses the notice on the same prefix. -/
theorem unconditional_park_overwrites_notice :
    let notified := execute initial [.register, .recheck 1 false, .notify 1]
    notified.phase = .runnable ∧ ({notified with phase := .asleep} : Cell).phase = .asleep ∧
      step notified (.park 1) = notified := by
  decide

/-- Capacity refusal cannot turn runnable work back into a sleeping waiter. -/
theorem failed_queue_admission_preserves_retry :
    execute initial [.register, .recheck 1 false, .notify 1, .enqueue 1 false, .park 1,
      .enqueue 1 true, .enqueue 1 true] = ⟨1, .queued⟩ := by decide

/-- Old notification, completion and parking actions cannot affect a new
registration, even when its physical waiter cell is reused. -/
theorem reused_cell_rejects_late_actions :
    execute initial [.register, .cancel 1, .register, .notify 1, .recheck 1 true,
      .enqueue 1 true, .park 1] = ⟨2, .checking⟩ := by decide

theorem cancelled_waiter_stays_cancelled :
    execute initial [.register, .cancel 1, .notify 1, .recheck 1 true,
      .enqueue 1 true, .park 1] = ⟨1, .cancelled⟩ := by decide

/-- A pre-registration notice is not retained by this cell. A successful
source recheck is therefore essential; the handshake cannot invent it. -/
theorem pre_registration_notice_needs_source_recheck :
    execute initial [.notify 0, .register, .recheck 1 true, .park 1] = ⟨1, .runnable⟩ ∧
      execute initial [.notify 0, .register, .recheck 1 false, .park 1] = ⟨1, .asleep⟩ := by
  decide

/-- A notice coalesced while queued cannot justify reusing that generation's
check after dequeue. Only the new registration's source check can arm it. -/
theorem claimed_waiter_needs_new_registration_check :
    let earlier := [.register, .notify 1, .enqueue 1 true, .notify 1, .claim 1, .register]
    execute initial (earlier ++ [.recheck 1 false, .park 1]) = ⟨2, .checking⟩ ∧
      execute initial (earlier ++ [.recheck 2 true, .park 2]) = ⟨2, .runnable⟩ := by
  decide

end Controls
/-! ### Admission and consumer handoff through the existing bounded queue

The queue owner binds each admitted slot to its registration generation.
Queue membership alone cannot authorize a newer registration in a reused
slot. Refusal keeps the cell runnable; no notification obligation is erased.
An existing matching membership is successful idempotent admission.

These are owner-local service transitions. The queue implementation, physical
link lifetime and synchronization with registration changes retain their own
contracts. A queue visit transfers a wake to a consumer; it does not execute
or complete a source computation. Future offers during a service slice are
queue offers, not proof of authority to register arbitrary source work.
-/

namespace QueueDelivery

open Mettapedia.Machines

structure State where
  ready : ReadyQueue.State
  cells : Nat → Cell
  bound : Nat → Option Nat
  keys : Nat → Option AsyncWait.Identity := fun _ => none
  pending : List AsyncWait.Identity := []

/-- Install one full question key in a vacant slot. A fresh idle cell first
enters the existing registration protocol; a re-armed checking cell already
has its new generation. A live key cannot be overwritten, and an occupied
queue slot cannot be repurposed. The source owner supplies the question serial. -/
def install (slot serial : Nat) (state : State) : Option (AsyncWait.Identity × State) :=
  let cell := if (state.cells slot).phase = .idle then step (state.cells slot) .register else state.cells slot
  if state.keys slot = none ∧ slot ∉ state.ready.tasks ∧ cell.phase = .checking then
    let key : AsyncWait.Identity := ⟨slot, cell.generation, serial⟩
    some (key, { state with
      cells := Function.update state.cells slot cell
      keys := Function.update state.keys slot (some key) })
  else none

/-- Admission uses the actual queue result. A present slot is reusable only
when its saved generation agrees with this runnable registration. -/
def offer (slot : Nat) (state : State) : State :=
  let cell := state.cells slot
  if cell.phase = .runnable then
    let result := ReadyQueue.step state.ready (.admit slot)
    let accepts := result.1.status = 0 ∨
      (result.1.status = 1 ∧ state.bound slot = some cell.generation)
    { ready := result.2
      cells := Function.update state.cells slot
        (step cell (.enqueue cell.generation (decide accepts)))
      bound := if accepts then Function.update state.bound slot (some cell.generation) else state.bound
      keys := state.keys
      pending := state.pending }
  else state

/-- Repeated notifications retain the original FIFO position. Journal
occurrences remain separate; this list coalesces one current wake obligation. -/
def retainWaiting (key : AsyncWait.Identity) (state : State) : State :=
  { state with pending := if key ∈ state.pending then state.pending else state.pending ++ [key] }

/-- Source admission honors an older pending prefix. Its head may retry
without a new event; a later key is retained behind it even if capacity opens.
Successful admission removes that key's pending ticket. -/
def offerCurrent (key : AsyncWait.Identity) (state : State) : State :=
  if state.keys key.owner = some key ∧ state.cells key.owner = ⟨key.generation, .runnable⟩ then
    if state.pending = [] ∨ state.pending.head? = some key then
      let offered := offer key.owner state
      if (offered.cells key.owner).phase = .queued then
        { offered with pending := offered.pending.filter (fun earlier => earlier != key) }
      else retainWaiting key offered
    else retainWaiting key state
  else state

/-- Cancellation retains the key so its own journal can still be retired.
A stale or different question cannot cancel this slot's current obligation. -/
def cancelCurrent (key : AsyncWait.Identity) (state : State) : State :=
  if state.keys key.owner = some key then
    { state with
      cells := Function.update state.cells key.owner (step (state.cells key.owner) (.cancel key.generation))
      pending := state.pending.filter (fun earlier => earlier.owner != key.owner) }
  else state

/-- Rebuild lost volatile admission only when its exact membership is absent.
The queue owner performs this between service slots; a concurrent pop/claim
would require its own synchronized ownership protocol. -/
def recoverAdmission (slot : Nat) (state : State) : State :=
  if slot ∈ state.ready.tasks ∧ state.bound slot = some (state.cells slot).generation then state
  else { state with cells := (Function.update state.cells slot
    (step (state.cells slot) (.retryAdmission (state.cells slot).generation))) }

/-- Deliver a recorded wake for the held registration, then attempt actual
queue admission. The input journal is not retired by this operation. A wake
has unit payload zero; data messages are not silently treated as wake hints. -/
def offerRecorded (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) : State :=
  if state.keys current.owner = some current ∧ inbox.owner = current ∧ event.owner = current ∧ event.payload = 0 ∧
      event ∈ EventPump.pending inbox ∧ (state.cells current.owner).generation = current.generation then
    let repaired := recoverAdmission current.owner state
    let awake := { repaired with cells := (Function.update repaired.cells current.owner
      (step (repaired.cells current.owner) (.notify current.generation))) }
    offerCurrent current awake
  else state

/-- Record through the existing journal owner before attempting volatile
admission. The returned journal still owns every accepted wake obligation. -/
def recordAndOffer (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) : EventPump.Inbox × State :=
  if state.keys current.owner = some current ∧ inbox.owner = current ∧ (state.cells current.owner).generation = current.generation ∧
      (state.cells current.owner).phase ≠ .idle then
    let recorded := EventPump.record inbox event
    (recorded, offerRecorded current recorded event state)
  else (inbox, state)

/-- A notice may be acknowledged only after the same registration has been
claimed by its consumer. This settles delivery of the wake, not source work
or external effects. Obsolete-registration cleanup is a separate disposition. -/
def acknowledgeClaimed (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) : EventPump.Inbox :=
  if state.keys current.owner = some current ∧ inbox.owner = current ∧ event.owner = current ∧ event.payload = 0 ∧
      event ∈ EventPump.pending inbox ∧
      state.cells current.owner = ⟨current.generation, .claimed⟩ then
    EventPump.settle (EventPump.claim inbox event.serial) event.serial
  else inbox

/-- Drain the coalesced wake-only inbox while its consumer claim or explicit
cancellation is still current, then remove old membership and register anew.
The returned old journal retains its records and receipts. It is not a claim
that the source computation or its external effects completed successfully. -/
def retireAndRearm (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (state : State) : EventPump.Inbox × State :=
  if state.keys current.owner = some current ∧ inbox.owner = current ∧ (state.cells current.owner).generation = current.generation ∧
      ((state.cells current.owner).phase = .claimed ∨ (state.cells current.owner).phase = .cancelled) ∧
      (EventPump.pending inbox).all (fun event => event.payload == 0) then
    (EventPump.drain (EventPump.pending inbox).length inbox,
      { state with ready := (ReadyQueue.step state.ready (.remove current.owner)).2
                   cells := Function.update state.cells current.owner (step (state.cells current.owner) .register)
                   keys := Function.update state.keys current.owner none
                   pending := state.pending.filter (fun earlier => earlier.owner != current.owner) })
  else (inbox, state)

/-- Only the generation retained at queue admission may claim this slot. -/
def claimSlot (bound : Nat → Option Nat) (cells : Nat → Cell) (slot : Nat) : Nat → Cell :=
  match bound slot with
  | none => cells
  | some generation => Function.update cells slot (step (cells slot) (.claim generation))

def claimVisits (bound : Nat → Option Nat) (cells : Nat → Cell) (visits : List Nat) : Nat → Cell :=
  visits.foldl (claimSlot bound) cells

/-- Raw queue traffic cannot re-admit a source-owned slot using its old
binding. Such slots must use `offer`, which checks the live registration. -/
def foreignOffers (bound : Nat → Option Nat) (cells : Nat → Cell) (offered : List Nat) : List Nat :=
  offered.filter fun slot => (bound slot).isNone && decide ((cells slot).phase = .idle)

/-- One actual queue visit, with its one-shot retirement and subsequent
offers. The binding stays attached to the slot until a fresh admission
replaces it; visits never reinterpret it as the current generation. -/
def service (offered : List Nat) (state : State) : Option Nat × State :=
  let visited := (ReadyQueue.step state.ready .visit).1.visited
  (visited,
    { ready := ReadyQueue.service state.ready false (foreignOffers state.bound state.cells offered)
      cells := match visited with | none => state.cells | some slot => claimSlot state.bound state.cells slot
      bound := state.bound
      keys := state.keys
      pending := state.pending })

def run : Nat → (Nat → List Nat) → State → List Nat × State
  | 0, _, state => ([], state)
  | slots + 1, offered, state =>
      let head := service (offered 0) state
      let tail := run slots (fun i => offered (i + 1)) head.2
      (head.1.toList ++ tail.1, tail.2)

@[simp] theorem offer_keys (slot : Nat) (state : State) : (offer slot state).keys = state.keys := by
  dsimp only [offer]
  split <;> rfl

@[simp] theorem offer_capacity (slot : Nat) (state : State) :
    (offer slot state).ready.capacity = state.ready.capacity := by
  dsimp only [offer]
  split
  · exact ReadyQueue.step_preserves_capacity state.ready (.admit slot)
  · rfl

@[simp] theorem offer_pending (slot : Nat) (state : State) : (offer slot state).pending = state.pending := by
  dsimp only [offer]
  split <;> rfl

@[simp] theorem retainWaiting_keys (key : AsyncWait.Identity) (state : State) :
    (retainWaiting key state).keys = state.keys := rfl

@[simp] theorem offerCurrent_keys (key : AsyncWait.Identity) (state : State) :
    (offerCurrent key state).keys = state.keys := by
  unfold offerCurrent
  split
  · split
    · dsimp only
      split <;> simp
    · rfl
  · rfl

@[simp] theorem recoverAdmission_keys (slot : Nat) (state : State) :
    (recoverAdmission slot state).keys = state.keys := by
  unfold recoverAdmission
  split <;> rfl

@[simp] theorem offerRecorded_keys (key : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) :
    (offerRecorded key inbox event state).keys = state.keys := by
  unfold offerRecorded
  split <;> simp

@[simp] theorem recordAndOffer_keys (key : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) :
    (recordAndOffer key inbox event state).2.keys = state.keys := by
  unfold recordAndOffer
  split <;> simp

@[simp] theorem run_keys (slots : Nat) (offered : Nat → List Nat) (state : State) :
    (run slots offered state).2.keys = state.keys := by
  induction slots generalizing state offered with
  | zero => rfl
  | succ slots ih => simpa only [run, ih] using (show (service (offered 0) state).2.keys = state.keys from rfl)

theorem install_establishes_key (slot serial : Nat) (before after : State)
    (key : AsyncWait.Identity) (installed : install slot serial before = some (key, after)) :
    key.owner = slot ∧ key.serial = serial ∧ after.keys slot = some key ∧
      after.cells slot = ⟨key.generation, .checking⟩ ∧
      after.ready = before.ready ∧ after.bound = before.bound := by
  let cell := if (before.cells slot).phase = .idle then step (before.cells slot) .register else before.cells slot
  change (if before.keys slot = none ∧ slot ∉ before.ready.tasks ∧ cell.phase = .checking then
    some (⟨slot, cell.generation, serial⟩, { before with
      cells := Function.update before.cells slot cell
      keys := Function.update before.keys slot (some ⟨slot, cell.generation, serial⟩) })
    else none) = some (key, after) at installed
  split at installed
  · rename_i accepted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj installed)
    have cellEq : cell = ⟨cell.generation, .checking⟩ := by
      exact congrArg (Cell.mk cell.generation) accepted.2.2
    exact ⟨rfl, rfl, by simp, by simpa using cellEq, rfl, rfl⟩
  · cases installed

theorem install_live_key_refused (slot serial : Nat) (state : State)
    (key : AsyncWait.Identity) (live : state.keys slot = some key) :
    install slot serial state = none := by simp [install, live]

theorem install_occupied_slot_refused (slot serial : Nat) (state : State)
    (occupied : slot ∈ state.ready.tasks) : install slot serial state = none := by
  simp [install, occupied]

theorem installed_key_unique (state : State) (first second : AsyncWait.Identity)
    (sameSlot : first.owner = second.owner)
    (firstInstalled : state.keys first.owner = some first)
    (secondInstalled : state.keys second.owner = some second) : first = second := by
  rw [sameSlot, secondInstalled] at firstInstalled
  exact (Option.some.inj firstInstalled).symm

theorem other_key_cannot_offer_or_cancel (key : AsyncWait.Identity) (state : State)
    (unowned : state.keys key.owner ≠ some key) :
    offerCurrent key state = state ∧ cancelCurrent key state = state := by
  simp [offerCurrent, cancelCurrent, unowned]

theorem other_key_cannot_record_or_acknowledge (key : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (unowned : state.keys key.owner ≠ some key) :
    recordAndOffer key inbox event state = (inbox, state) ∧
      offerRecorded key inbox event state = state ∧
      acknowledgeClaimed key inbox event state = inbox ∧
      retireAndRearm key inbox state = (inbox, state) := by
  simp [recordAndOffer, offerRecorded, acknowledgeClaimed, retireAndRearm, unowned]

private theorem admission_contains (capacity : Nat) (before after : List Nat) (slot : Nat)
    (admitted : EventPump.admit capacity before slot = some after) : slot ∈ after := by
  unfold EventPump.admit at admitted
  split at admitted
  · contradiction
  · split at admitted
    · cases admitted; assumption
    · split at admitted
      · cases admitted; simp
      · contradiction

theorem offer_refused (state : State) (slot : Nat)
    (full : EventPump.admit state.ready.capacity state.ready.tasks slot = none) :
    offer slot state = state := by
  by_cases runnable : (state.cells slot).phase = .runnable
  · simp [offer, runnable, ReadyQueue.step, full, step]
  · simp [offer, runnable]

/-- Reflection of admission: neither spare capacity nor bare membership
licenses replacing the generation already bound to a present entry. -/
theorem offerCurrent_refused_keeps_queue (key : AsyncWait.Identity) (state : State)
    (full : EventPump.admit state.ready.capacity state.ready.tasks key.owner = none) :
    (offerCurrent key state).cells = state.cells ∧ (offerCurrent key state).ready = state.ready := by
  unfold offerCurrent
  split
  · split
    · dsimp only
      rw [offer_refused state key.owner full]
      split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem offerCurrent_immediate (key : AsyncWait.Identity) (state : State)
    (owned : state.keys key.owner = some key)
    (runnable : state.cells key.owner = ⟨key.generation, .runnable⟩)
    (empty : state.pending = [])
    (queued : (offer key.owner state).cells key.owner = ⟨key.generation, .queued⟩) :
    offerCurrent key state = offer key.owner state := by
  have phase : ((offer key.owner state).cells key.owner).phase = .queued := congrArg Cell.phase queued
  simp only [offerCurrent, if_pos (And.intro owned runnable), empty, true_or, ↓reduceIte, phase,
    offer_pending, List.filter_nil]
  generalize result : offer key.owner state = offered
  have absent : offered.pending = [] := by rw [← result, offer_pending, empty]
  cases offered
  cases absent
  rfl

theorem offer_queued_iff (state : State) (slot generation : Nat)
    (runnable : state.cells slot = ⟨generation, .runnable⟩) :
    (offer slot state).cells slot = ⟨generation, .queued⟩ ↔
      ∃ tasks, EventPump.admit state.ready.capacity state.ready.tasks slot = some tasks ∧
        (slot ∈ state.ready.tasks → state.bound slot = some generation) := by
  cases admitted : EventPump.admit state.ready.capacity state.ready.tasks slot with
  | none => simp [offer, runnable, ReadyQueue.step, admitted, step]
  | some tasks =>
      by_cases member : slot ∈ state.ready.tasks
      · by_cases binding : state.bound slot = some generation <;>
          simp [offer, runnable, ReadyQueue.step, admitted, member, binding, step]
      · simp [offer, runnable, ReadyQueue.step, admitted, member, step]

theorem offer_admitted (state : State) (slot generation : Nat) (tasks : List Nat)
    (runnable : state.cells slot = ⟨generation, .runnable⟩)
    (admitted : EventPump.admit state.ready.capacity state.ready.tasks slot = some tasks)
    (binding : slot ∈ state.ready.tasks → state.bound slot = some generation) :
    (offer slot state).ready.tasks = tasks ∧
      slot ∈ (offer slot state).ready.tasks ∧
      (offer slot state).bound slot = some generation ∧
      (offer slot state).cells slot = ⟨generation, .queued⟩ := by
  have present := admission_contains state.ready.capacity state.ready.tasks tasks slot admitted
  by_cases member : slot ∈ state.ready.tasks
  · have same := binding member
    simpa [offer, runnable, ReadyQueue.step, admitted, member, same, step] using present
  · simpa [offer, runnable, ReadyQueue.step, admitted, member, step] using present

theorem offer_preserves_queue_invariant (state : State) (slot : Nat)
    (valid : ReadyQueue.invariant state.ready) : ReadyQueue.invariant (offer slot state).ready := by
  by_cases runnable : (state.cells slot).phase = .runnable
  · simpa only [offer, runnable, and_self, ↓reduceIte] using
      ReadyQueue.step_preserves_invariant state.ready (.admit slot) valid
  · simpa [offer, runnable] using valid

theorem offer_preserves_other_cell (state : State) (slot other : Nat) (different : other ≠ slot) :
    (offer slot state).cells other = state.cells other := by
  by_cases runnable : (state.cells slot).phase = .runnable <;> simp [offer, runnable, different]

/-- An old present slot is retired by service before the new generation may
reuse it. Refusing this offer preserves the entire runnable state. -/
theorem present_wrong_generation_refuses (state : State) (slot : Nat)
    (member : slot ∈ state.ready.tasks)
    (different : state.bound slot ≠ some (state.cells slot).generation) :
    offer slot state = state := by
  by_cases runnable : (state.cells slot).phase = .runnable
  · by_cases overflow : state.ready.tasks.length > state.ready.capacity
    · exact offer_refused state slot (by simp [EventPump.admit, overflow])
    · simp [offer, runnable, ReadyQueue.step, EventPump.admit, overflow, member, different, step]
  · simp [offer, runnable]

theorem missing_membership_recovers_runnable (state : State) (slot generation : Nat)
    (queued : state.cells slot = ⟨generation, .queued⟩)
    (missing : slot ∉ state.ready.tasks) :
    (recoverAdmission slot state).cells slot = ⟨generation, .runnable⟩ ∧
      (recoverAdmission slot state).ready = state.ready ∧
      (recoverAdmission slot state).bound = state.bound := by
  simp [recoverAdmission, missing, queued, step]

theorem present_membership_not_recovered (state : State) (slot : Nat)
    (member : slot ∈ state.ready.tasks)
    (binding : state.bound slot = some (state.cells slot).generation) :
    recoverAdmission slot state = state := by simp [recoverAdmission, member, binding]

/-- An already handed-off continuation cannot be reopened by queue recovery. -/
theorem claimed_cannot_be_requeued_by_recovery (state : State) (slot generation : Nat)
    (claimed : state.cells slot = ⟨generation, .claimed⟩) :
    recoverAdmission slot state = state := by
  unfold recoverAdmission
  split
  · rfl
  · have unchanged : step (state.cells slot) (.retryAdmission (state.cells slot).generation) = state.cells slot := by
      rw [claimed]
      simp [step]
    simp [unchanged]

theorem nonqueued_recovery_is_inert (state : State) (slot : Nat)
    (notQueued : (state.cells slot).phase ≠ .queued) : recoverAdmission slot state = state := by
  unfold recoverAdmission
  split
  · rfl
  · simp [step, notQueued]

theorem offerRecorded_from_armed (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (owned : state.keys current.owner = some current) (owner : inbox.owner = current)
    (target : event.owner = current) (wake : event.payload = 0)
    (pending : event ∈ EventPump.pending inbox)
    (armed : state.cells current.owner = ⟨current.generation, .armed⟩) :
    offerRecorded current inbox event state =
      offerCurrent current { state with cells := (Function.update state.cells current.owner
        ⟨current.generation, .runnable⟩) } := by
  have repaired := nonqueued_recovery_is_inert state current.owner (by simp [armed])
  simp [offerRecorded, owned, owner, target, wake, pending, armed, repaired, step]

/-- Actual journal acceptance, rather than a supplied pending-bit assumption,
establishes the retained obligation even when ready admission cannot succeed. -/
theorem recorded_notice_remains_pending (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State)
    (owned : state.keys current.owner = some current) (owner : inbox.owner = current) (generation : (state.cells current.owner).generation = current.generation)
    (registered : (state.cells current.owner).phase ≠ .idle)
    (accepted : event.owner = inbox.owner ∧ inbox.phase event.serial = none) :
    event ∈ EventPump.pending (recordAndOffer current inbox event state).1 := by
  simp only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))]
  obtain ⟨member, phase⟩ := EventPump.accepted_event_is_queued inbox event accepted
  exact List.mem_filter.mpr ⟨member, by simp [phase]⟩

theorem wrong_registration_is_not_offered (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (different : event.owner ≠ current) :
    offerRecorded current inbox event state = state := by simp [offerRecorded, different]

theorem unclaimed_notice_not_acknowledged (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State)
    (unclaimed : state.cells current.owner ≠ ⟨current.generation, .claimed⟩) :
    acknowledgeClaimed current inbox event state = inbox := by simp [acknowledgeClaimed, unclaimed]

theorem settled_notice_not_reoffered (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (settled : inbox.phase event.serial = some .settled) :
    offerRecorded current inbox event state = state ∧
      acknowledgeClaimed current inbox event state = inbox := by
  have absent : event ∉ EventPump.pending inbox := by simp [EventPump.pending, settled]
  simp [offerRecorded, acknowledgeClaimed, absent]

theorem stale_notice_not_recorded (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State)
    (stale : (state.cells current.owner).generation ≠ current.generation) :
    recordAndOffer current inbox event state = (inbox, state) := by simp [recordAndOffer, stale]

theorem unregistered_notice_not_recorded (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State)
    (idle : (state.cells current.owner).phase = .idle) :
    recordAndOffer current inbox event state = (inbox, state) := by simp [recordAndOffer, idle]

/-- Every coalesced wake already pending at retirement is disposed before
the new registration begins. Source claim and explicit cancellation remain
distinct caller states; neither is identified with source success. -/
theorem retireAndRearm_drains_and_advances (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (state : State) (owned : state.keys current.owner = some current) (owner : inbox.owner = current)
    (generation : (state.cells current.owner).generation = current.generation)
    (finished : (state.cells current.owner).phase = .claimed ∨ (state.cells current.owner).phase = .cancelled)
    (wakes : (EventPump.pending inbox).all (fun event => event.payload == 0) = true) :
    EventPump.pending (retireAndRearm current inbox state).1 = [] ∧
      (retireAndRearm current inbox state).2.cells current.owner = ⟨current.generation + 1, .checking⟩ ∧
      current.owner ∉ (retireAndRearm current inbox state).2.ready.tasks ∧
      (retireAndRearm current inbox state).2.keys current.owner = none := by
  have drained := EventPump.finite_inbox_drains_within_committed_slots inbox (EventPump.pending inbox).length le_rfl
  rcases finished with finished | finished <;>
    simp [retireAndRearm, owned, owner, generation, finished, wakes, drained, step, ReadyQueue.step]

theorem current_claim_acknowledges_notice (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (owned : state.keys current.owner = some current) (owner : inbox.owner = current)
    (target : event.owner = current) (wake : event.payload = 0)
    (pending : event ∈ EventPump.pending inbox)
    (claimed : state.cells current.owner = ⟨current.generation, .claimed⟩) :
    (acknowledgeClaimed current inbox event state).phase event.serial = some .settled := by
  have phase : inbox.phase event.serial = some .queued := by
    simpa only [decide_eq_true_eq] using (show
      decide (inbox.phase event.serial = some .queued) = true from (List.mem_filter.mp pending).2)
  simp [acknowledgeClaimed, owned, owner, target, wake, pending, claimed, EventPump.claim, EventPump.settle, phase]

theorem claimSlot_other (bound : Nat → Option Nat) (cells : Nat → Cell) (slot other : Nat)
    (different : other ≠ slot) : claimSlot bound cells slot other = cells other := by
  cases binding : bound slot <;> simp [claimSlot, binding, different]

@[simp] theorem foreignOffers_claimSlot (bound : Nat → Option Nat) (cells : Nat → Cell)
    (slot : Nat) (offered : List Nat) :
    foreignOffers bound (claimSlot bound cells slot) offered = foreignOffers bound cells offered := by
  unfold foreignOffers
  apply List.filter_congr
  intro other _
  by_cases same : other = slot
  · subst other
    cases binding : bound slot <;> simp [claimSlot, binding]
  · rw [claimSlot_other bound cells slot other same]

theorem claimSlot_current (bound : Nat → Option Nat) (cells : Nat → Cell) (slot generation : Nat)
    (binding : bound slot = some generation) (queued : cells slot = ⟨generation, .queued⟩) :
    claimSlot bound cells slot slot = ⟨generation, .claimed⟩ := by
  simp [claimSlot, binding, queued, step]

theorem claimSlot_stale (bound : Nat → Option Nat) (cells : Nat → Cell) (slot generation : Nat)
    (binding : bound slot = some generation) (stale : generation ≠ (cells slot).generation) :
    claimSlot bound cells slot = cells := by
  have same := stale_action_ignored (cells slot) (.claim generation) generation rfl stale
  simp [claimSlot, binding, same]

theorem claimSlot_preserves_claimed (bound : Nat → Option Nat) (cells : Nat → Cell)
    (slot target generation : Nat) (claimed : cells target = ⟨generation, .claimed⟩) :
    claimSlot bound cells slot target = ⟨generation, .claimed⟩ := by
  by_cases same : target = slot
  · subst slot
    cases binding : bound target <;> simp [claimSlot, binding, claimed, step]
  · rw [claimSlot_other bound cells slot target same, claimed]

theorem claimVisits_preserve_claimed (bound : Nat → Option Nat) (cells : Nat → Cell)
    (visits : List Nat) (target generation : Nat) (claimed : cells target = ⟨generation, .claimed⟩) :
    claimVisits bound cells visits target = ⟨generation, .claimed⟩ := by
  induction visits generalizing cells with
  | nil => exact claimed
  | cons slot rest ih => exact ih _ (claimSlot_preserves_claimed bound cells slot target generation claimed)

theorem visited_current_generation_is_claimed (bound : Nat → Option Nat) (cells : Nat → Cell)
    (visits : List Nat) (target generation : Nat) (binding : bound target = some generation)
    (queued : cells target = ⟨generation, .queued⟩) (visited : target ∈ visits) :
    claimVisits bound cells visits target = ⟨generation, .claimed⟩ := by
  induction visits generalizing cells with
  | nil => simp at visited
  | cons slot rest ih =>
      by_cases same : target = slot
      · subst slot
        exact claimVisits_preserve_claimed bound _ rest target generation
          (claimSlot_current bound cells target generation binding queued)
      · apply ih _ (by rw [claimSlot_other bound cells slot target same]; exact queued)
        exact (List.mem_cons.mp visited).resolve_left same

/-- The full reference service composes primitive queue operations and
generation-checked handoffs; its queue trace is the existing service trace. -/
theorem run_refines (slots : Nat) (offered : Nat → List Nat) (state : State) :
    run slots offered state =
      let queue := ReadyQueue.serviceRun slots (fun _ => false)
        (fun i => foreignOffers state.bound state.cells (offered i)) state.ready
      (queue.1, { ready := queue.2, cells := claimVisits state.bound state.cells queue.1, bound := state.bound, keys := state.keys, pending := state.pending }) := by
  induction slots generalizing offered state with
  | zero => rfl
  | succ slots ih =>
      simp only [run, ih, ReadyQueue.serviceRun, service]
      cases visited : (ReadyQueue.step state.ready .visit).1.visited <;>
        simp [claimVisits]

/-- Every admitted current-generation entry is handed to its consumer
within the existing queue-length bound, despite continuing tail arrivals.
This counts actual service slots, not wall time or source execution. -/
theorem queued_generation_gets_bounded_handoff (state : State) (target generation : Nat)
    (offered : Nat → List Nat) (valid : ReadyQueue.invariant state.ready)
    (member : target ∈ state.ready.tasks) (binding : state.bound target = some generation)
    (queued : state.cells target = ⟨generation, .queued⟩) :
    ∃ slots ≤ state.ready.tasks.length,
      (run slots offered state).2.cells target = ⟨generation, .claimed⟩ := by
  obtain ⟨slots, bounded, visited⟩ := ReadyQueue.queued_task_gets_bounded_service
    state.ready target (fun _ => false) (fun i => foreignOffers state.bound state.cells (offered i)) valid member
  refine ⟨slots, bounded, ?_⟩
  rw [run_refines]
  exact visited_current_generation_is_claimed state.bound state.cells _ target generation binding queued visited

/-- Actual admission supplies every premise of the bounded handoff result.
This is a service-slot guarantee after admission, with arbitrary later offers;
it is not a promise that a permanently full queue admits every pending waiter. -/
theorem admitted_generation_gets_bounded_handoff (state : State) (target generation : Nat)
    (tasks : List Nat) (offered : Nat → List Nat) (valid : ReadyQueue.invariant state.ready)
    (runnable : state.cells target = ⟨generation, .runnable⟩)
    (admitted : EventPump.admit state.ready.capacity state.ready.tasks target = some tasks)
    (binding : target ∈ state.ready.tasks → state.bound target = some generation) :
    ∃ slots ≤ (offer target state).ready.tasks.length,
      (run slots offered (offer target state)).2.cells target = ⟨generation, .claimed⟩ := by
  obtain ⟨_, member, bound, queued⟩ := offer_admitted state target generation tasks runnable admitted binding
  exact queued_generation_gets_bounded_handoff (offer target state) target generation offered
    (offer_preserves_queue_invariant state target valid) member bound queued

/-- A newly recorded wake survives a full ready queue as both an actual
journal entry and a runnable cell. Retrying admission needs no new arrival. -/
theorem recorded_notice_survives_full_queue (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (owned : state.keys current.owner = some current) (owner : inbox.owner = current)
    (target : event.owner = current) (wake : event.payload = 0)
    (fresh : inbox.phase event.serial = none)
    (armed : state.cells current.owner = ⟨current.generation, .armed⟩)
    (full : EventPump.admit state.ready.capacity state.ready.tasks current.owner = none) :
    event ∈ EventPump.pending (recordAndOffer current inbox event state).1 ∧
      (recordAndOffer current inbox event state).2.cells current.owner = ⟨current.generation, .runnable⟩ ∧
      (recordAndOffer current inbox event state).2.ready = state.ready := by
  have accepted := And.intro (target.trans owner.symm) fresh
  have generation : (state.cells current.owner).generation = current.generation := by simp [armed]
  have registered : (state.cells current.owner).phase ≠ .idle := by simp [armed]
  have pending := recorded_notice_remains_pending current inbox event state owned owner generation registered accepted
  have actualPending : event ∈ EventPump.pending (EventPump.record inbox event) := by
    simpa only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))] using pending
  have sameOwner : (EventPump.record inbox event).owner = current := by
    simp [EventPump.record, accepted, owner]
  have delivered := offerRecorded_from_armed current (EventPump.record inbox event) event state
    owned sameOwner target wake actualPending armed
  refine ⟨pending, ?_⟩
  simp only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))]
  rw [delivered]
  have kept := offerCurrent_refused_keeps_queue current
    { state with cells := Function.update state.cells current.owner ⟨current.generation, .runnable⟩ } full
  rw [kept.1, kept.2]
  simp

/-- The actual journal, admission and generation-bound service compose:
an admitted recorded wake reaches consumer handoff and can then be settled.
The registration remains fixed during this owner-local service slice. -/
theorem recorded_notice_bounded_handoff_and_ack (current : AsyncWait.Identity) (inbox : EventPump.Inbox)
    (event : EventPump.Event) (state : State) (tasks : List Nat) (offered : Nat → List Nat)
    (owned : state.keys current.owner = some current) (owner : inbox.owner = current) (target : event.owner = current) (wake : event.payload = 0)
    (fresh : inbox.phase event.serial = none) (valid : ReadyQueue.invariant state.ready)
    (empty : state.pending = [])
    (armed : state.cells current.owner = ⟨current.generation, .armed⟩)
    (admitted : EventPump.admit state.ready.capacity state.ready.tasks current.owner = some tasks)
    (binding : current.owner ∈ state.ready.tasks → state.bound current.owner = some current.generation) :
    event ∈ EventPump.pending (recordAndOffer current inbox event state).1 ∧
      ∃ slots ≤ (recordAndOffer current inbox event state).2.ready.tasks.length,
        (run slots offered (recordAndOffer current inbox event state).2).2.cells current.owner =
          ⟨current.generation, .claimed⟩ ∧
        (acknowledgeClaimed current (recordAndOffer current inbox event state).1 event
          (run slots offered (recordAndOffer current inbox event state).2).2).phase event.serial = some .settled := by
  have accepted := And.intro (target.trans owner.symm) fresh
  have generation : (state.cells current.owner).generation = current.generation := by simp [armed]
  have registered : (state.cells current.owner).phase ≠ .idle := by simp [armed]
  have pending := recorded_notice_remains_pending current inbox event state owned owner generation registered accepted
  have actualPending : event ∈ EventPump.pending (EventPump.record inbox event) := by
    simpa only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))] using pending
  have sameOwner : (EventPump.record inbox event).owner = current := by
    simp [EventPump.record, accepted, owner]
  let awake : State := { state with cells := (Function.update state.cells current.owner
    ⟨current.generation, .runnable⟩) }
  have queued := (offer_admitted awake current.owner current.generation tasks
    (by simp [awake]) admitted binding).2.2.2
  have immediate := offerCurrent_immediate current awake owned (by simp [awake]) empty queued
  have delivered : (recordAndOffer current inbox event state).2 = offer current.owner awake := by
    rw [← immediate]
    simpa only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))] using
      offerRecorded_from_armed current (EventPump.record inbox event) event state
        owned sameOwner target wake actualPending armed
  obtain ⟨slots, bounded, claimed⟩ := admitted_generation_gets_bounded_handoff awake current.owner
    current.generation tasks offered valid (by simp [awake]) admitted binding
  rw [← delivered] at bounded claimed
  exact ⟨pending, slots, bounded, claimed,
    current_claim_acknowledges_notice current _ event _
      (by simpa only [run_keys, recordAndOffer_keys] using owned)
      (by simpa only [recordAndOffer, if_pos (And.intro owned (And.intro owner (And.intro generation registered)))] using sameOwner)
      target wake pending claimed⟩

/-! ### FIFO admission before fresh queue traffic

The ready prefix and pending source suffix form one logical frontier. Actual
queue admission transfers a key from that suffix to the ready prefix. These
transitions preserve its order; no fairness premise is supplied to the
scheduler. Native operation duration and source execution are separate.
-/

namespace Admission

/-- The observable dispatch order before later arrivals. Full registration
keys stay in the pending suffix; physical ready links use their owner slots. -/
def frontier (state : State) : List Nat := state.ready.tasks ++ state.pending.map AsyncWait.Identity.owner

/-- Ready capacity, unique physical slots and live runnable pending keys.
These are representation invariants, not an assumption of eventual service. -/
structure Valid (state : State) : Prop where
  bounded : state.ready.tasks.length ≤ state.ready.capacity
  unique : (frontier state).Nodup
  waiting : ∀ key ∈ state.pending, state.keys key.owner = some key ∧
    state.cells key.owner = ⟨key.generation, .runnable⟩

theorem Valid.ready {state : State} (valid : Valid state) : ReadyQueue.invariant state.ready :=
  ⟨valid.unique.of_append_left, valid.bounded⟩

theorem Valid.pending_absent {state : State} (valid : Valid state)
    {key : AsyncWait.Identity} (member : key ∈ state.pending) : key.owner ∉ state.ready.tasks := by
  intro present
  exact valid.unique.disjoint present (List.mem_map.mpr ⟨key, member, rfl⟩)

theorem Valid.pending_other {state : State} (valid : Valid state)
    {key other : AsyncWait.Identity} {rest : List AsyncWait.Identity}
    (pending : state.pending = key :: rest) (member : other ∈ rest) : other.owner ≠ key.owner := by
  have unique := valid.unique.of_append_right
  rw [pending, List.map_cons, List.nodup_cons] at unique
  intro same
  exact unique.1 (List.mem_map.mpr ⟨other, member, same⟩)

/-- Any bounded unique ready queue starts with a valid empty backlog. -/
theorem valid_empty_pending (state : State) (ready : ReadyQueue.invariant state.ready)
    (empty : state.pending = []) : Valid state := by
  refine ⟨ready.2, by simpa [frontier, empty] using ready.1, ?_⟩
  intro key member
  simp [empty] at member

/-- Adding a fresh missing source slot derives the representation invariant.
Existing tickets keep their positions; the full key prevents two live tickets
with different serials from aliasing one slot. -/
theorem retainWaiting_valid (state : State) (key : AsyncWait.Identity) (valid : Valid state)
    (owned : state.keys key.owner = some key)
    (runnable : state.cells key.owner = ⟨key.generation, .runnable⟩)
    (missing : key.owner ∉ state.ready.tasks) : Valid (retainWaiting key state) := by
  by_cases present : key ∈ state.pending
  · simpa only [retainWaiting, if_pos present] using valid
  · have absent : key.owner ∉ state.pending.map AsyncWait.Identity.owner := by
      rintro member
      obtain ⟨other, member, same⟩ := List.mem_map.mp member
      have equal := installed_key_unique state other key same (valid.waiting other member).1 owned
      exact present (equal ▸ member)
    have missingFrontier : key.owner ∉ frontier state := by simp [frontier, missing, absent]
    have unique : (frontier state ++ [key.owner]).Nodup := by
      simp [List.nodup_append', valid.unique, missingFrontier]
    refine ⟨valid.bounded, ?_, ?_⟩
    · simpa [frontier, retainWaiting, present, List.append_assoc] using unique
    · intro other member
      simp only [retainWaiting, if_neg present, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · exact valid.waiting other earlier
      · exact ⟨owned, runnable⟩

theorem full_offer_retains_fifo_ticket (state : State) (key : AsyncWait.Identity)
    (owned : state.keys key.owner = some key)
    (runnable : state.cells key.owner = ⟨key.generation, .runnable⟩)
    (full : EventPump.admit state.ready.capacity state.ready.tasks key.owner = none) :
    offerCurrent key state = retainWaiting key state := by
  unfold offerCurrent
  rw [if_pos ⟨owned, runnable⟩]
  split
  · rw [offer_refused state key.owner full]
    simp only [runnable, reduceCtorEq, ↓reduceIte]
  · rfl

theorem full_offer_valid (state : State) (key : AsyncWait.Identity) (valid : Valid state)
    (owned : state.keys key.owner = some key)
    (runnable : state.cells key.owner = ⟨key.generation, .runnable⟩)
    (missing : key.owner ∉ state.ready.tasks)
    (full : EventPump.admit state.ready.capacity state.ready.tasks key.owner = none) :
    Valid (offerCurrent key state) := by
  rw [full_offer_retains_fifo_ticket state key owned runnable full]
  exact retainWaiting_valid state key valid owned runnable missing

/-- The primitive admission really appends one absent runnable slot. -/
theorem offer_fresh (state : State) (key : AsyncWait.Identity)
    (runnable : state.cells key.owner = ⟨key.generation, .runnable⟩)
    (absent : key.owner ∉ state.ready.tasks) (room : state.ready.tasks.length < state.ready.capacity) :
    offer key.owner state =
      { state with ready := ⟨state.ready.capacity, state.ready.tasks ++ [key.owner]⟩
                   cells := Function.update state.cells key.owner ⟨key.generation, .queued⟩
                   bound := Function.update state.bound key.owner (some key.generation) } := by
  simp [offer, runnable, ReadyQueue.step, EventPump.admit, absent, room,
    Nat.not_lt.mpr (Nat.le_of_lt room), step]

theorem move_head (state : State) (key : AsyncWait.Identity) (rest : List AsyncWait.Identity)
    (valid : Valid state) (pending : state.pending = key :: rest)
    (room : state.ready.tasks.length < state.ready.capacity) :
    let after := { offer key.owner state with pending := rest }
    Valid after ∧ frontier after = frontier state ∧ after.ready.capacity = state.ready.capacity := by
  have present : key ∈ state.pending := by simp [pending]
  have admitted := offer_fresh state key (valid.waiting key present).2 (valid.pending_absent present) room
  dsimp only
  rw [admitted]
  have order : frontier
      { state with ready := ⟨state.ready.capacity, state.ready.tasks ++ [key.owner]⟩
                   cells := Function.update state.cells key.owner ⟨key.generation, .queued⟩
                   bound := Function.update state.bound key.owner (some key.generation)
                   pending := rest } = frontier state := by simp [frontier, pending, List.append_assoc]
  refine ⟨⟨by simpa using Nat.succ_le_of_lt room, order ▸ valid.unique, ?_⟩, order, rfl⟩
  intro other member
  have previous := valid.waiting other (by simp [pending, member])
  exact ⟨previous.1, by simpa [valid.pending_other pending member] using previous.2⟩

/-- Promote only after actual admission. Stale or disposed keys are removed
without changing their cells. A full queue retains its oldest pending key. -/
def promote : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match state.pending with
      | [] => state
      | key :: rest =>
          if state.keys key.owner = some key ∧ state.cells key.owner = ⟨key.generation, .runnable⟩ then
            let offered := offer key.owner state
            if (offered.cells key.owner).phase = .queued then
              promote fuel { offered with pending := rest }
            else state
          else promote fuel { state with pending := rest }

/-- Filling preserves the complete logical frontier and the queue bound.
This theorem is for the explicit valid representation above. -/
theorem promote_preserves (fuel : Nat) (state : State) (valid : Valid state) :
    Valid (promote fuel state) ∧ frontier (promote fuel state) = frontier state ∧
      (promote fuel state).ready.capacity = state.ready.capacity := by
  induction fuel generalizing state with
  | zero => exact ⟨valid, rfl, rfl⟩
  | succ fuel ih =>
      cases pending : state.pending with
      | nil =>
          simp only [promote, pending]
          simpa using valid
      | cons key rest =>
          have member : key ∈ state.pending := by simp [pending]
          have live := valid.waiting key member
          by_cases room : state.ready.tasks.length < state.ready.capacity
          · have moved := move_head state key rest valid pending room
            have admitted := offer_fresh state key live.2 (valid.pending_absent member) room
            have queued : ((offer key.owner state).cells key.owner).phase = .queued := by simp [admitted]
            have later := ih _ moved.1
            simpa only [promote, pending, if_pos live, queued, ↓reduceIte] using
              And.intro later.1 (And.intro (later.2.1.trans moved.2.1) (later.2.2.trans moved.2.2))
          · have full : EventPump.admit state.ready.capacity state.ready.tasks key.owner = none := by
              simp [EventPump.admit, Nat.not_lt.mpr valid.bounded, valid.pending_absent member, room]
            have refused := offer_refused state key.owner full
            simp only [promote, pending]
            rw [if_pos live, refused]
            simp only [live.2, reduceCtorEq, ↓reduceIte]
            simpa using valid

/-- With enough promotion attempts, either the backlog is empty or the
physical queue is full. Positive capacity then prevents an idle dispatch
while the logical frontier is nonempty. -/
theorem promote_saturates (fuel : Nat) (state : State) (valid : Valid state)
    (enough : state.pending.length ≤ fuel) :
    (promote fuel state).pending = [] ∨
      (promote fuel state).ready.tasks.length = (promote fuel state).ready.capacity := by
  induction fuel generalizing state with
  | zero => exact Or.inl (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough))
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => exact Or.inl (by simp only [promote, pending])
      | cons key rest =>
          have member : key ∈ state.pending := by simp [pending]
          have live := valid.waiting key member
          by_cases room : state.ready.tasks.length < state.ready.capacity
          · have moved := move_head state key rest valid pending room
            have admitted := offer_fresh state key live.2 (valid.pending_absent member) room
            have queued : ((offer key.owner state).cells key.owner).phase = .queued := by simp [admitted]
            simp only [pending, List.length_cons] at enough
            simpa only [promote, pending, if_pos live, queued, ↓reduceIte] using
              ih { offer key.owner state with pending := rest } moved.1 (by dsimp; omega)
          · have full : EventPump.admit state.ready.capacity state.ready.tasks key.owner = none := by
              simp [EventPump.admit, Nat.not_lt.mpr valid.bounded, valid.pending_absent member, room]
            simp only [promote, pending]
            rw [if_pos live, offer_refused state key.owner full]
            simp only [live.2, reduceCtorEq, ↓reduceIte]
            exact Or.inr (by have bounded := valid.bounded; omega)

/-- Visit/retire the actual ready head before any new arrivals. A filled
queue cannot be empty while its logical frontier still contains work. -/
theorem service_frontier (state : State) (valid : Valid state)
    (filled : state.ready.tasks = [] → state.pending = []) :
    Valid (service [] state).2 ∧
      frontier (service [] state).2 = (frontier state).tail ∧
      (service [] state).1 = (frontier state).head? := by
  have queueValid := ReadyQueue.service_preserves_invariant state.ready false [] valid.ready
  have nextTasks : (service [] state).2.ready.tasks = state.ready.tasks.tail := by
    change (ReadyQueue.service state.ready false []).tasks = state.ready.tasks.tail
    rw [ReadyQueue.service, List.map_nil, ReadyQueue.run, ReadyQueue.afterVisit_tasks state.ready false valid.ready]
    cases state.ready.tasks <;> simp
  have order : frontier (service [] state).2 = (frontier state).tail := by
    change (service [] state).2.ready.tasks ++ state.pending.map AsyncWait.Identity.owner = _
    rw [nextTasks]
    cases tasks : state.ready.tasks with
    | nil => simp [frontier, tasks, filled tasks]
    | cons first rest => simp [frontier, tasks]
  refine ⟨⟨queueValid.2, ?_, ?_⟩, order, ?_⟩
  · rw [order]
    exact valid.unique.tail
  · intro key member
    have prior := valid.waiting key member
    refine ⟨prior.1, ?_⟩
    cases tasks : state.ready.tasks with
    | nil => simpa [service, ReadyQueue.step, tasks] using prior.2
    | cons first rest =>
        have different : key.owner ≠ first := by
          intro same
          exact valid.pending_absent member (by simp [tasks, same])
        simpa only [service, ReadyQueue.step, tasks, List.head?_cons,
          claimSlot_other state.bound state.cells first key.owner different] using prior.2
  · change state.ready.tasks.head? = (frontier state).head?
    cases tasks : state.ready.tasks with
    | nil => simp [frontier, tasks, filled tasks]
    | cons first rest => simp [frontier, tasks]

/-- Fresh foreign offers use the existing primitive admission operations.
They cannot pass a nonempty saturated source backlog. -/
def appendForeign (offered : List Nat) (state : State) : State :=
  if state.pending = [] then
    { state with ready := (ReadyQueue.run
        ((foreignOffers state.bound state.cells offered).map ReadyQueue.Action.admit) state.ready) }
  else state

@[simp] theorem appendForeign_cells (offered : List Nat) (state : State) :
    (appendForeign offered state).cells = state.cells := by unfold appendForeign; split <;> rfl

@[simp] theorem appendForeign_keys (offered : List Nat) (state : State) :
    (appendForeign offered state).keys = state.keys := by unfold appendForeign; split <;> rfl

@[simp] theorem appendForeign_capacity (offered : List Nat) (state : State) :
    (appendForeign offered state).ready.capacity = state.ready.capacity := by
  unfold appendForeign
  split
  · exact ReadyQueue.run_preserves_capacity _ _
  · rfl

theorem appendForeign_preserves (offered : List Nat) (state : State) (valid : Valid state) :
    Valid (appendForeign offered state) ∧
      ∃ arrivals, frontier (appendForeign offered state) = frontier state ++ arrivals := by
  by_cases empty : state.pending = []
  · simp only [appendForeign, if_pos empty]
    have ready := ReadyQueue.trace_preserves_invariant
      ((foreignOffers state.bound state.cells offered).map ReadyQueue.Action.admit) state.ready valid.ready
    refine ⟨⟨ready.2, ?_, ?_⟩, ?_⟩
    · simpa [frontier, empty] using ready.1
    · intro key member
      simp [empty] at member
    · obtain ⟨arrivals, order⟩ := ReadyQueue.admissions_preserve_prefix
        (foreignOffers state.bound state.cells offered) state.ready
      exact ⟨arrivals, by simpa [frontier, empty] using order⟩
  · simp only [appendForeign, if_neg empty]
    exact ⟨valid, [], by simp⟩

/-- Fill, visit, refill, then accept fresh foreign traffic. Capacity released
by the visit is offered to older registered waiters first. -/
def dispatch (offered : List Nat) (state : State) : Option Nat × State :=
  let prepared := promote state.pending.length state
  let visited := service [] prepared
  let refilled := promote visited.2.pending.length visited.2
  (visited.1, appendForeign offered refilled)

@[simp] theorem promote_capacity (fuel : Nat) (state : State) :
    (promote fuel state).ready.capacity = state.ready.capacity := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => simp only [promote, pending]
      | cons key rest =>
          simp only [promote, pending]
          split
          · split
            · simpa only [ih] using offer_capacity key.owner state
            · rfl
          · exact ih _

@[simp] theorem dispatch_capacity (offered : List Nat) (state : State) :
    (dispatch offered state).2.ready.capacity = state.ready.capacity := by
  simp only [dispatch, appendForeign_capacity, promote_capacity,
    service, ReadyQueue.service, ReadyQueue.run_preserves_capacity, ReadyQueue.afterVisit_preserves_capacity]

@[simp] theorem promote_keys (fuel : Nat) (state : State) :
    (promote fuel state).keys = state.keys := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => simp only [promote, pending]
      | cons key rest =>
          simp only [promote, pending]
          split
          · split
            · simpa only [ih] using offer_keys key.owner state
            · rfl
          · exact ih _

@[simp] theorem dispatch_keys (offered : List Nat) (state : State) :
    (dispatch offered state).2.keys = state.keys := by
  simp only [dispatch, appendForeign_keys, promote_keys, service]

/-- Positive capacity plus saturation prevents idle service of a nonempty
logical frontier. This common lemma supplies both order and handoff proofs. -/
theorem promote_no_idle (state : State) (valid : Valid state) (positive : 0 < state.ready.capacity) :
    (promote state.pending.length state).ready.tasks = [] →
      (promote state.pending.length state).pending = [] := by
  intro empty
  rcases promote_saturates state.pending.length state valid le_rfl with done | full
  · exact done
  · rw [empty, promote_capacity] at full
    simp only [List.length_nil] at full
    omega

/-- The scheduling transition refines one independent FIFO service step,
with exactly the suffix accepted by physical queue admission. -/
theorem dispatch_spec (offered : List Nat) (state : State) (valid : Valid state)
    (positive : 0 < state.ready.capacity) :
    Valid (dispatch offered state).2 ∧
      (dispatch offered state).1 = (frontier state).head? ∧
      ∃ arrivals, frontier (dispatch offered state).2 = (frontier state).tail ++ arrivals := by
  let prepared := promote state.pending.length state
  have prep := promote_preserves state.pending.length state valid
  have filled : prepared.ready.tasks = [] → prepared.pending = [] :=
    promote_no_idle state valid positive
  have served := service_frontier prepared prep.1 filled
  let visited := service [] prepared
  have refilled := promote_preserves visited.2.pending.length visited.2 served.1
  have appended := appendForeign_preserves offered _ refilled.1
  refine ⟨appended.1, served.2.2.trans (congrArg List.head? prep.2.1), ?_⟩
  obtain ⟨arrivals, order⟩ := appended.2
  refine ⟨arrivals, ?_⟩
  exact order.trans (congrArg (fun queue => queue ++ arrivals)
    (refilled.2.1.trans (served.2.1.trans (congrArg List.tail prep.2.1))))

/-- Read out the actually accepted suffix; it is not an assumed arrival
schedule or an ideal queue substituted for the concrete transition. -/
def admitted (offered : List Nat) (state : State) : List Nat :=
  (frontier (dispatch offered state).2).drop (frontier state).tail.length

theorem dispatch_frontier (offered : List Nat) (state : State) (valid : Valid state)
    (positive : 0 < state.ready.capacity) :
    frontier (dispatch offered state).2 = (frontier state).tail ++ admitted offered state := by
  obtain ⟨arrivals, order⟩ := (dispatch_spec offered state valid positive).2.2
  simp [admitted, order]

def run : Nat → (Nat → List Nat) → State → List Nat × State
  | 0, _, state => ([], state)
  | slots + 1, offered, state =>
      let head := dispatch (offered 0) state
      let tail := run slots (fun i => offered (i + 1)) head.2
      (head.1.toList ++ tail.1, tail.2)

@[simp] theorem run_keys (slots : Nat) (offered : Nat → List Nat) (state : State) :
    (run slots offered state).2.keys = state.keys := by
  induction slots generalizing state offered with
  | zero => rfl
  | succ slots ih => simpa only [run, ih] using dispatch_keys (offered 0) state

def admittedArrivals (state : State) (offered : Nat → List Nat) : Nat → List Nat
  | 0 => admitted (offered 0) state
  | n + 1 => admittedArrivals (dispatch (offered 0) state).2 (fun i => offered (i + 1)) n

theorem run_refines (slots : Nat) (offered : Nat → List Nat) (state : State)
    (valid : Valid state) (positive : 0 < state.ready.capacity) :
    (run slots offered state).1 = CooperativeQueue.servicesRetiring slots (fun _ => false)
      (admittedArrivals state offered) (frontier state) := by
  induction slots generalizing offered state with
  | zero => rfl
  | succ slots ih =>
      have spec := dispatch_spec (offered 0) state valid positive
      have order := dispatch_frontier (offered 0) state valid positive
      simp only [run, ih _ _ spec.1 (by simpa using positive), spec.2.1]
      rw [order]
      cases queue : frontier state <;>
        simp [CooperativeQueue.servicesRetiring, admittedArrivals]

/-- Every slot already in the ready/pending frontier is visited within its
initial length, even under arbitrary continued foreign offers. No capacity-
admission fairness premise appears: promotion constructs the admissions. -/
theorem frontier_gets_bounded_service (state : State) (offered : Nat → List Nat) (target : Nat)
    (valid : Valid state) (positive : 0 < state.ready.capacity) (member : target ∈ frontier state) :
    ∃ slots ≤ (frontier state).length, target ∈ (run slots offered state).1 := by
  obtain ⟨slots, bounded, visited⟩ := CooperativeQueue.queued_task_gets_bounded_service_with_retirement
    (frontier state) target (fun _ => false) (admittedArrivals state offered) member
  exact ⟨slots, bounded, by rw [run_refines slots offered state valid positive]; exact visited⟩

/-- Follow one full registration through pending admission, an actual ready
binding and consumer handoff. A visit alone is not this invariant. -/
def Tracked (key : AsyncWait.Identity) (state : State) : Prop :=
  state.keys key.owner = some key ∧
    ((state.cells key.owner = ⟨key.generation, .runnable⟩ ∧ key ∈ state.pending) ∨
      (state.cells key.owner = ⟨key.generation, .queued⟩ ∧
        state.bound key.owner = some key.generation ∧ key.owner ∈ state.ready.tasks) ∨
      state.cells key.owner = ⟨key.generation, .claimed⟩)

theorem move_head_tracked (state : State) (first key : AsyncWait.Identity)
    (rest : List AsyncWait.Identity) (valid : Valid state) (pending : state.pending = first :: rest)
    (room : state.ready.tasks.length < state.ready.capacity) (tracked : Tracked key state) :
    Tracked key { offer first.owner state with pending := rest } := by
  have member : first ∈ state.pending := by simp [pending]
  have live := valid.waiting first member
  rw [offer_fresh state first live.2 (valid.pending_absent member) room]
  rcases tracked with ⟨owned, waiting | queued | claimed⟩
  · rcases waiting with ⟨runnable, present⟩
    by_cases same : key = first
    · subst first
      exact ⟨owned, Or.inr (Or.inl ⟨by simp, by simp, by simp⟩)⟩
    · have later : key ∈ rest := by simpa only [pending, List.mem_cons, same, false_or] using present
      have different := valid.pending_other pending later
      exact ⟨owned, Or.inl ⟨by simpa [different] using runnable, later⟩⟩
  · obtain ⟨queued, bound, present⟩ := queued
    have different : key.owner ≠ first.owner := fun same => valid.pending_absent member (same ▸ present)
    exact ⟨owned, Or.inr (Or.inl ⟨by simpa [different] using queued,
      by simpa [different] using bound, List.mem_append_left _ present⟩)⟩
  · have different : key.owner ≠ first.owner := by
      intro same
      have atFirst : state.cells first.owner = ⟨key.generation, .claimed⟩ := by simpa only [same] using claimed
      have impossible := congrArg Cell.phase (atFirst.symm.trans live.2)
      cases impossible
    exact ⟨owned, Or.inr (Or.inr (by simpa [different] using claimed))⟩

theorem promote_tracked (fuel : Nat) (state : State) (key : AsyncWait.Identity)
    (valid : Valid state) (tracked : Tracked key state) : Tracked key (promote fuel state) := by
  induction fuel generalizing state with
  | zero => exact tracked
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => simpa only [promote, pending] using tracked
      | cons first rest =>
          have member : first ∈ state.pending := by simp [pending]
          have live := valid.waiting first member
          simp only [promote, pending]
          rw [if_pos live]
          by_cases room : state.ready.tasks.length < state.ready.capacity
          · have admitted := offer_fresh state first live.2 (valid.pending_absent member) room
            have queued : ((offer first.owner state).cells first.owner).phase = .queued := by simp [admitted]
            rw [if_pos queued]
            exact ih _ (move_head state first rest valid pending room).1
              (move_head_tracked state first key rest valid pending room tracked)
          · have full : EventPump.admit state.ready.capacity state.ready.tasks first.owner = none := by
              simp [EventPump.admit, Nat.not_lt.mpr valid.bounded, valid.pending_absent member, room]
            rw [offer_refused state first.owner full]
            simpa only [live.2, reduceCtorEq, ↓reduceIte] using tracked

theorem offer_preserves_claimed (state : State) (slot target generation : Nat)
    (claimed : state.cells target = ⟨generation, .claimed⟩) :
    (offer slot state).cells target = ⟨generation, .claimed⟩ := by
  by_cases same : target = slot
  · subst slot
    simp [offer, claimed]
  · dsimp only [offer]
    split <;> simpa [same] using claimed

theorem promote_preserves_claimed (fuel : Nat) (state : State) (target generation : Nat)
    (claimed : state.cells target = ⟨generation, .claimed⟩) :
    (promote fuel state).cells target = ⟨generation, .claimed⟩ := by
  induction fuel generalizing state with
  | zero => exact claimed
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => simpa only [promote, pending] using claimed
      | cons key rest =>
          simp only [promote, pending]
          split
          · split
            · exact ih _ (offer_preserves_claimed state key.owner target generation claimed)
            · exact claimed
          · exact ih _ claimed

theorem service_preserves_claimed (state : State) (offered : List Nat) (target generation : Nat)
    (claimed : state.cells target = ⟨generation, .claimed⟩) :
    (service offered state).2.cells target = ⟨generation, .claimed⟩ := by
  cases visited : (ReadyQueue.step state.ready .visit).1.visited with
  | none => simpa only [service, visited] using claimed
  | some slot => simpa only [service, visited] using claimSlot_preserves_claimed state.bound state.cells slot target generation claimed

theorem service_tracked (state : State) (key : AsyncWait.Identity)
    (valid : Valid state) (tracked : Tracked key state) : Tracked key (service [] state).2 := by
  rcases tracked with ⟨owned, waiting | queued | claimed⟩
  · obtain ⟨runnable, member⟩ := waiting
    refine ⟨owned, Or.inl ⟨?_, member⟩⟩
    cases tasks : state.ready.tasks with
    | nil => simpa [service, ReadyQueue.step, tasks] using runnable
    | cons first rest =>
        have different : key.owner ≠ first := by
          intro same
          exact valid.pending_absent member (by simp [tasks, same])
        simpa only [service, ReadyQueue.step, tasks, List.head?_cons,
          claimSlot_other state.bound state.cells first key.owner different] using runnable
  · obtain ⟨queued, bound, member⟩ := queued
    cases tasks : state.ready.tasks with
    | nil => simp [tasks] at member
    | cons first rest =>
        by_cases same : key.owner = first
        · refine ⟨owned, Or.inr (Or.inr ?_)⟩
          simpa only [service, ReadyQueue.step, tasks, List.head?_cons, ← same] using
            claimSlot_current state.bound state.cells key.owner key.generation bound queued
        · have later : key.owner ∈ rest := by simpa only [tasks, List.mem_cons, same, false_or] using member
          refine ⟨owned, Or.inr (Or.inl ⟨?_, bound, ?_⟩)⟩
          · simpa only [service, ReadyQueue.step, tasks, List.head?_cons,
              claimSlot_other state.bound state.cells first key.owner same] using queued
          · change key.owner ∈ (ReadyQueue.service state.ready false []).tasks
            simpa only [ReadyQueue.service, List.map_nil, ReadyQueue.run,
              ReadyQueue.afterVisit_tasks state.ready false valid.ready, tasks,
              Bool.false_eq_true, ↓reduceIte, List.append_nil] using later
  · exact ⟨owned, Or.inr (Or.inr (service_preserves_claimed state [] key.owner key.generation claimed))⟩

theorem service_visits_tracked (state : State) (key : AsyncWait.Identity)
    (valid : Valid state) (tracked : Tracked key state)
    (visited : (service [] state).1 = some key.owner) :
    (service [] state).2.cells key.owner = ⟨key.generation, .claimed⟩ := by
  change (ReadyQueue.step state.ready .visit).1.visited = some key.owner at visited
  have head : state.ready.tasks.head? = some key.owner := visited
  have member : key.owner ∈ state.ready.tasks := by
    cases tasks : state.ready.tasks with
    | nil => simp [tasks] at head
    | cons first rest =>
        have same : first = key.owner := Option.some.inj (by simpa only [tasks, List.head?_cons] using head)
        simp [same]
  rcases tracked.2 with waiting | ⟨queued, bound, _⟩ | claimed
  · exact False.elim (valid.pending_absent waiting.2 member)
  · simpa only [service, visited] using
      claimSlot_current state.bound state.cells key.owner key.generation bound queued
  · exact service_preserves_claimed state [] key.owner key.generation claimed

theorem appendForeign_tracked (offered : List Nat) (state : State) (key : AsyncWait.Identity)
    (tracked : Tracked key state) : Tracked key (appendForeign offered state) := by
  by_cases empty : state.pending = []
  · rw [appendForeign, if_pos empty]
    rcases tracked with ⟨owned, waiting | ⟨queued, bound, member⟩ | claimed⟩
    · exact ⟨owned, Or.inl waiting⟩
    · obtain ⟨arrivals, order⟩ := ReadyQueue.admissions_preserve_prefix
        (foreignOffers state.bound state.cells offered) state.ready
      exact ⟨owned, Or.inr (Or.inl ⟨queued, bound, by
        change key.owner ∈ (ReadyQueue.run _ _).tasks
        rw [order]
        exact List.mem_append_left _ member⟩)⟩
    · exact ⟨owned, Or.inr (Or.inr claimed)⟩
  · simpa only [appendForeign, if_neg empty] using tracked

theorem dispatch_tracked (offered : List Nat) (state : State) (key : AsyncWait.Identity)
    (valid : Valid state) (positive : 0 < state.ready.capacity) (tracked : Tracked key state) :
    Tracked key (dispatch offered state).2 := by
  let prepared := promote state.pending.length state
  have prep := promote_preserves state.pending.length state valid
  have filled : prepared.ready.tasks = [] → prepared.pending = [] :=
    promote_no_idle state valid positive
  have servedValid := (service_frontier prepared prep.1 filled).1
  exact appendForeign_tracked offered _ key
    (promote_tracked _ _ key servedValid
      (service_tracked prepared key prep.1 (promote_tracked _ state key valid tracked)))

theorem dispatch_preserves_claimed (offered : List Nat) (state : State) (target generation : Nat)
    (claimed : state.cells target = ⟨generation, .claimed⟩) :
    (dispatch offered state).2.cells target = ⟨generation, .claimed⟩ := by
  simp only [dispatch, appendForeign_cells]
  exact promote_preserves_claimed _ _ target generation
    (service_preserves_claimed _ [] target generation (promote_preserves_claimed _ state target generation claimed))

theorem dispatch_visits_tracked (offered : List Nat) (state : State) (key : AsyncWait.Identity)
    (valid : Valid state) (tracked : Tracked key state)
    (visited : (dispatch offered state).1 = some key.owner) :
    (dispatch offered state).2.cells key.owner = ⟨key.generation, .claimed⟩ := by
  have prep := promote_preserves state.pending.length state valid
  simp only [dispatch, appendForeign_cells]
  exact promote_preserves_claimed _ _ key.owner key.generation
    (service_visits_tracked _ key prep.1 (promote_tracked _ state key valid tracked) visited)

theorem run_preserves_claimed (slots : Nat) (offered : Nat → List Nat) (state : State)
    (target generation : Nat) (claimed : state.cells target = ⟨generation, .claimed⟩) :
    (run slots offered state).2.cells target = ⟨generation, .claimed⟩ := by
  induction slots generalizing state offered with
  | zero => exact claimed
  | succ slots ih => exact ih _ _ (dispatch_preserves_claimed (offered 0) state target generation claimed)

theorem run_visits_tracked (slots : Nat) (offered : Nat → List Nat) (state : State)
    (key : AsyncWait.Identity) (valid : Valid state) (positive : 0 < state.ready.capacity)
    (tracked : Tracked key state) (visited : key.owner ∈ (run slots offered state).1) :
    (run slots offered state).2.cells key.owner = ⟨key.generation, .claimed⟩ := by
  induction slots generalizing state offered with
  | zero => simp [run] at visited
  | succ slots ih =>
      simp only [run, List.mem_append, Option.mem_toList] at visited
      rcases visited with first | later
      · exact run_preserves_claimed slots _ _ key.owner key.generation
          (dispatch_visits_tracked (offered 0) state key valid tracked first)
      · exact ih _ _ (dispatch_spec (offered 0) state valid positive).1 (by simpa using positive)
          (dispatch_tracked (offered 0) state key valid positive tracked) later

/-- A current runnable source already retained in the FIFO suffix gets an
actual generation-bound consumer handoff. Arbitrary later foreign offers do
not enlarge its initial ready-plus-pending service-slot bound. -/
theorem pending_gets_bounded_handoff (state : State) (key : AsyncWait.Identity)
    (offered : Nat → List Nat) (valid : Valid state) (positive : 0 < state.ready.capacity)
    (member : key ∈ state.pending) :
    ∃ slots ≤ state.ready.tasks.length + state.pending.length,
      (run slots offered state).2.cells key.owner = ⟨key.generation, .claimed⟩ := by
  have frontierMember : key.owner ∈ frontier state :=
    List.mem_append_right _ (List.mem_map.mpr ⟨key, member, rfl⟩)
  obtain ⟨slots, bounded, visited⟩ := frontier_gets_bounded_service state offered key.owner valid positive frontierMember
  have waiting := valid.waiting key member
  refine ⟨slots, by simpa [frontier] using bounded, ?_⟩
  exact run_visits_tracked slots offered state key valid positive ⟨waiting.1, Or.inl ⟨waiting.2, member⟩⟩ visited

end Admission

namespace Controls

def current : AsyncWait.Identity := ⟨7, 1, 99⟩
def inbox : EventPump.Inbox := EventPump.FiniteBurst.initial current
def event (serial : Nat) : EventPump.Event := ⟨serial, current, 0⟩
def initial (capacity : Nat) (tasks : List Nat := []) : State :=
  { ready := ⟨capacity, tasks⟩
    cells := fun slot => if slot = 7 then ⟨1, .armed⟩ else ⟨0, .idle⟩
    bound := fun _ => none
    keys := Function.update (fun _ => none) current.owner (some current) }

def posted (capacity : Nat) (tasks : List Nat := []) :=
  recordAndOffer current inbox (event 101) (initial capacity tasks)

theorem full_queue_retains_record_and_runnable_cell :
    (posted 1 [9]).1.phase 101 = some .queued ∧
      (posted 1 [9]).2.cells 7 = ⟨1, .runnable⟩ ∧
      (posted 1 [9]).2.ready.tasks = [9] := by decide

theorem refused_notice_retries_without_new_arrival :
    let old := posted 1 [9]
    let drained := (service [] old.2).2
    let retried := offerRecorded current old.1 (event 101) drained
    retried.ready.tasks = [7] ∧ retried.cells 7 = ⟨1, .queued⟩ ∧
      (run 1 (fun _ => []) retried).2.cells 7 = ⟨1, .claimed⟩ := by decide

theorem existing_matching_membership_is_success :
    let state : State :=
      { ready := ⟨1, [7]⟩, cells := fun _ => ⟨1, .runnable⟩, bound := fun _ => some 1 }
    (offer 7 state).ready.tasks = [7] ∧ (offer 7 state).cells 7 = ⟨1, .queued⟩ := by decide

theorem stale_membership_is_drained_before_reuse :
    let state : State :=
      { ready := ⟨1, [7]⟩, cells := fun _ => ⟨2, .runnable⟩, bound := fun _ => some 1 }
    let drained := (service [7] state).2
    (offer 7 state).cells 7 = ⟨2, .runnable⟩ ∧
      drained.ready.tasks = [] ∧ drained.cells 7 = ⟨2, .runnable⟩ ∧
      (run 1 (fun _ => []) (offer 7 drained)).2.cells 7 = ⟨2, .claimed⟩ := by decide

theorem old_binding_cannot_claim_new_queued_registration :
    let state : State :=
      { ready := ⟨1, [7]⟩, cells := fun _ => ⟨2, .queued⟩, bound := fun _ => some 1 }
    (service [] state).2.cells 7 = ⟨2, .queued⟩ := by decide

theorem lost_queue_is_rebuilt_from_retained_notice :
    let accepted := posted 1
    let lost : State := { accepted.2 with ready := ⟨1, []⟩ }
    let recovered := offerRecorded current accepted.1 (event 101) lost
    recovered.ready.tasks = [7] ∧ recovered.bound 7 = some 1 ∧
      (run 1 (fun _ => []) recovered).2.cells 7 = ⟨1, .claimed⟩ := by decide

theorem admission_is_not_acknowledgement :
    let accepted := posted 1
    (acknowledgeClaimed current accepted.1 (event 101) accepted.2).phase 101 = some .queued := by decide

theorem claimed_wake_settlement_and_replay :
    let accepted := posted 1
    let claimed := (run 1 (fun _ => []) accepted.2).2
    let settled := acknowledgeClaimed current accepted.1 (event 101) claimed
    settled.phase 101 = some .settled ∧ settled.receipts = [101] ∧
      (offerRecorded current settled (event 101) claimed).ready.tasks = [] ∧
      (acknowledgeClaimed current settled (event 101) claimed).receipts = [101] := by decide

theorem coalesced_wakes_drain_before_rearm :
    let first := posted 1
    let both := recordAndOffer current first.1 (event 102) first.2
    let claimed := (run 1 (fun _ => []) both.2).2
    let retired := retireAndRearm current both.1 claimed
    retired.1.phase 101 = some .settled ∧ retired.1.phase 102 = some .settled ∧
      retired.2.cells 7 = ⟨2, .checking⟩ ∧ retired.2.ready.tasks = [] ∧
      (recordAndOffer current retired.1 (event 103) retired.2).1.phase 103 = none := by decide

theorem cancellation_disposes_wakes_without_claiming_work :
    let accepted := posted 1
    let cancelled : State := { accepted.2 with cells := fun _ => ⟨1, .cancelled⟩ }
    let retired := retireAndRearm current accepted.1 cancelled
    retired.1.phase 101 = some .settled ∧ retired.2.cells 7 = ⟨2, .checking⟩ ∧
      retired.2.ready.tasks = [] := by decide

theorem wrong_question_and_nonwake_data_cannot_trigger :
    let other : EventPump.Event := ⟨101, ⟨7, 1, 100⟩, 0⟩
    let data : EventPump.Event := ⟨102, current, 42⟩
    (recordAndOffer current inbox other (initial 1)).1.phase 101 = none ∧
      (recordAndOffer current inbox data (initial 1)).2.cells 7 = ⟨1, .armed⟩ := by decide

theorem nonwake_data_blocks_blanket_retirement :
    let data : EventPump.Event := ⟨102, current, 42⟩
    let recorded := EventPump.record inbox data
    let claimed : State := { initial 1 with cells := fun _ => ⟨1, .claimed⟩ }
    (retireAndRearm current recorded claimed).1.phase 102 = some .queued ∧
      (retireAndRearm current recorded claimed).2.cells 7 = ⟨1, .claimed⟩ := by decide

theorem serial_mismatch_cannot_touch_registration :
    let other : AsyncWait.Identity := { current with serial := 100 }
    let incoming : EventPump.Event := ⟨102, other, 0⟩
    let pending := EventPump.record (EventPump.FiniteBurst.initial other) incoming
    let handed := (run 1 (fun _ => []) (posted 1).2).2
    (offerRecorded other pending incoming (initial 1)).cells 7 = ⟨1, .armed⟩ ∧
      (recordAndOffer other (EventPump.FiniteBurst.initial other) incoming (initial 1)).1.phase 102 = none ∧
      (acknowledgeClaimed other pending incoming handed).phase 102 = some .queued ∧
      (retireAndRearm other pending handed).2.keys 7 = some current ∧
      (cancelCurrent other (initial 1)).cells 7 = ⟨1, .armed⟩ ∧
      (offerCurrent other { initial 1 with cells := fun _ => ⟨1, .runnable⟩ }).ready.tasks = [] := by decide

theorem installation_cannot_replace_live_or_queued_identity :
    let checking : State := { initial 1 with cells := fun _ => ⟨1, .checking⟩ }
    let occupied : State := { ready := ⟨1, [7]⟩, cells := fun _ => ⟨0, .idle⟩, bound := fun _ => none }
    (install 7 100 checking).isNone = true ∧ (install 7 100 occupied).isNone = true := by decide

theorem retirement_then_install_issues_new_generation :
    let handed := (run 1 (fun _ => []) (posted 1).2).2
    let retired := retireAndRearm current (posted 1).1 handed
    retired.2.keys 7 = none ∧
      (install 7 100 retired.2).map (fun result => result.1) = some ⟨7, 2, 100⟩ := by decide

/-- This valid frontier is produced by the actual full-queue notification
path, rather than supplied as a successful admission assumption. -/
theorem full_notice_frontier_valid : Admission.Valid (posted 1 [9]).2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro key member
  change key ∈ [current] at member
  have same := List.mem_singleton.mp member
  subst key
  exact ⟨by decide, by decide⟩

theorem full_notice_gets_bounded_handoff (offered : Nat → List Nat) :
    ∃ slots ≤ 2, (Admission.run slots offered (posted 1 [9]).2).2.cells 7 = ⟨1, .claimed⟩ := by
  simpa only [show (posted 1 [9]).2.ready.tasks.length + (posted 1 [9]).2.pending.length = 2 from rfl, current] using
    Admission.pending_gets_bounded_handoff (posted 1 [9]).2 current offered
      full_notice_frontier_valid (by decide) (by decide)

theorem refill_cannot_starve_retained_notice :
    (Admission.run 2 (fun _ => [9, 99, 9]) (posted 1 [9]).2).1 = [9, 7] ∧
      (Admission.run 2 (fun _ => [9, 99, 9]) (posted 1 [9]).2).2.cells 7 = ⟨1, .claimed⟩ := by decide

theorem empty_ready_prefix_has_no_spurious_idle_slot :
    let waiting := (service [] (posted 1 [9]).2).2
    (Admission.run 1 (fun _ => [9]) waiting).1 = [7] ∧
      (Admission.run 1 (fun _ => [9]) waiting).2.cells 7 = ⟨1, .claimed⟩ := by decide

def secondKey : AsyncWait.Identity := ⟨8, 1, 100⟩
def paired : State :=
  { ready := ⟨2, [9, 10]⟩
    cells := fun slot => if slot = 7 ∨ slot = 8 then ⟨1, .armed⟩ else ⟨0, .idle⟩
    bound := fun _ => none
    keys := fun slot => if slot = 7 then some current else if slot = 8 then some secondKey else none }
def firstPosted := recordAndOffer current inbox (event 101) paired
def bothPosted := recordAndOffer secondKey (EventPump.FiniteBurst.initial secondKey)
  ⟨102, secondKey, 0⟩ firstPosted.2

theorem two_real_notifications_form_valid_frontier : Admission.Valid bothPosted.2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro key member
  change key ∈ [current, secondKey] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem repeated_notice_keeps_age_and_distinct_waiters :
    let repeated := recordAndOffer current firstPosted.1 (event 103) bothPosted.2
    repeated.2.pending = [current, secondKey] ∧
      repeated.1.phase 101 = some .queued ∧ repeated.1.phase 103 = some .queued ∧
      (Admission.run 4 (fun _ => [9, 10, 88]) repeated.2).1 = [9, 10, 7, 8] ∧
      (Admission.run 4 (fun _ => [9, 10, 88]) repeated.2).2.cells 7 = ⟨1, .claimed⟩ ∧
      (Admission.run 4 (fun _ => [9, 10, 88]) repeated.2).2.cells 8 = ⟨1, .claimed⟩ := by decide

theorem later_ready_offer_cannot_pass_older_pending :
    let freed := (service [] bothPosted.2).2
    let offeredAgain := offerCurrent secondKey freed
    offeredAgain.ready.tasks = [10] ∧ offeredAgain.pending = [current, secondKey] ∧
      offeredAgain.cells 8 = ⟨1, .runnable⟩ := by decide

theorem cancellation_removes_pending_ticket_without_claim :
    let cancelled := cancelCurrent current bothPosted.2
    cancelled.pending = [secondKey] ∧
      (Admission.run 3 (fun _ => [9, 10]) cancelled).2.cells 7 = ⟨1, .cancelled⟩ ∧
      (Admission.run 3 (fun _ => [9, 10]) cancelled).2.cells 8 = ⟨1, .claimed⟩ := by decide

theorem stale_physical_membership_requires_more_than_one_promotion :
    let key : AsyncWait.Identity := ⟨7, 2, 100⟩
    let state : State :=
      { ready := ⟨2, [9, 7]⟩
        cells := fun slot => if slot = 7 then ⟨2, .runnable⟩ else ⟨0, .idle⟩
        bound := fun slot => if slot = 7 then some 1 else none
        keys := fun slot => if slot = 7 then some key else none
        pending := [key] }
    (Admission.dispatch [9, 99] state).2.pending = [key] ∧
      (Admission.dispatch [9, 99] state).2.ready.tasks = [7] ∧
      (Admission.run 3 (fun _ => [9, 99]) state).2.cells 7 = ⟨2, .claimed⟩ := by decide

theorem old_backlog_key_does_not_claim_reused_slot :
    let newer : AsyncWait.Identity := ⟨7, 2, 100⟩
    let state : State :=
      { ready := ⟨1, []⟩, cells := fun _ => ⟨2, .runnable⟩, bound := fun _ => none
        keys := fun _ => some newer, pending := [current] }
    (Admission.dispatch [] state).2.pending = [] ∧
      (Admission.dispatch [] state).2.cells 7 = ⟨2, .runnable⟩ := by decide

theorem serial_spoofed_backlog_key_is_inert :
    let newer : AsyncWait.Identity := ⟨7, 1, 100⟩
    let state : State :=
      { ready := ⟨1, []⟩, cells := fun _ => ⟨1, .runnable⟩, bound := fun _ => none
        keys := fun _ => some newer, pending := [current] }
    (Admission.dispatch [] state).2.pending = [] ∧
      (Admission.dispatch [] state).2.cells 7 = ⟨1, .runnable⟩ := by decide

theorem mismatched_cell_generation_is_not_promoted :
    let state : State :=
      { ready := ⟨1, []⟩, cells := fun _ => ⟨2, .runnable⟩, bound := fun _ => none
        keys := fun _ => some current, pending := [current] }
    (Admission.dispatch [] state).2.pending = [] ∧
      (Admission.dispatch [] state).2.cells 7 = ⟨2, .runnable⟩ := by decide

/-- No positive-capacity premise can be dropped: failed admission keeps
runnable work and its ticket through arbitrarily many scheduling slots. -/
theorem zero_capacity_retains_backlog (slots : Nat) (offered : Nat → List Nat) :
    Admission.run slots offered (posted 0).2 = ([], (posted 0).2) := by
  have fixed : ∀ offered, Admission.dispatch offered (posted 0).2 = (none, (posted 0).2) := by
    intro offered
    rfl
  induction slots generalizing offered with
  | zero => rfl
  | succ slots ih => simpa only [Admission.run, fixed, Option.toList_none, List.nil_append] using ih (fun i => offered (i + 1))

def saturated : State :=
  { ready := ⟨1, [9]⟩
    cells := fun slot => if slot = 7 then ⟨1, .runnable⟩ else ⟨0, .idle⟩
    bound := fun _ => none }

/-- Every service slot runs, yet refilling the capacity before the pending
waiter's offer prevents admission indefinitely. Queue fairness alone is not
fair admission for obligations outside the queue. -/
theorem continuous_foreign_refill_blocks_admission (slots : Nat) :
    (offer 7 (run slots (fun _ => [9]) saturated).2).cells 7 = ⟨1, .runnable⟩ := by
  have fixed : ∀ slots, (run slots (fun _ => [9]) saturated).2 = saturated := by
    intro slots
    induction slots with
    | zero => rfl
    | succ slots ih => simpa only [run, show service [9] saturated = (some 9, saturated) from rfl] using ih
  rw [fixed]
  rfl

#guard (posted 1 [9]).2.cells 7 == ⟨1, .runnable⟩
#guard ((run 1 (fun _ => []) (posted 1).2).2.cells 7) == ⟨1, .claimed⟩
#guard (acknowledgeClaimed current (posted 1).1 (event 101) (posted 1).2).phase 101 == some .queued

end Controls

end QueueDelivery

end ParkingHandshake

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
