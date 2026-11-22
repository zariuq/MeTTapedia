import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# What the semantics owes a 24-hour idle agent: cost obligations of the wait index

An agent parked on a provider, mail, a timer and the operator for a day must cost nothing while
nothing happens, and its memory must not grow with the time it waits. These are statements about
the **cost** of a runtime that implements the wait index of `OccurrenceCommits.CommitProtocol`,
not about timing correctness. Time enters only as idle ticks, in which no commit writes anything.

## The model

Regions are keys `K` (a head symbol, a channel, a path prefix: the coarse regions of the commit
protocol). Each parked firing `f` is registered on the keys it waits on (`regsOf f`). The runtime
keeps the parked firings and one entry per registration (`Index`). Events: an idle tick, a commit
that writes some keys, a firing that parks, and a firing that fires or is cancelled and leaves
its queues (`Event`). Guard evaluations happen only at a commit, one per registration on a key it
writes (`evaluations`).

## The obligations, as theorems

* **No polling: an idle tick costs nothing and changes nothing** (`idle_free`, `idle_irrelevant`):
  a run's evaluations and final index are those of the same run with all idle ticks removed, for
  any number of idle ticks. Work is a function of the events, not of elapsed time.
* **Work per commit is bounded by the registrations it hits** (`evaluations_le`): at most
  `|written| · |parked|`, and exactly the number of registrations on the written keys.
* **The index loses no wakeup** (`index_complete`): a guard on a key whose truth a commit changes
  is registered on a key the commit writes (K's `woken_requires_write`), so it is evaluated at that
  commit. By guard kind (`index_complete_positive`, `index_complete_absence`): a positive guard
  needs only the arrival queues (keys of what is made), an absence guard only the removal queues
  (keys of what is taken), a predicate query every write.
* **Parked memory is bounded by the parked firings, not by time** (`entries_card`): with eager
  withdrawal (a firing that fires leaves all its queues), the index holds exactly the
  registrations of the parked firings, `Σ_f |regsOf f|`; for the agent on four sources that is
  four entries forever (`Controls.eager_agent_flat`).
* **Timers cost one event per armed deadline** (`timer_work_le`): a deadline queue that fires the
  due timers at each tick does at most as much work as there were timers, however many ticks pass.

## Controls

* **Polling grows with time** (`Controls.polling_grows`): a runtime that re-evaluates every parked
  guard every `p` ticks does `n · |parked|` evaluations in `p · n` idle ticks, without bound.
* **Lazy withdrawal leaks per wake** (`Controls.lazy_agent_leaks`): a runtime that, when one arm
  of a four-source choice fires, withdraws only that arm's registration leaves three stale entries
  per wake: `4 + 3n` after `n` wakes, the shape of a choice leak in a waiting worker.
* **Ticks as messages are polling in disguise** (`Controls.ticks_as_messages`): a clock that makes
  one occurrence per real tick wakes every guard on the clock's region at every tick: `T` ticks
  cost `T` evaluations per such guard, where the deadline queue costs one per armed deadline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing.IdleWaitCost

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {K : Type u} [DecidableEq K] {F : Type v} [DecidableEq F]

/-- The wait index: the parked firings, and one entry per registration. -/
structure Index (K : Type u) (F : Type v) where
  parked : Finset F
  entries : Finset (K × F)

/-- Runtime events. -/
inductive Event (K : Type u) (F : Type v) where
  /-- A real tick passes; nothing is written. -/
  | idle
  /-- A commit writes these keys. -/
  | commit (written : Finset K)
  /-- A firing parks on its registrations. -/
  | park (f : F)
  /-- A parked firing fires, or is cancelled, and leaves its queues. -/
  | leave (f : F)

variable (regsOf : F → Finset K)

/-- The registrations of one firing, as index entries. -/
def entriesOf (f : F) : Finset (K × F) := (regsOf f).image fun g => (g, f)

/-- One event, with **eager withdrawal**: a firing that leaves is removed from all its queues. -/
def step (ix : Index K F) : Event K F → Index K F
  | .idle => ix
  | .commit _ => ix
  | .park f => if f ∈ ix.parked then ix else ⟨insert f ix.parked, ix.entries ∪ entriesOf regsOf f⟩
  | .leave f => ⟨ix.parked.erase f, ix.entries.filter fun e => e.2 ≠ f⟩

/-- Guard evaluations of one event: at a commit, one per registration on a written key. -/
def evaluationsOf (ix : Index K F) : Event K F → ℕ
  | .commit written => (ix.entries.filter fun e => e.1 ∈ written).card
  | _ => 0

/-- A run: the final index and the total evaluations. -/
def run (ix : Index K F) : List (Event K F) → Index K F × ℕ
  | [] => (ix, 0)
  | e :: es => let rest := run (step regsOf ix e) es; (rest.1, evaluationsOf ix e + rest.2)

/-- The total guard evaluations of a run. -/
def evaluations (ix : Index K F) (events : List (Event K F)) : ℕ := (run regsOf ix events).2

/-- Is the event an idle tick. -/
def Event.isIdle : Event K F → Bool
  | .idle => true
  | _ => false

/-! ## No polling -/

/-- **An idle tick costs nothing and changes nothing**: removing every idle tick from a run leaves
its final index and its evaluations unchanged. -/
theorem idle_free (ix : Index K F) (events : List (Event K F)) :
    run regsOf ix events = run regsOf ix (events.filter fun e => !e.isIdle) := by
  induction events generalizing ix with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | idle => simpa [run, step, evaluationsOf, Event.isIdle] using ih ix
      | commit w => simp [run, Event.isIdle, ih]
      | park f => simp [run, Event.isIdle, ih]
      | leave f => simp [run, Event.isIdle, ih]

/-- **Any number of idle ticks, anywhere, cost nothing.** -/
theorem idle_irrelevant (ix : Index K F) (before after : List (Event K F)) (n : ℕ) :
    run regsOf ix (before ++ List.replicate n (Event.idle : Event K F) ++ after) =
      run regsOf ix (before ++ after) := by
  have withIdle := idle_free regsOf ix (before ++ List.replicate n (Event.idle : Event K F) ++ after)
  have without := idle_free regsOf ix (before ++ after)
  rw [withIdle, without]
  simp [List.filter_append, Event.isIdle]

/-! ## Exact entries and the memory bound -/

/-- The index holds exactly the registrations of the parked firings. -/
def Exact (ix : Index K F) : Prop := ix.entries = ix.parked.biUnion (entriesOf regsOf)

theorem mem_entriesOf {f : F} {e : K × F} : e ∈ entriesOf regsOf f ↔ e.1 ∈ regsOf f ∧ e.2 = f := by
  constructor
  · intro member
    obtain ⟨g, inRegs, rfl⟩ := Finset.mem_image.mp member
    exact ⟨inRegs, rfl⟩
  · rintro ⟨inRegs, same⟩
    exact Finset.mem_image.mpr ⟨e.1, inRegs, by rw [← same]⟩

theorem exact_step {ix : Index K F} (exact : Exact regsOf ix) (e : Event K F) :
    Exact regsOf (step regsOf ix e) := by
  cases e with
  | idle => exact exact
  | commit w => exact exact
  | park f =>
      simp only [step]
      split_ifs with already
      · exact exact
      · show ix.entries ∪ entriesOf regsOf f = (insert f ix.parked).biUnion (entriesOf regsOf)
        rw [Finset.biUnion_insert, exact, Finset.union_comm]
  | leave f =>
      show ix.entries.filter (fun e => e.2 ≠ f) = (ix.parked.erase f).biUnion (entriesOf regsOf)
      rw [exact]
      ext e
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase, mem_entriesOf]
      constructor
      · rintro ⟨⟨g, parked, inRegs, same⟩, other⟩
        exact ⟨g, ⟨fun gf => other (same.trans gf), parked⟩, inRegs, same⟩
      · rintro ⟨g, ⟨notF, parked⟩, inRegs, same⟩
        exact ⟨⟨g, parked, inRegs, same⟩, fun ef => notF (same.symm.trans ef)⟩

theorem exact_run {ix : Index K F} (exact : Exact regsOf ix) (events : List (Event K F)) :
    Exact regsOf (run regsOf ix events).1 := by
  induction events generalizing ix with
  | nil => exact exact
  | cons e rest ih => exact ih (exact_step regsOf exact e)

/-- **Parked memory is the parked registrations**: with eager withdrawal the index holds
`Σ_{f parked} |regsOf f|` entries, after any run, however long. -/
theorem entries_card {ix : Index K F} (exact : Exact regsOf ix) (events : List (Event K F)) :
    (run regsOf ix events).1.entries.card =
      ∑ f ∈ (run regsOf ix events).1.parked, (regsOf f).card := by
  rw [exact_run regsOf exact events, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun f _ => ?_
    exact Finset.card_image_of_injective _ fun a b same => (Prod.mk.inj same).1
  · intro f _ f' _ apart
    refine Finset.disjoint_left.mpr fun e inF inF' => apart ?_
    exact ((mem_entriesOf regsOf).mp inF).2.symm.trans ((mem_entriesOf regsOf).mp inF').2

/-- The memory bound: at most `|parked| · r` entries when every firing has at most `r`
registrations. -/
theorem entries_card_le {ix : Index K F} (exact : Exact regsOf ix) (events : List (Event K F))
    {r : ℕ} (fewRegs : ∀ f, (regsOf f).card ≤ r) :
    (run regsOf ix events).1.entries.card ≤ (run regsOf ix events).1.parked.card * r := by
  rw [entries_card regsOf exact events]
  exact Finset.sum_le_card_nsmul _ _ _ (fun f _ => fewRegs f) |>.trans (by simp)

/-- **Work per commit is bounded by the registrations it hits**: at most `|written| · |parked|`
evaluations, under exact entries. -/
theorem evaluations_le {ix : Index K F} (exact : Exact regsOf ix) (written : Finset K) :
    evaluationsOf ix (.commit written) ≤ written.card * ix.parked.card := by
  simp only [evaluationsOf]
  have sub : ix.entries.filter (fun e => e.1 ∈ written) ⊆ written ×ˢ ix.parked := by
    intro e member
    obtain ⟨inEntries, inWritten⟩ := Finset.mem_filter.mp member
    rw [exact] at inEntries
    obtain ⟨f, parked, inF⟩ := Finset.mem_biUnion.mp inEntries
    exact Finset.mem_product.mpr ⟨inWritten, ((mem_entriesOf regsOf).mp inF).2 ▸ parked⟩
  exact (Finset.card_le_card sub).trans (Finset.card_product _ _).le

/-! ## The index loses no wakeup -/

section Completeness

variable {O : Type*} [DecidableEq O] {R : Type*} (label : O → R) (key : R → K)

/-- The keys a commit writes. -/
def writtenKeys (d : Commit O R) : Finset K := (d.taken ∪ d.made).image fun o => key (label o)

/-- **The index is complete.** If a commit changes the truth of a test on the region of key `g`,
then `g` is among the keys the commit writes, so every firing registered on `g` is evaluated at
that commit. -/
theorem index_complete {store : Finset O} {d : Commit O R} {g : K} {test : Finset O → Prop}
    (before : ¬ test (regionOf label store fun r => decide (key r = g)))
    (after : test (regionOf label (fire store d) fun r => decide (key r = g))) :
    g ∈ writtenKeys label key d := by
  obtain ⟨o, written, inRegion⟩ := woken_requires_write before after
  exact Finset.mem_image.mpr ⟨o, written, by simpa using inRegion⟩

/-- The keys of what a commit makes: the arrival queues it feeds. -/
def madeKeys (d : Commit O R) : Finset K := d.made.image fun o => key (label o)

/-- The keys of what a commit takes: the removal queues it feeds. -/
def takenKeys (d : Commit O R) : Finset K := d.taken.image fun o => key (label o)

/-- **By guard kind, as in K's wait index**: a positive (upward-closed) guard is woken only through
an arrival queue, a key of something made. -/
theorem index_complete_positive {store : Finset O} {d : Commit O R} {g : K} {test : Finset O → Prop}
    (upward : ∀ ⦃small large : Finset O⦄, small ⊆ large → test small → test large)
    (before : ¬ test (regionOf label store fun r => decide (key r = g)))
    (after : test (regionOf label (fire store d) fun r => decide (key r = g))) :
    g ∈ madeKeys label key d := by
  obtain ⟨o, made, inRegion⟩ := positive_woken_by_make upward before after
  exact Finset.mem_image.mpr ⟨o, made, by simpa using inRegion⟩

/-- An absence (downward-closed) guard is woken only through a removal queue, a key of something
taken. -/
theorem index_complete_absence {store : Finset O} {d : Commit O R} {g : K} {test : Finset O → Prop}
    (downward : ∀ ⦃small large : Finset O⦄, small ⊆ large → test large → test small)
    (before : ¬ test (regionOf label store fun r => decide (key r = g)))
    (after : test (regionOf label (fire store d) fun r => decide (key r = g))) :
    g ∈ takenKeys label key d := by
  obtain ⟨o, taken, inRegion⟩ := absence_woken_by_take downward before after
  exact Finset.mem_image.mpr ⟨o, taken, by simpa using inRegion⟩

omit [DecidableEq F] in
/-- A registered firing is evaluated at a commit that writes one of its keys. -/
theorem registered_evaluated {ix : Index K F} {f : F} {g : K} {written : Finset K}
    (registered : (g, f) ∈ ix.entries) (hit : g ∈ written) :
    (g, f) ∈ ix.entries.filter fun e => e.1 ∈ written :=
  Finset.mem_filter.mpr ⟨registered, hit⟩

end Completeness

/-! ## Timers -/

/-- At real time `t` the deadline queue fires every due timer, once; work is one per due timer. -/
def timerWork : Finset (ℕ × F) → List ℕ → ℕ
  | _, [] => 0
  | timers, t :: ts =>
      (timers.filter fun x => x.1 ≤ t).card + timerWork (timers.filter fun x => ¬ x.1 ≤ t) ts

omit [DecidableEq F] in
/-- **Timers cost one event per armed deadline**, however many ticks pass. -/
theorem timer_work_le (timers : Finset (ℕ × F)) (ticks : List ℕ) :
    timerWork timers ticks ≤ timers.card := by
  induction ticks generalizing timers with
  | nil => exact Nat.zero_le _
  | cons t rest ih =>
      have split := Finset.card_filter_add_card_filter_not (s := timers) (fun x => x.1 ≤ t)
      have := ih (timers.filter fun x => ¬ x.1 ≤ t)
      simp only [timerWork]
      omega

/-! ## Controls -/

namespace Controls

/-- A runtime that re-evaluates every parked guard every `p` ticks: evaluations in `T` idle ticks. -/
def pollRun (p parked : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => pollRun p parked t + if (t + 1) % p = 0 then parked else 0

theorem pollRun_period (p parked n : ℕ) (positive : 0 < p) :
    pollRun p parked (p * n) = n * parked := by
  induction n with
  | zero => simp [pollRun]
  | succ n ih =>
      have block : ∀ j, j < p → pollRun p parked (p * n + j) = n * parked := by
        intro j
        induction j with
        | zero => intro _; simpa using ih
        | succ j ihj =>
            intro lt
            show pollRun p parked (p * n + j) + _ = _
            rw [ihj (by omega)]
            have : (p * n + j + 1) % p ≠ 0 := by
              rw [show p * n + j + 1 = (j + 1) + p * n by ring, Nat.add_mul_mod_self_left,
                Nat.mod_eq_of_lt lt]
              omega
            simp [this]
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have last := block q (by omega)
      rw [show p * (n + 1) = p * n + q + 1 by rw [hq]; ring]
      show pollRun p parked (p * n + q) + _ = _
      rw [last]
      have : (p * n + q + 1) % p = 0 := by
        rw [show p * n + q + 1 = p * (n + 1) by rw [hq]; ring]
        exact Nat.mul_mod_right p (n + 1)
      simp [this]
      ring

/-- **Polling grows with time**: in `p · n` idle ticks a polling runtime does `n · |parked|`
evaluations, without bound, while the index does none. -/
theorem polling_grows (p parked : ℕ) (positive : 0 < p) (nonempty : 0 < parked) (bound : ℕ) :
    bound < pollRun p parked (p * (bound + 1)) ∧
      evaluations (fun _ : Bool => ({true} : Finset Bool)) ⟨{false}, {(true, false)}⟩
        (List.replicate (p * (bound + 1)) (Event.idle : Event Bool Bool)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [pollRun_period p parked _ positive]
    nlinarith
  · unfold evaluations
    rw [idle_free]
    simp [Event.isIdle, run]

/-- The four sources of the idle agent: provider, mail, timer, operator. -/
abbrev Source := Fin 4

/-- Each parked firing of the agent waits on all four sources. -/
def allSources : ℕ → Finset Source := fun _ => Finset.univ

/-- One cycle of the agent: firing `k` fires (by some source) and the agent parks again as
firing `k + 1`. -/
def cycle (k : ℕ) : List (Event Source ℕ) := [.leave k, .park (k + 1)]

/-- `n` cycles after parking firing `0`. -/
def cycles : ℕ → List (Event Source ℕ)
  | 0 => [.park 0]
  | n + 1 => cycles n ++ cycle n

/-- **With eager withdrawal the idle agent's index stays flat**: four entries after any number of
wakes. -/
theorem eager_agent_flat (n : ℕ) :
    (run allSources ⟨∅, ∅⟩ (cycles n)).1.entries.card = 4 ∧
      (run allSources ⟨∅, ∅⟩ (cycles n)).1.parked = {n} := by
  have exact : Exact allSources (⟨∅, ∅⟩ : Index Source ℕ) := by simp [Exact]
  have parkedIs : ∀ n, (run allSources ⟨∅, ∅⟩ (cycles n)).1.parked = {n} := by
    intro n
    induction n with
    | zero => simp [cycles, run, step]
    | succ n ih =>
        have runAppend : ∀ (ix : Index Source ℕ) (l l' : List (Event Source ℕ)),
            (run allSources ix (l ++ l')).1 = (run allSources (run allSources ix l).1 l').1 := by
          intro ix l l'
          induction l generalizing ix with
          | nil => rfl
          | cons e rest ihl => exact ihl _
        rw [cycles, runAppend, cycle]
        simp only [run, step, ih]
        simp
  refine ⟨?_, parkedIs n⟩
  rw [entries_card allSources exact, parkedIs n]
  simp [allSources]

/-- One event with **lazy withdrawal**: a firing that fires leaves only the queue that woke it,
here source `0`. -/
def lazyStep (ix : Index Source ℕ) : Event Source ℕ → Index Source ℕ
  | .leave f => ⟨ix.parked.erase f, ix.entries.erase (0, f)⟩
  | e => step allSources ix e

def lazyRun (ix : Index Source ℕ) : List (Event Source ℕ) → Index Source ℕ
  | [] => ix
  | e :: es => lazyRun (lazyStep ix e) es

theorem lazyRun_append (ix : Index Source ℕ) (l l' : List (Event Source ℕ)) :
    lazyRun (lazyRun ix l) l' = lazyRun ix (l ++ l') := by
  induction l generalizing ix with
  | nil => rfl
  | cons e rest ih => exact ih _

/-- **Lazy withdrawal leaks per wake**: after `n` wakes of the four-source agent, the index holds
`4 + 3n` entries, three of them stale for every wake, and every entry names a firing at most `n`. -/
theorem lazy_agent_leaks (n : ℕ) :
    (lazyRun ⟨∅, ∅⟩ (cycles n)).entries.card = 4 + 3 * n ∧
      (∀ e ∈ (lazyRun ⟨∅, ∅⟩ (cycles n)).entries, e.2 ≤ n) ∧
      (∀ g : Source, (g, n) ∈ (lazyRun ⟨∅, ∅⟩ (cycles n)).entries) ∧
      (lazyRun ⟨∅, ∅⟩ (cycles n)).parked = {n} := by
  induction n with
  | zero =>
      have start : lazyRun ⟨∅, ∅⟩ (cycles 0) = ⟨{0}, entriesOf allSources 0⟩ := by
        simp [cycles, lazyRun, lazyStep, step]
      rw [start]
      refine ⟨by decide, fun e member => le_of_eq ((mem_entriesOf allSources).mp member).2,
        fun g => (mem_entriesOf allSources).mpr ⟨by simp [allSources], rfl⟩, rfl⟩
  | succ n ih =>
      obtain ⟨card, bounded, present, parkedIs⟩ := ih
      rw [cycles, ← lazyRun_append, cycle]
      set ix := lazyRun ⟨∅, ∅⟩ (cycles n)
      have notParked : n + 1 ∉ ix.parked.erase n := by simp [parkedIs]
      have fresh : Disjoint (ix.entries.erase (0, n)) (entriesOf allSources (n + 1)) := by
        refine Finset.disjoint_left.mpr fun e inOld inNew => ?_
        have := bounded e (Finset.mem_of_mem_erase inOld)
        have := ((mem_entriesOf allSources).mp inNew).2
        omega
      have after : lazyRun ix [.leave n, .park (n + 1)] =
          ⟨insert (n + 1) (ix.parked.erase n), ix.entries.erase (0, n) ∪ entriesOf allSources (n + 1)⟩ := by
        simp only [lazyRun, lazyStep, step]
        exact if_neg notParked
      rw [after]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint fresh, Finset.card_erase_of_mem (present 0), card,
          entriesOf, Finset.card_image_of_injective _ (fun a b same => (Prod.mk.inj same).1)]
        simp [allSources]
        omega
      · intro e member
        rcases Finset.mem_union.mp member with old | new
        · have := bounded e (Finset.mem_of_mem_erase old); omega
        · exact le_of_eq ((mem_entriesOf allSources).mp new).2
      · intro g
        exact Finset.mem_union_right _ ((mem_entriesOf allSources).mpr ⟨by simp [allSources], rfl⟩)
      · simp [parkedIs]

/-- **Ticks as messages are polling in disguise**: a clock that makes one occurrence per real tick
writes the clock's key at every tick, so a firing registered on it is evaluated at every tick:
`T` evaluations in `T` ticks. -/
theorem ticks_as_messages (T : ℕ) :
    evaluations (fun _ : Unit => ({()} : Finset Unit)) ⟨{()}, {((), ())}⟩
      (List.replicate T (Event.commit {()})) = T := by
  unfold evaluations
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [List.replicate_succ]
      simp only [run, step, evaluationsOf] at ih ⊢
      rw [ih]
      simp
      omega

/-- **The deadline queue fires each armed deadline once**: two timers due at `5` and `9`, and
`100` ticks: two events. -/
theorem deadline_queue_once :
    timerWork ({(5, 0), (9, 1)} : Finset (ℕ × ℕ)) (List.range 100) = 2 := by
  decide

end Controls

end Mettapedia.GSLT.Timing.IdleWaitCost
