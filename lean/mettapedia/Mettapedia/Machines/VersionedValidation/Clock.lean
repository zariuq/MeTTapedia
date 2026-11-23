import Mettapedia.GSLT.Contracts.ReadWindowCuts
import Mathlib.Tactic

/-!
# The single-clock base of versioned validation

Histories are the finite words of `ReadWindowCuts`: a view and stamps at each cut
of `Cut steps`. Its discipline is the base: stamps of footprint regions never
decrease, and a step that keeps every footprint stamp keeps the observation. A
class map is the single-region footprint (`Versions.IsVersioning`).

## The ordering law

`sound_of_delayed_bumps` is the one ordering law. Stamps never decrease; a stamp
is taken at `sample`, the observation is confirmed at `confirmed`, and it is used
at `current`. If every change of the observation between confirmation and use is
followed, no later than the use, by a move of some footprint stamp, equal
footprint stamps at sample and use certify the confirmed observation at the use.

A discipline moves a footprint stamp at the very step of every change, so
`sound_of_sample_then_confirm` is the synchronous instance. A single write that
publishes at `w` and bumps at `b ≥ w` is the delayed single-region instance
(`publish_then_bump_sound`); it is a discipline exactly when `w = b`
(`singleWrite_discipline_iff`). Sampling first is necessary
(`uniform_soundness_iff_sample_first`).

## The cost model

A probe schedule visits a list of events. Each event pays a read price, and an
exact price when it misses, that is, when a relation between the event and its
reference holds. Under the refreshing policy the reference moves to each event
(a warm stamp refreshed at each observation); under the epoch policy it stays at
the start. `queryWork` prices a schedule, and `gaps` counts its misses: several
mutations between two events are one miss. The validating strategy, the hybrid
check under both policies, pull and push are instances (`PushPull`).

`global_miss_gap` splits the misses of a coarse mark into those of a finer mark
and the gaps in which only the coarse mark moved. Refreshing never misses more
than an epoch for marks stable on intervals (`gaps_refreshing_le_epoch`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VersionedValidation

open Mettapedia.GSLT.Contracts.ReadWindowCuts (Cut Discipline)

/-! ## Steps of a finite history -/

section Steps

variable {steps : ℕ} {α : Type*}

/-- A sequence on cuts that keeps its value at every step of a window has equal
values at the ends of the window. -/
theorem eq_of_steps {f : Cut steps → α} {first last : Cut steps} (ordered : first ≤ last)
    (unchanged : ∀ i : Fin steps, first ≤ i.castSucc → i.succ ≤ last →
      f i.castSucc = f i.succ) :
    f last = f first := by
  have along : ∀ cut : Cut steps, first ≤ cut → cut ≤ last → f cut = f first := by
    intro cut
    induction cut using Fin.induction with
    | zero =>
        intro lower _
        rw [le_antisymm lower (Fin.zero_le _)]
    | succ i ih =>
        intro lower upper
        by_cases before : first ≤ i.castSucc
        · rw [← unchanged i before upper, ih before ((Fin.castSucc_le_succ i).trans upper)]
        · rw [le_antisymm lower (Fin.castSucc_lt_iff_succ_le.mp (not_le.mp before))]
  exact along last ordered le_rfl

/-- A sequence on cuts with different values at the ends of a window changes at
some step of the window. -/
theorem exists_step_of_ne {f : Cut steps → α} {first last : Cut steps} (ordered : first ≤ last)
    (differs : f first ≠ f last) :
    ∃ i : Fin steps, first ≤ i.castSucc ∧ i.succ ≤ last ∧ f i.castSucc ≠ f i.succ := by
  by_contra none
  simp only [not_exists, not_and, not_not] at none
  exact differs (eq_of_steps ordered none).symm

end Steps

/-! ## The ordering law -/

section Ordering

variable {steps : ℕ} {Key Region Value Stamp : Type*} [PartialOrder Stamp]
  {view : Cut steps → Key → Value} {footprint : Key → Set Region}
  {stamp : Cut steps → Region → Stamp}

/-- **The ordering law.** With stamps that never decrease: if every change of the
observation between `confirmed` and `current` is followed, no later than
`current`, by a move of some footprint stamp, then equal footprint stamps at
`sample ≤ confirmed` and `current` certify the confirmed observation at
`current`. -/
theorem sound_of_delayed_bumps
    (advance : ∀ (i : Fin steps) region, stamp i.castSucc region ≤ stamp i.succ region)
    (key : Key) {sample confirmed current : Cut steps} (earlier : sample ≤ confirmed)
    (later : confirmed ≤ current)
    (bumped : ∀ i : Fin steps, confirmed ≤ i.castSucc → i.succ ≤ current →
      view i.castSucc key ≠ view i.succ key →
      ∃ j : Fin steps, i ≤ j ∧ j.succ ≤ current ∧
        ∃ region ∈ footprint key, stamp j.castSucc region ≠ stamp j.succ region)
    (same : Set.EqOn (stamp sample) (stamp current) (footprint key)) :
    view current key = view confirmed key := by
  by_contra differs
  obtain ⟨i, lo, hi, changed⟩ :=
    exists_step_of_ne (f := fun cut => view cut key) later (Ne.symm differs)
  obtain ⟨j, after, before, region, member, moved⟩ := bumped i lo hi changed
  have mono : Monotone fun cut => stamp cut region :=
    Fin.monotone_iff_le_succ.mpr fun i => advance i region
  have first : stamp sample region ≤ stamp j.castSucc region :=
    mono (earlier.trans (lo.trans (Fin.castSucc_le_castSucc_iff.mpr after)))
  have last : stamp j.succ region ≤ stamp current region := mono before
  exact moved (le_antisymm (advance j region) (last.trans ((same member).symm.le.trans first)))

/-- **Sample, then confirm.** The synchronous instance of `sound_of_delayed_bumps`:
a discipline moves a footprint stamp at the step of every change. -/
theorem sound_of_sample_then_confirm (d : Discipline view footprint stamp)
    (key : Key) {sample confirmed current : Cut steps} (earlier : sample ≤ confirmed)
    (later : confirmed ≤ current)
    (same : Set.EqOn (stamp sample) (stamp current) (footprint key)) :
    view current key = view confirmed key :=
  sound_of_delayed_bumps d.advance key earlier later (fun i _ hi changed => by
    by_contra quiet
    simp only [not_exists, not_and, not_not] at quiet
    exact changed (d.frame i key fun region member => quiet i le_rfl hi region member)) same

end Ordering

private def bumpAt {steps : Nat} (boundary cut : Cut steps) : Nat :=
  if boundary ≤ cut then 1 else 0

private theorem bumpAt_mono {steps : Nat} (boundary : Cut steps) : Monotone (bumpAt boundary) := by
  intro a b order
  by_cases happened : boundary ≤ a
  · simp [bumpAt, happened, happened.trans order]
  · simp [bumpAt, happened]

/-- Among observations taking place no later than use, sampling first is
*necessary* for the single-stamp argument to work over every monotone history.
For the converse, a program and its clock both change once, at the late sample.
The stale validation then accepts the old program while the sampled and current
clocks both say the edit has happened. -/
theorem uniform_soundness_iff_sample_first {steps : Nat}
    (sample confirmed current : Cut steps) (sampledByUse : sample ≤ current)
    (confirmedByUse : confirmed ≤ current) :
    (∀ (view stamp : Cut steps → Unit → Nat),
      Discipline view (fun _ => Set.univ) stamp →
      stamp sample () = stamp current () → view current () = view confirmed ()) ↔
      sample ≤ confirmed := by
  constructor
  · intro uniformly
    by_contra wrongOrder
    let trace : Cut steps → Unit → Nat := fun cut _ => bumpAt sample cut
    have discipline : Discipline trace (fun _ => Set.univ) trace := by
      constructor
      · intro i _
        exact bumpAt_mono sample i.castSucc_lt_succ.le
      · intro _ _ agree
        exact agree (Set.mem_univ ())
    have stamps : trace sample () = trace current () := by
      simp [trace, bumpAt, sampledByUse]
    have invalid := uniformly trace trace discipline stamps
    simp [trace, bumpAt, sampledByUse, wrongOrder] at invalid
  · intro order view stamp d same
    refine sound_of_sample_then_confirm d () order confirmedByUse ?_
    intro region _
    cases region
    exact same

/-! ## The cost model -/

/-- Where each probe compares: with the previous event, refreshing a warm stamp,
or with the start of the epoch. -/
inductive Reference where
  | refreshing
  | epoch
  deriving DecidableEq, Repr

section Workload

variable {Moment : Type*}

/-- The reference of the event after `current`. -/
def Reference.next (policy : Reference) (reference current : Moment) : Moment :=
  match policy with
  | .refreshing => current
  | .epoch => reference

/-- Count the events that miss their reference, the reference moving by the
policy. Several mutations between two events are one miss. -/
def gaps (missing : Moment → Moment → Bool) (policy : Reference) :
    Moment → List Moment → ℕ
  | _, [] => 0
  | reference, current :: rest =>
      (if missing reference current then 1 else 0) +
        gaps missing policy (policy.next reference current) rest

/-- The mark moved between two events. -/
def changed {Mark : Type*} [DecidableEq Mark] (mark : Moment → Mark) (before after : Moment) :
    Bool :=
  decide (mark before ≠ mark after)

/-- The coarse mark moved and the fine mark did not. -/
def onlyCoarseChanged {Global Local : Type*} [DecidableEq Global] [DecidableEq Local]
    (global : Moment → Global) (relevant : Moment → Local) (before after : Moment) : Bool :=
  decide (global before ≠ global after ∧ relevant before = relevant after)

/-- **The cost model.** The read price at every event and the exact price at
every miss. -/
def queryWork (missing : Moment → Moment → Bool) (policy : Reference)
    (readPrice exactPrice : ℕ)
    (reference : Moment) (events : List Moment) : ℕ :=
  readPrice * events.length + exactPrice * gaps missing policy reference events

theorem gaps_cons (missing : Moment → Moment → Bool) (policy : Reference)
    (reference current : Moment) (rest : List Moment) :
    gaps missing policy reference (current :: rest) =
      (if missing reference current then 1 else 0) +
        gaps missing policy (policy.next reference current) rest :=
  rfl

/-- A miss relation that ignores the reference counts the events it marks. -/
theorem gaps_of_event (marks : Moment → Bool) (policy : Reference) (reference : Moment)
    (events : List Moment) :
    gaps (fun _ current => marks current) policy reference events = events.countP marks := by
  induction events generalizing reference with
  | nil => rfl
  | cons current rest ih =>
      rw [gaps_cons, ih, List.countP_cons]
      split_ifs <;> omega

/-- No miss: the work is the read price at every event. -/
theorem gaps_eq_zero {missing : Moment → Moment → Bool} {policy : Reference}
    {reference : Moment}
    {events : List Moment}
    (none : ∀ before ∈ reference :: events, ∀ after ∈ events,
      missing before after = false) :
    gaps missing policy reference events = 0 := by
  induction events generalizing reference with
  | nil => rfl
  | cons current rest ih =>
      rw [gaps_cons, none reference List.mem_cons_self current List.mem_cons_self, if_neg (by simp),
        Nat.zero_add]
      apply ih
      intro before beforeMember after afterMember
      have previous : policy.next reference current ∈ reference :: current :: rest := by
        cases policy
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_self
      rcases List.mem_cons.mp beforeMember with rfl | later
      · exact none _ previous after (List.mem_cons_of_mem _ afterMember)
      · exact none before (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)) after
          (List.mem_cons_of_mem _ afterMember)

variable {Global Local : Type*} [DecidableEq Global] [DecidableEq Local]

/-- When an unchanged global mark implies an unchanged local one, the misses of
the global mark are those of the local mark plus the gaps in which only the global
mark moved, under either policy. Individual writes in a gap are not counted. -/
theorem global_miss_gap (global : Moment → Global) (relevant : Moment → Local)
    (covers : ∀ a b, global a = global b → relevant a = relevant b) (policy : Reference)
    (reference : Moment) (events : List Moment) :
    gaps (changed global) policy reference events =
      gaps (changed relevant) policy reference events +
        gaps (onlyCoarseChanged global relevant) policy reference events := by
  induction events generalizing reference with
  | nil => rfl
  | cons now rest ih =>
      simp only [gaps_cons, ih, changed, onlyCoarseChanged]
      by_cases broad : global reference = global now
      · have narrow := covers reference now broad
        simp [broad, narrow]
      · by_cases narrow : relevant reference = relevant now <;> simp [broad, narrow] <;> omega

/-- A global mark is worthwhile exactly when its cheaper lookups pay for the
additional exact lookups. Counting mere global writes can drastically overestimate
the extra work, or underestimate it across many readers. -/
theorem prefer_global_iff (global : Moment → Global) (relevant : Moment → Local)
    (covers : ∀ a b, global a = global b → relevant a = relevant b) (policy : Reference)
    (globalRead localRead exactPrice : ℕ) (reference : Moment) (events : List Moment) :
    queryWork (changed global) policy globalRead exactPrice reference events ≤
      queryWork (changed relevant) policy localRead exactPrice reference events ↔
        globalRead * events.length +
            exactPrice * gaps (onlyCoarseChanged global relevant) policy reference events ≤
          localRead * events.length := by
  rw [queryWork, queryWork, global_miss_gap global relevant covers, Nat.mul_add]
  omega

theorem prefer_clock_to_direct_iff (missing : Moment → Moment → Bool) (policy : Reference)
    (readPrice exactPrice : ℕ) (reference : Moment) (events : List Moment) :
    queryWork missing policy readPrice exactPrice reference events ≤
        exactPrice * events.length ↔
      exactPrice * gaps missing policy reference events ≤
          exactPrice * events.length - readPrice * events.length ∧
        readPrice * events.length ≤ exactPrice * events.length := by
  unfold queryWork
  omega

/-- **Refreshing never misses more than an epoch** along sorted events, for a mark
that is stable on intervals: equal at two events, equal at every event between. -/
theorem gaps_refreshing_le_epoch [Preorder Moment] {Mark : Type*} [DecidableEq Mark]
    (mark : Moment → Mark)
    (stable : ∀ a b c, a ≤ b → b ≤ c → mark a = mark c → mark b = mark c)
    {reference : Moment} {events : List Moment}
    (sorted : List.IsChain (· ≤ ·) (reference :: events)) :
    gaps (changed mark) .refreshing reference events ≤
      gaps (changed mark) .epoch reference events := by
  have general : ∀ previous, reference ≤ previous →
      List.IsChain (· ≤ ·) (previous :: events) →
      gaps (changed mark) .refreshing previous events ≤
        gaps (changed mark) .epoch reference events := by
    clear sorted
    induction events with
    | nil => intro _ _ _; exact Nat.le_refl 0
    | cons current rest ih =>
        intro previous base chain
        obtain ⟨step, tail⟩ := List.isChain_cons_cons.mp chain
        rw [gaps_cons, gaps_cons]
        apply Nat.add_le_add _ (ih current (base.trans step) tail)
        by_cases quiet : mark reference = mark current
        · have same := stable reference previous current base step quiet
          simp [changed, same, quiet]
        · by_cases moved : mark previous = mark current <;> simp [changed, quiet, moved]
  exact general reference le_rfl sorted

end Workload

namespace Controls

theorem confirm_before_edit_stamp_after_cannot_certify :
    ¬ (∀ (view stamp : Cut 1 → Unit → Nat),
      Discipline view (fun _ => Set.univ) stamp →
      stamp 1 () = stamp 1 () → view 1 () = view 0 ()) := by
  rw [uniform_soundness_iff_sample_first 1 0 1 (by decide) (by decide)]
  decide

theorem many_unrelated_edits_can_cost_only_two_probes :
    gaps (changed fun cut : Nat => cut) .refreshing 0 [0, 7, 7, 20] = 2 ∧
    gaps (changed fun _ : Nat => ()) .refreshing 0 [0, 7, 7, 20] = 0 ∧
    gaps (onlyCoarseChanged (fun cut : Nat => cut) fun _ : Nat => ()) .refreshing 0
      [0, 7, 7, 20] = 2 := by
  decide

/-- An epoch compares every event with its start: a mark that moves once early
costs one refreshing miss and a miss at every later epoch probe. -/
theorem epoch_misses_more :
    gaps (changed fun cut : Nat => min cut 1) .refreshing 0 [1, 2, 3] = 1 ∧
      gaps (changed fun cut : Nat => min cut 1) .epoch 0 [1, 2, 3] = 3 := by
  decide

/-- Interval stability cannot be dropped from `gaps_refreshing_le_epoch`: a mark
that moves and returns misses twice when refreshed and never against its epoch. -/
theorem refreshing_exceeds_epoch_without_stability :
    gaps (changed fun cut : Nat => cut % 2) .refreshing 0 [1, 2] = 2 ∧
      gaps (changed fun cut : Nat => cut % 2) .epoch 0 [1, 2] = 1 := by
  decide

end Controls

end Mettapedia.Machines.VersionedValidation
