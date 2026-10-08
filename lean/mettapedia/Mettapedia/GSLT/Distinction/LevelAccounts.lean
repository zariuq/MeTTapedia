import Mettapedia.GSLT.Causality.TraceCostValuation
import Mettapedia.GSLT.Distinction.HistoryGrammar
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Level-indexed accounts and qualified replay

A run has more than one account.  The object's **reference account** is what
the language charges and what a program may read; the host's **work** is what
its execution actually costs; **overhead** is the copying, validation and
recording around it.  Each is its own account of the same runs
(`CategoryTheory.RunAccount`), with its own independently defined meter
(`LevelReadings`).

* **Qualified replay** (`QualifiedReplay`).  Replaying an alternative run in
  place of the original, between the same endpoints, preserves an account
  exactly when the two runs have the same account.  That condition is a
  congruence: it survives any context before and after
  (`QualifiedReplay.inContext`), passes to every erasure along a monoid
  homomorphism (`QualifiedReplay.map`), and is the equality of the readings of
  every execution over the two runs (`qualifiedReplay_iff_read`).  For the
  three readings together it is the three equalities (`LevelReadings.total_iff`).
* **What a program reads is observed** (`replay_preserves_read`).  A component
  the program reads is a homomorphic image of the account, so a qualified
  replay preserves it.  The converse fails (controls): erasing is lossy, so an
  erased component needs its own explicit erasure, and a host meter is related
  to the reference only through a checked bound.
* **Checked bounds** (`onPath_le_of_grade_le`, `CheckedBound`).  For accounts of
  occurrence paths, a bound checked on every occurrence holds on every path.
* **Exactness only where it holds** (`exact_replay`, `nonneg_exact_eq_zero`,
  `unit_work_not_exact`).  `HistoryGrammar`'s local Livšic theorem is for real
  event costs with free fork and erasure: there an exact cost takes the same
  value on any two labelled paths with the same endpoints, so endpoints decide
  replay.  A nonnegative exact cost is zero, so this never transfers to work;
  one unit per event separates `{x} → {x}` by the empty history (`0`) and by
  fork-then-erase (`2`).  For work, span or a Need account the condition is the
  account equality itself.
* **Span is not a path cost; storage release is not work**
  (`span_not_path_function`, `work_factors_through_path`, `release_not_refund`,
  `live_storage_not_monotone`, `peak_not_additive`).  Work is a function of the
  occurrences performed; span is not even a function of them, and depends on
  the dependency structure.  Releasing storage lowers the live bytes and never
  the work.
* **Whole-parent suspension** (`Machine.whole_parent_resumption`).  Pausing a
  productive block and resuming its complete residual keeps the published
  events, the outcome and every level of the account, for any family of
  independently defined prices.

* **Machine runs as occurrence paths** (`ProductiveBlocks.Machine.trace`,
  `ProductiveBlocks.Machine.spent_eq_onPath_add`).  The continuing transitions
  of a machine are the occurrences of its own GSLT, and a run's account is the
  valuation of its trace plus the transition that ends it.  So
  `ProductiveBlocks.Machine.spent_le` is the checked bound on the trace
  (`ProductiveBlocks.Machine.spent_le_of_onPath`), a pointwise price bound is a
  `CheckedBound` (`ProductiveBlocks.Machine.checkedBound`), and on a segment the
  account is the run account of the trace, where qualified replay applies
  (`ProductiveBlocks.Machine.spent_eq_pathAccount`).

None of this identifies the reference account with the host's instruction
count, and none of it is a statement about compiled code.
-/

set_option autoImplicit false

open _root_.CategoryTheory

namespace Mettapedia.GSLT.Distinction.LevelAccounts

open Mettapedia.Effects

universe u v w

/-! ## Three readings -/

/-- **Three readings of the runs of a host**: the object's reference account,
the host's work, and copy, validation and recording overhead, each its own
account. -/
structure LevelReadings (C : Type u) [Category.{v} C] (R H O : Type w) [Monoid R] [Monoid H]
    [Monoid O] where
  reference : RunAccount C R
  work : RunAccount C H
  overhead : RunAccount C O

namespace LevelReadings

variable {C : Type u} [Category.{v} C] {R H O : Type w} [Monoid R] [Monoid H] [Monoid O]

/-- The three readings side by side. -/
def total (readings : LevelReadings C R H O) : RunAccount C (R × H × O) :=
  readings.reference.prod (readings.work.prod readings.overhead)

/-- Erasing work and overhead leaves the reference reading. -/
theorem total_map_fst (readings : LevelReadings C R H O) :
    readings.total.map (MonoidHom.fst R (H × O)) = readings.reference := by
  ext
  rfl

end LevelReadings

/-! ## Qualified replay -/

variable {C : Type u} [Category.{v} C] {M N : Type w} [Monoid M] [Monoid N]

/-- **Replaying `alternative` in place of `original` is qualified** for an
account when the two runs, between the same endpoints, have the same account. -/
def QualifiedReplay (account : RunAccount C M) {source target : C}
    (original alternative : source ⟶ target) : Prop :=
  account.of original = account.of alternative

namespace QualifiedReplay

variable {account : RunAccount C M} {source target : C} {original alternative : source ⟶ target}

theorem refl (account : RunAccount C M) (run : source ⟶ target) : QualifiedReplay account run run :=
  rfl

theorem symm (qualified : QualifiedReplay account original alternative) :
    QualifiedReplay account alternative original :=
  Eq.symm qualified

theorem trans {third : source ⟶ target} (first : QualifiedReplay account original alternative)
    (second : QualifiedReplay account alternative third) : QualifiedReplay account original third :=
  Eq.trans first second

/-- **Qualified replay is a congruence**: it holds inside any context. -/
theorem inContext (qualified : QualifiedReplay account original alternative) {before after : C}
    (prefixRun : before ⟶ source) (suffixRun : target ⟶ after) :
    QualifiedReplay account (prefixRun ≫ original ≫ suffixRun) (prefixRun ≫ alternative ≫ suffixRun) := by
  unfold QualifiedReplay at qualified ⊢
  simp only [RunAccount.of_comp, qualified]

/-- **Qualified replay passes to every erasure** along a monoid homomorphism. -/
theorem map (qualified : QualifiedReplay account original alternative) (change : M →* N) :
    QualifiedReplay (account.map change) original alternative := by
  unfold QualifiedReplay at qualified ⊢
  simp only [RunAccount.map_of, qualified]

end QualifiedReplay

/-- **Qualified replay is equality of readings**: every execution over the
original run reads like the same execution over the alternative. -/
theorem qualifiedReplay_iff_read (account : RunAccount C M) {source target : C}
    (original alternative : source ⟶ target) :
    QualifiedReplay account original alternative ↔
      ∀ result : PUnit.{w + 1}, account.read ⟨original, result⟩ = account.read ⟨alternative, result⟩ := by
  constructor
  · intro qualified result
    change (account.of original, result) = (account.of alternative, result)
    rw [qualified]
  · intro readsAlike
    have same := congrArg Prod.fst (readsAlike PUnit.unit)
    exact same

/-- **What a program reads is preserved by a qualified replay**: a read
component is a homomorphic image of the account. -/
theorem replay_preserves_read {D : Type w} [Monoid D] (account : RunAccount C M) (read : M →* D)
    {source target : C} {original alternative : source ⟶ target}
    (qualified : QualifiedReplay account original alternative) :
    read (account.of original) = read (account.of alternative) :=
  qualified.map read

/-- **For the three readings together, qualified replay is the three
equalities.** -/
theorem LevelReadings.total_iff {R H O : Type w} [Monoid R] [Monoid H] [Monoid O]
    (readings : LevelReadings C R H O) {source target : C} (original alternative : source ⟶ target) :
    QualifiedReplay readings.total original alternative ↔
      QualifiedReplay readings.reference original alternative ∧
        QualifiedReplay readings.work original alternative ∧
          QualifiedReplay readings.overhead original alternative := by
  unfold QualifiedReplay LevelReadings.total
  change (readings.reference.of original, readings.work.of original, readings.overhead.of original) =
      (readings.reference.of alternative, readings.work.of alternative,
        readings.overhead.of alternative) ↔ _
  simp only [Prod.mk.injEq]

/-! ## Checked bounds on occurrence paths -/

section Checked

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory

variable {theory : GSLT} {P : InteractionPresentation theory}

/-- **A bound checked on every occurrence holds on every path.** -/
theorem onPath_le_of_grade_le (reference work : OccurrenceValuation P ℕ) (factor : ℕ)
    (checked : ∀ {s t : theory.Term} (occurrence : Occurrence P s t),
      work.grade occurrence ≤ factor * reference.grade occurrence)
    {s t : theory.Term} (path : OccurrencePath P s t) :
    work.onPath path ≤ factor * reference.onPath path := by
  induction path with
  | refl => simp [OccurrenceValuation.onPath]
  | cons occurrence rest ih =>
      simp only [OccurrenceValuation.onPath, Nat.mul_add]
      exact Nat.add_le_add (checked occurrence) ih

/-- **A checked bound between two meters**: the host's work on every path is at
most `factor` times the reference account. -/
def CheckedBound (reference work : OccurrenceValuation P ℕ) (factor : ℕ) : Prop :=
  ∀ {s t : theory.Term} (path : OccurrencePath P s t), work.onPath path ≤ factor * reference.onPath path

theorem CheckedBound.of_occurrences {reference work : OccurrenceValuation P ℕ} {factor : ℕ}
    (checked : ∀ {s t : theory.Term} (occurrence : Occurrence P s t),
      work.grade occurrence ≤ factor * reference.grade occurrence) :
    CheckedBound reference work factor :=
  fun path => onPath_le_of_grade_le reference work factor checked path

end Checked

/-! ## Exactness only for the real-valued fork-and-erase instance -/

section Exactness

open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.Cybernetics.DistinctionCalculus.History (Event)

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- **With free fork and erasure, an exact real cost licenses replay by
endpoints**: any two labelled paths with the same endpoints have the same
cost. -/
theorem exact_replay {cost : Event V → ℝ} (exact : Exact G cost) {live result : Multiset V}
    {first second : List (Event V)} (one : LabelledPath G live first result)
    (two : LabelledPath G live second result) :
    (first.map cost).sum = (second.map cost).sum := by
  obtain ⟨potential, laws⟩ := exact
  rw [labelledPath_cost G laws one, labelledPath_cost G laws two]

omit [DecidableEq V] in
/-- **A nonnegative exact cost is zero**: fork charges the potential and erasure
its negative. -/
theorem nonneg_exact_eq_zero {cost : Event V → ℝ} (exact : Exact G cost)
    (nonneg : ∀ event, 0 ≤ cost event) (event : Event V) : cost event = 0 := by
  obtain ⟨potential, laws⟩ := exact
  have zero : ∀ x, potential x = 0 := by
    intro x
    have fork := (laws x x).2.1
    have erase := (laws x x).2.2.1
    have forkNonneg := nonneg (.fork x)
    have eraseNonneg := nonneg (.erase x)
    linarith
  cases event with
  | evolve x => rw [(laws x x).1, zero, zero, sub_zero]
  | fork x => rw [(laws x x).2.1, zero]
  | merge x y => rw [(laws x y).2.2.2, zero, zero, zero]; ring
  | erase x => rw [(laws x x).2.2.1, zero, neg_zero]

/-- One unit of work per event. -/
def unitWork : Event V → ℝ := fun _ => 1

omit [DecidableEq V] in
/-- **Unit work is not exact**, whatever the grammar. -/
theorem unit_work_not_exact [Nonempty V] : ¬ Exact G (unitWork (V := V)) := by
  intro exact
  obtain ⟨x⟩ := ‹Nonempty V›
  have zero := nonneg_exact_eq_zero G exact (fun _ => zero_le_one) (.fork x)
  simp [unitWork] at zero

/-- **The naive transfer fails for work**: the empty history and fork-then-erase
both go from `{x}` to `{x}`, with work `0` and `2`. -/
theorem work_replay_not_by_endpoints (x : V) :
    LabelledPath G {x} [] {x} ∧ LabelledPath G {x} [.fork x, .erase x] {x} ∧
      (([] : List (Event V)).map unitWork).sum = 0 ∧
      (([.fork x, .erase x] : List (Event V)).map unitWork).sum = 2 := by
  refine ⟨.nil _, ?_, by simp, by norm_num [unitWork]⟩
  have forked : Fires G (.fork x) {x} (x ::ₘ {x}) := .fork (Multiset.mem_singleton_self x)
  have erased : Fires G (.erase x) (x ::ₘ {x}) {x} := by
    have fires : Fires G (.erase x) (x ::ₘ {x}) ((x ::ₘ ({x} : Multiset V)).erase x) :=
      .erase (Multiset.mem_cons_self x _)
    rwa [Multiset.erase_cons_head] at fires
  exact .cons forked (.cons erased (.nil _))

end Exactness

/-! ## Span is not a path cost; storage release is not work -/

section Span

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.NonFactorization

/-- A schedule of occurrences: one occurrence, two in sequence, or two
independent ones in parallel. -/
inductive Schedule (Occurrence : Type) where
  | single (occurrence : Occurrence)
  | sequence (first second : Schedule Occurrence)
  | parallel (left right : Schedule Occurrence)

namespace Schedule

variable {Occurrence : Type}

/-- The occurrences a schedule performs, serialized left to right. -/
def occurrences : Schedule Occurrence → List Occurrence
  | .single occurrence => [occurrence]
  | .sequence first second => first.occurrences ++ second.occurrences
  | .parallel left right => left.occurrences ++ right.occurrences

/-- Its work and span, each occurrence one unit. -/
def cost : Schedule Occurrence → WorkSpan
  | .single _ => ⟨1, 1⟩
  | .sequence first second => WorkSpan.sequential first.cost second.cost
  | .parallel left right => WorkSpan.parallel left.cost right.cost

theorem work_eq_length (schedule : Schedule Occurrence) :
    schedule.cost.work = schedule.occurrences.length := by
  induction schedule with
  | single => rfl
  | sequence first second ihFirst ihSecond =>
      simp [cost, occurrences, WorkSpan.sequential, ihFirst, ihSecond]
  | parallel left right ihLeft ihRight =>
      simp [cost, occurrences, WorkSpan.parallel, ihLeft, ihRight]

end Schedule

/-- **Work is a path cost**: it is a function of the occurrences performed. -/
theorem work_factors_through_path {Occurrence : Type} :
    Factors (Schedule.occurrences (Occurrence := Occurrence)) fun schedule => schedule.cost.work :=
  ⟨List.length, fun schedule => (schedule.work_eq_length).symm⟩

/-- **Span is not a function of the occurrences**: the same two occurrences, in
the same order, have span `2` in sequence and `1` in parallel. -/
def span_not_path_function :
    NonTrivialFiber (Schedule.occurrences (Occurrence := Bool)) fun schedule => schedule.cost.span where
  left := .sequence (.single true) (.single false)
  right := .parallel (.single true) (.single false)
  sameShadow := rfl
  differentValue := by decide

/-- A storage event. -/
inductive StorageEvent where
  | allocate (bytes : ℕ)
  | release (bytes : ℕ)

/-- The live-byte change of an event: releasing lowers it. -/
def StorageEvent.live : StorageEvent → ℤ
  | .allocate bytes => bytes
  | .release bytes => -bytes

/-- Work: every event is one unit. -/
def storageWork (events : List StorageEvent) : ℕ := events.length

/-- Live bytes after the events. -/
def liveBytes (events : List StorageEvent) : ℤ := (events.map StorageEvent.live).sum

/-- **Releasing storage is not a refund of work.** -/
theorem release_not_refund :
    liveBytes [.allocate 4, .release 4] = liveBytes [] ∧
      storageWork [.allocate 4, .release 4] = 2 ∧ storageWork [] = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp [liveBytes, StorageEvent.live]

/-- Work only grows along a run. -/
theorem storageWork_prefix {first whole : List StorageEvent} (prefixed : first <+: whole) :
    storageWork first ≤ storageWork whole :=
  prefixed.length_le

/-- **Live storage does not only grow**: it is not a work account. -/
theorem live_storage_not_monotone :
    [StorageEvent.allocate 4] <+: [.allocate 4, .release 4] ∧
      liveBytes [.allocate 4, .release 4] < liveBytes [.allocate 4] := by
  refine ⟨⟨[.release 4], rfl⟩, ?_⟩
  simp [liveBytes, StorageEvent.live]

/-- Peak live bytes along a run. -/
def peakBytes : List StorageEvent → ℤ → ℤ
  | [], current => max current 0
  | event :: rest, current => max current (peakBytes rest (current + event.live))

/-- **Peak storage is not additive** over sequential composition. -/
theorem peak_not_additive :
    peakBytes ([.allocate 1, .release 1] ++ [.allocate 1, .release 1]) 0 = 1 ∧
      peakBytes [.allocate 1, .release 1] 0 + peakBytes [.allocate 1, .release 1] 0 = 2 := by
  constructor <;> simp [peakBytes, StorageEvent.live]

end Span

/-! ## Whole-parent suspension and resumption -/

namespace Machine

open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {State Event Verdict Request Level : Type}
  (machine : ProductiveBlocks.Machine State Event Verdict Request)

/-- **Whole-parent suspension keeps spent work and the complete residual.**
Pausing a block after `first` steps and resuming its complete residual gives
the uninterrupted events and outcome, and every level of the account adds
exactly. -/
theorem whole_parent_resumption (price : Level → State → ℕ) (first second : ℕ)
    {state residual : State} {events : List Event}
    (paused : machine.run first state = (events, .exhausted residual)) :
    machine.run (first + second) state =
        (events ++ (machine.run second residual).1, (machine.run second residual).2) ∧
      ∀ level, machine.spent (price level) (first + second) state =
        machine.spent (price level) first state + machine.spent (price level) second residual := by
  refine ⟨machine.established_and_pending first second state residual events paused, fun level => ?_⟩
  rw [machine.spent_add, paused]
  rfl

end Machine

end Mettapedia.GSLT.Distinction.LevelAccounts

/-! ## Machine runs as occurrence paths -/

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Distinction.LevelAccounts (onPath_le_of_grade_le CheckedBound
  CheckedBound.of_occurrences)

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- The continuing transitions of a machine, silent or publishing, as the
occurrences of its own GSLT: one site, with the transition as evidence. -/
def presentation : InteractionPresentation machine.gslt where
  Site := Unit
  Event _ state next := PLift (machine.gslt.Step state next)
  sound evidence := evidence.down

/-- A price on states as a valuation of the machine's occurrences: an occurrence
is charged the price of the state it leaves. -/
def priceValuation (price : State → ℕ) : OccurrenceValuation machine.presentation ℕ where
  grade {state _} _ := price state

/-- **The trace of a finite run**: its continuing transitions as an occurrence
path, from the start to the state where the run stops. -/
def trace : ℕ → (state : State) → Σ stop, OccurrencePath machine.presentation state stop
  | 0, state => ⟨state, OccurrencePath.refl (P := machine.presentation) state⟩
  | fuel + 1, state =>
      match found : machine.step state with
      | some (.silent next) =>
          ⟨(trace fuel next).1, .cons ⟨(), ⟨Or.inl found⟩⟩ (trace fuel next).2⟩
      | some (.publish events next) =>
          ⟨(trace fuel next).1, .cons ⟨(), ⟨Or.inr ⟨events, found⟩⟩⟩ (trace fuel next).2⟩
      | none => ⟨state, OccurrencePath.refl (P := machine.presentation) state⟩
      | some (.finish _) => ⟨state, OccurrencePath.refl (P := machine.presentation) state⟩
      | some (.fail _) => ⟨state, OccurrencePath.refl (P := machine.presentation) state⟩
      | some (.call _ _) => ⟨state, OccurrencePath.refl (P := machine.presentation) state⟩

/-- The price of the transition that ends a finite run: finishing, failing and
calling out are charged; a stuck state and spent fuel are not. -/
def endCharge (price : State → ℕ) : ℕ → State → ℕ
  | 0, _ => 0
  | fuel + 1, state =>
      match machine.step state with
      | none => 0
      | some (.silent next) => endCharge price fuel next
      | some (.publish _ next) => endCharge price fuel next
      | some (.finish _) => price state
      | some (.fail _) => price state
      | some (.call _ _) => price state

/-- **A run's account is the valuation of its trace plus the transition that ends
it.** -/
theorem spent_eq_onPath_add (price : State → ℕ) (fuel : ℕ) (state : State) :
    machine.spent price fuel state =
      (machine.priceValuation price).onPath (machine.trace fuel state).2 +
        machine.endCharge price fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [trace]
      split <;> rename_i found <;>
        simp only [Machine.spent, endCharge, found, ih, OccurrenceValuation.onPath, priceValuation,
          Nat.add_assoc, Nat.zero_add]

/-- A pointwise bound between two prices bounds the transitions that end runs. -/
theorem endCharge_le (instructions allocations : State → ℕ) (factor : ℕ)
    (bound : ∀ state, allocations state ≤ factor * instructions state) (fuel : ℕ) (state : State) :
    machine.endCharge allocations fuel state ≤ factor * machine.endCharge instructions fuel state := by
  induction fuel generalizing state with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp only [endCharge, found]; exact Nat.zero_le _
      | some transition =>
          cases transition with
          | silent next => simp only [endCharge, found]; exact ih next
          | publish events next => simp only [endCharge, found]; exact ih next
          | finish verdict => simp only [endCharge, found]; exact bound state
          | fail events => simp only [endCharge, found]; exact bound state
          | call request saved => simp only [endCharge, found]; exact bound state

/-- **`Machine.spent_le` is the occurrence-path bound
`onPath_le_of_grade_le` on the machine's trace**, together with the bound on the
transition that ends the run. -/
theorem spent_le_of_onPath (instructions allocations : State → ℕ) (factor : ℕ)
    (bound : ∀ state, allocations state ≤ factor * instructions state) (fuel : ℕ) (state : State) :
    machine.spent allocations fuel state ≤ factor * machine.spent instructions fuel state := by
  rw [machine.spent_eq_onPath_add, machine.spent_eq_onPath_add, Nat.mul_add]
  exact Nat.add_le_add
    (onPath_le_of_grade_le (machine.priceValuation instructions) (machine.priceValuation allocations)
      factor (fun {source _} _ => bound source) _)
    (machine.endCharge_le instructions allocations factor bound fuel state)

/-- **A pointwise bound between two prices is a checked bound** on every occurrence
path of the machine. -/
theorem checkedBound (instructions allocations : State → ℕ) (factor : ℕ)
    (bound : ∀ state, allocations state ≤ factor * instructions state) :
    CheckedBound (machine.priceValuation instructions) (machine.priceValuation allocations) factor :=
  CheckedBound.of_occurrences fun {source _} _ => bound source

/-- A run segment that ends with its exact residual has its trace end at the
residual, with no transition that ends it. -/
theorem trace_of_exhausted (price : State → ℕ) {fuel : ℕ} {state residual : State}
    {events : List Event} (ran : machine.run fuel state = (events, .exhausted residual)) :
    (machine.trace fuel state).1 = residual ∧ machine.endCharge price fuel state = 0 := by
  induction fuel generalizing state events with
  | zero =>
      cases ran
      exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      rw [trace]
      split <;> rename_i found
      · rw [machine.run_succ_silent found] at ran
        simp only [endCharge, found]
        exact ih ran
      · rw [machine.run_succ_publish found] at ran
        have rest : (machine.run fuel _).2 = .exhausted residual := congrArg Prod.snd ran
        simp only [endCharge, found]
        exact ih (Prod.ext rfl rest)
      · rw [machine.run_succ_stuck found] at ran
        cases ran
      · rw [machine.run_succ_finish found] at ran
        cases ran
      · rw [machine.run_succ_fail found] at ran
        cases ran
      · rw [machine.run_succ_call found] at ran
        cases ran

open Mettapedia.GSLT.Causality.TraceCostValuation (pathAccount) in
/-- **On a segment, the account of the machine run is the run account of its
trace**: qualified replay of occurrence paths applies to machine runs. -/
theorem spent_eq_pathAccount (price : State → ℕ) {fuel : ℕ} {state residual : State}
    {events : List Event} (ran : machine.run fuel state = (events, .exhausted residual)) :
    (pathAccount (machine.priceValuation price)).of (machine.trace fuel state).2 =
      Multiplicative.ofAdd (machine.spent price fuel state) := by
  rw [machine.spent_eq_onPath_add, (machine.trace_of_exhausted price ran).2, Nat.add_zero]
  rfl

end Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine
