import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.Machines.RevisionDependencySet
import Mathlib.Logic.Relation

/-!
# Scoped cache coherence through mutation

A cached result is reused while the store it was computed from changes. This
module states when such reuse is correct, in three forms, and keeps four
neighbouring obligations apart.

**The authorized observation.** Every form compares a cached answer with an
independently defined observation `authorized : environment → query → answer`.
The cache's own bookkeeping never replaces it.

1. **Validation by captured readings** (`ReadsDetermine`, `Cached`,
   `Recorded`). A computation consults an ordered list of stores and captures
   their readings in a `CapturedReadView`. When the authorized answer is
   determined by those readings, publication permission (`CanPublish`) implies
   that the cached answer is the current authorized answer
   (`Recorded.answer_of_canPublish`). The ordered effectful validation of the
   native adapter discharges this when every observer is truthful and the
   *whole* consulted support is preserved by every observation
   (`Recorded.answer_of_checkObserved`). The key made of the query, the
   consulted stores and their readings satisfies `SoundKey`
   (`soundKey_readingKey`). A publication either preserves the readings of a
   kept entry or invalidates it (`canPublish_invalidate`).
2. **Notification counters along a run** (`Notifies`). When every transition
   that can change an observation advances its counter, and counters never
   decrease, equal counters at two points of one run give equal observations
   (`Notifies.observe_eq_of_counter_eq`). A stamp that determines the query and
   the counter is a `SoundKey` on the points of one run
   (`Notifies.soundKey_run`), and across sessions when it also separates
   session identities (`Notifies.soundKey_sessions`); a reused identity is the
   counterexample in the store instance. A counter
   summarizes readings only within one lineage; the identity is what names the
   lineage. A validation may also be weaker than equality
   (`Certifies`): a prefix certificate certifies a prefix observation, not the
   full one.
3. **Epochs** (`EpochStep`). A table keyed by the whole query, without
   captured readings, is coherent when it is cleared before every epoch, every
   transition inside an epoch preserves the consulted readings, and each entry
   is recorded from the current authorized observation
   (`epochCoherent_of_reflTransGen`).

**Separate obligations.**

* *A key is not a read window.* Currency is a statement about states. A
  physical read of several parts is current only if every part is read inside
  a window whose opening and closing keys agree (`Notifies.windowRead_eq`).
  The window hypothesis is where acquire and release ordering and data-race
  freedom enter; a key comparison does not provide them.
* *A live owner is not currency.* Keeping storage alive prevents dangling
  bytes; it says nothing about whether the cached observation is current.
* *Hidden dependencies.* An observation that depends on a store outside the
  consulted support is not determined by the support
  (`not_readsDetermine_of_hidden`). A native adapter therefore either consults
  or stabilizes its symbol table and its episode and library context, and an
  opaque callback's private revision is not certified by rechecking its outer
  pointer (`Controls.outer_pointer_recheck_does_not_certify`).
* *Separate observations.* Eviction preserves answers and loses reuse
  (`eviction_preserves_answer_loses_reuse`). Exhaustion is a resource
  observation, never a logical refusal (`logicalEntry_sound`,
  `exhaustedAsRefusal_unsound`).

These are statements about models of stores and caches. They do not prove any
C implementation, its memory model or its compiled code.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CacheCoherence

open Mettapedia.GSLT.Dynamics.MemoizationObserver
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Machines

/-! ## 1. Validation by captured readings -/

section Readings

variable {Dep Reading Query Answer : Type} [DecidableEq Dep]

/-- **The authorized answer is determined by the consulted readings**, on a
domain of environments: two environments of the domain that agree on every
store consulted in the first give the same authorized answer. -/
def ReadsDetermineOn (domain : RevisionEnvironment Dep Reading → Prop)
    (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep) : Prop :=
  ∀ captured live query, domain captured → domain live →
    RevisionEnvironment.AgreesOn (consults captured query).toFinset live captured →
      authorized live query = authorized captured query

/-- Determination by the consulted readings on every environment. -/
def ReadsDetermine (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep) : Prop :=
  ∀ captured live query,
    RevisionEnvironment.AgreesOn (consults captured query).toFinset live captured →
      authorized live query = authorized captured query

theorem ReadsDetermine.on {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults)
    (domain : RevisionEnvironment Dep Reading → Prop) :
    ReadsDetermineOn domain authorized consults :=
  fun captured live query _ _ agrees => determines captured live query agrees

/-- **A hidden dependency defeats determination.** Two environments that agree
on the consulted stores and give different authorized answers refute it. -/
theorem not_readsDetermine_of_hidden
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    {captured live : RevisionEnvironment Dep Reading} {query : Query}
    (agrees : RevisionEnvironment.AgreesOn (consults captured query).toFinset live captured)
    (differs : authorized live query ≠ authorized captured query) :
    ¬ ReadsDetermine authorized consults :=
  fun determines => differs (determines captured live query agrees)

/-- The key of a computed answer: the query, the stores it consulted in order,
and their readings in the same order. -/
def readingKey (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (point : RevisionEnvironment Dep Reading × Query) : Query × List Dep × List Reading :=
  (point.2, consults point.1 point.2, (consults point.1 point.2).map point.1.current)

/-- **The reading key is sound**, derived from determination by the consulted
readings, not assumed. -/
theorem soundKey_readingKey
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults) :
    SoundKey (readingKey consults) (fun point => authorized point.1 point.2) := by
  rintro ⟨first, query⟩ ⟨second, query'⟩ same
  simp only [readingKey, Prod.mk.injEq] at same
  obtain ⟨rfl, stores, readings⟩ := same
  rw [stores] at readings
  have agrees : RevisionEnvironment.AgreesOn (consults second query).toFinset first second := by
    intro store member
    exact List.map_inj_left.mp readings store (List.mem_toFinset.mp member)
  exact determines second first query agrees

/-- The same on a domain: the reading key is sound for points whose
environments lie in the domain. -/
theorem soundKey_readingKey_on
    {domain : RevisionEnvironment Dep Reading → Prop}
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermineOn domain authorized consults) :
    SoundKey (fun point : {point : RevisionEnvironment Dep Reading × Query // domain point.1} =>
        readingKey consults point.1)
      (fun point => authorized point.1.1 point.1.2) := by
  rintro ⟨⟨first, query⟩, firstIn⟩ ⟨⟨second, query'⟩, secondIn⟩ same
  simp only [readingKey, Prod.mk.injEq] at same
  obtain ⟨rfl, stores, readings⟩ := same
  rw [stores] at readings
  have agrees : RevisionEnvironment.AgreesOn (consults second query).toFinset first second := by
    intro store member
    exact List.map_inj_left.mp readings store (List.mem_toFinset.mp member)
  exact determines second first query secondIn firstIn agrees

variable [DecidableEq Reading]

/-- Consult a list of stores in order, from a view. -/
def consultAll (live : RevisionEnvironment Dep Reading) :
    CapturedReadView Dep Reading → List Dep → CapturedReadView Dep Reading
  | view, [] => view
  | view, store :: rest => consultAll live (view.consult live store) rest

theorem consultAll_captured (live : RevisionEnvironment Dep Reading) :
    ∀ (view : CapturedReadView Dep Reading) (stores : List Dep),
      (consultAll live view stores).captured = view.captured
  | _, [] => rfl
  | view, store :: rest => by
      rw [consultAll, consultAll_captured live _ rest]
      rfl

theorem consultAll_captureComplete (live : RevisionEnvironment Dep Reading) :
    ∀ (view : CapturedReadView Dep Reading) (stores : List Dep),
      (consultAll live view stores).captureComplete = view.captureComplete
  | _, [] => rfl
  | view, store :: rest => by
      rw [consultAll, consultAll_captureComplete live _ rest]
      rfl

theorem mem_consultAll_consulted (live : RevisionEnvironment Dep Reading) :
    ∀ (view : CapturedReadView Dep Reading) (stores : List Dep) (store : Dep),
      store ∈ (consultAll live view stores).consulted ↔
        store ∈ view.consulted ∨ store ∈ stores
  | view, [], store => by simp [consultAll]
  | view, read :: rest, store => by
      rw [consultAll, mem_consultAll_consulted live _ rest,
        CapturedReadView.mem_consulted_consult_iff]
      simp only [List.mem_cons]
      tauto

/-- Consulting the captured environment itself records no mismatch. -/
theorem consultAll_firstMismatch (live : RevisionEnvironment Dep Reading) :
    ∀ (view : CapturedReadView Dep Reading) (stores : List Dep),
      view.captured = live → view.firstMismatch = none →
        (consultAll live view stores).firstMismatch = none
  | _, [], _, unpoisoned => unpoisoned
  | view, store :: rest, captured, unpoisoned => by
      have none : view.mismatchAt live store = none := by
        rw [CapturedReadView.mismatchAt_eq_none_iff, captured]
      rw [consultAll]
      exact consultAll_firstMismatch live (view.consult live store) rest captured
        (by simp [CapturedReadView.consult, unpoisoned, none])

/-- A cached result: the query, the captured view of its reads, and the
answer. -/
structure Cached (Dep Reading Query Answer : Type) where
  query : Query
  view : CapturedReadView Dep Reading
  answer : Answer

/-- **An honestly recorded result**: its answer is the authorized answer of
the captured environment, and that answer is determined by the stores the
view consulted. -/
def Recorded (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (entry : Cached Dep Reading Query Answer) : Prop :=
  entry.answer = authorized entry.view.captured entry.query ∧
    ∀ live, RevisionEnvironment.AgreesOn entry.view.consulted.toFinset live entry.view.captured →
      authorized live entry.query = authorized entry.view.captured entry.query

/-- Compute an answer in an environment and capture the stores it consults. -/
def record (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (environment : RevisionEnvironment Dep Reading) (query : Query) :
    Cached Dep Reading Query Answer :=
  ⟨query, consultAll environment (CapturedReadView.admit environment) (consults environment query),
    authorized environment query⟩

theorem record_view_captured (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (environment : RevisionEnvironment Dep Reading) (query : Query) :
    (record authorized consults environment query).view.captured = environment :=
  consultAll_captured environment _ _

theorem mem_record_consulted (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (environment : RevisionEnvironment Dep Reading) (query : Query) (store : Dep) :
    store ∈ (record authorized consults environment query).view.consulted ↔
      store ∈ consults environment query := by
  simp [record, mem_consultAll_consulted, CapturedReadView.admit]

theorem record_complete (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (environment : RevisionEnvironment Dep Reading) (query : Query) :
    (record authorized consults environment query).view.captureComplete = true :=
  consultAll_captureComplete environment _ _

theorem record_unpoisoned (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep)
    (environment : RevisionEnvironment Dep Reading) (query : Query) :
    (record authorized consults environment query).view.firstMismatch = none :=
  consultAll_firstMismatch environment _ _ rfl rfl

/-- Recording under determination is honest. -/
theorem recorded_record {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults)
    (environment : RevisionEnvironment Dep Reading) (query : Query) :
    Recorded authorized (record authorized consults environment query) := by
  refine ⟨by rw [record_view_captured]; rfl, ?_⟩
  intro live agrees
  rw [record_view_captured] at agrees ⊢
  apply determines environment live query
  intro store member
  apply agrees store
  rw [List.mem_toFinset, mem_record_consulted]
  exact List.mem_toFinset.mp member

/-- **Publication permission gives the current authorized answer.** -/
theorem Recorded.answer_of_canPublish
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {entry : Cached Dep Reading Query Answer} (recorded : Recorded authorized entry)
    {live : RevisionEnvironment Dep Reading} (publish : entry.view.CanPublish live) :
    entry.answer = authorized live entry.query := by
  have agrees := (CapturedReadView.valid_dependencies_iff entry.view live).mp publish.2.2
  rw [recorded.1, recorded.2 live agrees]

/-- **The ordered native validation gives the current authorized answer at
publication**, after every observer effect. Truthfulness and preservation of
the whole consulted support are the premises; preservation of each sampled key
alone is not enough (`Controls.late_observer_accepts_stale_answer`). -/
theorem Recorded.answer_of_checkObserved {State : Type}
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {entry : Cached Dep Reading Query Answer} (recorded : Recorded authorized entry)
    (projection : State → RevisionEnvironment Dep Reading)
    (observe : Dep → State → Reading × State)
    (complete : entry.view.captureComplete = true)
    (unpoisoned : entry.view.firstMismatch = none)
    (truthful : ∀ store ∈ entry.view.consulted.toFinset, ∀ state,
      (observe store state).1 = (projection state).current store)
    (stable : ∀ store ∈ entry.view.consulted.toFinset, ∀ state,
      RevisionEnvironment.AgreesOn entry.view.consulted.toFinset
        (projection (observe store state).2) (projection state))
    (state : State)
    (accepted : (RevisionEnvironment.checkObserved entry.view.captured observe
      entry.view.consulted state).1 = true) :
    entry.answer = authorized (projection (RevisionEnvironment.checkObserved
      entry.view.captured observe entry.view.consulted state).2) entry.query :=
  recorded.answer_of_canPublish
    ((CapturedReadView.checkObserved_canPublish entry.view projection observe complete
      unpoisoned truthful stable state).mp accepted)

/-- A live environment that agrees with an earlier one on the consulted stores
has the same publication permission. -/
theorem canPublish_iff_of_agreesOn (view : CapturedReadView Dep Reading)
    {before after : RevisionEnvironment Dep Reading}
    (agrees : RevisionEnvironment.AgreesOn view.consulted.toFinset after before) :
    view.CanPublish after ↔ view.CanPublish before := by
  unfold CapturedReadView.CanPublish
  rw [RevisionDependencySet.validAt_iff_of_agreesOn_storeSupport view.dependencies
    (by rw [CapturedReadView.dependencies_storeSupport]; exact agrees)]

/-- Drop every entry that consulted a touched store. -/
def invalidate (touched : Dep → Bool) (table : List (Cached Dep Reading Query Answer)) :
    List (Cached Dep Reading Query Answer) :=
  table.filter fun entry => entry.view.consulted.all fun store => !touched store

/-- **The transition-level invariant.** When a publication touches at least
every store whose reading it changes, every kept entry that could publish
before can publish after, so it still gives the current authorized answer. -/
theorem canPublish_invalidate {touched : Dep → Bool}
    {before after : RevisionEnvironment Dep Reading}
    (covers : ∀ store, after.current store ≠ before.current store → touched store = true)
    {table : List (Cached Dep Reading Query Answer)}
    {entry : Cached Dep Reading Query Answer} (kept : entry ∈ invalidate touched table)
    (publishBefore : entry.view.CanPublish before) :
    entry ∈ table ∧ entry.view.CanPublish after := by
  obtain ⟨member, untouched⟩ := List.mem_filter.mp kept
  refine ⟨member, (canPublish_iff_of_agreesOn entry.view ?_).mpr publishBefore⟩
  intro store consulted
  by_contra changed
  have hit := covers store changed
  have clean := List.all_eq_true.mp untouched store (List.mem_toFinset.mp consulted)
  simp [hit] at clean

end Readings

/-! ## 2. Notification counters along a run -/

section Notification

universe uState uAction uQuery uObs uKey uSession uIdentity uPart uCertificate

variable {State : Type uState} {Action : Type uAction} {Query : Type uQuery} {Obs : Type uObs}

/-- Run a list of actions. -/
def execute (step : State → Action → State) : State → List Action → State
  | state, [] => state
  | state, action :: rest => execute step (step state action) rest

theorem execute_append (step : State → Action → State) (state : State)
    (first second : List Action) :
    execute step state (first ++ second) = execute step (execute step state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih (step state action)

/-- The state of a run after its first `time` actions. -/
def runAt (step : State → Action → State) (origin : State) (actions : List Action)
    (time : Nat) : State :=
  execute step origin (actions.take time)

theorem runAt_later (step : State → Action → State) (origin : State) (actions : List Action)
    (earlier extra : Nat) :
    runAt step origin actions (earlier + extra) =
      execute step (runAt step origin actions earlier) ((actions.drop earlier).take extra) := by
  rw [runAt, runAt, List.take_add, execute_append]

/-- **Notification**: an invariant preserved by every transition; counters that
never decrease; and every transition that leaves a query's counter unchanged
leaves its observation unchanged. -/
structure Notifies (step : State → Action → State) (invariant : State → Prop)
    (counter : State → Query → Nat) (observe : State → Query → Obs) : Prop where
  preserves : ∀ state action, invariant state → invariant (step state action)
  monotone : ∀ state action query, counter state query ≤ counter (step state action) query
  notifies : ∀ state action query, invariant state →
    counter (step state action) query = counter state query →
      observe (step state action) query = observe state query

namespace Notifies

variable {step : State → Action → State} {invariant : State → Prop}
  {counter : State → Query → Nat} {observe : State → Query → Obs}

theorem invariant_execute (notifying : Notifies step invariant counter observe)
    {state : State} (holds : invariant state) (actions : List Action) :
    invariant (execute step state actions) := by
  induction actions generalizing state with
  | nil => exact holds
  | cons action rest ih => exact ih (notifying.preserves state action holds)

theorem counter_le_execute (notifying : Notifies step invariant counter observe)
    (state : State) (actions : List Action) (query : Query) :
    counter state query ≤ counter (execute step state actions) query := by
  induction actions generalizing state with
  | nil => exact le_rfl
  | cons action rest ih =>
      exact (notifying.monotone state action query).trans (ih (step state action))

theorem observe_execute_of_counter_eq (notifying : Notifies step invariant counter observe)
    {state : State} (holds : invariant state) (actions : List Action) (query : Query)
    (same : counter (execute step state actions) query = counter state query) :
    observe (execute step state actions) query = observe state query := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have first := notifying.monotone state action query
      have later := notifying.counter_le_execute (step state action) rest query
      have unchanged : counter (step state action) query = counter state query := by
        change counter (execute step (step state action) rest) query = _ at same
        omega
      have tail : counter (execute step (step state action) rest) query =
          counter (step state action) query := by
        change counter (execute step (step state action) rest) query = _ at same
        omega
      exact (ih (notifying.preserves state action holds) tail).trans
        (notifying.notifies state action query holds unchanged)

theorem counter_runAt_mono (notifying : Notifies step invariant counter observe)
    (origin : State) (actions : List Action) {earlier later : Nat} (ordered : earlier ≤ later)
    (query : Query) :
    counter (runAt step origin actions earlier) query ≤
      counter (runAt step origin actions later) query := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [runAt_later]
  exact notifying.counter_le_execute _ _ query

/-- **Equal counters at two points of a run give equal observations.** -/
theorem observe_eq_of_counter_eq (notifying : Notifies step invariant counter observe)
    {origin : State} (holds : invariant origin) (actions : List Action)
    {earlier later : Nat} (ordered : earlier ≤ later) (query : Query)
    (same : counter (runAt step origin actions later) query =
      counter (runAt step origin actions earlier) query) :
    observe (runAt step origin actions later) query =
      observe (runAt step origin actions earlier) query := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [runAt_later] at same ⊢
  exact notifying.observe_execute_of_counter_eq
    (notifying.invariant_execute holds _) _ query same

/-- **A stamp determining the query and its counter is a sound key on the
points of one run.** The points are pairs of a time and a query. -/
theorem soundKey_run {Key : Type uKey} (notifying : Notifies step invariant counter observe)
    {origin : State} (holds : invariant origin) (actions : List Action)
    (stamp : State → Query → Key)
    (determines : ∀ first second query query', stamp first query = stamp second query' →
      query = query' ∧ counter first query = counter second query') :
    SoundKey (fun point : Nat × Query => stamp (runAt step origin actions point.1) point.2)
      (fun point => observe (runAt step origin actions point.1) point.2) := by
  rintro ⟨first, query⟩ ⟨second, query'⟩ same
  obtain ⟨rfl, counted⟩ := determines _ _ _ _ same
  rcases le_total first second with ordered | ordered
  · exact (notifying.observe_eq_of_counter_eq holds actions ordered query counted.symm).symm
  · exact notifying.observe_eq_of_counter_eq holds actions ordered query counted

/-- **Across sessions** the stamp must also separate session identities. Each
session runs its own actions from its own origin; identities are preserved by
transitions and differ between sessions. -/
theorem soundKey_sessions {Session : Type uSession} {Identity : Type uIdentity}
    {Key : Type uKey}
    (notifying : Notifies step invariant counter observe)
    (origin : Session → State) (actions : Session → List Action)
    (holds : ∀ session, invariant (origin session))
    (identity : State → Identity)
    (keepsIdentity : ∀ state action, identity (step state action) = identity state)
    (distinct : Function.Injective fun session => identity (origin session))
    (stamp : State → Query → Key)
    (determines : ∀ first second query query', stamp first query = stamp second query' →
      identity first = identity second ∧ query = query' ∧
        counter first query = counter second query') :
    SoundKey
      (fun point : Session × Nat × Query =>
        stamp (runAt step (origin point.1) (actions point.1) point.2.1) point.2.2)
      (fun point => observe (runAt step (origin point.1) (actions point.1) point.2.1)
        point.2.2) := by
  have identityRun : ∀ (state : State) (list : List Action),
      identity (execute step state list) = identity state := by
    intro state list
    induction list generalizing state with
    | nil => rfl
    | cons action rest ih => exact (ih _).trans (keepsIdentity state action)
  rintro ⟨session, first, query⟩ ⟨session', second, query'⟩ same
  obtain ⟨identical, sameQuery, counted⟩ := determines _ _ _ _ same
  have sameSession : session = session' := by
    apply distinct
    simpa only [runAt, identityRun] using identical
  subst sameSession
  exact notifying.soundKey_run (holds session) (actions session) stamp
    (fun first second query query' equal =>
      let ⟨_, sameQuery, counted⟩ := determines first second query query' equal
      ⟨sameQuery, counted⟩) (first, query) (second, query') same

/-- A physical read of an observation made of parts: part `index` is read at
time `times index` of the run. -/
def windowRead {Part : Type uPart} (step : State → Action → State) (origin : State)
    (actions : List Action) (parts : State → Query → Nat → Part) (query : Query)
    (times : Nat → Nat) (index : Nat) : Part :=
  parts (runAt step origin actions (times index)) query index

/-- **A read window, separately from the key.** When every part is read inside
a window whose opening and closing counters agree, the physical read is the
observation at the opening. The key comparison alone does not place the reads
inside the window; that is the ordering and race-freedom obligation. -/
theorem windowRead_eq {Part : Type uPart} {parts : State → Query → Nat → Part}
    (notifying : Notifies step invariant counter parts)
    {origin : State} (holds : invariant origin) (actions : List Action)
    {opening closing : Nat} (query : Query)
    (sameKey : counter (runAt step origin actions closing) query =
      counter (runAt step origin actions opening) query)
    (times : Nat → Nat) (width : Nat)
    (inside : ∀ index < width, opening ≤ times index ∧ times index ≤ closing) :
    ∀ index < width, windowRead step origin actions parts query times index =
      parts (runAt step origin actions opening) query index := by
  intro index bounded
  obtain ⟨afterOpening, beforeClosing⟩ := inside index bounded
  have low := notifying.counter_runAt_mono origin actions afterOpening query
  have high := notifying.counter_runAt_mono origin actions beforeClosing query
  have equal : counter (runAt step origin actions (times index)) query =
      counter (runAt step origin actions opening) query := by omega
  exact congrFun (notifying.observe_eq_of_counter_eq holds actions afterOpening query equal) index

end Notifies

/-- **A certificate certifies an observation** when its acceptance after any
run from a state of the invariant preserves that observation. The observation
may depend on the certificate: a prefix certificate fixes the length of the
prefix it certifies. -/
def Certifies {Certificate : Type uCertificate} (step : State → Action → State) (invariant : State → Prop)
    (certificate : State → Certificate) (accepts : Certificate → State → Bool)
    (observe : Certificate → State → Obs) : Prop :=
  ∀ state actions, invariant state →
    accepts (certificate state) (execute step state actions) = true →
      observe (certificate state) (execute step state actions) =
        observe (certificate state) state

/-- Counter equality certifies the observation it notifies. -/
theorem Notifies.certifies {step : State → Action → State} {invariant : State → Prop}
    {counter : State → Query → Nat} {observe : State → Query → Obs}
    (notifying : Notifies step invariant counter observe) (query : Query) :
    Certifies step invariant (fun state => counter state query)
      (fun count state => decide (counter state query = count))
      (fun _ state => observe state query) := by
  intro state actions holds accepted
  exact notifying.observe_execute_of_counter_eq holds actions query (of_decide_eq_true accepted)

end Notification

/-! ## 3. Epochs: clear before each epoch, frozen within it -/

section Epochs

variable {State Dep Reading Query Answer : Type} [DecidableEq Dep] [DecidableEq Query]

/-- A table keyed by the whole query answers with the current authorized
observation. -/
def EpochCoherent (environment : State → RevisionEnvironment Dep Reading)
    (authorized : RevisionEnvironment Dep Reading → Query → Answer) (state : State)
    (table : Table Query Answer) : Prop :=
  Coherent id (authorized (environment state)) table

/-- The steps of an epoch discipline: clear the table and move to any state;
move to a state that keeps every consulted reading; or record the current
authorized answer of a query. -/
inductive EpochStep (environment : State → RevisionEnvironment Dep Reading)
    (authorized : RevisionEnvironment Dep Reading → Query → Answer)
    (consults : RevisionEnvironment Dep Reading → Query → List Dep) :
    State × Table Query Answer → State × Table Query Answer → Prop
  | clear (state next : State) (table : Table Query Answer) :
      EpochStep environment authorized consults (state, table) (next, Table.empty)
  | frozen (state next : State) (table : Table Query Answer)
      (keeps : ∀ query, RevisionEnvironment.AgreesOn
        (consults (environment state) query).toFinset (environment next) (environment state)) :
      EpochStep environment authorized consults (state, table) (next, table)
  | record (state : State) (table : Table Query Answer) (query : Query) :
      EpochStep environment authorized consults (state, table)
        (state, store id (authorized (environment state)) table query)

omit [DecidableEq Query] in
theorem soundKey_id (observe : Query → Answer) : SoundKey (id : Query → Query) observe :=
  fun _ _ same => congrArg observe same

/-- **Each epoch step preserves coherence.** -/
theorem epochCoherent_step {environment : State → RevisionEnvironment Dep Reading}
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults)
    {before after : State × Table Query Answer}
    (moves : EpochStep environment authorized consults before after)
    (coherent : EpochCoherent environment authorized before.1 before.2) :
    EpochCoherent environment authorized after.1 after.2 := by
  cases moves with
  | clear state next table => exact coherent_empty _ _
  | frozen state next table keeps =>
      intro key answer stored query sameKey
      rw [determines (environment state) (environment next) query (keeps query)]
      exact coherent key answer stored query sameKey
  | record state table query =>
      exact coherent_store_of_soundKey (soundKey_id _) coherent query

/-- **Coherence along every epoch run.** -/
theorem epochCoherent_of_reflTransGen {environment : State → RevisionEnvironment Dep Reading}
    {authorized : RevisionEnvironment Dep Reading → Query → Answer}
    {consults : RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults)
    {start finish : State × Table Query Answer}
    (run : Relation.ReflTransGen (EpochStep environment authorized consults) start finish)
    (coherent : EpochCoherent environment authorized start.1 start.2) :
    EpochCoherent environment authorized finish.1 finish.2 := by
  induction run with
  | refl => exact coherent
  | tail _ moves ih => exact epochCoherent_step determines moves ih

omit [DecidableEq Dep] [DecidableEq Query] in
/-- Lookups in a coherent epoch table are the current authorized answers. -/
theorem epoch_lookup {environment : State → RevisionEnvironment Dep Reading}
    {authorized : RevisionEnvironment Dep Reading → Query → Answer} {state : State}
    {table : Table Query Answer} (coherent : EpochCoherent environment authorized state table)
    (query : Query) :
    lookupOrCompute id (authorized (environment state)) table query =
      authorized (environment state) query :=
  lookupOrCompute_eq_obs coherent query

end Epochs

/-! ## 4. Separate observations: reuse and exhaustion -/

section Separate

variable {X K O : Type}

/-- **Eviction preserves the answer and loses the reuse.** Work is a separate
observation from the answer. -/
theorem eviction_preserves_answer_loses_reuse {key : X → K} {obs : X → O}
    {table : Table K O} (coherent : Coherent key obs table) (point : X) {stored : O}
    (present : table (key point) = some stored) :
    lookupOrCompute key obs Table.empty point = lookupOrCompute key obs table point ∧
      Reused key table point ∧ ¬ Reused key (Table.empty : Table K O) point := by
  refine ⟨lookupOrCompute_evict coherent (fun _ _ impossible => by cases impossible) point,
    by simp [Reused, present], by simp [Reused, Table.empty]⟩

variable {Query Answer : Type}

/-- The outcome of a fuel-bounded run: an answer, a refusal, or exhaustion of
the fuel. -/
inductive RunOutcome (Answer : Type) where
  | answered (answer : Answer)
  | refused
  | exhausted
  deriving DecidableEq

/-- A fuel-bounded run is **adequate** to a logical observation (`none` is the
logical refusal) when its answers and refusals are logical; exhaustion claims
nothing. -/
def Adequate (logical : Query → Option Answer) (run : Query → Nat → RunOutcome Answer) : Prop :=
  ∀ query fuel, (∀ answer, run query fuel = .answered answer → logical query = some answer) ∧
    (run query fuel = .refused → logical query = none)

/-- What may be cached from an outcome: answers and refusals, not exhaustion. -/
def logicalEntry : RunOutcome Answer → Option (Option Answer)
  | .answered answer => some (some answer)
  | .refused => some none
  | .exhausted => none

/-- The faulty policy that records exhaustion as a refusal. -/
def exhaustedAsRefusal : RunOutcome Answer → Option (Option Answer)
  | .answered answer => some (some answer)
  | .refused => some none
  | .exhausted => some none

/-- **Cached logical entries are logical observations**, at every fuel. -/
theorem logicalEntry_sound {logical : Query → Option Answer}
    {run : Query → Nat → RunOutcome Answer} (adequate : Adequate logical run)
    {query : Query} {fuel : Nat} {entry : Option Answer}
    (cached : logicalEntry (run query fuel) = some entry) : entry = logical query := by
  cases outcome : run query fuel with
  | answered answer =>
      rw [outcome] at cached
      cases cached
      exact ((adequate query fuel).1 answer outcome).symm
  | refused =>
      rw [outcome] at cached
      cases cached
      exact ((adequate query fuel).2 outcome).symm
  | exhausted =>
      rw [outcome] at cached
      cases cached

/-- Logical entries do not depend on the fuel that produced them. -/
theorem logicalEntry_fuel_independent {logical : Query → Option Answer}
    {run : Query → Nat → RunOutcome Answer} (adequate : Adequate logical run)
    {query : Query} {fuel fuel' : Nat} {entry entry' : Option Answer}
    (first : logicalEntry (run query fuel) = some entry)
    (second : logicalEntry (run query fuel') = some entry') : entry = entry' :=
  (logicalEntry_sound adequate first).trans (logicalEntry_sound adequate second).symm

/-- **Exhaustion recorded as refusal is unsound** whenever an answerable query
exhausts some fuel. -/
theorem exhaustedAsRefusal_unsound {logical : Query → Option Answer}
    {run : Query → Nat → RunOutcome Answer} {query : Query} {fuel : Nat} {answer : Answer}
    (exhausted : run query fuel = .exhausted) (answerable : logical query = some answer) :
    exhaustedAsRefusal (run query fuel) = some none ∧ logical query ≠ none := by
  rw [exhausted, answerable]
  exact ⟨rfl, Option.some_ne_none answer⟩

end Separate

/-! ## Controls -/

namespace Controls

open Mettapedia.Machines.RevisionDependencySetCanary (Store environment)

/-! ### Late observers, using the existing authority-observation fixture -/

section Late

open Mettapedia.Machines.AuthorityObservationControls

/-- The authorized observation reads the evidence and the model stores. -/
def evidencePlusModel (live : RevisionEnvironment Store Nat) (_ : Unit) : Nat :=
  live.current .evidence + live.current .model

/-- The cached sum `7 + 3`, with the capture of the existing fixture. -/
def sumEntry : Cached Store Nat Unit Nat := ⟨(), capture, 10⟩

theorem sumEntry_recorded : Recorded evidencePlusModel sumEntry := by
  refine ⟨rfl, ?_⟩
  intro live agrees
  have evidence := agrees .evidence (by decide)
  have model := agrees .model (by decide)
  simp only [evidencePlusModel, evidence, model]

/-- Positive: the stable observer with bookkeeping validates the current
answer. -/
theorem stable_observer_validates_current_answer :
    sumEntry.answer = evidencePlusModel (projection (RevisionEnvironment.checkObserved
      sumEntry.view.captured stableObserve sumEntry.view.consulted initial).2) () :=
  sumEntry_recorded.answer_of_checkObserved projection stableObserve rfl rfl
    (fun store _ state => stable_observer_truthful store state)
    (fun store _ state => stable_observer_preserves_support store state _) initial rfl

/-- **Negative: every check accepts, each observer is truthful and keeps its
own key, and the cached answer is stale at publication.** The premise that the
whole consulted support is preserved cannot be weakened to the sampled key. -/
theorem late_observer_accepts_stale_answer :
    (RevisionEnvironment.checkObserved sumEntry.view.captured lateObserve
        sumEntry.view.consulted initial).1 = true ∧
      (∀ store state, (lateObserve store state).1 = (projection state).current store) ∧
      (∀ store state, (projection (lateObserve store state).2).current store =
        (projection state).current store) ∧
      sumEntry.answer ≠ evidencePlusModel (projection (RevisionEnvironment.checkObserved
        sumEntry.view.captured lateObserve sumEntry.view.consulted initial).2) () := by
  refine ⟨rfl, late_observer_truthful, late_observer_preserves_own_key, ?_⟩
  decide

end Late

/-! ### Sticky mismatch and incomplete capture: the gate is conservative -/

section Conservative

open Mettapedia.Machines.CapturedReadViewCanary

/-- The authorized observation of the evidence binding. -/
def evidenceBinding (live : RevisionEnvironment Store (Option Nat)) (_ : Unit) : Option Nat :=
  live.current .evidence

/-- A computation that saw a replaced binding during its run. -/
def sawReplacementEntry : Cached Store (Option Nat) Unit (Option Nat) :=
  ⟨(), sawReplacement, some 7⟩

/-- **A sticky mismatch refuses publication even when the answer happens to be
current**: publication permission is sufficient for currency, not
necessary. -/
theorem sticky_mismatch_refuses_current_answer :
    sawReplacementEntry.answer = evidenceBinding bindings () ∧
      ¬ sawReplacementEntry.view.CanPublish bindings :=
  ⟨rfl, restored_binding_cannot_publish⟩

/-- The same for a dropped capture obligation. -/
theorem incomplete_capture_refuses_current_answer :
    (⟨(), { observed with captureComplete := false }, some 7⟩ :
        Cached Store (Option Nat) Unit (Option Nat)).answer = evidenceBinding bindings () ∧
      ¬ ({ observed with captureComplete := false }).CanPublish bindings :=
  ⟨rfl, incomplete_capture_cannot_publish⟩

/-! ### Negative lookups and ordered duplicate rows -/

/-- The authorized complete ordered result of a value query. -/
def rowsOf (live : RevisionEnvironment Nat (List (Nat × Nat))) (query : Nat) :
    List (Nat × Nat) :=
  live.current query

/-- A cached complete result, captured by the existing read view. -/
def rowEntry (query : Nat) : Cached Nat (List (Nat × Nat)) Nat (List (Nat × Nat)) :=
  ⟨query, observedQuery query, (RevisionEnvironment.matchingRows acceptsValue queryRows).current query⟩

theorem rowEntry_recorded (query : Nat) : Recorded rowsOf (rowEntry query) := by
  refine ⟨rfl, ?_⟩
  intro live agrees
  exact agrees query (by simp [rowEntry, observedQuery, CapturedReadView.consult,
    CapturedReadView.admit])

/-- Positive: an insertion outside the consulted query keeps the cached
result publishable and current. -/
theorem nonmatching_insertion_keeps_cached_rows :
    (rowEntry 7).answer = rowsOf
      (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(2, 8)])) 7 :=
  (rowEntry_recorded 7).answer_of_canPublish nonmatching_insertion_can_publish

/-- **Negative lookup**: a cached absence is stale after a matching insertion,
and publication is refused. -/
theorem cached_absence_stale_after_insertion :
    (rowEntry 9).answer = [] ∧
      rowsOf (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(3, 9)])) 9 =
        [(3, 9)] ∧
      ¬ (rowEntry 9).view.CanPublish
        (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(3, 9)])) :=
  ⟨rfl, rfl, matching_insertion_invalidates_absence⟩

/-- **Ordered duplicate rows**: an equal payload is a new occurrence; the
cached result is stale and publication is refused. -/
theorem duplicate_row_stales_cached_rows :
    (rowEntry 7).answer = [(0, 7)] ∧
      rowsOf (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(2, 7)])) 7 =
        [(0, 7), (2, 7)] ∧
      ¬ (rowEntry 7).view.CanPublish
        (RevisionEnvironment.matchingRows acceptsValue (queryRows ++ [(2, 7)])) :=
  ⟨rfl, rfl, duplicate_payload_invalidates_complete_query⟩

end Conservative

/-! ### Native adapter premises and opaque callbacks -/

/-- The stores a native adapter can depend on. -/
inductive NativeStore where
  | outerPointer
  | privateRevision
  | symbolTable
  | episodeContext
  deriving DecidableEq

/-- An opaque callback's answer depends on its private revision and on the
process-global symbol table and the episode and library context. -/
def callbackAnswer (live : RevisionEnvironment NativeStore Nat) (_ : Unit) : Nat × Nat × Nat :=
  (live.current .privateRevision, live.current .symbolTable, live.current .episodeContext)

/-- Rechecking only the outer pointer. -/
def outerPointerOnly (_ : RevisionEnvironment NativeStore Nat) (_ : Unit) : List NativeStore :=
  [.outerPointer]

/-- Consulting the private revision, but neither the symbol table nor the
context. -/
def privateRevisionOnly (_ : RevisionEnvironment NativeStore Nat) (_ : Unit) :
    List NativeStore :=
  [.outerPointer, .privateRevision]

/-- Consulting every store the answer depends on. -/
def everyDependency (_ : RevisionEnvironment NativeStore Nat) (_ : Unit) : List NativeStore :=
  [.outerPointer, .privateRevision, .symbolTable, .episodeContext]

def nativeBase : RevisionEnvironment NativeStore Nat := ⟨fun _ => 0⟩

/-- **An opaque callback's private revision is not certified by rechecking
its outer pointer.** -/
theorem outer_pointer_recheck_does_not_certify :
    ¬ ReadsDetermine callbackAnswer outerPointerOnly := by
  apply not_readsDetermine_of_hidden (captured := nativeBase)
    (live := nativeBase.update .privateRevision 1) (query := ())
  · intro store member
    simp only [outerPointerOnly, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    rfl
  · decide

/-- Positive: consulting every dependency certifies the callback. -/
theorem every_dependency_certifies : ReadsDetermine callbackAnswer everyDependency := by
  intro captured live query agrees
  have privateRevision := agrees .privateRevision (by simp [everyDependency])
  have symbolTable := agrees .symbolTable (by simp [everyDependency])
  have episodeContext := agrees .episodeContext (by simp [everyDependency])
  simp only [callbackAnswer, privateRevision, symbolTable, episodeContext]

/-- The adapter premise: the symbol table and the episode context are
stabilized at given values. -/
def Stabilized (table context : Nat) (live : RevisionEnvironment NativeStore Nat) : Prop :=
  live.current .symbolTable = table ∧ live.current .episodeContext = context

/-- **Positive under the premise**: with a stabilized symbol table and context,
consulting the private revision suffices. -/
theorem private_revision_certifies_under_stabilization (table context : Nat) :
    ReadsDetermineOn (Stabilized table context) callbackAnswer privateRevisionOnly := by
  intro captured live query capturedStable liveStable agrees
  have privateRevision := agrees .privateRevision (by simp [privateRevisionOnly])
  simp only [callbackAnswer, privateRevision, capturedStable.1, capturedStable.2,
    liveStable.1, liveStable.2]

/-- **Negative without the premise**: a symbol-table change the adapter does
not consult changes the answer. -/
theorem private_revision_without_stabilization_fails :
    ¬ ReadsDetermine callbackAnswer privateRevisionOnly := by
  apply not_readsDetermine_of_hidden (captured := nativeBase)
    (live := nativeBase.update .symbolTable 1) (query := ())
  · intro store member
    simp only [privateRevisionOnly, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  · decide

/-! ### Exhaustion is not refusal -/

/-- A countdown: query `n` is answered by `n` once the fuel reaches `n`. -/
def countdown (query fuel : Nat) : RunOutcome Nat :=
  if query ≤ fuel then .answered query else .exhausted

theorem countdown_adequate : Adequate (fun query : Nat => some query) countdown := by
  intro query fuel
  constructor
  · intro answer ran
    unfold countdown at ran
    split at ran
    · cases ran
      rfl
    · cases ran
  · intro ran
    unfold countdown at ran
    split at ran <;> cases ran

/-- Positive: the logical entry recorded at enough fuel is the logical
answer. -/
theorem countdown_logical_entry : logicalEntry (countdown 3 5) = some (some 3) := by decide

/-- Negative: the exhausted run at fuel zero recorded as a refusal contradicts
the logical answer. -/
theorem countdown_exhaustion_is_not_refusal :
    exhaustedAsRefusal (countdown 1 0) = some none ∧ (some 1 : Option Nat) ≠ none ∧
      logicalEntry (countdown 1 0) = none := by
  decide

/-! ### Reuse is a separate observation -/

/-- Positive and negative at once: evicting a coherent entry keeps the answer
and loses the reuse. -/
theorem eviction_example :
    lookupOrCompute (id : Nat → Nat) (fun query => query + 1) Table.empty 4 =
        lookupOrCompute id (fun query => query + 1)
          (store id (fun query => query + 1) Table.empty 4) 4 ∧
      Reused id (store id (fun query : Nat => query + 1) Table.empty 4) 4 ∧
      ¬ Reused (id : Nat → Nat) (Table.empty : Table Nat Nat) 4 :=
  eviction_preserves_answer_loses_reuse
    (coherent_store_of_soundKey (soundKey_id _) (coherent_empty _ _) 4) 4 (store_key _ _ _ _)

end Controls

#print axioms soundKey_readingKey
#print axioms soundKey_readingKey_on
#print axioms recorded_record
#print axioms Recorded.answer_of_canPublish
#print axioms Recorded.answer_of_checkObserved
#print axioms canPublish_invalidate
#print axioms Notifies.observe_eq_of_counter_eq
#print axioms Notifies.soundKey_run
#print axioms Notifies.soundKey_sessions
#print axioms Notifies.windowRead_eq
#print axioms Notifies.certifies
#print axioms epochCoherent_of_reflTransGen
#print axioms epoch_lookup
#print axioms eviction_preserves_answer_loses_reuse
#print axioms logicalEntry_sound
#print axioms exhaustedAsRefusal_unsound
#print axioms Controls.late_observer_accepts_stale_answer
#print axioms Controls.stable_observer_validates_current_answer
#print axioms Controls.sticky_mismatch_refuses_current_answer
#print axioms Controls.cached_absence_stale_after_insertion
#print axioms Controls.duplicate_row_stales_cached_rows
#print axioms Controls.outer_pointer_recheck_does_not_certify
#print axioms Controls.private_revision_certifies_under_stabilization
#print axioms Controls.private_revision_without_stabilization_fails
#print axioms Controls.countdown_exhaustion_is_not_refusal

end Mettapedia.GSLT.Dynamics.CacheCoherence
