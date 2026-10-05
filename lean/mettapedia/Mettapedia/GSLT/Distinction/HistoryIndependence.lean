import Mettapedia.GSLT.Distinction.HistoryGrammar
import Mettapedia.GSLT.Causality.SiteValuationDescent

/-!
# Independence for the parallel composition of histories

`HistoryGrammar.interleavings_differ` shows that the parallel composition of
the free history algebra is not interleaving-invariant: `fork x` then `erase x`
runs on `{x}`, the other order does not.  A parallel composition needs an
independence relation before it denotes runs.  This module supplies one, from
what the events actually do to a configuration, and places it in the shared
trace core (`GSLT.Causality.EventConcurrency`).

* **What an event does** (`consumed`, `read`, `produced`, `fires_iff`).  Each
  event consumes nodes, reads nodes without consuming them, and produces nodes;
  it fires exactly when the consumed and read nodes are present, and then
  replaces the consumed nodes by the produced ones.  A fork reads the node it
  copies; evolution, merge and erasure consume theirs.
* **Concurrency at a configuration** (`Concurrent`): both consumed parts, and
  each event's read part, fit in the configuration together.  Concurrent events
  each still fire after the other, and the two orders reach one configuration
  (`run_swap`).  Two forks of one node share a read and are concurrent
  (`shared_read_concurrent`); a fork and the erasure of the only copy are not
  (`interleavings_differ_not_concurrent`), while with two copies they are
  (`doubled_concurrent`).
* **The history concurrency** (`concurrency`): this independence of enabled
  events, with its residuals, is an `EventConcurrency.Concurrency`.  The bag of
  events is a property of the trace (`events_descend`), and so is every event
  cost in a commutative monoid (`costValuation_descends`, a site valuation of
  `Causality.SiteValuationDescent`), including the real
  costs of the local Livšic theorem; the ordered event list is not
  (`eventList_not_descends`).

The relation is state-dependent: whether two events commute depends on the
multiplicities in the configuration, not on their syntax.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryIndependence

open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- The nodes an event consumes. -/
def consumed : Event V → Multiset V
  | .evolve x => {x}
  | .fork _ => 0
  | .merge x y => pair x y
  | .erase x => {x}

/-- The nodes an event reads without consuming them: a fork reads the node it
copies. -/
def read : Event V → Multiset V
  | .fork x => {x}
  | _ => 0

/-- The nodes an event produces. -/
def produced : Event V → Multiset V
  | .evolve x => {G.evolve x}
  | .fork x => {x}
  | .merge x y => {G.merge x y}
  | .erase _ => 0

/-- **An event fires exactly when its consumed and read nodes are present**, and
replaces the consumed nodes by the produced ones. -/
theorem fires_iff (event : Event V) (live result : Multiset V) :
    Fires G event live result ↔
      consumed event + read event ≤ live ∧ result = live - consumed event + produced G event := by
  constructor
  · intro fires
    cases fires with
    | @evolve x live member =>
        refine ⟨by simpa [consumed, read] using member, ?_⟩
        simp only [consumed, produced, Multiset.sub_singleton]
        rw [add_comm, Multiset.singleton_add]
    | @fork x live member =>
        refine ⟨by simpa [consumed, read] using member, ?_⟩
        simp only [consumed, produced, tsub_zero]
        rw [add_comm, Multiset.singleton_add]
    | @merge x y live enabled =>
        refine ⟨by simpa [consumed, read] using enabled, ?_⟩
        simp only [consumed, produced]
        rw [add_comm, Multiset.singleton_add]
    | @erase x live member =>
        refine ⟨by simpa [consumed, read] using member, ?_⟩
        simp [consumed, produced, Multiset.sub_singleton]
  · rintro ⟨enabled, rfl⟩
    cases event with
    | evolve x =>
        have member : x ∈ live := by simpa [consumed, read] using enabled
        have fires := Fires.evolve (G := G) member
        simp only [consumed, produced, Multiset.sub_singleton]
        rwa [add_comm, Multiset.singleton_add]
    | fork x =>
        have member : x ∈ live := by simpa [consumed, read] using enabled
        have fires := Fires.fork (G := G) member
        simp only [consumed, produced, tsub_zero]
        rwa [add_comm, Multiset.singleton_add]
    | merge x y =>
        have le : pair x y ≤ live := by simpa [consumed, read] using enabled
        have fires := Fires.merge (G := G) le
        simp only [consumed, produced]
        rwa [add_comm, Multiset.singleton_add]
    | erase x =>
        have member : x ∈ live := by simpa [consumed, read] using enabled
        have fires := Fires.erase (G := G) member
        simpa [consumed, produced, Multiset.sub_singleton] using fires

/-- **Concurrency at a configuration**: both consumed parts, together with
either event's read part, are present. -/
def Concurrent (live : Multiset V) (first second : Event V) : Prop :=
  consumed first + consumed second + read first ≤ live ∧
    consumed first + consumed second + read second ≤ live

omit [DecidableEq V] in
theorem Concurrent.symm {live : Multiset V} {first second : Event V}
    (concurrent : Concurrent live first second) : Concurrent live second first :=
  ⟨by simpa [add_comm (consumed second)] using concurrent.2,
    by simpa [add_comm (consumed second)] using concurrent.1⟩

omit [DecidableEq V] in
theorem Concurrent.enabled_left {live : Multiset V} {first second : Event V}
    (concurrent : Concurrent live first second) : consumed first + read first ≤ live :=
  le_trans (by
    rw [add_right_comm]
    exact le_self_add) concurrent.1

omit [DecidableEq V] in
theorem Concurrent.consumed_le {live : Multiset V} {first second : Event V}
    (concurrent : Concurrent live first second) : consumed first + consumed second ≤ live :=
  le_trans le_self_add concurrent.1

/-- The second event still fires after the first. -/
theorem Concurrent.enabled_after {live : Multiset V} {first second : Event V}
    (concurrent : Concurrent live first second) :
    consumed second + read second ≤ live - consumed first + produced G first := by
  refine le_trans ?_ le_self_add
  apply le_tsub_of_add_le_left
  simpa [add_assoc] using concurrent.2

/-- Both orders of two concurrent events reach one configuration. -/
theorem swap_result {live consumedFirst consumedSecond producedFirst producedSecond : Multiset V}
    (le : consumedFirst + consumedSecond ≤ live) :
    live - consumedFirst + producedFirst - consumedSecond + producedSecond =
      live - consumedSecond + producedSecond - consumedFirst + producedFirst := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp le
  have one : consumedFirst + consumedSecond + rest - consumedFirst + producedFirst - consumedSecond =
      rest + producedFirst := by
    rw [add_assoc consumedFirst consumedSecond rest, add_tsub_cancel_left, add_assoc,
      add_tsub_cancel_left]
  have two : consumedFirst + consumedSecond + rest - consumedSecond + producedSecond - consumedFirst =
      rest + producedSecond := by
    rw [add_comm consumedFirst consumedSecond, add_assoc consumedSecond consumedFirst rest,
      add_tsub_cancel_left, add_assoc, add_tsub_cancel_left]
  rw [one, two, add_right_comm]

/-- **The swap law of the history grammar**: two concurrent events run in either
order, to one configuration. -/
theorem run_swap {live : Multiset V} {first second : Event V}
    (concurrent : Concurrent live first second) :
    run G [first, second] live =
        some (live - consumed first + produced G first - consumed second + produced G second) ∧
      run G [second, first] live = run G [first, second] live := by
  have firstFires : step G first live = some (live - consumed first + produced G first) :=
    (step_eq_some_iff G first live _).mpr ((fires_iff G first live _).mpr
      ⟨concurrent.enabled_left, rfl⟩)
  have secondFires : step G second live = some (live - consumed second + produced G second) :=
    (step_eq_some_iff G second live _).mpr ((fires_iff G second live _).mpr
      ⟨concurrent.symm.enabled_left, rfl⟩)
  have secondAfter : step G second (live - consumed first + produced G first) =
      some (live - consumed first + produced G first - consumed second + produced G second) :=
    (step_eq_some_iff G second _ _).mpr ((fires_iff G second _ _).mpr
      ⟨concurrent.enabled_after G, rfl⟩)
  have firstAfter : step G first (live - consumed second + produced G second) =
      some (live - consumed second + produced G second - consumed first + produced G first) :=
    (step_eq_some_iff G first _ _).mpr ((fires_iff G first _ _).mpr
      ⟨concurrent.symm.enabled_after G, rfl⟩)
  have forward : run G [first, second] live =
      some (live - consumed first + produced G first - consumed second + produced G second) := by
    simp only [run, firstFires, Option.bind_some, secondAfter]
  refine ⟨forward, ?_⟩
  rw [forward]
  simp only [run, secondFires, Option.bind_some, firstAfter]
  rw [swap_result concurrent.consumed_le]

/-! ## The history concurrency in the shared trace core -/

/-- The history GSLT's interaction presentation: the site of a step is its
event. -/
abbrev presentation : InteractionPresentation (historyGSLT G) where
  Site := Event V
  Event event live result := PLift (Fires G event live result)
  sound evidence := ⟨_, evidence.down⟩

theorem target_eq {live : Multiset V} (event : (presentation G).Enabled live) :
    event.target = live - consumed event.site + produced G event.site :=
  ((fires_iff G _ _ _).mp event.evidence.down).2

/-- The residual of `second` after a concurrent `first`: the same event, fired at
`first`'s target. -/
def residual {live : Multiset V} (first second : (presentation G).Enabled live)
    (concurrent : Concurrent live first.site second.site) : (presentation G).Enabled first.target where
  site := second.site
  target := first.target - consumed second.site + produced G second.site
  evidence := ⟨(fires_iff G _ _ _).mpr ⟨by
    rw [target_eq G first]
    exact concurrent.enabled_after G, rfl⟩⟩

/-- **Independence for parallel composition**: concurrency of enabled events,
with residuals, in the shared trace core. -/
def concurrency : Concurrency (presentation G) where
  Independent {live} first second := Concurrent live first.site second.site
  symm concurrent := concurrent.symm
  residual {_ first second} concurrent := residual G first second concurrent
  residual_site _ := rfl
  close {live first second} concurrent := by
    change first.target - consumed second.site + produced G second.site =
      second.target - consumed first.site + produced G first.site
    rw [target_eq G first, target_eq G second]
    exact swap_result concurrent.consumed_le

/-- **The bag of events is a property of the trace.** -/
theorem events_descend : Descends (concurrency G).tiles (bagValuation (presentation G)) :=
  (concurrency G).bagValuation_descends

theorem onPath_cast {A : Type} [AddMonoid A] (valuation : OccurrenceValuation (presentation G) A)
    {s t t' : (historyGSLT G).Term} (h : t = t') (p : OccurrencePath (presentation G) s t) :
    valuation.onPath (h ▸ p) = valuation.onPath p :=
  valuation.onPath_cast h p

/-- An event cost. -/
def costValuation {A : Type} [AddMonoid A] (cost : Event V → A) :
    OccurrenceValuation (presentation G) A where
  grade occurrence := cost occurrence.site

/-- **Every event cost in a commutative monoid is a property of the trace.** -/
theorem costValuation_descends {A : Type} [AddCommMonoid A] (cost : Event V → A) :
    Descends (concurrency G).tiles (costValuation G cost) :=
  (concurrency G).siteValuation_descends cost

/-- The real event costs of the local Livšic theorem are properties of the
trace. -/
theorem realCost_descends (cost : Event V → ℝ) :
    Descends (concurrency G).tiles (costValuation G cost) :=
  costValuation_descends G cost

/-! ## Controls -/

omit [DecidableEq V] in
/-- **The interleavings that differ are not concurrent**: a fork and the erasure
of the only copy of its node. -/
theorem interleavings_differ_not_concurrent (x : V) :
    ¬ Concurrent ({x} : Multiset V) (.fork x) (.erase x) := by
  rintro ⟨first, _⟩
  have size := Multiset.card_le_card first
  simp [consumed, read] at size

/-- With two copies of the node, the fork and the erasure are concurrent and
commute. -/
theorem doubled_concurrent (x : V) :
    Concurrent (x ::ₘ {x} : Multiset V) (.fork x) (.erase x) ∧
      run G [.fork x, .erase x] (x ::ₘ {x}) = some (x ::ₘ {x}) ∧
      run G [.erase x, .fork x] (x ::ₘ {x}) = some (x ::ₘ {x}) := by
  have concurrent : Concurrent (x ::ₘ {x} : Multiset V) (.fork x) (.erase x) := by
    constructor <;> simp [consumed, read, Multiset.singleton_add]
  refine ⟨concurrent, ?_, ?_⟩
  · simp [run, step]
  · simp [run, step]

omit [DecidableEq V] in
/-- **Shared reads commute**: two forks of the only copy of a node are
concurrent. -/
theorem shared_read_concurrent (x : V) : Concurrent ({x} : Multiset V) (.fork x) (.fork x) := by
  constructor <;> simp [consumed, read]

/-- A read and a consuming event on the only copy are not concurrent, and the
reading event does not run after the consuming one when evolution moves the
node. -/
theorem read_consume_not_concurrent (x : V) (moves : G.evolve x ≠ x) :
    ¬ Concurrent ({x} : Multiset V) (.fork x) (.evolve x) ∧
      run G [.fork x, .evolve x] {x} = some (G.evolve x ::ₘ {x}) ∧
      run G [.evolve x, .fork x] {x} = none := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨first, _⟩
    have size := Multiset.card_le_card first
    simp [consumed, read] at size
  · simp [run, step]
  · simp [run, step, moves.symm]

/-- The three-cycle grammar evolves nodes `0` and `1` of `{0, 1}` concurrently. -/
def cyclePair : (concurrency cycleGrammar).Pair ((0 : Fin 3) ::ₘ {1}) where
  first := ⟨.evolve 0, _, ⟨.evolve (by simp)⟩⟩
  second := ⟨.evolve 1, _, ⟨.evolve (by simp)⟩⟩
  independent := by
    change Concurrent _ (.evolve 0) (.evolve 1)
    constructor <;> decide

/-- **The ordered event list is not a property of the trace.** -/
def eventList : OccurrenceValuation (presentation cycleGrammar)
    (Mettapedia.GSLT.Causality.Mazurkiewicz.SiteWord (Event (Fin 3))) where
  grade occurrence := ⟨[occurrence.site]⟩

theorem eventList_not_descends : ¬ Descends (concurrency cycleGrammar).tiles eventList := by
  intro descends
  have same := (descends_iff_tiles _ _).1 descends cyclePair
  change eventList.onPath (cyclePair.route (concurrency cycleGrammar)) =
    eventList.onPath (cyclePair.swapped (concurrency cycleGrammar)) at same
  unfold Concurrency.Pair.swapped at same
  rw [onPath_cast] at same
  have lists := congrArg Mettapedia.GSLT.Causality.Mazurkiewicz.SiteWord.toList same
  simp [Concurrency.Pair.route, OccurrenceValuation.onPath, eventList, Concurrency.occ,
    cyclePair, concurrency] at lists

end Mettapedia.GSLT.Distinction.HistoryIndependence
