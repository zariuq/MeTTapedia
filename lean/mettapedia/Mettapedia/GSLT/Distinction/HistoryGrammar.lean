import Mettapedia.Cybernetics.DistinctionCalculus.History
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Causality.Trace

/-!
# The history grammar of the distinction calculus as a GSLT

The event grammar of `dcalculus_v2` §4 (`Cybernetics.DistinctionCalculus.History`)
has four events on a node set: evolution `T`, fork `Δ`, merge `⋆` and erasure
`ε`.  Its operational reading is a GSLT whose terms are configurations, the
multisets of live nodes, and whose steps fire one enabled event
(`historyGSLT`).  The events themselves label the steps of a
Hennessy–Milner system (`eventSystem`).

* **Histories are labelled paths and traces** (`run_eq_some_iff`): running a
  sequential history from a configuration succeeds exactly when there is a
  labelled path with those events.  A labelled path gives a running trace of
  the GSLT (`GSLT.Causality.Trace`) with one entry per event
  (`labelledPath_trace`), every running trace carries a sequential history of
  the same length (`trace_labelledPath`), and reachability in the GSLT is the
  existence of a history (`multiStep_iff_labelledPath`).
* **A step forgets its event** (`step_forgets_event`): erasing one copy of an
  idempotent node and merging two copies of it have the same endpoints.  The
  endpoint relation of a GSLT therefore cannot recover event costs; they live
  on the labelled system.
* **The parallel composition of the free history algebra is not
  interleaving-invariant** (`interleavings_differ`): `fork x` then `erase x`
  runs on `{x}`, `erase x` then `fork x` does not.  A parallel composition of
  histories needs an independence relation before it denotes runs.
* **Copy and merge** on configurations: the copy of a merge reaches the
  configuration of the merge of the copies (`copy_of_merge_runs`); if both
  Frobenius laws held on configurations, every two nodes would be equal
  (`frobenius_runs_force_subsingleton`, through `History.no_frobenius_merge`).
* **Costs on events, local Livšic** (`exact_iff_locallyClosed`): with free fork
  and erasure an event cost is the differential of an extensive potential
  exactly when it vanishes on the three elementary loops, and an exact cost
  sums to the change of potential along every labelled path
  (`labelledPath_cost`), so to zero on every closed history.
* **Without erasure the local test is unavailable** (`cycle_control`): on a
  three-cycle of evolution there is no loop on one or two nodes, the cost `1`
  per evolution is not exact, and the closed history around the cycle costs
  `3`.  Rho has no general deletion, so this is the regime of its global loop
  law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryGrammar

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus.History

universe u

/-- The two operations an event grammar needs: evolution and merge. -/
structure Grammar (V : Type u) where
  evolve : V → V
  merge : V → V → V

variable {V : Type u} [DecidableEq V] (G : Grammar V)

/-- The two-node configuration `{x, y}`. -/
def pair (x y : V) : Multiset V := x ::ₘ y ::ₘ 0

/-- One event fires on a configuration. -/
inductive Fires : Event V → Multiset V → Multiset V → Prop where
  | evolve {x : V} {live : Multiset V} : x ∈ live →
      Fires (.evolve x) live (G.evolve x ::ₘ live.erase x)
  | fork {x : V} {live : Multiset V} : x ∈ live → Fires (.fork x) live (x ::ₘ live)
  | merge {x y : V} {live : Multiset V} : pair x y ≤ live →
      Fires (.merge x y) live (G.merge x y ::ₘ (live - pair x y))
  | erase {x : V} {live : Multiset V} : x ∈ live → Fires (.erase x) live (live.erase x)

/-- **The history GSLT**: configurations rewritten by one event. -/
abbrev historyGSLT : GSLT.{u} where
  Term := Multiset V
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ event, Fires G event source target
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-- Events label the steps. -/
abbrev eventSystem : HennessyMilner.System.{0, u} (historyGSLT G) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Event V
  act := Fires G
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- Fire one event, if it is enabled. -/
def step : Event V → Multiset V → Option (Multiset V)
  | .evolve x, live => if x ∈ live then some (G.evolve x ::ₘ live.erase x) else none
  | .fork x, live => if x ∈ live then some (x ::ₘ live) else none
  | .merge x y, live =>
      if pair x y ≤ live then some (G.merge x y ::ₘ (live - pair x y)) else none
  | .erase x, live => if x ∈ live then some (live.erase x) else none

theorem step_eq_some_iff (event : Event V) (live result : Multiset V) :
    step G event live = some result ↔ Fires G event live result := by
  constructor
  · intro fired
    cases event with
    | evolve x =>
        simp only [step] at fired
        split_ifs at fired with enabled
        cases fired
        exact .evolve enabled
    | fork x =>
        simp only [step] at fired
        split_ifs at fired with enabled
        cases fired
        exact .fork enabled
    | merge x y =>
        simp only [step] at fired
        split_ifs at fired with enabled
        cases fired
        exact .merge enabled
    | erase x =>
        simp only [step] at fired
        split_ifs at fired with enabled
        cases fired
        exact .erase enabled
  · intro fires
    cases fires with
    | evolve enabled => simp [step, enabled]
    | fork enabled => simp [step, enabled]
    | merge enabled => simp [step, enabled]
    | erase enabled => simp [step, enabled]

/-- Run a sequential history: fire its events in order, failing at the first
event that is not enabled. -/
def run : List (Event V) → Multiset V → Option (Multiset V)
  | [], live => some live
  | event :: rest, live => (step G event live).bind (run rest)

/-- A labelled path of the event system. -/
inductive LabelledPath : Multiset V → List (Event V) → Multiset V → Prop where
  | nil (live : Multiset V) : LabelledPath live [] live
  | cons {live middle result : Multiset V} {event : Event V} {rest : List (Event V)} :
      Fires G event live middle → LabelledPath middle rest result →
        LabelledPath live (event :: rest) result

/-- **Sequential histories are labelled paths.** -/
theorem run_eq_some_iff (history : List (Event V)) (live result : Multiset V) :
    run G history live = some result ↔ LabelledPath G live history result := by
  induction history generalizing live with
  | nil =>
      constructor
      · intro ran
        cases ran
        exact .nil _
      · intro path
        cases path
        rfl
  | cons event rest inductionHypothesis =>
      constructor
      · intro ran
        simp only [run] at ran
        cases fired : step G event live with
        | none => rw [fired] at ran; cases ran
        | some middle =>
            rw [fired] at ran
            exact .cons ((step_eq_some_iff G event live middle).mp fired)
              ((inductionHypothesis middle).mp ran)
      · intro path
        cases path with
        | cons fires rest' =>
            simp only [run]
            rw [(step_eq_some_iff G event live _).mpr fires]
            exact (inductionHypothesis _).mpr rest'

/-- A trace of the history GSLT runs from one configuration to another when
its entries chain. -/
def TraceRuns : List (TraceEntry (historyGSLT G)) → Multiset V → Multiset V → Prop
  | [], live, result => live = result
  | entry :: rest, live, result => entry.source = live ∧ TraceRuns rest entry.target result

/-- **A history gives a trace**: a labelled path yields a running trace with one
entry per event. -/
theorem labelledPath_trace {live result : Multiset V} {history : List (Event V)}
    (path : LabelledPath G live history result) :
    ∃ trace : Trace (historyGSLT G), TraceRuns G trace live result ∧
      trace.length = history.length := by
  induction path with
  | nil live => exact ⟨[], rfl, rfl⟩
  | @cons live middle result event rest fires _ inductionHypothesis =>
      obtain ⟨trace, runs, length⟩ := inductionHypothesis
      refine ⟨⟨live, middle, ⟨event, fires⟩⟩ :: trace, ⟨rfl, runs⟩, ?_⟩
      change trace.length + 1 = rest.length + 1
      rw [length]

/-- **A trace carries a history**: every running trace is the shadow of a
sequential history of the same length. -/
theorem trace_labelledPath : ∀ (trace : List (TraceEntry (historyGSLT G)))
    {live result : Multiset V}, TraceRuns G trace live result →
      ∃ history, LabelledPath G live history result ∧ history.length = trace.length
  | [], live, result, runs => by
      change live = result at runs
      subst runs
      exact ⟨[], .nil _, rfl⟩
  | entry :: rest, live, result, runs => by
      obtain ⟨source, runsRest⟩ := runs
      obtain ⟨history, path, length⟩ := trace_labelledPath rest runsRest
      obtain ⟨event, fires⟩ := entry.step
      subst source
      exact ⟨event :: history, .cons fires path, by simp [length]⟩

/-- Reachability in the history GSLT is the existence of a sequential
history. -/
theorem multiStep_iff_labelledPath (live result : (historyGSLT G).Term) :
    (historyGSLT G).MultiStep live result ↔ ∃ history, LabelledPath G live history result := by
  constructor
  · intro steps
    induction steps with
    | refl live => exact ⟨[], .nil _⟩
    | step first _ inductionHypothesis =>
        obtain ⟨event, fires⟩ := first
        obtain ⟨history, rest⟩ := inductionHypothesis
        exact ⟨event :: history, .cons fires rest⟩
  · rintro ⟨history, path⟩
    induction path with
    | nil live => exact .refl _
    | cons fires _ inductionHypothesis => exact .step ⟨_, fires⟩ inductionHypothesis

/-! ## What a step forgets -/

/-- One labelled step: its event and its endpoints. -/
def LabelledStep := {transition : Event V × Multiset V × Multiset V //
  Fires G transition.1 transition.2.1 transition.2.2}

/-- The endpoints of a labelled step: what the GSLT step records. -/
def LabelledStep.endpoints (transition : LabelledStep G) : Multiset V × Multiset V :=
  transition.1.2

/-- The event of a labelled step. -/
def LabelledStep.event (transition : LabelledStep G) : Event V := transition.1.1

/-- **A step forgets its event.** For a node whose merge with itself is itself,
erasing one of two copies and merging the two copies have the same
endpoints. -/
def step_forgets_event (x : V) (idempotent : G.merge x x = x) :
    NonTrivialFiber (LabelledStep.endpoints G) (LabelledStep.event G) where
  left := ⟨(.erase x, pair x x, (pair x x).erase x), .erase (by simp [pair])⟩
  right := ⟨(.merge x x, pair x x, G.merge x x ::ₘ (pair x x - pair x x)),
    .merge le_rfl⟩
  sameShadow := by
    simp [LabelledStep.endpoints, pair, idempotent]
  differentValue := by
    simp [LabelledStep.event]

/-- **Interleavings of a parallel pair can differ in enablement.** -/
theorem interleavings_differ (x : V) :
    run G [.fork x, .erase x] {x} = some {x} ∧ run G [.erase x, .fork x] {x} = none := by
  constructor
  · simp [run, step]
  · simp [run, step]

/-! ## Copy and merge on configurations -/

theorem pair_sub_pair (x y : V) : pair x y - pair x y = 0 := by
  simp [pair]

theorem fork_pair_sub_pair (x y : V) : x ::ₘ pair x y - pair x y = {x} := by
  rw [Multiset.cons_sub_of_le x le_rfl, pair_sub_pair]
  rfl

theorem fork_right_pair_sub_pair (x y : V) : y ::ₘ pair x y - pair x y = {y} := by
  rw [Multiset.cons_sub_of_le y le_rfl, pair_sub_pair]
  rfl

omit [DecidableEq V] in
theorem pair_le_fork_left (x y : V) : pair x y ≤ x ::ₘ pair x y :=
  Multiset.le_cons_self _ _

omit [DecidableEq V] in
theorem pair_le_fork_right (x y : V) : pair x y ≤ y ::ₘ pair x y :=
  Multiset.le_cons_self _ _

/-- The left side of the first Frobenius law: merge, then copy. -/
theorem run_merge_then_fork (x y : V) :
    run G [.merge x y, .fork (G.merge x y)] (pair x y) =
      some (G.merge x y ::ₘ G.merge x y ::ₘ 0) := by
  simp [run, step]

/-- The right side of the first Frobenius law: copy the left node, then merge. -/
theorem run_fork_left_then_merge (x y : V) :
    run G [.fork x, .merge x y] (pair x y) = some (G.merge x y ::ₘ {x}) := by
  have enabled : x ∈ pair x y := by simp [pair]
  simp only [run, step, if_pos enabled, Option.bind_some, if_pos (pair_le_fork_left x y),
    fork_pair_sub_pair]

/-- The right side of the mirror law: copy the right node, then merge. -/
theorem run_fork_right_then_merge (x y : V) :
    run G [.fork y, .merge x y] (pair x y) = some (G.merge x y ::ₘ {y}) := by
  have enabled : y ∈ pair x y := by simp [pair]
  simp only [run, step, if_pos enabled, Option.bind_some, if_pos (pair_le_fork_right x y),
    fork_right_pair_sub_pair]

/-- **The copy of a merge is the merge of the copies**, on configurations:
always true. -/
theorem copy_of_merge_runs (x y : V) :
    run G [.fork x, .fork y, .merge x y, .merge x y] (pair x y) =
      run G [.merge x y, .fork (G.merge x y)] (pair x y) := by
  rw [run_merge_then_fork]
  have forkX : x ∈ pair x y := by simp [pair]
  have forkY : y ∈ x ::ₘ pair x y := by simp [pair]
  have firstMerge : pair x y ≤ y ::ₘ x ::ₘ pair x y :=
    (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
  have firstRest : y ::ₘ x ::ₘ pair x y - pair x y = pair x y := by
    rw [Multiset.cons_sub_of_le y (Multiset.le_cons_self _ _),
      Multiset.cons_sub_of_le x le_rfl, pair_sub_pair]
    exact Multiset.cons_swap y x 0
  have secondMerge : pair x y ≤ G.merge x y ::ₘ pair x y := Multiset.le_cons_self _ _
  have secondRest : G.merge x y ::ₘ pair x y - pair x y = {G.merge x y} := by
    rw [Multiset.cons_sub_of_le _ le_rfl, pair_sub_pair]
    rfl
  simp only [run, step, if_pos forkX, if_pos forkY, Option.bind_some, if_pos firstMerge,
    firstRest, if_pos secondMerge, secondRest]
  rfl

omit [DecidableEq V] in
theorem doubled_eq_iff (first second : V) :
    first ::ₘ first ::ₘ 0 = first ::ₘ {second} ↔ first = second := by
  rw [Multiset.cons_inj_right]
  exact Multiset.singleton_inj

/-- **No Frobenius law on configurations.** If, for every two nodes, both
Frobenius laws hold on the configurations they reach, every two nodes are
equal. -/
theorem frobenius_runs_force_subsingleton
    (frobenius : ∀ x y : V, run G [.merge x y, .fork (G.merge x y)] (pair x y) =
      run G [.fork x, .merge x y] (pair x y))
    (mirror : ∀ x y : V, run G [.merge x y, .fork (G.merge x y)] (pair x y) =
      run G [.fork y, .merge x y] (pair x y)) :
    ∀ x y : V, x = y := by
  have left : ∀ x y : V, diagonal (G.merge x y) = (x, G.merge x y) := by
    intro x y
    have same := frobenius x y
    rw [run_merge_then_fork, run_fork_left_then_merge, Option.some.injEq] at same
    rw [(doubled_eq_iff _ _).mp same]
    rfl
  have right : ∀ x y : V, diagonal (G.merge x y) = (G.merge x y, y) := by
    intro x y
    have same := mirror x y
    rw [run_merge_then_fork, run_fork_right_then_merge, Option.some.injEq] at same
    rw [(doubled_eq_iff _ _).mp same]
    rfl
  exact no_frobenius_merge G.merge left right

/-! ## Costs on events: local Livšic -/

/-- The cost of a history of the free algebra: the sum over its events. -/
def integral (cost : Event V → ℝ) : Hist V → ℝ
  | .empty => 0
  | .singleton event => cost event
  | .seq first second => integral cost first + integral cost second
  | .par first second => integral cost first + integral cost second

/-- An event cost is **exact** when it is the event differential of an
extensive potential. -/
def Exact (cost : Event V → ℝ) : Prop :=
  ∃ potential : V → ℝ, ∀ x y : V,
    cost (.evolve x) = potential (G.evolve x) - potential x ∧
      cost (.fork x) = potential x ∧
      cost (.erase x) = -potential x ∧
      cost (.merge x y) = potential (G.merge x y) - potential x - potential y

/-- An event cost is **locally closed** when it vanishes on the three
elementary loops `Δ_x ε_x`, `Δ_x T_x ε_{Tx}` and `Δ_x Δ_y ⋆_{xy} ε_{x⋆y}`. -/
def LocallyClosed (cost : Event V → ℝ) : Prop :=
  ∀ x y : V, integral cost (forkErase x) = 0 ∧
    integral cost (forkEvolveErase x (G.evolve x)) = 0 ∧
    integral cost (forkMergeErase x y (G.merge x y)) = 0

omit [DecidableEq V] in
/-- **Local Livšic** (`dcalculus_v2`, Theorem "Local Livšic"): with free fork and
erasure, an event cost is exact exactly when it is locally closed; the
potential is the fork component. -/
theorem exact_iff_locallyClosed (cost : Event V → ℝ) : Exact G cost ↔ LocallyClosed G cost := by
  constructor
  · rintro ⟨potential, laws⟩ x y
    obtain ⟨evolveLaw, forkLaw, -, -⟩ := laws x y
    obtain ⟨-, forkLawY, -, -⟩ := laws y x
    obtain ⟨-, -, eraseLaw, mergeLaw⟩ := laws x y
    obtain ⟨-, -, eraseEvolved, -⟩ := laws (G.evolve x) y
    obtain ⟨-, -, eraseMerged, -⟩ := laws (G.merge x y) y
    refine ⟨?_, ?_, ?_⟩
    · simp only [forkErase, integral, forkLaw, eraseLaw]
      ring
    · simp only [forkEvolveErase, integral, forkLaw, evolveLaw, eraseEvolved]
      ring
    · simp only [forkMergeErase, integral, forkLaw, forkLawY, mergeLaw, eraseMerged]
      ring
  · intro closed
    refine ⟨fun x => cost (.fork x), fun x y => ?_⟩
    have eraseLoop := (closed x y).1
    have evolveLoop := (closed x y).2.1
    have mergeLoop := (closed x y).2.2
    have eraseLoopEvolved := (closed (G.evolve x) y).1
    have eraseLoopMerged := (closed (G.merge x y) y).1
    simp only [forkErase, forkEvolveErase, forkMergeErase, integral] at eraseLoop evolveLoop mergeLoop eraseLoopEvolved eraseLoopMerged
    refine ⟨?_, rfl, ?_, ?_⟩
    · show cost (.evolve x) = cost (.fork (G.evolve x)) - cost (.fork x)
      linarith
    · show cost (.erase x) = -cost (.fork x)
      linarith
    · show cost (.merge x y) = cost (.fork (G.merge x y)) - cost (.fork x) - cost (.fork y)
      linarith

/-- The extensive potential of a configuration. -/
def configurationPotential (potential : V → ℝ) (live : Multiset V) : ℝ :=
  (live.map potential).sum

omit [DecidableEq V] in
theorem configurationPotential_cons (potential : V → ℝ) (x : V) (live : Multiset V) :
    configurationPotential potential (x ::ₘ live) = potential x + configurationPotential potential live := by
  simp [configurationPotential]

theorem configurationPotential_erase (potential : V → ℝ) {x : V} {live : Multiset V}
    (member : x ∈ live) :
    configurationPotential potential live =
      potential x + configurationPotential potential (live.erase x) := by
  conv_lhs => rw [← Multiset.cons_erase member]
  exact configurationPotential_cons potential x _

theorem configurationPotential_sub (potential : V → ℝ) {part live : Multiset V}
    (le : part ≤ live) :
    configurationPotential potential live =
      configurationPotential potential (live - part) + configurationPotential potential part := by
  conv_lhs => rw [← Multiset.sub_add_cancel le]
  simp [configurationPotential]

/-- **Stokes on labelled paths**: an exact cost sums, along every labelled path,
to the change of the extensive potential. -/
theorem labelledPath_cost {cost : Event V → ℝ} {potential : V → ℝ}
    (laws : ∀ x y : V,
      cost (.evolve x) = potential (G.evolve x) - potential x ∧
        cost (.fork x) = potential x ∧
        cost (.erase x) = -potential x ∧
        cost (.merge x y) = potential (G.merge x y) - potential x - potential y)
    {live result : Multiset V} {history : List (Event V)}
    (path : LabelledPath G live history result) :
    (history.map cost).sum =
      configurationPotential potential result - configurationPotential potential live := by
  induction path with
  | nil live => simp
  | cons fires _ inductionHypothesis =>
      rw [List.map_cons, List.sum_cons, inductionHypothesis]
      cases fires with
      | @evolve x live enabled =>
          rw [(laws x x).1, configurationPotential_erase potential enabled,
            configurationPotential_cons]
          ring
      | @fork x live enabled =>
          rw [(laws x x).2.1, configurationPotential_cons]
          ring
      | @merge x y live enabled =>
          rw [(laws x y).2.2.2, configurationPotential_sub potential enabled,
            configurationPotential_cons]
          simp only [configurationPotential, pair, Multiset.map_cons, Multiset.map_zero,
            Multiset.sum_cons, Multiset.sum_zero]
          ring
      | @erase x live enabled =>
          rw [(laws x x).2.2.1, configurationPotential_erase potential enabled]
          ring

/-- An exact cost vanishes on every closed labelled path. -/
theorem exact_closed_cost_zero {cost : Event V → ℝ} (exact : Exact G cost)
    {live : Multiset V} {history : List (Event V)} (path : LabelledPath G live history live) :
    (history.map cost).sum = 0 := by
  obtain ⟨potential, laws⟩ := exact
  rw [labelledPath_cost G laws path, sub_self]

/-! ## Without erasure: the three-cycle -/

/-- Evolution around a three-cycle; the merge plays no part. -/
def cycleGrammar : Grammar (Fin 3) where
  evolve x := x + 1
  merge x _ := x

/-- Cost one per evolution, nothing else. -/
def cycleCost : Event (Fin 3) → ℝ
  | .evolve _ => 1
  | _ => 0

/-- **The three-cycle control.** Evolution has no fixed point and no
two-cycle, so no loop on one or two nodes exists without fork and erasure; the
cost one per evolution is not the differential of any potential; the closed
history around the cycle costs `3`; and once fork and erasure are available,
no extension of the cost to them is locally closed. -/
theorem cycle_control :
    (∀ x : Fin 3, cycleGrammar.evolve x ≠ x ∧ cycleGrammar.evolve (cycleGrammar.evolve x) ≠ x) ∧
      (¬ ∃ potential : Fin 3 → ℝ, ∀ x,
        cycleCost (.evolve x) = potential (cycleGrammar.evolve x) - potential x) ∧
      LabelledPath cycleGrammar {0} [.evolve 0, .evolve 1, .evolve 2] {0} ∧
      ([Event.evolve 0, .evolve 1, .evolve 2].map cycleCost).sum = 3 ∧
      ∀ cost : Event (Fin 3) → ℝ, (∀ x, cost (.evolve x) = 1) →
        ¬ LocallyClosed cycleGrammar cost := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · rintro ⟨potential, laws⟩
    have at0 : (1 : ℝ) = potential 1 - potential 0 := laws 0
    have at1 : (1 : ℝ) = potential 2 - potential 1 := laws 1
    have at2 : (1 : ℝ) = potential 0 - potential 2 := laws 2
    linarith
  · refine .cons (.evolve (by simp)) (.cons (.evolve (by decide)) (.cons (.evolve (by decide))
      ?_))
    exact .nil _
  · simp [cycleCost]
    norm_num
  · intro cost evolveCost closed
    obtain ⟨potential, laws⟩ := (exact_iff_locallyClosed cycleGrammar cost).mpr closed
    have at0 : cost (.evolve 0) = potential 1 - potential 0 := (laws 0 0).1
    have at1 : cost (.evolve 1) = potential 2 - potential 1 := (laws 1 0).1
    have at2 : cost (.evolve 2) = potential 0 - potential 2 := (laws 2 0).1
    rw [evolveCost] at at0 at1 at2
    linarith

end Mettapedia.GSLT.Distinction.HistoryGrammar
