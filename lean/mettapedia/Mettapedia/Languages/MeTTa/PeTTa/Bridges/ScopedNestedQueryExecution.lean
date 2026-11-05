import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource

/-!
# Nested query-leg execution with exact scoped residuals

Query legs are entered in authored order and read the current shared world.
Each captured list is visited before the enclosing suffix, without flattening
later queries into an earlier snapshot. The supplied leaf implementation has
its own checked source law. Reference handoff and suspension retain the exact
reached cursor; completing the described branch does not finish its collector.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open NestedQuerySource (Leg)
open ScopedMatchEntry (entrance)

variable {Context : Type}

inductive Stop (Context : Type) where
  | complete (state : State Context)
  | reference (saved : ScopedCursor Context)
  | suspended (request : ScopeBoundary) (saved : ScopedCursor Context)

def Stop.outcome (pending : List (CollectionWork Context)) : Stop Context →
    Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary
  | .complete state => .exhausted (state.cursor pending)
  | .reference saved => .exhausted saved
  | .suspended request saved => .suspended request saved

structure Execution (Context : Type) where
  budget : Nat
  events : List CollectedAnswer
  stop : Stop Context

def Execution.observation (pending : List (CollectionWork Context)) (execution : Execution Context) :=
  (execution.events, execution.stop.outcome pending)

abbrev Worker (Context : Type) :=
  Control → State Context → Context → List Nat → List (CollectionWork Context) → Execution Context

/-- Exact events and endpoint at the worker's supplied source budget.
Interruption at smaller budgets and concurrent observation of interior states
require separate execution/admission laws. -/
def Correct (program : SpaceSemantics.Program) (body destination : Atom) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending,
    (ScopedQuerySource.machine .relational program).run (worker caller state context origins pending).budget
      (entrance body destination caller state context origins pending) =
      (worker caller state context origins pending).observation pending

structure Leaf (program : SpaceSemantics.Program) (Context : Type) where
  source : Atom
  destination : Atom
  execute : Worker Context
  exact : Correct program source destination execute

def source : List Leg → Atom → Atom
  | [], body => body
  | leg :: rest, body => ScopedMatchPreparation.source leg.1 leg.2 (source rest body)

/-- Only the known child-evaluation head is removed from the descriptor;
inherited bindings, destination, reservations and cut boundary are retained. -/
def visit (worker : Worker Context) (older : List Goal) (context : Context) (origins : List Nat) :
    List (Nat × Control) → State Context → List (CollectionWork Context) → Execution Context
  | [], state, _ => ⟨0, [], .complete state⟩
  | entry :: rest, state, pending =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    match first.stop with
    | .reference _ => first
    | .suspended _ _ => first
    | .complete next =>
      let later := visit worker older context origins rest next pending
      ⟨first.budget + later.budget, first.events ++ later.events, later.stop⟩

theorem visit_exact (program : SpaceSemantics.Program) (body destination : Atom) (worker : Worker Context)
    (correct : Correct program body destination worker) (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (state : State Context) (pending : List (CollectionWork Context))
    (shapes : ∀ entry ∈ selected, entry.2.goals = .evaluate body destination :: older) :
    (ScopedQuerySource.machine .relational program).run (visit worker older context origins selected state pending).budget
      (state.cursor (ScopedQuerySource.work context origins selected ++ pending)) =
      (visit worker older context origins selected state pending).observation pending := by
  induction selected generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    let tail := ScopedQuerySource.work context origins rest ++ pending
    let caller := {entry.2 with goals := older}
    let first := worker caller state context (origins ++ [entry.1]) tail
    have shaped := shapes entry List.mem_cons_self
    have restored : ({entry.2 with goals := .evaluate body destination :: older} : Control) = entry.2 := by
      rw [← shaped]
    have actual := correct caller state context (origins ++ [entry.1]) tail
    change (ScopedQuerySource.machine .relational program).run first.budget
      (state.cursor (({entry.2 with goals := .evaluate body destination :: older}, context, origins ++ [entry.1]) :: tail)) =
      first.observation tail at actual
    rw [restored] at actual
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first, caller, tail, ScopedQuerySource.work] at stopped
      simpa only [visit, first, caller, tail, stopped, Execution.observation, Stop.outcome,
        ScopedQuerySource.work, List.map_cons, List.cons_append] using actual
    | suspended request saved =>
      dsimp only [first, caller, tail, ScopedQuerySource.work] at stopped
      simpa only [visit, first, caller, tail, stopped, Execution.observation, Stop.outcome,
        ScopedQuerySource.work, List.map_cons, List.cons_append] using actual
    | complete next =>
      have prefixRun : (ScopedQuerySource.machine .relational program).run first.budget
          (state.cursor ((entry.2, context, origins ++ [entry.1]) :: tail)) =
          (first.events, .exhausted (next.cursor tail)) := by
        simpa only [Execution.observation, stopped, Stop.outcome] using actual
      have later := ih next (fun entry member => shapes entry (List.mem_cons_of_mem _ member))
      have joined := (ScopedQuerySource.machine .relational program).established_and_pending first.budget
        (visit worker older context origins rest next pending).budget _ _ _ prefixRun
      change (ScopedQuerySource.machine .relational program).run _ _ =
        (first.events ++ ((ScopedQuerySource.machine .relational program).run _
          (next.cursor (ScopedQuerySource.work context origins rest ++ pending))).1,
          ((ScopedQuerySource.machine .relational program).run _
          (next.cursor (ScopedQuerySource.work context origins rest ++ pending))).2) at joined
      rw [later] at joined
      dsimp only [first, caller, tail, ScopedQuerySource.work] at stopped
      simpa only [visit, first, caller, tail, stopped, Execution.observation,
        ScopedQuerySource.work, List.map_cons, List.cons_append] using joined

def run (program : SpaceSemantics.Program) (leaf : Leaf program Context) : List Leg → Worker Context
  | [], caller, state, context, origins, pending => leaf.execute caller state context origins pending
  | leg :: rest, caller, state, context, origins, pending =>
    let entered := ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending
    match entered.result with
    | .reference saved => ⟨entered.budget, [], .reference saved⟩
    | .captured selected =>
      let later := visit (run program leaf rest) caller.goals context origins selected.choices state pending
      ⟨entered.budget + later.budget, later.events, later.stop⟩

/-- Every nested chain receipt is an exact finite source execution, including
late handoff and suspension. Successful completion is not a premise. -/
theorem run_exact (program : SpaceSemantics.Program) (leaf : Leaf program Context) (legs : List Leg) :
    Correct program (source legs leaf.source) leaf.destination (run program leaf legs) := by
  induction legs with
  | nil => exact leaf.exact
  | cons leg rest ih =>
    intro caller state context origins pending
    let entered := ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending
    have actual := entered.exact
    cases result : entered.result with
    | reference saved =>
      dsimp only [entered] at result
      simpa only [run, entered, result, source, Execution.observation, Stop.outcome,
        ScopedMatchEntry.Result.observation] using actual
    | captured selected =>
      have prefixRun : (ScopedQuerySource.machine .relational program).run entered.budget
          (entrance (source (leg :: rest) leaf.source) leaf.destination caller state context origins pending) =
          ([], .exhausted (state.cursor (ScopedQuerySource.work context origins selected.choices ++ pending))) := by
        simpa only [result, source, ScopedMatchEntry.Result.observation] using actual
      have later := visit_exact program (source rest leaf.source) leaf.destination (run program leaf rest)
        ih caller.goals context origins selected.choices state pending selected.shape
      have joined := (ScopedQuerySource.machine .relational program).established_and_pending entered.budget
        (visit (run program leaf rest) caller.goals context origins selected.choices state pending).budget _ _ [] prefixRun
      rw [later] at joined
      dsimp only [entered] at result
      simpa only [run, entered, result, Execution.observation, List.nil_append] using joined

/-- Installing this route in an existing source computation requires its
actual frontier and child-evaluation head. Unrelated work is not overwritten. -/
theorem reached_exact (program : SpaceSemantics.Program) (leaf : Leaf program Context) (legs : List Leg)
    (control : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (older : List Goal)
    (frontier : state.scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .evaluate (source legs leaf.source) leaf.destination :: older) :
    let caller := {control with goals := older}
    let execution := run program leaf legs caller state context origins pending
    (ScopedQuerySource.machine .relational program).run execution.budget
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) = execution.observation pending := by
  dsimp only
  have restored : ({control with goals := .evaluate (source legs leaf.source) leaf.destination :: older} : Control) = control := by
    rw [← atGoal]
  have same : entrance (source legs leaf.source) leaf.destination {control with goals := older} state context origins pending =
      (state.allocator, ⟨state.world, state.scope :: state.parents⟩) := by
    change state.cursor (({control with goals := .evaluate (source legs leaf.source) leaf.destination :: older}, context, origins) :: pending) = _
    rw [restored, ← frontier]
    rfl
  rw [← same]
  exact run_exact program leaf legs _ _ _ _ _

/-- Conservation of a store measure against the actual local collector.
Only completed branch prefixes are covered; public events alone would miss
packets recorded inside a collection. -/
def Balanced (measure : Effects.State → Nat) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending after,
    (worker caller state context origins pending).stop = .complete after →
      measure after.world.state + state.scope.collected.length =
        measure state.world.state + after.scope.collected.length

theorem visit_balanced (measure : Effects.State → Nat) (worker : Worker Context)
    (balanced : Balanced measure worker) (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (state : State Context) (pending : List (CollectionWork Context))
    (after : State Context) (completed : (visit worker older context origins selected state pending).stop = .complete after) :
    measure after.world.state + state.scope.collected.length =
      measure state.world.state + after.scope.collected.length := by
  induction selected generalizing state after with
  | nil =>
    have same : state = after := Stop.complete.inj completed
    subst after
    rfl
  | cons entry rest ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | suspended request saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | complete middle =>
      have firstBalance := balanced {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) middle stopped
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      have laterBalance := ih middle after completed
      omega

theorem run_balanced (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (measure : Effects.State → Nat) (balanced : Balanced measure leaf.execute) (legs : List Leg) :
    Balanced measure (run program leaf legs) := by
  induction legs with
  | nil => exact balanced
  | cons leg rest ih =>
    intro caller state context origins pending after completed
    unfold run at completed
    dsimp only at completed
    split at completed
    · cases completed
    next selected captured =>
      exact visit_balanced measure (run program leaf rest) ih caller.goals context origins
        selected.choices state pending after completed

/-- With an initially empty local collector, successful packet production
is exactly the increase of the conserved measure. Collector exit and copying
are subsequent source operations, not included in this statement. -/
theorem completed_packet_count (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (measure : Effects.State → Nat) (balanced : Balanced measure leaf.execute) (legs : List Leg)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (after : State Context)
    (initiallyEmpty : state.scope.collected = [])
    (completed : (run program leaf legs caller state context origins pending).stop = .complete after) :
    measure after.world.state = measure state.world.state + after.scope.collected.length := by
  have balance := run_balanced program leaf measure balanced legs caller state context origins pending after completed
  simpa only [initiallyEmpty, List.length_nil, Nat.add_zero] using balance

/-- Invariants of the execution carrier. Source observations use `State.cursor`
with the actual pending work; the scope's stored frontier is only metadata. -/
def Preserves (invariant : State Context → Prop) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending after,
    invariant state → (worker caller state context origins pending).stop = .complete after → invariant after

theorem visit_preserves (invariant : State Context → Prop) (worker : Worker Context)
    (preserves : Preserves invariant worker) (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (state : State Context) (pending : List (CollectionWork Context))
    (after : State Context) (valid : invariant state)
    (completed : (visit worker older context origins selected state pending).stop = .complete after) : invariant after := by
  induction selected generalizing state after with
  | nil =>
    have same : state = after := Stop.complete.inj completed
    subst after
    exact valid
  | cons entry rest ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | suspended request saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | complete middle =>
      have nextValid := preserves {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) middle valid stopped
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      exact ih middle after nextValid completed

theorem run_preserves (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (invariant : State Context → Prop) (preserves : Preserves invariant leaf.execute) (legs : List Leg) :
    Preserves invariant (run program leaf legs) := by
  induction legs with
  | nil => exact preserves
  | cons leg rest ih =>
    intro caller state context origins pending after valid completed
    unfold run at completed
    dsimp only at completed
    split at completed
    · cases completed
    next selected captured =>
      exact visit_preserves invariant (run program leaf rest) ih caller.goals context origins
        selected.choices state pending after valid completed

/-- Source-frame-qualified preservation. Typed payload laws need facts about
the reached caller, not an unrestricted promise for every possible caller. -/
def PreservesOn (goodCaller : Control → Prop) (invariant : State Context → Prop) (worker : Worker Context) : Prop :=
  ∀ caller state context origins pending after,
    goodCaller caller → invariant state →
    (worker caller state context origins pending).stop = .complete after → invariant after

theorem visit_preserves_on (goodCaller : Control → Prop) (invariant : State Context → Prop) (worker : Worker Context)
    (preserves : PreservesOn goodCaller invariant worker) (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (state : State Context) (pending : List (CollectionWork Context))
    (after : State Context)
    (callers : ∀ entry ∈ selected, goodCaller {entry.2 with goals := older}) (valid : invariant state)
    (completed : (visit worker older context origins selected state pending).stop = .complete after) : invariant after := by
  induction selected generalizing state after with
  | nil =>
    have same : state = after := Stop.complete.inj completed
    subst after
    exact valid
  | cons entry rest ih =>
    let first := worker {entry.2 with goals := older} state context (origins ++ [entry.1])
      (ScopedQuerySource.work context origins rest ++ pending)
    cases stopped : first.stop with
    | reference saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | suspended request saved =>
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      cases completed
    | complete middle =>
      have nextValid := preserves {entry.2 with goals := older} state context (origins ++ [entry.1])
        (ScopedQuerySource.work context origins rest ++ pending) middle (callers entry List.mem_cons_self) valid stopped
      dsimp only [first] at stopped
      simp only [visit, stopped] at completed
      exact ih middle after (fun choice member => callers choice (List.mem_cons_of_mem _ member)) nextValid completed

/-- Each query phase derives the next phase's caller facts from the actual
captured selection. No successful source run is supplied by this premise. -/
theorem run_preserves_family (program : SpaceSemantics.Program) (leaf : Leaf program Context)
    (goodCaller : List Leg → Control → Prop) (invariant : State Context → Prop)
    (atLeaf : PreservesOn (goodCaller []) invariant leaf.execute)
    (atCapture : ∀ leg rest caller state context origins pending
      (selected : ScopedMatchEntry.Selection (source rest leaf.source) leaf.destination caller.goals),
      goodCaller (leg :: rest) caller → invariant state →
      (ScopedMatchEntry.execute program leg.1 leg.2 (source rest leaf.source) leaf.destination caller state context origins pending).result =
        .captured selected →
      ∀ entry ∈ selected.choices, goodCaller rest {entry.2 with goals := caller.goals})
    (legs : List Leg) : PreservesOn (goodCaller legs) invariant (run program leaf legs) := by
  induction legs with
  | nil => exact atLeaf
  | cons leg rest ih =>
    intro caller state context origins pending after callerValid valid completed
    unfold run at completed
    dsimp only at completed
    split at completed
    · cases completed
    next selected captured =>
      exact visit_preserves_on (goodCaller rest) invariant (run program leaf rest) ih caller.goals context origins
        selected.choices state pending after
        (atCapture leg rest caller state context origins pending selected callerValid valid captured) valid completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryExecution
