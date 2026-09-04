import Mathlib.Data.Multiset.Basic
import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.ObservationDemandControl
import Mettapedia.GSLT.Core.ObservationScopeCompletion
import Mettapedia.GSLT.Core.WeightedOccurrenceControl
import Mettapedia.Languages.MeTTa.BindingVersions

/-!
# Strategy-independent MeTTa search state and scoped control

A search strategy is not the meaning of a MeTTa program.  This module gives
one occurrence-bearing branching kernel and then separates four independent
choices:

* the controller chooses which live occurrence to expand;
* the binding image records branch-local substitution state;
* a world handle names shared effect authority;
* the observation demand chooses whether order is visible.

When a pure finite kernel supplies an additive denotation, its completed
denotation is a multiset.  Any two occurrence-preserving controllers that
finish therefore agree on that bag, although their streams and finite prefixes
may differ.  This is inherited from `InferenceControl` and hence from the
branching GSLT accounting law, rather than re-proved for DFS or BFS separately.

Committed choice is represented by a scope identifier.  A commit removes all
pending continuations in the same scope regardless of their queue positions,
then retains the selected continuation's successors.  Thus commitment is not
implemented as stack truncation and remains meaningful for FIFO, portfolios,
and parallel frontiers.  Which answer wins is intentionally observable for a
first/ordered demand; the module does not falsely claim bag invariance for
competing commits.

Finally, binding capture uses `BindingVersions.Image`: exclusive local deltas
are promoted to immutable shared versions only when a continuation escapes.
The logical substitution is preserved exactly at that boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SearchStateStack

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationScopeCompletion
open Mettapedia.GSLT.Core.BranchCaptureAlgebra
open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open Mettapedia.Languages.MeTTa.BindingVersions

universe uControl uBinding uWorld uAnswer uMemory

variable {Control : Type uControl} {Binding : Type uBinding}
  {WorldHandle : Type uWorld} {Answer : Type uAnswer}
  {Memory : Type uMemory} {Node : Type*}

/-! ## One occurrence-bearing kernel, many controllers -/

/-- A stable semantic occurrence identity.  Equal answer values produced by
different occurrences remain distinct events. -/
abbrev OccurrenceId := Nat

/-- A delimiter for committed choice.  Scope identifiers are semantic
control data, not positions in a particular scheduler's queue. -/
abbrev ScopeId := Nat

/-- One resumable search occurrence.  `world` is a handle to shared effect
authority, not a copied world value. -/
@[ext] structure Continuation
    (Control : Type uControl) (Binding : Type uBinding)
    (WorldHandle : Type uWorld) where
  occurrence : OccurrenceId
  control : Control
  bindings : Binding
  world : WorldHandle
  scopes : List ScopeId
deriving DecidableEq, Repr

/-- Strategy-independent authorization of an emission and its successors. -/
structure Kernel
    (Control : Type uControl) (Binding : Type uBinding)
    (WorldHandle : Type uWorld) (Answer : Type uAnswer) where
  emit : Continuation Control Binding WorldHandle → Option Answer
  successors : Continuation Control Binding WorldHandle →
    List (Continuation Control Binding WorldHandle)

namespace Kernel

/-- Forget the MeTTa-specific fields only after retaining them in each node;
the resulting object is the generic branching coalgebra used by GSLT control. -/
def toBranchingSystem
    (kernel : Kernel Control Binding WorldHandle Answer) :
    BranchingSystem (Continuation Control Binding WorldHandle) Answer where
  emit := kernel.emit
  successors := kernel.successors

/-- Any stateful controller is a realization of the same kernel. -/
abbrev Strategy
    (_kernel : Kernel Control Binding WorldHandle Answer)
    (Memory : Type uMemory) :=
  Controller (Continuation Control Binding WorldHandle) Answer Memory

/-- Completed occurrence-preserving strategies agree exactly at bag level.
No search order appears in the statement. -/
theorem completed_strategies_bag_agree
    (kernel : Kernel Control Binding WorldHandle Answer)
    {FirstMemory SecondMemory : Type*}
    (first : kernel.Strategy FirstMemory)
    (second : kernel.Strategy SecondMemory)
    (denotation : AdditiveDenotation kernel.toBranchingSystem)
    (roots : List (Continuation Control Binding WorldHandle))
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        kernel.toBranchingSystem first firstFuel
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        kernel.toBranchingSystem second secondFuel
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial second roots)).search.frontier = []) :
    eventBag
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
          kernel.toBranchingSystem first firstFuel
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)).search.events =
      eventBag
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
          kernel.toBranchingSystem second secondFuel
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial second roots)).search.events :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.completed_controllers_bag_agree
    kernel.toBranchingSystem first second denotation roots firstFuel secondFuel
    firstComplete secondComplete

/-- Every controlled run is also a path in the generic inference-control
GSLT.  This is the bridge from a concrete MeTTa kernel to the deeper theory. -/
def controlGSLT
    (kernel : Kernel Control Binding WorldHandle Answer)
    (strategy : kernel.Strategy Memory) :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.toGSLT
    kernel.toBranchingSystem strategy

end Kernel

/-! ## Observation-indexed equality -/

/-- Readouts retain which equality contract the consumer requested. -/
inductive Readout (Answer : Type uAnswer) where
  | first (answer : Option Answer)
  | finitePrefix (answers : List Answer)
  | completeBag (answers : Multiset Answer)
  | orderedStream (answers : List Answer)
  | undetermined (answers : List Answer)

/-- Interpret one event stream according to an explicit observation demand. -/
def observe (demand : CompletionDemand) (answers : List Answer) : Readout Answer :=
  match demand with
  | .first => .first answers.head?
  | .finitePrefix count => .finitePrefix (answers.take count)
  | .completeBag => .completeBag answers
  | .orderedStream => .orderedStream answers
  | .undetermined => .undetermined answers

/-- Permuting a completed stream cannot change its complete-bag readout. -/
theorem observe_completeBag_eq_of_perm {first second : List Answer}
    (same : first.Perm second) :
    observe .completeBag first = observe .completeBag second := by
  change Readout.completeBag (first : Multiset Answer) =
    Readout.completeBag (second : Multiset Answer)
  exact congrArg Readout.completeBag (Quot.sound same)

/-- Complete-bag equality preserves multiplicity; it is not set equality. -/
theorem duplicate_occurrences_are_observable (answer : Answer) :
    observe .completeBag [answer, answer] ≠ observe .completeBag [answer] := by
  intro equal
  have sameCardinality := congrArg (fun readout =>
    match readout with
    | .completeBag answers => answers.card
    | _ => 0) equal
  simp [observe] at sameCardinality

/-! ## Binding capture at a scheduler boundary -/

/-- Fork only the binding component through a generic forkable realization.
The selected occurrence keeps its identity and the child receives a fresh
identity supplied by the occurrence authority.  Control, world authority, and
scope membership are transported without being reinterpreted. -/
def Continuation.forkBindings
    {Logical Seed Update : Type*}
    (store : ForkableStore Logical Binding Seed Update)
    (continuation : Continuation Control Binding WorldHandle)
    (seed : Seed) (childOccurrence : OccurrenceId) :
    Continuation Control Binding WorldHandle ×
      Continuation Control Binding WorldHandle :=
  let images := store.fork continuation.bindings seed
  ({ continuation with bindings := images.1 },
   { continuation with
      occurrence := childOccurrence
      bindings := images.2 })

/-- Both continuation images retain the source logical substitution exactly,
independently of the physical fork realization. -/
theorem forkBindings_denotations_exact
    {Logical Seed Update : Type*}
    (store : ForkableStore Logical Binding Seed Update)
    (continuation : Continuation Control Binding WorldHandle)
    (seed : Seed) (childOccurrence : OccurrenceId) :
    store.denote
        (continuation.forkBindings store seed childOccurrence).1.bindings =
        store.denote continuation.bindings ∧
      store.denote
        (continuation.forkBindings store seed childOccurrence).2.bindings =
        store.denote continuation.bindings := by
  constructor
  · exact store.fork_left_exact continuation.bindings seed
  · exact store.fork_right_exact continuation.bindings seed

/-- A physical fork neither duplicates one semantic occurrence identity nor
derives a child identity from scheduler position. -/
theorem forkBindings_occurrences
    {Logical Seed Update : Type*}
    (store : ForkableStore Logical Binding Seed Update)
    (continuation : Continuation Control Binding WorldHandle)
    (seed : Seed) (childOccurrence : OccurrenceId) :
    (continuation.forkBindings store seed childOccurrence).1.occurrence =
        continuation.occurrence ∧
      (continuation.forkBindings store seed childOccurrence).2.occurrence =
        childOccurrence := by
  simp [Continuation.forkBindings]

/-- Physical binding capture preserves every non-binding authority. -/
theorem forkBindings_preserves_context
    {Logical Seed Update : Type*}
    (store : ForkableStore Logical Binding Seed Update)
    (continuation : Continuation Control Binding WorldHandle)
    (seed : Seed) (childOccurrence : OccurrenceId) :
    let images := continuation.forkBindings store seed childOccurrence
    images.1.control = continuation.control ∧
      images.2.control = continuation.control ∧
      images.1.world = continuation.world ∧
      images.2.world = continuation.world ∧
      images.1.scopes = continuation.scopes ∧
      images.2.scopes = continuation.scopes := by
  simp [Continuation.forkBindings]

/-- Promote only the binding image when a continuation leaves its exclusive
execution quantum.  Control, occurrence identity, world authority, and scope
membership are unchanged. -/
def Continuation.escapeBindings
    (continuation : Continuation Control Image WorldHandle) :
    Continuation Control Image WorldHandle :=
  { continuation with bindings := continuation.bindings.escape }

@[simp] theorem escapeBindings_occurrence
    (continuation : Continuation Control Image WorldHandle) :
    continuation.escapeBindings.occurrence = continuation.occurrence := rfl

@[simp] theorem escapeBindings_control
    (continuation : Continuation Control Image WorldHandle) :
    continuation.escapeBindings.control = continuation.control := rfl

@[simp] theorem escapeBindings_world
    (continuation : Continuation Control Image WorldHandle) :
    continuation.escapeBindings.world = continuation.world := rfl

@[simp] theorem escapeBindings_scopes
    (continuation : Continuation Control Image WorldHandle) :
    continuation.escapeBindings.scopes = continuation.scopes := rfl

/-- Escape preserves the authoritative logical substitution. -/
theorem escapeBindings_exact
    (continuation : Continuation Control Image WorldHandle) :
    Image.denote continuation.escapeBindings.bindings =
      Image.denote continuation.bindings :=
  escape_exact continuation.bindings

/-- After escape the binding component admits an independently owned,
multi-shot frontier entry. -/
theorem escapeBindings_admits_ownedMultiShot
    (continuation : Continuation Control Image WorldHandle) :
    Admitted (Image.capacity continuation.escapeBindings.bindings)
      .ownedMultiShot :=
  escape_admits_multiShot continuation.bindings

/-! ## Scheduler-independent scoped commitment -/

/-- Expansion may commit the selected occurrence's innermost authored scope.
`none` is ordinary nondeterministic expansion. -/
structure ScopedExpansion (Node : Type*) (Answer : Type*) where
  emit : Option Answer
  successors : List Node
  commitScope : Option ScopeId

/-- A scoped kernel also exposes the scopes carried by each live node. -/
structure ScopedKernel (Node : Type*) (Answer : Type*) where
  scopes : Node → List ScopeId
  expand : Node → ScopedExpansion Node Answer

/-- Remove every pending occurrence owned by the committed scope. -/
def pruneScope (scopes : Node → List ScopeId) (scope : ScopeId)
    (frontier : List Node) : List Node :=
  frontier.filter fun node => scope ∉ scopes node

@[simp] theorem mem_pruneScope_iff [DecidableEq Node]
    (scopes : Node → List ScopeId) (scope : ScopeId)
    (node : Node) (frontier : List Node) :
    node ∈ pruneScope scopes scope frontier ↔
      node ∈ frontier ∧ scope ∉ scopes node := by
  simp [pruneScope]

/-- Scope pruning is independent of the physical order of the pending queue. -/
theorem pruneScope_perm (scopes : Node → List ScopeId) (scope : ScopeId)
    {first second : List Node} (same : first.Perm second) :
    (pruneScope scopes scope first).Perm
      (pruneScope scopes scope second) := by
  exact same.filter _

/-- Events and residual work produced by a scoped kernel. -/
structure ScopedSnapshot (Node : Type*) (Answer : Type*) where
  events : List (Emission Node Answer)
  frontier : List Node
deriving DecidableEq, Repr

namespace ScopedSnapshot

def initial (roots : List Node) : ScopedSnapshot Node Answer :=
  ⟨[], roots⟩

private def eventFor (node : Node) : Option Answer → List (Emission Node Answer)
  | none => []
  | some answer => [⟨node, answer⟩]

/-- One scoped step.  The scheduler may reorder occurrences, but a commit is
interpreted by scope membership rather than queue position. -/
def tick (kernel : ScopedKernel Node Answer) (scheduler : Scheduler Node)
    (snapshot : ScopedSnapshot Node Answer) : ScopedSnapshot Node Answer :=
  match scheduler.reorder snapshot.frontier with
  | [] => snapshot
  | node :: pending =>
      let expansion := kernel.expand node
      let retained :=
        match expansion.commitScope with
        | none => pending
        | some scope => pruneScope kernel.scopes scope pending
      { events := snapshot.events ++ eventFor node expansion.emit
        frontier := scheduler.integrate retained expansion.successors }

def run (kernel : ScopedKernel Node Answer) (scheduler : Scheduler Node) :
    Nat → ScopedSnapshot Node Answer → ScopedSnapshot Node Answer
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => tick kernel scheduler
      (run kernel scheduler fuel snapshot)

/-- An ordinary expansion retains every pending and generated occurrence
exactly once, regardless of scheduling policy. -/
theorem tick_frontier_perm_of_noCommit
    (kernel : ScopedKernel Node Answer) (scheduler : Scheduler Node)
    (snapshot : ScopedSnapshot Node Answer) (node : Node)
    (pending : List Node)
    (selected : scheduler.reorder snapshot.frontier = node :: pending)
    (ordinary : (kernel.expand node).commitScope = none) :
    (tick kernel scheduler snapshot).frontier.Perm
      (pending ++ (kernel.expand node).successors) := by
  simp only [tick, selected]
  rw [ordinary]
  exact scheduler.integrate_complete pending (kernel.expand node).successors

/-- A committing expansion retains exactly the out-of-scope pending
occurrences and the selected branch's successors. -/
theorem tick_frontier_perm_of_commit
    (kernel : ScopedKernel Node Answer) (scheduler : Scheduler Node)
    (snapshot : ScopedSnapshot Node Answer) (node : Node)
    (pending : List Node) (scope : ScopeId)
    (selected : scheduler.reorder snapshot.frontier = node :: pending)
    (commits : (kernel.expand node).commitScope = some scope) :
    (tick kernel scheduler snapshot).frontier.Perm
      (pruneScope kernel.scopes scope pending ++
        (kernel.expand node).successors) := by
  simp only [tick, selected]
  rw [commits]
  exact scheduler.integrate_complete _ _

/-- A sibling in the committed scope is absent from the retained pending
frontier. -/
theorem committed_sibling_is_pruned [DecidableEq Node]
    (kernel : ScopedKernel Node Answer) (scope : ScopeId)
    (pending : List Node) (sibling : Node)
    (inside : scope ∈ kernel.scopes sibling) :
    sibling ∉ pruneScope kernel.scopes scope pending := by
  simp [pruneScope, inside]

/-- Pending work outside the committed scope survives. -/
theorem outside_scope_survives [DecidableEq Node]
    (kernel : ScopedKernel Node Answer) (scope : ScopeId)
    (pending : List Node) (node : Node)
    (live : node ∈ pending) (outside : scope ∉ kernel.scopes node) :
    node ∈ pruneScope kernel.scopes scope pending := by
  simp [pruneScope, live, outside]

end ScopedSnapshot

/-! ## Stateful controllers over scoped commitment

Committed choice does not force a fixed traversal discipline.  A controller
may change its scheduling policy after every expansion while the kernel alone
retains authority to request scope pruning.
-/

/-- A strategy with private memory for a scoped kernel.  Its scheduler may
change over time; its `advance` function observes but does not authorize an
expansion. -/
structure ScopedController (Node : Type*) (Answer : Type*) (Memory : Type*) where
  initialMemory : Memory
  scheduler : Memory → Scheduler Node
  advance : Memory → Node → ScopedExpansion Node Answer → Memory

namespace ScopedController

/-- Embed a fixed scheduler as the memory-free special case. -/
def fixed (scheduler : Scheduler Node) : ScopedController Node Answer Unit where
  initialMemory := ()
  scheduler _ := scheduler
  advance _ _ _ := ()

end ScopedController

/-- Search observations and strategy memory evolve together. -/
structure ControlledScopedSnapshot
    (Node : Type*) (Answer : Type*) (Memory : Type*) where
  search : ScopedSnapshot Node Answer
  memory : Memory
deriving DecidableEq, Repr

namespace ControlledScopedSnapshot

def initial (controller : ScopedController Node Answer Memory)
    (roots : List Node) : ControlledScopedSnapshot Node Answer Memory :=
  ⟨ScopedSnapshot.initial roots, controller.initialMemory⟩

/-- One controlled scoped step.  The strategy chooses an occurrence; the
kernel decides whether that occurrence commits a scope. -/
def tick (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (snapshot : ControlledScopedSnapshot Node Answer Memory) :
    ControlledScopedSnapshot Node Answer Memory :=
  let scheduler := controller.scheduler snapshot.memory
  { search := ScopedSnapshot.tick kernel scheduler snapshot.search
    memory :=
      match scheduler.reorder snapshot.search.frontier with
      | [] => snapshot.memory
      | node :: _ =>
          controller.advance snapshot.memory node (kernel.expand node) }

def run (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory) :
    Nat → ControlledScopedSnapshot Node Answer Memory →
      ControlledScopedSnapshot Node Answer Memory
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => tick kernel controller
      (run kernel controller fuel snapshot)

@[simp] theorem tick_search (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (snapshot : ControlledScopedSnapshot Node Answer Memory) :
    (tick kernel controller snapshot).search =
      ScopedSnapshot.tick kernel
        (controller.scheduler snapshot.memory) snapshot.search := rfl

/-- With no selected occurrence a controller cannot mutate even its private
memory. -/
theorem tick_memory_eq_of_reorder_nil
    (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (snapshot : ControlledScopedSnapshot Node Answer Memory)
    (empty : (controller.scheduler snapshot.memory).reorder
      snapshot.search.frontier = []) :
    (tick kernel controller snapshot).memory = snapshot.memory := by
  simp [tick, empty]

/-- Stateful strategy changes cannot alter the frontier conservation law for
an ordinary expansion. -/
theorem tick_frontier_perm_of_noCommit
    (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (snapshot : ControlledScopedSnapshot Node Answer Memory)
    (node : Node) (pending : List Node)
    (selected : (controller.scheduler snapshot.memory).reorder
      snapshot.search.frontier = node :: pending)
    (ordinary : (kernel.expand node).commitScope = none) :
    (tick kernel controller snapshot).search.frontier.Perm
      (pending ++ (kernel.expand node).successors) := by
  exact ScopedSnapshot.tick_frontier_perm_of_noCommit
    kernel (controller.scheduler snapshot.memory) snapshot.search
    node pending selected ordinary

/-- Stateful strategy changes cannot alter which pending occurrences a
kernel-authorized scoped commit removes. -/
theorem tick_frontier_perm_of_commit
    (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (snapshot : ControlledScopedSnapshot Node Answer Memory)
    (node : Node) (pending : List Node) (scope : ScopeId)
    (selected : (controller.scheduler snapshot.memory).reorder
      snapshot.search.frontier = node :: pending)
    (commits : (kernel.expand node).commitScope = some scope) :
    (tick kernel controller snapshot).search.frontier.Perm
      (pruneScope kernel.scopes scope pending ++
        (kernel.expand node).successors) := by
  exact ScopedSnapshot.tick_frontier_perm_of_commit
    kernel (controller.scheduler snapshot.memory) snapshot.search
    node pending scope selected commits

/-- Observation budgets compose while carrying strategy memory and scoped
frontier state together. -/
theorem run_add (kernel : ScopedKernel Node Answer)
    (controller : ScopedController Node Answer Memory)
    (left right : Nat)
    (snapshot : ControlledScopedSnapshot Node Answer Memory) :
    run kernel controller (left + right) snapshot =
      run kernel controller right (run kernel controller left snapshot) := by
  induction right with
  | zero => rw [Nat.add_zero]; rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      simp only [run]
      rw [inductionHypothesis]

end ControlledScopedSnapshot

/-! ## Shared-world effects and observation-relative serializability -/

/-- A tiny reference language used to expose the effect law.  Production
effects may be space operations, transactions, I/O, or foreign calls. -/
inductive CounterAction where
  | add (amount : Nat)
  | set (value : Nat)
deriving DecidableEq, Repr

def CounterAction.run : Nat → CounterAction → Nat
  | state, .add amount => state + amount
  | _, .set value => value

/-- A batch is reorderable only relative to its declared observer. -/
def SerializableCounterAt {View : Type*} (observeWorld : Nat → View)
    (initialWorld : Nat) (actions : List CounterAction) : Prop :=
  SerializableAt observeWorld CounterAction.run initialWorld actions

private theorem activateAll_add (initialWorld : Nat) (amounts : List Nat) :
    activateAll (fun state amount : Nat => state + amount)
      initialWorld amounts = initialWorld + amounts.sum := by
  induction amounts generalizing initialWorld with
  | nil => simp [activateAll]
  | cons amount rest inductionHypothesis =>
      change activateAll (fun state amount : Nat => state + amount)
        (initialWorld + amount) rest =
          initialWorld + (amount + rest.sum)
      rw [inductionHypothesis]
      omega

/-- Addition effects commute and therefore admit every serial ordering under
exact final-state observation. -/
theorem additions_are_serializable (initialWorld : Nat)
    (amounts : List Nat) :
    SerializableAt id (fun state amount : Nat => state + amount)
      initialWorld amounts := by
  intro ordering same
  simp only [id_eq]
  rw [activateAll_add, activateAll_add, same.sum_eq]

/-- Negative control: two writes to the same world cell are not serializable
under exact observation. -/
theorem competing_sets_are_not_serializable :
    ¬ SerializableCounterAt id 0
      [CounterAction.set 1, CounterAction.set 2] := by
  intro serializable
  have swapped := serializable
    [CounterAction.set 2, CounterAction.set 1] (by decide)
  norm_num [SerializableCounterAt, activateAll, CounterAction.run] at swapped

/-! ## Positive and negative controls -/

namespace Canaries

/-- Pure alternatives may expose different streams while denoting the same
completed occurrence bag. -/
theorem pure_streams_differ_bags_agree :
    (Mettapedia.GSLT.Core.BranchingTemporal.run
          FiniteSearch.system Scheduler.breadthFirst 3
          (Mettapedia.GSLT.Core.BranchingTemporal.initial
            [FiniteSearch.twoAnswers])).events.map
          Emission.value ≠
        (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
          Scheduler.reverseBreadthFirst 3
          (Mettapedia.GSLT.Core.BranchingTemporal.initial
            [FiniteSearch.twoAnswers])).events.map
          Emission.value ∧
      eventBag
          (Mettapedia.GSLT.Core.BranchingTemporal.run
            FiniteSearch.system Scheduler.breadthFirst 3
            (Mettapedia.GSLT.Core.BranchingTemporal.initial
              [FiniteSearch.twoAnswers])).events =
        eventBag
          (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
            Scheduler.reverseBreadthFirst 3
            (Mettapedia.GSLT.Core.BranchingTemporal.initial
              [FiniteSearch.twoAnswers])).events :=
  Mettapedia.GSLT.Core.BranchingTemporal.FiniteSearch.twoAnswers_streams_differ_bags_agree

inductive CommitNode where
  | root
  | left
  | right
deriving DecidableEq, Repr

def commitKernel : ScopedKernel CommitNode Bool where
  scopes
    | .root => []
    | .left => [0]
    | .right => [0]
  expand
    | .root => ⟨none, [.left, .right], none⟩
    | .left => ⟨some false, [], some 0⟩
    | .right => ⟨some true, [], some 0⟩

/-- Breadth-first selection commits the left witness. -/
theorem breadthFirst_commits_left :
    (ScopedSnapshot.run commitKernel Scheduler.breadthFirst 2
      (ScopedSnapshot.initial [.root])).events.map Emission.value = [false] := by
  decide

/-- A different lawful scheduler commits the right witness. -/
theorem reverse_commits_right :
    (ScopedSnapshot.run commitKernel Scheduler.reverseBreadthFirst 2
      (ScopedSnapshot.initial [.root])).events.map Emission.value = [true] := by
  decide

/-- Commitment is a finer observation than pure complete-bag search: the
controller may choose a different winner, so no bag-equivalence theorem is
claimed without an additional commitment-compatibility hypothesis. -/
theorem competing_commits_are_strategy_observable :
    (ScopedSnapshot.run commitKernel Scheduler.breadthFirst 2
        (ScopedSnapshot.initial [.root])).events.map Emission.value ≠
      (ScopedSnapshot.run commitKernel Scheduler.reverseBreadthFirst 2
        (ScopedSnapshot.initial [.root])).events.map Emission.value := by
  decide

/-- A controller may change strategy between expansions without changing the
scope law.  This canary starts breadth-first at the root, then deliberately
selects the reverse order among the two committed alternatives. -/
def adaptiveCommitController : ScopedController CommitNode Bool Bool where
  initialMemory := false
  scheduler reversed :=
    if reversed then Scheduler.reverseBreadthFirst
    else Scheduler.breadthFirst
  advance _ _ _ := true

theorem adaptive_controller_commits_right :
    (ControlledScopedSnapshot.run commitKernel adaptiveCommitController 2
      (ControlledScopedSnapshot.initial adaptiveCommitController
        [.root])).search.events.map Emission.value = [true] := by
  decide

end Canaries

#print axioms Kernel.completed_strategies_bag_agree
#print axioms observe_completeBag_eq_of_perm
#print axioms duplicate_occurrences_are_observable
#print axioms forkBindings_denotations_exact
#print axioms forkBindings_occurrences
#print axioms forkBindings_preserves_context
#print axioms escapeBindings_exact
#print axioms escapeBindings_admits_ownedMultiShot
#print axioms pruneScope_perm
#print axioms ScopedSnapshot.tick_frontier_perm_of_noCommit
#print axioms ScopedSnapshot.tick_frontier_perm_of_commit
#print axioms ControlledScopedSnapshot.tick_memory_eq_of_reorder_nil
#print axioms ControlledScopedSnapshot.tick_frontier_perm_of_noCommit
#print axioms ControlledScopedSnapshot.tick_frontier_perm_of_commit
#print axioms ControlledScopedSnapshot.run_add
#print axioms additions_are_serializable
#print axioms competing_sets_are_not_serializable
#print axioms Canaries.pure_streams_differ_bags_agree
#print axioms Canaries.competing_commits_are_strategy_observable
#print axioms Canaries.adaptive_controller_commits_right

end Mettapedia.Languages.MeTTa.SearchStateStack
