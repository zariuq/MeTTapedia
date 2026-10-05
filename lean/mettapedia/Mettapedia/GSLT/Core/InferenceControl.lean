import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.Machines.OccurrenceCone
import Mettapedia.Machines.SnapshotBatch

/-!
# Occurrence-preserving inference control

This module separates an inference system from the policy that schedules its
live work.  A controller may carry memory and change scheduling policy after
each selected occurrence.  Every scheduler it exposes must preserve the
frontier by permutation, so control alone cannot invent, duplicate, or discard
an inference occurrence.

The separation is deliberate:

* the branching system authorizes successors;
* the controller orders live occurrences;
* certified pruning is a separate semantic operation;
* an objective or proof authority determines what counts as success.

The last section connects this interface to `OccurrenceMachineCore`.
Successor-list positions become stable path components, so equal successor
states remain distinct work occurrences under every controller.
-/

namespace Mettapedia.GSLT.Core.InferenceControl

open Mettapedia.GSLT.Core.BranchingTemporal

/-! ## Stateful, occurrence-preserving controllers -/

/-- A controller chooses an occurrence-preserving scheduler from its current
memory and updates that memory after one live node is expanded.  The update
may inspect the selected node, its possible emission, and its generated work;
it does not authorize those observations. -/
structure Controller (Node Answer Memory : Type*) where
  initialMemory : Memory
  scheduler : Memory → Scheduler Node
  advance : Memory → Node → Option Answer → List Node → Memory

namespace Controller

variable {Node Answer Memory Command : Type*}

/-- Embed an ordinary stateless scheduler as a controller. -/
def fixed (scheduler : Scheduler Node) : Controller Node Answer Unit where
  initialMemory := ()
  scheduler _ := scheduler
  advance _ _ _ _ := ()

/-- An open authored controller language.  `Command` is intentionally a type
parameter: a language may use terms, quoted processes, ATP selections, or
finite-controller states without extending a central host enumeration. -/
structure Program (Node Answer Command Memory : Type*) where
  initialMemory : Memory
  command : Memory → Command
  advance : Memory → Node → Option Answer → List Node → Memory

/-- Interpret authored control commands as occurrence-preserving schedulers.
The command interpreter is the semantic capability boundary. -/
def Program.realize (program : Program Node Answer Command Memory)
    (interpret : Command → Scheduler Node) : Controller Node Answer Memory where
  initialMemory := program.initialMemory
  scheduler memory := interpret (program.command memory)
  advance := program.advance

end Controller

/-- Search observations and controller memory evolve together.  Memory is not
part of the answer observation, but it remains available for exact resumption. -/
structure Snapshot (Node Answer Memory : Type*) where
  search : BranchingTemporal.Snapshot Node Answer
  memory : Memory

namespace Snapshot

variable {Node Answer Memory : Type*}

/-- Transfer controller memory at a captured boundary without rebuilding any
search state. A different controller may interpret the transferred memory;
its scheduler still owes the ordinary occurrence-preservation contract. -/
def mapMemory {NextMemory : Type*} (transfer : Memory → NextMemory)
    (snapshot : Snapshot Node Answer Memory) : Snapshot Node Answer NextMemory where
  search := snapshot.search
  memory := transfer snapshot.memory

@[simp] theorem mapMemory_search {NextMemory : Type*}
    (transfer : Memory → NextMemory) (snapshot : Snapshot Node Answer Memory) :
    (mapMemory transfer snapshot).search = snapshot.search :=
  rfl

@[simp] theorem mapMemory_id (snapshot : Snapshot Node Answer Memory) :
    mapMemory id snapshot = snapshot :=
  rfl

theorem mapMemory_comp {NextMemory FinalMemory : Type*}
    (first : Memory → NextMemory) (second : NextMemory → FinalMemory)
    (snapshot : Snapshot Node Answer Memory) :
    mapMemory second (mapMemory first snapshot) =
      mapMemory (second ∘ first) snapshot :=
  rfl

theorem mapMemory_sound_iff {NextMemory : Type*}
    (system : BranchingSystem Node Answer) (roots : List Node)
    (transfer : Memory → NextMemory) (snapshot : Snapshot Node Answer Memory) :
    (mapMemory transfer snapshot).search.Sound system roots ↔
      snapshot.search.Sound system roots :=
  Iff.rfl

/-- Transport the search nodes of a realization, keeping controller memory
and every ordered occurrence. -/
def mapNodes {NextNode : Type*} (mapping : Node → NextNode)
    (snapshot : Snapshot Node Answer Memory) : Snapshot NextNode Answer Memory where
  search := snapshot.search.mapNodes mapping
  memory := snapshot.memory

/-- Transport occurrence representations and controller memory together.
Ordered emissions and the entire frontier use the existing node transport;
the memory map must separately preserve the controller's future operations. -/
def mapState {NextNode NextMemory : Type*} (mapping : Node → NextNode)
    (transfer : Memory → NextMemory) (snapshot : Snapshot Node Answer Memory) :
    Snapshot NextNode Answer NextMemory :=
  (snapshot.mapNodes mapping).mapMemory transfer

@[simp] theorem mapState_id (snapshot : Snapshot Node Answer Memory) :
    snapshot.mapState id id = snapshot := by
  cases snapshot
  simp [mapState, mapNodes, mapMemory]

theorem mapState_comp {NextNode FinalNode NextMemory FinalMemory : Type*}
    (first : Node → NextNode) (second : NextNode → FinalNode)
    (one : Memory → NextMemory) (two : NextMemory → FinalMemory)
    (snapshot : Snapshot Node Answer Memory) :
    (snapshot.mapState first one).mapState second two =
      snapshot.mapState (second ∘ first) (two ∘ one) := by
  simp [mapState, mapNodes, mapMemory, BranchingTemporal.Snapshot.mapNodes,
    Emission.mapOrigin, List.map_map, Function.comp_def]

def initial (controller : Controller Node Answer Memory) (roots : List Node) :
    Snapshot Node Answer Memory where
  search := BranchingTemporal.initial roots
  memory := controller.initialMemory

/-- One controlled expansion.  The chosen scheduler performs the search step;
only then is controller memory advanced.  Exhausted frontiers retain their
memory exactly. -/
def tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) : Snapshot Node Answer Memory :=
  let scheduler := controller.scheduler snapshot.memory
  { search := BranchingTemporal.tick system scheduler snapshot.search
    memory :=
      match scheduler.reorder snapshot.search.frontier with
      | [] => snapshot.memory
      | node :: _ =>
          controller.advance snapshot.memory node (system.emit node)
            (system.successors node) }

/-- A state translation compares independently supplied branching authorities
and controllers. Local emission, successor, selection, integration and memory
update laws determine the whole step; equality of checkpoints is not assumed. -/
theorem tick_mapState {NextNode NextMemory : Type*} (mapping : Node → NextNode)
    (transfer : Memory → NextMemory)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer NextMemory)
    (emits : ∀ node, source.emit node = target.emit (mapping node))
    (successors : ∀ node,
      (source.successors node).map mapping = target.successors (mapping node))
    (reorders : ∀ memory nodes,
      ((first.scheduler memory).reorder nodes).map mapping =
        (second.scheduler (transfer memory)).reorder (nodes.map mapping))
    (integrates : ∀ memory pending generated,
      ((first.scheduler memory).integrate pending generated).map mapping =
        (second.scheduler (transfer memory)).integrate
          (pending.map mapping) (generated.map mapping))
    (advances : ∀ memory node emission generated,
      transfer (first.advance memory node emission generated) =
        second.advance (transfer memory) (mapping node) emission (generated.map mapping))
    (snapshot : Snapshot Node Answer Memory) :
    (tick source first snapshot).mapState mapping transfer =
      tick target second (snapshot.mapState mapping transfer) := by
  have searchEquality := BranchingTemporal.tick_mapNodes mapping source target
    (first.scheduler snapshot.memory) (second.scheduler (transfer snapshot.memory))
    emits successors (reorders snapshot.memory) (integrates snapshot.memory) snapshot.search
  have memoryEquality : transfer (tick source first snapshot).memory =
      (tick target second (snapshot.mapState mapping transfer)).memory := by
    simp only [tick, mapState, mapNodes, mapMemory, BranchingTemporal.Snapshot.mapNodes]
    rw [← reorders]
    cases ordered : (first.scheduler snapshot.memory).reorder snapshot.search.frontier with
    | nil => rfl
    | cons node pending =>
        simp only [List.map_cons]
        rw [← emits, ← successors]
        exact advances _ _ _ _
  exact congrArg₂ (fun search memory => (⟨search, memory⟩ : Snapshot NextNode Answer NextMemory))
    searchEquality memoryEquality

/-- The node-only comparison is the identity-memory instance of the common
state translation, retaining its original interface. -/
theorem tick_mapNodes {NextNode : Type*} (mapping : Node → NextNode)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer Memory)
    (emits : ∀ node, source.emit node = target.emit (mapping node))
    (successors : ∀ node,
      (source.successors node).map mapping = target.successors (mapping node))
    (reorders : ∀ memory nodes,
      ((first.scheduler memory).reorder nodes).map mapping =
        (second.scheduler memory).reorder (nodes.map mapping))
    (integrates : ∀ memory pending generated,
      ((first.scheduler memory).integrate pending generated).map mapping =
        (second.scheduler memory).integrate (pending.map mapping) (generated.map mapping))
    (advances : ∀ memory node emission generated,
      first.advance memory node emission generated =
        second.advance memory (mapping node) emission (generated.map mapping))
    (snapshot : Snapshot Node Answer Memory) :
    (tick source first snapshot).mapNodes mapping =
      tick target second (snapshot.mapNodes mapping) :=
  tick_mapState mapping id source target first second emits successors reorders integrates
    advances snapshot

/-- Observe a bounded number of globally scheduled work occurrences. -/
def run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) :
    Nat → Snapshot Node Answer Memory → Snapshot Node Answer Memory
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => tick system controller (run system controller fuel snapshot)

/-- Local state-translation laws preserve every finite prefix, including its
ordered answer occurrences, still-live frontier and transferred continuation. -/
theorem run_mapState {NextNode NextMemory : Type*} (mapping : Node → NextNode)
    (transfer : Memory → NextMemory)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer NextMemory)
    (emits : ∀ node, source.emit node = target.emit (mapping node))
    (successors : ∀ node,
      (source.successors node).map mapping = target.successors (mapping node))
    (reorders : ∀ memory nodes,
      ((first.scheduler memory).reorder nodes).map mapping =
        (second.scheduler (transfer memory)).reorder (nodes.map mapping))
    (integrates : ∀ memory pending generated,
      ((first.scheduler memory).integrate pending generated).map mapping =
        (second.scheduler (transfer memory)).integrate
          (pending.map mapping) (generated.map mapping))
    (advances : ∀ memory node emission generated,
      transfer (first.advance memory node emission generated) =
        second.advance (transfer memory) (mapping node) emission (generated.map mapping))
    (fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    (run source first fuel snapshot).mapState mapping transfer =
      run target second fuel (snapshot.mapState mapping transfer) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [run, tick_mapState mapping transfer source target first second emits successors
        reorders integrates advances, ih]
      rfl

/-- Stateful observation budgets compose exactly.  Resumption carries both
the live search occurrences and the controller's memory; neither component is
reconstructed from the emitted answers. -/
theorem run_add (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (left right : Nat) (snapshot : Snapshot Node Answer Memory) :
    run system controller (left + right) snapshot =
      run system controller right (run system controller left snapshot) := by
  induction right with
  | zero => rw [Nat.add_zero]; rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      simp only [run]
      rw [inductionHypothesis]

private theorem reorder_nil (controller : Controller Node Answer Memory)
    (memory : Memory) : (controller.scheduler memory).reorder [] = [] := by
  have lengthZero : ((controller.scheduler memory).reorder []).length = 0 := by
    simpa using
      ((controller.scheduler memory).reorder_complete []).length_eq
  exact List.length_eq_zero_iff.mp lengthZero

/-- A controller cannot manufacture work or update its private memory after
the search frontier is exhausted. -/
theorem tick_eq_self_of_frontier_nil
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory)
    (empty : snapshot.search.frontier = []) :
    tick system controller snapshot = snapshot := by
  have reordered :
      (controller.scheduler snapshot.memory).reorder
          snapshot.search.frontier = [] := by
    rw [empty, reorder_nil]
  simp [tick, BranchingTemporal.tick, reordered]

theorem run_eq_self_of_frontier_nil
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory)
    (empty : snapshot.search.frontier = []) (fuel : Nat) :
    run system controller fuel snapshot = snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [run, inductionHypothesis]
      exact tick_eq_self_of_frontier_nil system controller snapshot empty

/-- Once a stateful controlled run has completed, a larger observation budget
cannot retract completion or alter controller memory. -/
theorem completion_persists
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (small extra : Nat)
    (complete :
      (run system controller small snapshot).search.frontier = []) :
    run system controller extra (run system controller small snapshot) =
      run system controller small snapshot := by
  exact run_eq_self_of_frontier_nil system controller _ complete extra

@[simp] theorem tick_search (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) :
    (tick system controller snapshot).search =
      BranchingTemporal.tick system
        (controller.scheduler snapshot.memory) snapshot.search :=
  rfl

theorem events_prefix_tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) :
    snapshot.search.events.IsPrefix
      (tick system controller snapshot).search.events := by
  simpa using BranchingTemporal.events_prefix_tick system
    (controller.scheduler snapshot.memory) snapshot.search

theorem events_prefix_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) :
    snapshot.search.events.IsPrefix
      (run system controller fuel snapshot).search.events := by
  induction fuel with
  | zero => exact List.prefix_rfl
  | succ fuel inductionHypothesis =>
      exact inductionHypothesis.trans
        (events_prefix_tick system controller (run system controller fuel snapshot))

/-- Controller memory cannot weaken the ordinary reachability invariant. -/
theorem sound_tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    {roots : List Node} {snapshot : Snapshot Node Answer Memory}
    (sound : snapshot.search.Sound system roots) :
    (tick system controller snapshot).search.Sound system roots := by
  simpa using BranchingTemporal.sound_tick system
    (controller.scheduler snapshot.memory) sound

/-- Every emitted event and every live occurrence in a controlled run remains
generated by the original roots. -/
theorem sound_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    {roots : List Node} {snapshot : Snapshot Node Answer Memory}
    (sound : snapshot.search.Sound system roots) (fuel : Nat) :
    (run system controller fuel snapshot).search.Sound system roots := by
  induction fuel with
  | zero => exact sound
  | succ fuel inductionHypothesis =>
      exact sound_tick system controller inductionHypothesis

/-- A stateful controller preserves every additive answer account one step at
a time, even when it changes scheduling policy after each step. -/
theorem account_tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system)
    (snapshot : Snapshot Node Answer Memory) :
    account denotation (tick system controller snapshot).search =
      account denotation snapshot.search := by
  simpa using BranchingTemporal.account_tick system
    (controller.scheduler snapshot.memory) denotation snapshot.search

theorem account_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system) (fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) :
    account denotation (run system controller fuel snapshot).search =
      account denotation snapshot.search := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      exact (account_tick system controller denotation _).trans
        inductionHypothesis

/-- A completed stateful run emits the denotation of the initial frontier.
This is stronger than order independence: the controller may change policy
and memory during the run. -/
theorem completed_run_denotation (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (denotation : AdditiveDenotation system) (roots : List Node) (fuel : Nat)
    (complete :
      (run system controller fuel (initial controller roots)).search.frontier = []) :
    eventBag
        (run system controller fuel (initial controller roots)).search.events =
      foldValues denotation.value roots := by
  have preserved := account_run system controller denotation fuel
    (initial controller roots)
  unfold account at preserved
  rw [complete] at preserved
  simpa [initial, BranchingTemporal.initial, foldValues, eventBag]
    using preserved

/-- Any two completed stateful controllers agree on the answer bag, although
their streams, costs, and completion times may differ. -/
theorem completed_controllers_bag_agree
    (system : BranchingSystem Node Answer)
    {FirstMemory SecondMemory : Type*}
    (first : Controller Node Answer FirstMemory)
    (second : Controller Node Answer SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (run system first firstFuel (initial first roots)).search.frontier = [])
    (secondComplete :
      (run system second secondFuel (initial second roots)).search.frontier = []) :
    eventBag (run system first firstFuel (initial first roots)).search.events =
      eventBag
        (run system second secondFuel (initial second roots)).search.events := by
  rw [completed_run_denotation system first denotation roots firstFuel
      firstComplete,
    completed_run_denotation system second denotation roots secondFuel
      secondComplete]

/-- Finite descent is independent of controller memory and policy changes. -/
theorem foldRanks_tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (certificate : DescentCertificate system)
    (snapshot : Snapshot Node Answer Memory) :
    foldRanks certificate.rank (tick system controller snapshot).search.frontier =
      foldRanks certificate.rank snapshot.search.frontier - 1 := by
  simpa using BranchingTemporal.foldRanks_tick system
    (controller.scheduler snapshot.memory) certificate snapshot.search

theorem foldRanks_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (certificate : DescentCertificate system) (fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) :
    foldRanks certificate.rank
        (run system controller fuel snapshot).search.frontier =
      foldRanks certificate.rank snapshot.search.frontier - fuel := by
  induction fuel with
  | zero => simp [run]
  | succ fuel inductionHypothesis =>
      rw [run, foldRanks_tick, inductionHypothesis]
      omega

/-- A finite descent certificate gives a sufficient completion budget for
every stateful controller in the interface. -/
theorem run_completes_at_rank (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (certificate : DescentCertificate system)
    (snapshot : Snapshot Node Answer Memory) :
    (run system controller
      (foldRanks certificate.rank snapshot.search.frontier)
      snapshot).search.frontier = [] := by
  apply (certificate.foldRanks_eq_zero_iff _).mp
  rw [foldRanks_run]
  omega

/-- The stateful construction is a conservative extension of the existing
stateless scheduler semantics. -/
theorem fixed_run_search (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (fuel : Nat)
    (snapshot : BranchingTemporal.Snapshot Node Answer) :
    (run system (Controller.fixed scheduler) fuel
      { search := snapshot, memory := () }).search =
      BranchingTemporal.run system scheduler fuel snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [run, BranchingTemporal.run]
      rw [tick_search, inductionHypothesis]
      rfl

/-! ## Fairness is evidence about a controller, not permission to step -/

/-- The occurrence selected by the controller in this snapshot, if any. -/
def selected (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) : Option Node :=
  BranchingTemporal.selected (controller.scheduler snapshot.memory)
    snapshot.search.frontier

/-- Absence of a selected occurrence preserves the complete snapshot, including
controller memory. No branch expansion or controller update is authorized. -/
theorem tick_of_selected_none (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (snapshot : Snapshot Node Answer Memory)
    (empty : selected controller snapshot = none) :
    tick system controller snapshot = snapshot := by
  cases ordered : (controller.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | nil =>
      cases snapshot
      simp [tick, BranchingTemporal.tick, ordered]
  | cons node rest =>
      simp [selected, BranchingTemporal.selected, ordered] at empty

/-- Stateful-controller fairness from a particular initial frontier.  It says
that every occurrence which ever becomes live is eventually selected.  This
is deliberately not built into `Controller`: depth-first, best-first, learned,
and adversarial policies remain lawful controllers even when a separate
liveness claim about them would be false. -/
def FairFrom (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node) : Prop :=
  ∀ node,
    (∃ fuel, node ∈
      (run system controller fuel (initial controller roots)).search.frontier) →
    ∃ fuel,
      selected controller (run system controller fuel
        (initial controller roots)) = some node

/-- A generated successor is live immediately after its parent occurrence is
selected, even when that selection also changes controller memory. -/
theorem successor_mem_tick_of_selected
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) {parent child : Node}
    (selection : selected controller snapshot = some parent)
    (childMember : child ∈ system.successors parent) :
    child ∈ (tick system controller snapshot).search.frontier := by
  exact BranchingTemporal.successor_mem_tick_of_selected system
    (controller.scheduler snapshot.memory) snapshot.search selection childMember

/-- Selecting an emitting occurrence appends its event to the controlled
observation stream. -/
theorem event_mem_tick_of_selected
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) {node : Node} {answer : Answer}
    (selection : selected controller snapshot = some node)
    (emits : system.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (tick system controller snapshot).search.events := by
  exact BranchingTemporal.event_mem_tick_of_selected system
    (controller.scheduler snapshot.memory) snapshot.search selection emits

/-! ## Finite coverage, including captured controller states -/

/-- A live node is selected now or remains live after the controlled tick.
Changing controller memory cannot discard a waiting node. -/
theorem member_selected_or_live (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) {node : Node}
    (member : node ∈ snapshot.search.frontier) :
    selected controller snapshot = some node ∨
      node ∈ (tick system controller snapshot).search.frontier := by
  have orderedMember :=
    ((controller.scheduler snapshot.memory).reorder_complete _).mem_iff.mpr member
  cases ordered : (controller.scheduler snapshot.memory).reorder
      snapshot.search.frontier with
  | nil => simp [ordered] at orderedMember
  | cons head pending =>
      rw [ordered] at orderedMember
      rcases List.mem_cons.mp orderedMember with equal | waiting
      · subst node
        exact Or.inl (by simp [selected, BranchingTemporal.selected, ordered])
      · right
        change node ∈ (BranchingTemporal.tick system
          (controller.scheduler snapshot.memory) snapshot.search).frontier
        simp only [BranchingTemporal.tick, ordered]
        exact ((controller.scheduler snapshot.memory).integrate_complete _ _).mem_iff.mpr
          (List.mem_append_left _ waiting)

/-- A node live at a captured boundary is selected during the following
interval or remains live at its end. No fairness premise is required. -/
theorem entry_selected_or_live (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (start extra : Nat) {node : Node}
    (member : node ∈ (run system controller start snapshot).search.frontier) :
    (∃ index, start ≤ index ∧ index < start + extra ∧
      selected controller (run system controller index snapshot) = some node) ∨
      node ∈ (run system controller (start + extra) snapshot).search.frontier := by
  induction extra with
  | zero => exact Or.inr (by simpa using member)
  | succ extra inductionHypothesis =>
      rcases inductionHypothesis with ⟨index, afterStart, beforeEnd, selection⟩ | live
      · exact Or.inl ⟨index, afterStart, by omega, selection⟩
      · rcases member_selected_or_live system controller _ live with selection | waiting
        · exact Or.inl ⟨start + extra, by omega, by omega, selection⟩
        · exact Or.inr (by simpa [Nat.add_assoc, run] using waiting)

/-- Every node generated from the captured frontier has already been selected
or is still reachable from the current frontier. This also applies after
resumption with noninitial controller memory. -/
theorem generated_selected_or_reachable (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (fuel : Nat) {node : Node}
    (generated : Generated system snapshot.search.frontier node) :
    (∃ index, index < fuel ∧
      selected controller (run system controller index snapshot) = some node) ∨
      Generated system (run system controller fuel snapshot).search.frontier node := by
  induction generated generalizing fuel with
  | root member =>
      have enters : _ ∈ (run system controller 0 snapshot).search.frontier := member
      rcases entry_selected_or_live system controller snapshot 0 fuel enters with
        ⟨index, _, beforeEnd, selection⟩ | live
      · exact Or.inl ⟨index, by simpa using beforeEnd, selection⟩
      · exact Or.inr (Generated.root (by simpa using live))
  | successor _ childMember inductionHypothesis =>
      rcases inductionHypothesis fuel with ⟨index, beforeEnd, selection⟩ | reachable
      · have enters := successor_mem_tick_of_selected system controller _ selection childMember
        obtain ⟨extra, endEq⟩ := Nat.le.dest (Nat.succ_le_of_lt beforeEnd)
        rcases entry_selected_or_live system controller snapshot (index + 1) extra enters with
          ⟨next, _, nextBeforeEnd, nextSelection⟩ | live
        · exact Or.inl ⟨next, by omega, nextSelection⟩
        · exact Or.inr (Generated.root (by simpa [endEq] using live))
      · exact Or.inr (Generated.successor reachable childMember)

/-- An emitting node selected before a finite boundary has its event in that
boundary's retained stream, regardless of later controller changes. -/
theorem selected_emission_mem_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) {index fuel : Nat} {node : Node} {answer : Answer}
    (beforeEnd : index < fuel)
    (selection : selected controller (run system controller index snapshot) = some node)
    (emits : system.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (run system controller fuel snapshot).search.events := by
  have event := event_mem_tick_of_selected system controller _ selection emits
  obtain ⟨extra, endEq⟩ := Nat.le.dest (Nat.succ_le_of_lt beforeEnd)
  rw [← endEq, run_add]
  obtain ⟨tail, prefixEq⟩ := events_prefix_run system controller extra
    (run system controller (index + 1) snapshot)
  rw [← prefixEq]
  exact List.mem_append_left _ event

/-- A generated emitting node is represented by a retained event or remains
reachable from pending work. An emitted value may itself encode unresolved
work; interpreting that value as success is a separate observation. -/
theorem generated_emitted_or_reachable (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (fuel : Nat) {node : Node} {answer : Answer}
    (generated : Generated system snapshot.search.frontier node)
    (emits : system.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (run system controller fuel snapshot).search.events ∨
      Generated system (run system controller fuel snapshot).search.frontier node := by
  rcases generated_selected_or_reachable system controller snapshot fuel generated with
    ⟨index, beforeEnd, selection⟩ | reachable
  · exact Or.inl (selected_emission_mem_run system controller snapshot beforeEnd selection emits)
  · exact Or.inr reachable

/-- Stateful fairness reaches every finitely generated occurrence, not merely
the occurrences present in the initial frontier. -/
theorem fair_selects_generated
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : FairFrom system controller roots) {node : Node}
    (generated : Generated system roots node) :
    ∃ fuel,
      selected controller (run system controller fuel
        (initial controller roots)) = some node := by
  induction generated with
  | root member =>
      apply fair
      exact ⟨0, by
        simpa [run, initial, BranchingTemporal.initial] using member⟩
  | successor parentGenerated childMember inductionHypothesis =>
      obtain ⟨fuel, parentSelected⟩ := inductionHypothesis
      apply fair
      refine ⟨fuel + 1, ?_⟩
      change _ ∈ (tick system controller
        (run system controller fuel
          (initial controller roots))).search.frontier
      exact successor_mem_tick_of_selected system controller _
        parentSelected childMember

/-- A fair controller eventually emits every reachable answer occurrence.
Soundness required only lawful scheduling; this stronger conclusion consumes
an explicit liveness hypothesis. -/
theorem fair_emits_reachable
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : FairFrom system controller roots) {node : Node} {answer : Answer}
    (generated : Generated system roots node)
    (emits : system.emit node = some answer) :
    ∃ fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system controller fuel
          (initial controller roots)).search.events := by
  obtain ⟨fuel, selection⟩ :=
    fair_selects_generated system controller roots fair generated
  refine ⟨fuel + 1, ?_⟩
  change _ ∈ (tick system controller
    (run system controller fuel
      (initial controller roots))).search.events
  exact event_mem_tick_of_selected system controller _ selection emits

/-- Embedding a stateless scheduler preserves its fairness contract exactly.
This transports the existing breadth/depth-first witnesses into the open
controller interface without re-proving their traversal behavior. -/
theorem fixed_fair_iff (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (roots : List Node) :
    FairFrom system (Controller.fixed scheduler) roots ↔
      BranchingTemporal.FairFrom system scheduler roots := by
  constructor
  · intro fair node live
    have controllerLive : ∃ fuel, node ∈
        (run system (Controller.fixed scheduler) fuel
          (initial (Controller.fixed scheduler) roots)).search.frontier := by
      obtain ⟨fuel, member⟩ := live
      refine ⟨fuel, ?_⟩
      change node ∈
        (run system (Controller.fixed scheduler) fuel
          { search := BranchingTemporal.initial roots, memory := () }).search.frontier
      rw [fixed_run_search]
      exact member
    obtain ⟨fuel, selection⟩ := fair node controllerLive
    refine ⟨fuel, ?_⟩
    change BranchingTemporal.selected scheduler
      (run system (Controller.fixed scheduler) fuel
        { search := BranchingTemporal.initial roots, memory := () }).search.frontier =
      some node at selection
    rw [fixed_run_search] at selection
    exact selection
  · intro fair node live
    have schedulerLive : ∃ fuel, node ∈
        (BranchingTemporal.run system scheduler fuel
          (BranchingTemporal.initial roots)).frontier := by
      obtain ⟨fuel, member⟩ := live
      refine ⟨fuel, ?_⟩
      change node ∈
        (run system (Controller.fixed scheduler) fuel
          { search := BranchingTemporal.initial roots, memory := () }).search.frontier
        at member
      rw [fixed_run_search] at member
      exact member
    obtain ⟨fuel, selection⟩ := fair node schedulerLive
    refine ⟨fuel, ?_⟩
    change BranchingTemporal.selected scheduler
      (run system (Controller.fixed scheduler) fuel
        { search := BranchingTemporal.initial roots, memory := () }).search.frontier =
      some node
    rw [fixed_run_search]
    exact selection

/-! ## The controlled machine as a GSLT -/

/-- The operational theory of a controlled search.  A live configuration has
exactly its controlled tick as a successor.  An exhausted configuration has
no stuttering rewrite, so completion remains observable. -/
def toGSLT (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) : GSLT where
  Term := Snapshot Node Answer Memory
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    source.search.frontier ≠ [] ∧ target = tick system controller source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem toGSLT_step_iff (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (source target : Snapshot Node Answer Memory) :
    (toGSLT system controller).Step source target ↔
      source.search.frontier ≠ [] ∧
        target = tick system controller source :=
  Iff.rfl

/-- A live controlled tick is a genuine step of the control GSLT. -/
theorem tick_step_of_live (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory)
    (live : snapshot.search.frontier ≠ []) :
    (toGSLT system controller).Step snapshot
      (tick system controller snapshot) :=
  ⟨live, rfl⟩

/-- Completion is not silently represented by an infinite stuttering loop. -/
theorem no_step_of_complete (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory)
    (complete : snapshot.search.frontier = []) :
    ¬ ∃ target, (toGSLT system controller).Step snapshot target := by
  rintro ⟨target, live, _⟩
  exact live complete

/-- Every proper prefix below `fuel` still has live work.  This is the exact
side condition needed to interpret a fuel-bounded run as that many control
rewrites rather than silently padding a shorter run with terminal stutters. -/
def LiveThrough (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory)
    (fuel : Nat) (snapshot : Snapshot Node Answer Memory) : Prop :=
  ∀ elapsed, elapsed < fuel →
    (run system controller elapsed snapshot).search.frontier ≠ []

private theorem multistep_tail
    {theory : GSLT} {first middle last : theory.Term}
    (path : theory.MultiStep first middle)
    (lastStep : theory.Step middle last) :
    theory.MultiStep first last := by
  induction path with
  | refl _ => exact .step lastStep (.refl _)
  | step firstStep rest inductionHypothesis =>
      exact .step firstStep (inductionHypothesis lastStep)

/-- Under its explicit non-stuttering side condition, a controlled run is a
finite derivation in the control GSLT.  This is the bridge by which ordinary
finite-trace authorities may audit controller execution. -/
theorem run_multistep (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (fuel : Nat)
    (snapshot : Snapshot Node Answer Memory)
    (live : LiveThrough system controller fuel snapshot) :
    (toGSLT system controller).MultiStep snapshot
      (run system controller fuel snapshot) := by
  induction fuel with
  | zero => exact .refl _
  | succ fuel inductionHypothesis =>
      apply multistep_tail (inductionHypothesis ?_)
      · exact ⟨live fuel (Nat.lt_succ_self fuel), rfl⟩
      · intro elapsed elapsedLess
        exact live elapsed (Nat.lt_trans elapsedLess (Nat.lt_succ_self fuel))

end Snapshot

/-! ## Exact occurrence traces for controlled machines -/

open Mettapedia.Machines

/-- A live work occurrence carries both its machine state and the exact path
of successor-list positions that produced it. -/
structure WorkOccurrence (State : Type*) where
  state : State
  trace : List Nat
deriving DecidableEq, Repr

namespace WorkOccurrence

def root {State : Type*} (state : State) : WorkOccurrence State :=
  ⟨state, []⟩

/-- Add exact successor-index paths to any branching system.  This is the
generic occurrence decoration used by language machines whose state carriers
do not fit the older universe-monomorphic `OccurrenceMachineCore`. -/
def lift {State Answer : Type*} (base : BranchingSystem State Answer) :
    BranchingSystem (WorkOccurrence State) (Answer × List Nat) where
  emit occurrence :=
    (base.emit occurrence.state).map fun answer =>
      (answer, occurrence.trace)
  successors occurrence :=
    (base.successors occurrence.state).zipIdx.map fun (state, edge) =>
      ⟨state, occurrence.trace ++ [edge]⟩

variable {Term State Answer : Type}

/-- Turn an occurrence machine into a branching system whose nodes retain
transition identity and whose emissions retain answer identity. -/
def system (machine : OccurrenceMachineCore Term State Answer) :
    BranchingSystem (WorkOccurrence State) (Answer × List Nat) :=
  lift { emit := machine.answer, successors := machine.next }

/-- Executability invariant for one work occurrence relative to a root state. -/
def ValidFrom (machine : OccurrenceMachineCore Term State Answer)
    (initial : State) (occurrence : WorkOccurrence State) : Prop :=
  machine.follow initial occurrence.trace = some occurrence.state

@[simp] theorem root_valid
    (machine : OccurrenceMachineCore Term State Answer) (state : State) :
    ValidFrom machine state (root state) :=
  rfl

private theorem getElem?_eq_some_of_mem_zipIdx {values : List State}
    {value : State} {index : Nat} (member : (value, index) ∈ values.zipIdx) :
    values[index]? = some value := by
  have located := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ values.zipIdx, entry = (value, index) from
      ⟨_, member, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairEquality⟩ := located
  have indexEquality : foundIndex = index :=
    (Prod.ext_iff.mp pairEquality).2
  subst indexEquality
  rw [List.getElem?_eq_getElem foundBound]
  exact congrArg some (Prod.ext_iff.mp pairEquality).1

theorem follow_append
    (machine : OccurrenceMachineCore Term State Answer)
    (state : State) (first second : List Nat) :
    machine.follow state (first ++ second) =
      (machine.follow state first).bind fun middle =>
        machine.follow middle second := by
  induction first generalizing state with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      simp only [List.cons_append, OccurrenceMachineCore.follow]
      cases lookup : (machine.next state)[edge]? with
      | none => simp
      | some target =>
          simpa using inductionHypothesis target

/-- Every generated child extends its parent's executable occurrence trace by
the selected successor-list index. -/
theorem successor_valid
    (machine : OccurrenceMachineCore Term State Answer)
    {initial : State} {parent child : WorkOccurrence State}
    (parentValid : ValidFrom machine initial parent)
    (childMember : child ∈ (system machine).successors parent) :
    ValidFrom machine initial child := by
  rcases List.mem_map.mp childMember with
    ⟨⟨target, edge⟩, edgeMember, childEquality⟩
  subst child
  have edgeLookup : (machine.next parent.state)[edge]? = some target :=
    getElem?_eq_some_of_mem_zipIdx edgeMember
  simp only [ValidFrom]
  rw [follow_append, parentValid]
  simp [OccurrenceMachineCore.follow, edgeLookup]

/-- Generated work is exactly rooted in an executable occurrence path; a
controller cannot forge a path by reordering the frontier. -/
theorem generated_valid
    (machine : OccurrenceMachineCore Term State Answer)
    {initial : State} {occurrence : WorkOccurrence State}
    (generated : Generated (system machine) [root initial] occurrence) :
    ValidFrom machine initial occurrence := by
  induction generated with
  | root member =>
      simp only [List.mem_singleton] at member
      rw [member]
      rfl
  | successor _ childMember inductionHypothesis =>
      exact successor_valid machine inductionHypothesis childMember

/-- An executable successor-index path fixes the complete machine input,
including its world and control frames. Equal values alone do not fix a path. -/
theorem eq_of_valid_trace
    (machine : OccurrenceMachineCore Term State Answer)
    {initial : State} {left right : WorkOccurrence State}
    (leftValid : ValidFrom machine initial left)
    (rightValid : ValidFrom machine initial right)
    (traceEquality : left.trace = right.trace) : left = right := by
  have leftRun : machine.follow initial left.trace = some left.state := leftValid
  have rightRun : machine.follow initial right.trace = some right.state := rightValid
  rw [← traceEquality] at rightRun
  have stateEquality : left.state = right.state :=
    Option.some.inj (leftRun.symm.trans rightRun)
  cases left
  cases right
  simp_all

/-- Every controlled emission is a replayable answer certificate for the
underlying occurrence machine. -/
theorem controlled_emission_sound
    (machine : OccurrenceMachineCore Term State Answer)
    {Memory : Type*}
    (controller : Controller (WorkOccurrence State) (Answer × List Nat) Memory)
    (initialState : State) (fuel : Nat)
    {event : Emission (WorkOccurrence State) (Answer × List Nat)}
    (member : event ∈
      (Snapshot.run (system machine) controller fuel
        (Snapshot.initial controller [root initialState])).search.events) :
    ∃ final,
      machine.follow initialState event.value.2 = some final ∧
        machine.answer final = some event.value.1 := by
  have runSound := Snapshot.sound_run (system machine) controller
    (roots := [root initialState])
    (snapshot := Snapshot.initial controller [root initialState])
    (BranchingTemporal.initial_sound (system machine) [root initialState]) fuel
  have eventValid := runSound.2 event member
  have originValid := generated_valid machine eventValid.1
  have emitted := eventValid.2
  change (machine.answer event.origin.state).map
    (fun answer => (answer, event.origin.trace)) = some event.value at emitted
  cases answerAtOrigin : machine.answer event.origin.state with
  | none =>
      rw [answerAtOrigin] at emitted
      contradiction
  | some answer =>
      have valueEquality : event.value = (answer, event.origin.trace) := by
        rw [answerAtOrigin] at emitted
        exact (Option.some.inj emitted).symm
      rw [valueEquality]
      exact ⟨event.origin.state, originValid, answerAtOrigin⟩

end WorkOccurrence

/-! ## Preparation without premature publication

A worker may capture one pure expansion before the controller selects its
occurrence. Preparation changes private storage only. Publication still uses
the original controller and its complete frontier. The capture check names the
whole input observation it preserves; equality of a recipe name alone is not
such a check. Effects and observations of global speculative cost require
their own admission law.
-/

namespace Preparation

variable {Node Answer Key Memory : Type*} [DecidableEq Key]

/-- One retained operation, including the input used to compute it. Neither
answer occurrences nor the ordered successor list are aggregated. -/
structure Capture (Node Answer : Type*) where
  input : Node
  emission : Option Answer
  generated : List Node
deriving DecidableEq, Repr

namespace Capture

/-- Preserve the recorded input and ordered generated occurrences under a
node representation map. This transport does not authenticate the payload. -/
def mapNodes {NextNode : Type*} (mapping : Node → NextNode)
    (frame : Capture Node Answer) : Capture NextNode Answer :=
  ⟨mapping frame.input, frame.emission, frame.generated.map mapping⟩

@[simp] theorem mapNodes_id (frame : Capture Node Answer) : frame.mapNodes id = frame := by
  cases frame
  simp [mapNodes]

theorem mapNodes_comp {NextNode FinalNode : Type*}
    (first : Node → NextNode) (second : NextNode → FinalNode)
    (frame : Capture Node Answer) :
    (frame.mapNodes first).mapNodes second = frame.mapNodes (second ∘ first) := by
  simp [mapNodes, List.map_map]

theorem mapNodes_injective {NextNode : Type*} (mapping : Node → NextNode)
    (faithful : Function.Injective mapping) : Function.Injective (mapNodes (Answer := Answer) mapping) := by
  intro first second equal
  have input := faithful (congrArg Capture.input equal)
  have emission := congrArg Capture.emission equal
  have generated := (List.map_injective_iff.mpr faithful) (congrArg Capture.generated equal)
  cases first
  cases second
  simp only [mapNodes] at input emission generated
  cases input
  cases emission
  cases generated
  rfl

end Capture

abbrev Cache (Key Node Answer : Type*) := Key → Option (Capture Node Answer)

/-- Compute a captured expansion from the branching authority. -/
def capture (system : BranchingSystem Node Answer) (node : Node) :
    Capture Node Answer := ⟨node, system.emit node, system.successors node⟩

omit [DecidableEq Key] in
theorem capture_mapNodes {NextNode : Type*} (mapping : Node → NextNode)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (emits : ∀ node, source.emit node = target.emit (mapping node))
    (successors : ∀ node,
      (source.successors node).map mapping = target.successors (mapping node))
    (node : Node) : (capture source node).mapNodes mapping = capture target (mapping node) := by
  simp [capture, Capture.mapNodes, emits, successors]

/-- The existing private-write kernel supplies preparation. Distinct keys
permit physical reordering; logical occurrence identity belongs in the key. -/
def kernel (system : BranchingSystem Node Answer) (key : Node → Key) :
    Mettapedia.Machines.SnapshotBatch.Kernel Unit Node Unit Key
      (Option (Capture Node Answer)) where
  destination := key
  compute _ node _ _ := some (capture system node)

/-- Captures retain their actual source input and its authorized expansion. -/
def Valid (system : BranchingSystem Node Answer) (domain : Node → Prop)
    (cache : Cache Key Node Answer) : Prop :=
  ∀ address retained, cache address = some retained →
    domain retained.input ∧ retained.emission = system.emit retained.input ∧
      retained.generated = system.successors retained.input

/-- A successful input check preserves both observations of one expansion.
This is a local footprint/authority obligation, not assumed equality of runs. -/
def SoundMatch (system : BranchingSystem Node Answer) (domain : Node → Prop)
    (acceptInput : Node → Node → Bool) : Prop :=
  ∀ captured current, domain captured → domain current →
    acceptInput captured current = true →
      system.emit captured = system.emit current ∧
        system.successors captured = system.successors current

/-- A missing or invalidated capture uses the ordinary operation. The input
check runs before any captured answer or successor is published. -/
def read (system : BranchingSystem Node Answer) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (cache : Cache Key Node Answer)
    (node : Node) : Capture Node Answer :=
  match cache (key node) with
  | none => capture system node
  | some retained =>
      if acceptInput retained.input node then retained else capture system node

def cachedSystem (system : BranchingSystem Node Answer) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (cache : Cache Key Node Answer) :
    BranchingSystem Node Answer where
  emit node := (read system key acceptInput cache node).emission
  successors node := (read system key acceptInput cache node).generated

omit [DecidableEq Key] in
theorem empty_valid (system : BranchingSystem Node Answer) (domain : Node → Prop) :
    Valid system domain (fun _ : Key => none) := by
  intro address retained impossible
  contradiction

theorem valid_step (system : BranchingSystem Node Answer) (key : Node → Key)
    (domain : Node → Prop) (cache : Cache Key Node Answer)
    (valid : Valid system domain cache) (node : Node) (admitted : domain node) :
    Valid system domain ((kernel system key).step () (fun _ => ()) cache node) := by
  intro address retained stored
  by_cases same : address = key node
  · subst address
    have equal : capture system node = retained := by
      have sameCapture : some (capture system node) = some retained := by
        simpa [kernel, Mettapedia.Machines.SnapshotBatch.Kernel.step] using stored
      exact Option.some.inj sameCapture
    subst retained
    exact ⟨admitted, rfl, rfl⟩
  · apply valid address retained
    simpa [kernel, Mettapedia.Machines.SnapshotBatch.Kernel.step,
      Function.update_of_ne same] using stored

theorem valid_run (system : BranchingSystem Node Answer) (key : Node → Key)
    (domain : Node → Prop) (cache : Cache Key Node Answer)
    (valid : Valid system domain cache) (nodes : List Node)
    (admitted : ∀ node ∈ nodes, domain node) :
    Valid system domain ((kernel system key).run () (fun _ => ()) cache nodes) := by
  induction nodes generalizing cache with
  | nil => exact valid
  | cons node rest ih =>
      rw [Mettapedia.Machines.SnapshotBatch.Kernel.run_cons]
      exact ih _ (valid_step system key domain cache valid node (admitted node (by simp)))
        (fun next member => admitted next (List.mem_cons_of_mem node member))

omit [DecidableEq Key] in
theorem read_agrees (system : BranchingSystem Node Answer) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput) (cache : Cache Key Node Answer)
    (valid : Valid system domain cache) (node : Node) (admitted : domain node) :
    (read system key acceptInput cache node).emission = system.emit node ∧
      (read system key acceptInput cache node).generated = system.successors node := by
  cases found : cache (key node) with
  | none => simp [read, found, capture]
  | some retained =>
      by_cases accepted : acceptInput retained.input node = true
      · obtain ⟨capturedAdmitted, emission, generated⟩ := valid _ _ found
        have current := sound retained.input node capturedAdmitted admitted accepted
        simpa [read, found, accepted] using
          And.intro (emission.trans current.1) (generated.trans current.2)
      · simp [read, found, accepted, capture]

omit [DecidableEq Key] in
/-- The original selection and controller update are preserved from local
agreement on the live frontier. No answer-bag quotient is used. -/
theorem tick_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput) (cache : Cache Key Node Answer)
    (valid : Valid system domain cache) (state : Snapshot Node Answer Memory)
    (live : ∀ node ∈ state.search.frontier, domain node) :
    Snapshot.tick (cachedSystem system key acceptInput cache) controller state =
      Snapshot.tick system controller state := by
  cases ordered : (controller.scheduler state.memory).reorder state.search.frontier with
  | nil => simp [Snapshot.tick, BranchingTemporal.tick, ordered]
  | cons node pending =>
      have member : node ∈ state.search.frontier :=
        (controller.scheduler state.memory).mem_reorder_iff.mp (by simp [ordered])
      have agree := read_agrees system key domain acceptInput sound cache valid node (live node member)
      simp only [Snapshot.tick, BranchingTemporal.tick, ordered, cachedSystem]
      rw [agree.1, agree.2]

private theorem live_tick (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (domain : Node → Prop)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (state : Snapshot Node Answer Memory)
    (live : ∀ node ∈ state.search.frontier, domain node) :
    ∀ node ∈ (Snapshot.tick system controller state).search.frontier, domain node := by
  rw [Snapshot.tick_search]
  cases ordered : (controller.scheduler state.memory).reorder state.search.frontier with
  | nil => simpa [BranchingTemporal.tick, ordered] using live
  | cons selected pending =>
      intro node member
      have inCombined : node ∈ pending ∨ node ∈ system.successors selected := by
        apply (controller.scheduler state.memory).mem_integrate_iff.mp
        simpa [BranchingTemporal.tick, ordered] using member
      rcases inCombined with waiting | generated
      · apply live node
        exact (controller.scheduler state.memory).mem_reorder_iff.mp (by simp [ordered, waiting])
      · apply closed selected (live selected ?_) node generated
        exact (controller.scheduler state.memory).mem_reorder_iff.mp (by simp [ordered])

/-- A physical realization retains the original logical snapshot and an
independently changing private preparation store. -/
structure Session (Key Node Answer Memory : Type*) where
  state : Snapshot Node Answer Memory
  cache : Cache Key Node Answer

namespace Session

def Valid (system : BranchingSystem Node Answer) (domain : Node → Prop)
    (session : Session Key Node Answer Memory) : Prop :=
  Preparation.Valid system domain session.cache ∧
    ∀ node ∈ session.state.search.frontier, domain node

/-- Preparation performs actual private writes while leaving the agenda,
ordered observations and controller memory untouched. -/
def prepare (system : BranchingSystem Node Answer) (key : Node → Key)
    (session : Session Key Node Answer Memory) (nodes : List Node) :
    Session Key Node Answer Memory :=
  { session with cache := (kernel system key).run () (fun _ => ()) session.cache nodes }

/-- Parallel preparation computes against one immutable initial store and
publishes completed writes. This is the existing independent batch algorithm. -/
def prepareBatch (system : BranchingSystem Node Answer) (key : Node → Key)
    (session : Session Key Node Answer Memory) (nodes : List Node) :
    Session Key Node Answer Memory :=
  { session with cache := (kernel system key).batch () (fun _ => ()) session.cache nodes }

theorem prepareBatch_eq_prepare (system : BranchingSystem Node Answer) (key : Node → Key)
    (session : Session Key Node Answer Memory) (nodes : List Node)
    (distinct : (nodes.map key).Nodup) :
    prepareBatch system key session nodes = prepare system key session nodes := by
  have same := (kernel system key).batch_eq_run () (fun _ => ()) session.cache nodes distinct
  exact congrArg (fun cache => ({ session with cache := cache } : Session Key Node Answer Memory)) same

theorem prepare_perm (system : BranchingSystem Node Answer) (key : Node → Key)
    (session : Session Key Node Answer Memory) {left right : List Node}
    (permutation : left.Perm right) (distinct : (left.map key).Nodup) :
    prepare system key session left = prepare system key session right := by
  have same := (kernel system key).run_perm () (fun _ => ()) session.cache permutation distinct
  exact congrArg (fun cache => ({ session with cache := cache } : Session Key Node Answer Memory)) same

theorem prepare_valid (system : BranchingSystem Node Answer) (key : Node → Key)
    (domain : Node → Prop) (session : Session Key Node Answer Memory)
    (valid : session.Valid system domain) (nodes : List Node)
    (admitted : ∀ node ∈ nodes, domain node) :
    (prepare system key session nodes).Valid system domain :=
  ⟨valid_run system key domain session.cache valid.1 nodes admitted, valid.2⟩

/-- Publication asks the original parent agenda to select one occurrence.
Physical completion order never supplies this selection. -/
def publish (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (key : Node → Key) (acceptInput : Node → Node → Bool)
    (session : Session Key Node Answer Memory) : Session Key Node Answer Memory :=
  { session with
    state := Snapshot.tick (cachedSystem system key acceptInput session.cache)
      controller session.state }

/-- Reusing an existing capture requires its input check. An uncached
operation follows the ordinary direct path. -/
def ready (key : Node → Key) (acceptInput : Node → Node → Bool)
    (session : Session Key Node Answer Memory) (node : Node) : Bool :=
  match session.cache (key node) with
  | none => true
  | some retained => acceptInput retained.input node

/-- Strict invalidation retains both the full logical snapshot and the
prepared operation. The left result is publication; the right is suspension,
not exhaustion. Unlike `read`'s restart profile, this profile never recomputes
an invalidated operation. -/
def publishChecked (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (session : Session Key Node Answer Memory) :
    Session Key Node Answer Memory ⊕ Session Key Node Answer Memory :=
  match Snapshot.selected controller session.state with
  | none => .inl session
  | some node =>
      if ready key acceptInput session node then
        .inl (publish system controller key acceptInput session)
      else .inr session

omit [DecidableEq Key] in
/-- A failed authority check preserves all owned residuals and prepared data;
there is no second operation evaluation or logical controller update. -/
theorem publishChecked_refused (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (session : Session Key Node Answer Memory)
    (node : Node) (selected : Snapshot.selected controller session.state = some node)
    (refused : ready key acceptInput session node = false) :
    publishChecked system controller key acceptInput session = .inr session := by
  simp [publishChecked, selected, refused]

omit [DecidableEq Key] in
/-- An accepted strict operation uses exactly the existing publication path;
the empty-frontier case retains the complete state rather than inventing work. -/
theorem publishChecked_accepted_eq (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (session next : Session Key Node Answer Memory)
    (accepted : publishChecked system controller key acceptInput session = .inl next) :
    next = publish system controller key acceptInput session := by
  cases selection : Snapshot.selected controller session.state with
  | none =>
      have same : session = next := by simpa [publishChecked, selection] using accepted
      have idle := Snapshot.tick_of_selected_none
        (cachedSystem system key acceptInput session.cache) controller session.state selection
      subst next
      simp [publish, idle]
  | some node =>
      by_cases allowed : ready key acceptInput session node = true
      · simpa [publishChecked, selection, allowed] using (Sum.inl.inj
          (show Sum.inl (publish system controller key acceptInput session) =
            (Sum.inl next : Session Key Node Answer Memory ⊕ Session Key Node Answer Memory) by
            simpa [publishChecked, selection, allowed] using accepted)).symm
      · simp [publishChecked, selection, allowed] at accepted

omit [DecidableEq Key] in
/-- Refusal retains the exact session; it does not erase captured operations,
controller memory, return obligations or unfinished worlds. -/
theorem publishChecked_refused_eq (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (session next : Session Key Node Answer Memory)
    (refused : publishChecked system controller key acceptInput session = .inr next) :
    next = session := by
  cases selection : Snapshot.selected controller session.state with
  | none => simp [publishChecked, selection] at refused
  | some node =>
      by_cases allowed : ready key acceptInput session node = true
      · simp [publishChecked, selection, allowed] at refused
      · exact (Sum.inr.inj (show Sum.inr session =
          (Sum.inr next : Session Key Node Answer Memory ⊕ Session Key Node Answer Memory) by
          simpa [publishChecked, selection, allowed] using refused)).symm

omit [DecidableEq Key] in
theorem publish_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput) (session : Session Key Node Answer Memory)
    (valid : session.Valid system domain) :
    (publish system controller key acceptInput session).state =
      Snapshot.tick system controller session.state :=
  tick_agrees system controller key domain acceptInput sound session.cache valid.1 session.state valid.2

omit [DecidableEq Key] in
/-- Accepted strict publication has the same complete state as ordinary
parent selection. The capture and input laws are local prerequisites. -/
theorem publishChecked_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput) (session : Session Key Node Answer Memory)
    (valid : session.Valid system domain) (node : Node)
    (selected : Snapshot.selected controller session.state = some node)
    (accepted : ready key acceptInput session node = true) :
    publishChecked system controller key acceptInput session =
      .inl { session with state := Snapshot.tick system controller session.state } := by
  simp only [publishChecked, selected]
  rw [if_pos accepted]
  have same := publish_agrees system controller key domain acceptInput sound session valid
  exact congrArg Sum.inl (congrArg
    (fun state => ({ session with state := state } : Session Key Node Answer Memory)) same)

omit [DecidableEq Key] in
theorem publish_valid (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (session : Session Key Node Answer Memory) (valid : session.Valid system domain) :
    (publish system controller key acceptInput session).Valid system domain := by
  constructor
  · exact valid.1
  · rw [publish_agrees system controller key domain acceptInput sound session valid]
    exact live_tick system controller domain closed session.state valid.2

end Session

/-- A physical transcript records preparation and parent publication
separately. It does not restrict the authored controller's command language. -/
inductive Action (Node : Type*) where
  | prepare (nodes : List Node)
  | publish
  deriving DecidableEq

def Action.inputs : Action Node → List Node
  | .prepare nodes => nodes
  | .publish => []

def Action.publications : Action Node → Nat
  | .prepare _ => 0
  | .publish => 1

def applyAction (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (session : Session Key Node Answer Memory) :
    Action Node → Session Key Node Answer Memory
  | .prepare nodes => session.prepare system key nodes
  | .publish => session.publish system controller key acceptInput

/-- Preparation may finish in any admitted order between parent selections.
Every unfinished snapshot keeps its private captures and logical frontier. -/
def execute (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) :
    List (Action Node) → Session Key Node Answer Memory → Session Key Node Answer Memory
  | [], session => session
  | action :: rest, session =>
      execute system controller key acceptInput rest
        (applyAction system controller key acceptInput session action)

/-- Splitting a physical transcript keeps both already prepared operations
and the full parent-controlled snapshot; the prefix is never replayed. -/
theorem execute_append (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (first second : List (Action Node))
    (session : Session Key Node Answer Memory) :
    execute system controller key acceptInput (first ++ second) session =
      execute system controller key acceptInput second
        (execute system controller key acceptInput first session) := by
  induction first generalizing session with
  | nil => rfl
  | cons action rest ih => simpa [execute] using ih (applyAction system controller key acceptInput session action)

def publications (actions : List (Action Node)) : Nat :=
  (actions.map Action.publications).sum

/-- Arbitrary interleavings of admitted preparation and logical publication
retain exactly the reference prefix, including controller memory and complete
residuals. Physical preparation charges are deliberately absent from this
semantic projection; cost-dependent admission needs a stronger observer law. -/
theorem execute_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (actions : List (Action Node)) (session : Session Key Node Answer Memory)
    (valid : session.Valid system domain)
    (admitted : ∀ action ∈ actions, ∀ node ∈ action.inputs, domain node) :
    (execute system controller key acceptInput actions session).state =
      Snapshot.run system controller (publications actions) session.state := by
  induction actions generalizing session with
  | nil => rfl
  | cons action rest ih =>
      have restAdmitted : ∀ next ∈ rest, ∀ node ∈ next.inputs, domain node :=
        fun next member => admitted next (List.mem_cons_of_mem action member)
      cases action with
      | prepare nodes =>
          have nextValid := Session.prepare_valid system key domain session valid nodes
            (admitted (.prepare nodes) (by simp))
          simpa [execute, applyAction, publications, Action.publications,
            Session.prepare] using ih _ nextValid restAdmitted
      | publish =>
          have nextValid := Session.publish_valid system controller key domain
            acceptInput sound closed session valid
          simp only [execute, applyAction]
          rw [ih _ nextValid restAdmitted,
            Session.publish_agrees system controller key domain acceptInput sound session valid]
          simp only [publications, List.map_cons, Action.publications, List.sum_cons]
          rw [Snapshot.run_add]
          rfl

/-! ## Bounded strict execution with its unexecuted continuation -/

/-- The executor retains its physical transcript as well as the whole owned
session. `ticks` counts accepted parent ticks, not speculative work or time.
Refused publication stays at the head of `remaining` for later revalidation. -/
structure Checkpoint (Key Node Answer Memory : Type*) where
  session : Session Key Node Answer Memory
  remaining : List (Action Node)
  ticks : Nat

namespace Checkpoint

def Valid (system : BranchingSystem Node Answer) (domain : Node → Prop)
    (point : Checkpoint Key Node Answer Memory) : Prop :=
  point.session.Valid system domain ∧
    ∀ action ∈ point.remaining, ∀ node ∈ action.inputs, domain node

/-- One bounded executor action. Preparation leaves logical selection alone;
accepted publication removes exactly its action; refusal retains that action
and every later action without advancing the accepted-tick counter. -/
def step (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (key : Node → Key) (acceptInput : Node → Node → Bool)
    (point : Checkpoint Key Node Answer Memory) : Checkpoint Key Node Answer Memory :=
  match point.remaining with
  | [] => point
  | .prepare nodes :: rest =>
      { point with session := point.session.prepare system key nodes, remaining := rest }
  | .publish :: rest =>
      match point.session.publishChecked system controller key acceptInput with
      | .inl next => ⟨next, rest, point.ticks + 1⟩
      | .inr next => { point with session := next }

def run (system : BranchingSystem Node Answer) (controller : Controller Node Answer Memory)
    (key : Node → Key) (acceptInput : Node → Node → Bool) :
    Nat → Checkpoint Key Node Answer Memory → Checkpoint Key Node Answer Memory
  | 0, point => point
  | fuel + 1, point => step system controller key acceptInput
      (run system controller key acceptInput fuel point)

/-- A bounded split preserves the cache, remaining physical actions and the
cumulative tick counter; completed preparations and ticks are not replayed. -/
theorem run_add (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (first second : Nat)
    (point : Checkpoint Key Node Answer Memory) :
    run system controller key acceptInput (first + second) point =
      run system controller key acceptInput second
        (run system controller key acceptInput first point) := by
  induction second with
  | zero => simp only [Nat.add_zero, run]
  | succ second ih =>
      rw [Nat.add_succ]
      simp only [run]
      rw [ih]

/-- A refused operation cannot consume its continuation merely because more
executor budget is supplied. Logical suspension is distinct from exhaustion. -/
theorem run_refused (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (acceptInput : Node → Node → Bool) (point : Checkpoint Key Node Answer Memory)
    (rest : List (Action Node)) (pending : point.remaining = .publish :: rest)
    (refused : point.session.publishChecked system controller key acceptInput =
      .inr point.session) (fuel : Nat) :
    run system controller key acceptInput fuel point = point := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      have restore : (⟨point.session, .publish :: rest, point.ticks⟩ :
          Checkpoint Key Node Answer Memory) = point := by
        rw [← pending]
      simpa [run, ih, step, pending, refused] using restore

theorem step_valid (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (point : Checkpoint Key Node Answer Memory) (valid : point.Valid system domain) :
    (step system controller key acceptInput point).Valid system domain := by
  cases pending : point.remaining with
  | nil => simpa [step, pending] using valid
  | cons action rest =>
      have tail : ∀ next ∈ rest, ∀ node ∈ next.inputs, domain node := by
        intro next member node input
        exact valid.2 next (by simp [pending, member]) node input
      cases action with
      | prepare nodes =>
          have prepared := Session.prepare_valid system key domain point.session valid.1 nodes
            (valid.2 (.prepare nodes) (by simp [pending]))
          exact ⟨by simpa [step, pending] using prepared, by simpa [step, pending] using tail⟩
      | publish =>
          cases outcome : point.session.publishChecked system controller key acceptInput with
          | inl next =>
              have same := Session.publishChecked_accepted_eq system controller key
                acceptInput point.session next outcome
              have published := Session.publish_valid system controller key domain
                acceptInput sound closed point.session valid.1
              exact ⟨by simpa [step, pending, outcome, same] using published,
                by simpa [step, pending, outcome] using tail⟩
          | inr next =>
              have same := Session.publishChecked_refused_eq system controller key
                acceptInput point.session next outcome
              simpa [step, pending, outcome, same, Valid] using valid

theorem run_valid (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (point : Checkpoint Key Node Answer Memory) (valid : point.Valid system domain) (fuel : Nat) :
    (run system controller key acceptInput fuel point).Valid system domain := by
  induction fuel with
  | zero => exact valid
  | succ fuel ih => exact step_valid system controller key domain acceptInput sound closed _ ih

/-- Each physical step advances the reference snapshot only on accepted
parent publication. Failed authority checks and preparation are stuttering
steps for this projection, while their physical costs remain separate. -/
theorem step_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (point : Checkpoint Key Node Answer Memory) (valid : point.Valid system domain)
    (initial : Snapshot Node Answer Memory)
    (aligned : point.session.state = Snapshot.run system controller point.ticks initial) :
    (step system controller key acceptInput point).session.state =
      Snapshot.run system controller (step system controller key acceptInput point).ticks initial := by
  cases pending : point.remaining with
  | nil => simpa [step, pending] using aligned
  | cons action rest =>
      cases action with
      | prepare nodes => simpa [step, pending, Session.prepare] using aligned
      | publish =>
          cases outcome : point.session.publishChecked system controller key acceptInput with
          | inl next =>
              have same := Session.publishChecked_accepted_eq system controller key
                acceptInput point.session next outcome
              have logical := Session.publish_agrees system controller key domain
                acceptInput sound point.session valid.1
              simp only [step, pending, outcome, same]
              rw [logical, aligned]
              rfl
          | inr next =>
              have same := Session.publishChecked_refused_eq system controller key
                acceptInput point.session next outcome
              simpa [step, pending, outcome, same] using aligned

/-- Arbitrary bounded slices retain exactly the independently executed native
prefix at their cumulative accepted tick count, including after a refusal.
This does not identify speculative physical work with serial-prefix cost. -/
theorem run_agrees (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (key : Node → Key)
    (domain : Node → Prop) (acceptInput : Node → Node → Bool)
    (sound : SoundMatch system domain acceptInput)
    (closed : ∀ node, domain node → ∀ next ∈ system.successors node, domain next)
    (point : Checkpoint Key Node Answer Memory) (valid : point.Valid system domain)
    (initial : Snapshot Node Answer Memory)
    (aligned : point.session.state = Snapshot.run system controller point.ticks initial)
    (fuel : Nat) :
    (run system controller key acceptInput fuel point).session.state =
      Snapshot.run system controller (run system controller key acceptInput fuel point).ticks initial := by
  induction fuel with
  | zero => exact aligned
  | succ fuel ih =>
      exact step_agrees system controller key domain acceptInput sound _
        (run_valid system controller key domain acceptInput sound closed point valid fuel) initial ih

end Checkpoint

namespace Controls

def system : BranchingSystem (Nat × Bool) Nat where
  emit node := some (if node.2 then 9 else 7)
  successors _ := []

def acceptInput (captured current : Nat × Bool) : Bool := decide (captured = current)

def controller : Controller (Nat × Bool) Nat Unit :=
  Controller.fixed Scheduler.breadthFirst

def session : Session Nat (Nat × Bool) Nat Unit :=
  ⟨Snapshot.initial controller [(0, false), (1, false)], fun _ => none⟩

/-- Finishing the later occurrence first leaves the original ordered
frontier untouched. Its answer is still not the next publication. -/
theorem later_preparation_does_not_select :
    (session.prepare system Prod.fst [(1, false)]).state = session.state ∧
      ((session.prepare system Prod.fst [(1, false)]).publish system controller
        Prod.fst acceptInput).state.search.events = [⟨(0, false), 7⟩] := by
  exact ⟨rfl, by decide⟩

/-- Reverse physical completion keeps two equal answers as two emissions,
with their different producing occurrences in logical order. -/
theorem reverse_preparation_preserves_duplicate_answers :
    (execute system controller Prod.fst acceptInput
      [.prepare [(1, false), (0, false)], .publish, .publish] session).state.search.events =
      [⟨(0, false), 7⟩, ⟨(1, false), 7⟩] := by
  decide

/-- A same-key capture from a different input is refused before publication;
the ordinary expansion of the current input supplies the answer. -/
theorem changed_input_refuses_old_answer :
    let prepared := session.prepare system Prod.fst [(0, false)]
    (read system Prod.fst acceptInput prepared.cache (0, true)).emission = some 9 ∧
      (read system Prod.fst acceptInput prepared.cache (0, true)).emission ≠ some 7 := by
  decide

/-- Ignoring the captured input publishes an old answer. Source-key equality
alone is insufficient for the required local input authority. -/
theorem key_only_check_changes_answer :
    let prepared := session.prepare system Prod.fst [(0, false)]
    (read system Prod.fst (fun _ _ => true) prepared.cache (0, true)).emission = some 7 ∧
      system.emit (0, true) = some 9 := by
  decide

/-- The strict profile suspends on that changed input. It retains the old
prepared operation and every frontier entry for subsequent explicit handling. -/
theorem changed_input_suspends_complete_residual :
    let prepared := session.prepare system Prod.fst [(0, false)]
    let changed := { prepared with state :=
      { prepared.state with search := { prepared.state.search with frontier := [(0, true)] } } }
    changed.publishChecked system controller Prod.fst acceptInput = .inr changed := by
  rfl

/-- A completion-first controller is a different logical policy, despite
both runs eventually producing the same bag of equal values. -/
theorem completion_first_changes_origin :
    ((session.prepare system Prod.fst [(1, false)]).publish system
      (Controller.fixed Scheduler.reverseBreadthFirst) Prod.fst acceptInput).state.search.events ≠
      ((session.prepare system Prod.fst [(1, false)]).publish system controller
        Prod.fst acceptInput).state.search.events := by
  decide

def strictPoint : Checkpoint Nat (Nat × Bool) Nat Unit :=
  ⟨session, [.prepare [(1, false), (0, false)], .publish, .publish], 0⟩

/-- A slice after preparation retains both equal-answer publications. The next
slice consumes those exact actions and keeps their original producing order. -/
theorem strict_preparation_slice_keeps_duplicate_occurrences :
    (Checkpoint.run system controller Prod.fst acceptInput 1 strictPoint).remaining =
      [.publish, .publish] ∧
    (Checkpoint.run system controller Prod.fst acceptInput 2
      (Checkpoint.run system controller Prod.fst acceptInput 1 strictPoint)).session.state.search.events =
      [⟨(0, false), 7⟩, ⟨(1, false), 7⟩] ∧
    (Checkpoint.run system controller Prod.fst acceptInput 3 strictPoint).ticks = 2 := by
  decide

def refusedPoint : Checkpoint Nat (Nat × Bool) Nat Unit :=
  let prepared := session.prepare system Prod.fst [(0, false)]
  let changed := { prepared with state :=
    { prepared.state with search := { prepared.state.search with frontier := [(0, true)] } } }
  ⟨changed, [.publish, .prepare [(0, true)], .publish], 4⟩

/-- More budget neither hides refusal nor discards its pending continuation.
The existing cumulative tick count and full captured operation survive. -/
theorem strict_refusal_keeps_whole_checkpoint (fuel : Nat) :
    Checkpoint.run system controller Prod.fst acceptInput fuel refusedPoint = refusedPoint := by
  exact Checkpoint.run_refused system controller Prod.fst acceptInput refusedPoint
    [.prepare [(0, true)], .publish] rfl rfl fuel

/-- Revalidating the changed input permits the original pending publication;
the retained suffix is still present, and the old answer is never published. -/
theorem strict_revalidation_resumes_original_continuation :
    let repaired := { refusedPoint with
      session := refusedPoint.session.prepare system Prod.fst [(0, true)] }
    let result := Checkpoint.run system controller Prod.fst acceptInput 1 repaired
    result.remaining = [.prepare [(0, true)], .publish] ∧ result.ticks = 5 ∧
      result.session.state.search.events = [⟨(0, true), 9⟩] := by
  decide

/-- Finishing the supplied physical transcript does not prove the search is
closed. Both logical occurrences remain pending after preparation alone. -/
theorem finished_preparation_is_not_search_exhaustion :
    let result := Checkpoint.run system controller Prod.fst acceptInput 1
      (⟨session, [.prepare [(1, false), (0, false)]], 0⟩ :
        Checkpoint Nat (Nat × Bool) Nat Unit)
    result.remaining = [] ∧ result.session.state.search.frontier ≠ [] ∧ result.ticks = 0 := by
  decide

end Controls

end Preparation

/-! ## Executable discriminators -/

namespace Examples

open BranchingTemporal.FiniteSearch

/-- Stateful control may alternate policies while retaining exact work. -/
def alternatingController :
    Controller (FiniteSearch Bool) Bool Bool where
  initialMemory := false
  scheduler
    | false => Scheduler.breadthFirst
    | true => Scheduler.reverseBreadthFirst
  advance memory _ _ _ := !memory

/-- The stateful controller is executable and reaches both answer
occurrences. -/
example :
    (Snapshot.run system alternatingController 3
      (Snapshot.initial alternatingController [twoAnswers])).search.frontier = [] := by
  decide

/-- Equal answer values at different transition positions remain distinct
controlled emissions with distinct traces. -/
example :
    let machine := OccurrenceMachineCore.duplicateExample
    let controller : Controller
        (WorkOccurrence OccurrenceMachineCore.DuplicateExampleState)
        (Nat × List Nat) Unit :=
      Controller.fixed Scheduler.breadthFirst
    let result := Snapshot.run (WorkOccurrence.system machine) controller 3
      (Snapshot.initial controller
        [WorkOccurrence.root
          (.root : OccurrenceMachineCore.DuplicateExampleState)])
    result.search.events.map Emission.value = [(7, [0]), (7, [1])] := by
  decide

/-- Erasing transition traces preserves duplicate answer occurrences rather
than turning the result into a set. -/
example :
    let machine := OccurrenceMachineCore.duplicateExample
    let controller : Controller
        (WorkOccurrence OccurrenceMachineCore.DuplicateExampleState)
        (Nat × List Nat) Unit :=
      Controller.fixed Scheduler.breadthFirst
    let result := Snapshot.run (WorkOccurrence.system machine) controller 3
      (Snapshot.initial controller
        [WorkOccurrence.root
          (.root : OccurrenceMachineCore.DuplicateExampleState)])
    result.search.events.map (fun event => event.value.1) = [7, 7] := by
  decide

/-- Trace erasure is genuinely lossy even when the two answer values are
equal. -/
example : (7, [0]) ≠ (7, [1]) := by
  decide

/-- The one-node controller is fair: its only possible live occurrence is
selected at the initial snapshot. -/
example :
    Snapshot.FairFrom
      ({ emit := fun _ : Unit => some (), successors := fun _ => [] } :
        BranchingSystem Unit Unit)
      (Controller.fixed Scheduler.breadthFirst) [()] := by
  intro node _
  cases node
  exact ⟨0, rfl⟩

/-- Lawful occurrence preservation alone does not imply fairness: embedded
depth-first control retains the established silent-loop starvation witness. -/
example :
    ¬ Snapshot.FairFrom BranchingTemporal.Starvation.system
      (Controller.fixed Scheduler.depthFirst)
      BranchingTemporal.Starvation.roots := by
  intro fair
  exact BranchingTemporal.Starvation.depthFirst_not_fair
    ((Snapshot.fixed_fair_iff _ _ _).mp fair)

end Examples

#print axioms Snapshot.sound_run
#print axioms Snapshot.run_add
#print axioms Snapshot.completion_persists
#print axioms Snapshot.account_run
#print axioms Snapshot.completed_controllers_bag_agree
#print axioms Snapshot.run_completes_at_rank
#print axioms Snapshot.fair_emits_reachable
#print axioms Snapshot.run_multistep
#print axioms WorkOccurrence.generated_valid
#print axioms WorkOccurrence.controlled_emission_sound
#print axioms WorkOccurrence.eq_of_valid_trace
#print axioms Preparation.Session.prepareBatch_eq_prepare
#print axioms Preparation.execute_agrees
#print axioms Preparation.Session.publishChecked_refused
#print axioms Preparation.Session.publishChecked_agrees
#print axioms Preparation.Checkpoint.run_add
#print axioms Preparation.Checkpoint.run_refused
#print axioms Preparation.Checkpoint.run_agrees
#print axioms Snapshot.mapState_id
#print axioms Snapshot.mapState_comp
#print axioms Snapshot.tick_mapState
#print axioms Snapshot.run_mapState
#print axioms Preparation.Capture.mapNodes_id
#print axioms Preparation.Capture.mapNodes_comp
#print axioms Preparation.Capture.mapNodes_injective
#print axioms Preparation.capture_mapNodes

end Mettapedia.GSLT.Core.InferenceControl
