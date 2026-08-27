import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.Machines.OccurrenceCone

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

/-- Observe a bounded number of globally scheduled work occurrences. -/
def run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) :
    Nat → Snapshot Node Answer Memory → Snapshot Node Answer Memory
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => tick system controller (run system controller fuel snapshot)

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

end Mettapedia.GSLT.Core.InferenceControl
