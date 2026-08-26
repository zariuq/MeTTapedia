import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Dynamics.CollapseAlgebra

/-!
# Weighted occurrences and controller portfolios

This file keeps four coordinates separate:

* occurrence identity distinguishes equal answers reached by distinct work;
* semantic weight is authored candidate data;
* counted multiplicity is an optional compression of repeated rows;
* scheduling priority only reorders the live frontier.

Controller invariance is deliberately proved before assuming any algebra on
the semantic weight.  A commutative additive structure is needed only when a
readout combines weights belonging to equal answers.  In particular, a
semantic weight does not replace occurrence multiplicity, and a priority is
not a semantic weight.
-/

namespace Mettapedia.GSLT.Core.WeightedOccurrenceControl

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.Collapse

universe uOccurrence uAnswer uReceipt uValue uNode uMemory

/-- One exact emitted occurrence.  `semanticWeight` is candidate data, not a
scheduler score.  Repeated equal answers remain distinct through `occurrence`
and `receipt`. -/
@[ext] structure WeightedOccurrence
    (Occurrence : Type uOccurrence) (Answer : Type uAnswer)
    (Receipt : Type uReceipt) (Value : Type uValue) where
  occurrence : Occurrence
  answer : Answer
  semanticWeight : Value
  receipt : Receipt
deriving DecidableEq, Repr

namespace WeightedOccurrence

/-- Forget the semantic annotation and occurrence identity when feeding the
legacy counted-collapse interface.  The unit multiplicity records that this
value denotes one occurrence.  This projection is intentionally lossy. -/
def toCountedObs
    (observation : WeightedOccurrence Occurrence Answer Receipt Value) :
    Obs Answer Receipt :=
  ⟨observation.answer, 1, observation.receipt⟩

/-- Forget only the weight, retaining the exact occurrence and receipt. -/
def eraseWeight
    (observation : WeightedOccurrence Occurrence Answer Receipt Value) :
    Occurrence × Answer × Receipt :=
  (observation.occurrence, observation.answer, observation.receipt)

end WeightedOccurrence

/-- The exact completed observation of a controller run.  The existing event
bag already retains every `WeightedOccurrence` as an answer value; no merging
by answer or weight occurs here. -/
abbrev weightedEventBag
    {Node : Type uNode} {Occurrence : Type uOccurrence}
    {Answer : Type uAnswer} {Receipt : Type uReceipt} {Value : Type uValue}
    (events : List
      (Emission Node (WeightedOccurrence Occurrence Answer Receipt Value))) :
    Multiset (WeightedOccurrence Occurrence Answer Receipt Value) :=
  eventBag events

/-- Any two completed occurrence-preserving controllers agree on the exact
weighted occurrence bag.  No semiring hypothesis is needed: scheduling cannot
change authored annotations in the first place. -/
theorem completed_controllers_weighted_bag_agree
    {Node : Type uNode} {Occurrence : Type uOccurrence}
    {Answer : Type uAnswer} {Receipt : Type uReceipt} {Value : Type uValue}
    (system :
      BranchingSystem Node (WeightedOccurrence Occurrence Answer Receipt Value))
    {FirstMemory SecondMemory : Type*}
    (first : Controller Node
      (WeightedOccurrence Occurrence Answer Receipt Value) FirstMemory)
    (second : Controller Node
      (WeightedOccurrence Occurrence Answer Receipt Value) SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (Snapshot.run system first firstFuel
        (Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (Snapshot.run system second secondFuel
        (Snapshot.initial second roots)).search.frontier = []) :
    weightedEventBag
        (Snapshot.run system first firstFuel
          (Snapshot.initial first roots)).search.events =
      weightedEventBag
        (Snapshot.run system second secondFuel
          (Snapshot.initial second roots)).search.events :=
  Snapshot.completed_controllers_bag_agree system first second denotation roots
    firstFuel secondFuel firstComplete secondComplete

section Readout

variable {Occurrence : Type uOccurrence} {Answer : Type uAnswer}
  {Receipt : Type uReceipt} {Value : Type uValue}

/-- Add the semantic weights of occurrences carrying one answer.  This is a
readout of the exact occurrence bag, not its representation. -/
def answerWeight [DecidableEq Answer] [AddCommMonoid Value]
    (wanted : Answer)
    (observations :
      Multiset (WeightedOccurrence Occurrence Answer Receipt Value)) : Value :=
  ((observations.filter fun observation => observation.answer = wanted).map
    WeightedOccurrence.semanticWeight).sum

theorem answerWeight_congr [DecidableEq Answer] [AddCommMonoid Value]
    (wanted : Answer)
    {first second :
      Multiset (WeightedOccurrence Occurrence Answer Receipt Value)}
    (same : first = second) :
    answerWeight wanted first = answerWeight wanted second := by
  rw [same]

/-- Controller-independent exact weighted bags induce controller-independent
additive readouts.  Addition is required here, and only here. -/
theorem completed_controllers_answerWeight_agree
    [DecidableEq Answer] [AddCommMonoid Value]
    {Node : Type uNode}
    (system :
      BranchingSystem Node (WeightedOccurrence Occurrence Answer Receipt Value))
    {FirstMemory SecondMemory : Type*}
    (first : Controller Node
      (WeightedOccurrence Occurrence Answer Receipt Value) FirstMemory)
    (second : Controller Node
      (WeightedOccurrence Occurrence Answer Receipt Value) SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (Snapshot.run system first firstFuel
        (Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (Snapshot.run system second secondFuel
        (Snapshot.initial second roots)).search.frontier = [])
    (wanted : Answer) :
    answerWeight wanted
        (weightedEventBag
          (Snapshot.run system first firstFuel
            (Snapshot.initial first roots)).search.events) =
      answerWeight wanted
        (weightedEventBag
          (Snapshot.run system second secondFuel
            (Snapshot.initial second roots)).search.events) := by
  apply answerWeight_congr
  exact completed_controllers_weighted_bag_agree system first second denotation
    roots firstFuel secondFuel firstComplete secondComplete

end Readout

/-! ## A generic round-robin controller -/

/-- Cyclic successor for a nonempty finite scheduler family. -/
def nextIndex {count : Nat} [NeZero count] (index : Fin count) : Fin count :=
  ⟨(index.val + 1) % count, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne count))⟩

/-! ## Independent scorer queues over one occurrence store -/

/-- One portfolio lane updates its own pending queue after a selected
occurrence has been removed.  The update may implement stack, FIFO, KBO,
valuation, or learned ordering, but it must return every pending and generated
occurrence exactly once. -/
structure QueueDiscipline (Node : Type*) where
  integrate : List Node → List Node → List Node
  integrate_complete : ∀ pending generated,
    (integrate pending generated).Perm (pending ++ generated)

namespace QueueDiscipline

variable {Node : Type*}

def breadthFirst : QueueDiscipline Node where
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := .refl _

def depthFirst : QueueDiscipline Node where
  integrate pending generated := generated ++ pending
  integrate_complete _ _ := List.perm_append_comm

end QueueDiscipline

/-- A live occurrence is stored once semantically while each scorer retains
an independent complete queue view.  Queue completeness is the capability
boundary: a ranker may reorder, but cannot prune, duplicate, or synthesize an
occurrence. -/
structure PortfolioFrontier (Node : Type*) (count : Nat) where
  live : List Node
  queues : Fin count → List Node
  queue_complete : ∀ lane, (queues lane).Perm live

namespace PortfolioFrontier

variable {Node : Type*} {count : Nat}

def initial (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) : PortfolioFrontier Node count where
  live := roots
  queues lane := (disciplines lane).integrate [] roots
  queue_complete lane := by
    simpa using (disciplines lane).integrate_complete [] roots

/-- Select from one queue without changing the shared live occurrence store. -/
def selected (frontier : PortfolioFrontier Node count) (lane : Fin count) :
    Option Node :=
  (frontier.queues lane).head?

theorem selected_mem {frontier : PortfolioFrontier Node count}
    {lane : Fin count} {node : Node}
    (selection : frontier.selected lane = some node) :
    node ∈ frontier.live := by
  have queueMember : node ∈ frontier.queues lane := by
    unfold selected at selection
    cases queue : frontier.queues lane with
    | nil => simp [queue] at selection
    | cons head tail =>
        simp only [queue, List.head?_cons, Option.some.injEq] at selection
        simp [selection]
  exact (frontier.queue_complete lane).mem_iff.mp queueMember

/-- Remove one selected occurrence from every queue by identity, then let
each lane independently integrate the same generated occurrences. -/
def advance [DecidableEq Node]
    (disciplines : Fin count → QueueDiscipline Node)
    (frontier : PortfolioFrontier Node count)
    (selected : Node) (generated : List Node) :
    PortfolioFrontier Node count where
  live := frontier.live.erase selected ++ generated
  queues lane :=
    (disciplines lane).integrate
      ((frontier.queues lane).erase selected) generated
  queue_complete lane := by
    exact ((disciplines lane).integrate_complete _ _).trans
      (((frontier.queue_complete lane).erase selected).append_right generated)

end PortfolioFrontier

/-- Events, the independent portfolio frontier, and the selected lane advance
together.  The controller cursor is resumable state, not answer data. -/
structure PortfolioSnapshot (Node Answer : Type*) (count : Nat) where
  events : List (Emission Node Answer)
  frontier : PortfolioFrontier Node count
  cursor : Fin count

namespace PortfolioSnapshot

variable {Node Answer : Type*} {count : Nat}

def initial [NeZero count]
    (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) :
    PortfolioSnapshot Node Answer count :=
  ⟨[], PortfolioFrontier.initial disciplines roots, start⟩

private def eventFor (node : Node) : Option Answer → List (Emission Node Answer)
  | none => []
  | some answer => [⟨node, answer⟩]

/-- One portfolio step selects from exactly one independent queue, removes the
selected occurrence from all queues, and gives every lane the same authorized
successor occurrences. -/
def tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count) :
    PortfolioSnapshot Node Answer count :=
  match snapshot.frontier.selected snapshot.cursor with
  | none => snapshot
  | some node =>
      { events := snapshot.events ++ eventFor node (system.emit node)
        frontier := snapshot.frontier.advance disciplines node
          (system.successors node)
        cursor := nextIndex snapshot.cursor }

def run [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node) :
    Nat → PortfolioSnapshot Node Answer count →
      PortfolioSnapshot Node Answer count
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      tick system disciplines (run system disciplines fuel snapshot)

theorem events_prefix_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count) :
    snapshot.events.IsPrefix (tick system disciplines snapshot).events := by
  cases selection : snapshot.frontier.selected snapshot.cursor with
  | none => simp [tick, selection]
  | some node =>
      cases emitted : system.emit node <;>
        simp [tick, selection, emitted, eventFor]

/-- The completed-answer account of an independent portfolio uses the shared
live occurrence store, never any scorer queue's private order. -/
def account {system : BranchingSystem Node Answer}
    (denotation : AdditiveDenotation system)
    (snapshot : PortfolioSnapshot Node Answer count) : Multiset Answer :=
  eventBag snapshot.events +
    foldValues denotation.value snapshot.frontier.live

@[simp] private theorem eventBag_eventFor (node : Node)
    (answer : Option Answer) :
    eventBag (eventFor node answer) = optionBag answer := by
  cases answer <;> simp [eventFor, eventBag, optionBag]

/-- One independent-portfolio step preserves the completed answer bag.  This
is the algebraic reason scorer queues may differ physically while none becomes
an answer or successor authority. -/
theorem account_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (denotation : AdditiveDenotation system)
    (snapshot : PortfolioSnapshot Node Answer count) :
    account denotation (tick system disciplines snapshot) =
      account denotation snapshot := by
  cases ordered : snapshot.frontier.queues snapshot.cursor with
  | nil =>
      have selection : snapshot.frontier.selected snapshot.cursor = none := by
        simp [PortfolioFrontier.selected, ordered]
      simp [tick, selection]
  | cons node pending =>
      have selection :
          snapshot.frontier.selected snapshot.cursor = some node := by
        simp [PortfolioFrontier.selected, ordered]
      have queuePerm :
          (node :: pending).Perm snapshot.frontier.live := by
        simpa [ordered] using
          snapshot.frontier.queue_complete snapshot.cursor
      have erasedPerm :
          pending.Perm (snapshot.frontier.live.erase node) := by
        simpa using queuePerm.erase node
      have originalValue :
          foldValues denotation.value snapshot.frontier.live =
            foldValues denotation.value (node :: pending) :=
        foldValues_perm denotation.value queuePerm.symm
      have erasedValue :
          foldValues denotation.value
              (snapshot.frontier.live.erase node) =
            foldValues denotation.value pending :=
        foldValues_perm denotation.value erasedPerm.symm
      rw [account, account]
      simp only [tick, selection, PortfolioFrontier.advance]
      rw [eventBag_append, eventBag_eventFor, foldValues_append,
        erasedValue, originalValue]
      simp only [foldValues]
      rw [denotation.unfold]
      ac_rfl

theorem account_run [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (denotation : AdditiveDenotation system) (fuel : Nat)
    (snapshot : PortfolioSnapshot Node Answer count) :
    account denotation (run system disciplines fuel snapshot) =
      account denotation snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      exact (account_tick system disciplines denotation _).trans
        inductionHypothesis

/-- A completed independent portfolio emits the branching system's additive
denotation, regardless of its lane orders or round-robin cursor. -/
theorem completed_run_denotation [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (start : Fin count) (fuel : Nat)
    (complete :
      (run system disciplines fuel
        (initial disciplines roots start)).frontier.live = []) :
    eventBag
        (run system disciplines fuel
          (initial disciplines roots start)).events =
      foldValues denotation.value roots := by
  have preserved := account_run system disciplines denotation fuel
    (initial disciplines roots start)
  unfold account at preserved
  rw [complete] at preserved
  simpa [initial, PortfolioFrontier.initial, foldValues, eventBag] using preserved

end PortfolioSnapshot

/-- Round-robin over any nonempty finite family of occurrence-preserving
schedulers.  Each family member may implement DFS, BFS, KBO, an authored
valuation, or a checked learned permutation.  The family changes only the
scheduler selected at a step; successor authority remains in the branching
system. -/
def roundRobinController {count : Nat} [NeZero count]
    (family : Fin count → Scheduler Node) (start : Fin count) :
    Controller Node Answer (Fin count) where
  initialMemory := start
  scheduler := family
  advance memory _ _ _ := nextIndex memory

/-- A round-robin portfolio inherits ordinary reachability soundness without
any theorem about the score carriers used by its member schedulers. -/
theorem roundRobin_run_sound {count : Nat} [NeZero count]
    (family : Fin count → Scheduler Node) (start : Fin count)
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) :
    (Snapshot.run system (roundRobinController family start) fuel
      (Snapshot.initial (roundRobinController family start) roots)).search.Sound
        system roots :=
  Snapshot.sound_run system (roundRobinController family start)
    (BranchingTemporal.initial_sound system roots) fuel

namespace Canaries

def first : WeightedOccurrence Nat Bool Unit Nat :=
  ⟨0, true, 2, ()⟩

def second : WeightedOccurrence Nat Bool Unit Nat :=
  ⟨1, true, 2, ()⟩

def heavier : WeightedOccurrence Nat Bool Unit Nat :=
  ⟨0, true, 3, ()⟩

/-- Positive multiplicity control: equal answers from distinct occurrences
remain two observations. -/
theorem duplicate_answers_remain_two :
    ({first, second} : Multiset (WeightedOccurrence Nat Bool Unit Nat)).card = 2 := by
  decide

/-- Negative projection control: legacy counted observations do not determine
semantic weight.  Multiplicity and weight cannot share one field. -/
theorem counted_projection_forgets_weight :
    first.toCountedObs = heavier.toCountedObs ∧ first ≠ heavier := by
  constructor
  · rfl
  · intro same
    have sameWeight := congrArg WeightedOccurrence.semanticWeight same
    norm_num [first, heavier] at sameWeight

/-- Negative aggregation control: additive answer weights do not retain which
occurrence supplied them. -/
theorem answerWeight_forgets_occurrence :
    answerWeight true ({first} : Multiset (WeightedOccurrence Nat Bool Unit Nat)) =
        answerWeight true ({second} : Multiset (WeightedOccurrence Nat Bool Unit Nat)) ∧
      ({first} : Multiset (WeightedOccurrence Nat Bool Unit Nat)) ≠ {second} := by
  decide

/-- A concrete DFS/BFS portfolio reaches the right-hand answer in the standard
starvation system.  This is a discriminator for the mechanism, not a general
fairness theorem for arbitrary portfolios. -/
def depthBreadthFamily : Fin 2 → Scheduler BranchingTemporal.Starvation.Node :=
  fun index =>
    if index = 0 then Scheduler.depthFirst else Scheduler.breadthFirst

def depthBreadthController :
    Controller BranchingTemporal.Starvation.Node Nat (Fin 2) :=
  roundRobinController depthBreadthFamily 0

/-- Independent DFS and BFS queues over the same occurrence store.  Each lane
retains its own pending order when another lane is selected. -/
def depthBreadthDisciplines :
    Fin 2 → QueueDiscipline BranchingTemporal.Starvation.Node :=
  fun index =>
    if index = 0 then QueueDiscipline.depthFirst
    else QueueDiscipline.breadthFirst

def depthBreadthPortfolioInitial : PortfolioSnapshot
    BranchingTemporal.Starvation.Node Nat 2 :=
  PortfolioSnapshot.initial depthBreadthDisciplines
    BranchingTemporal.Starvation.roots 0

/-- After the DFS lane expands the loop once, its stack and the BFS queue hold
different complete orders over the same two live occurrences. -/
theorem independent_queues_diverge_after_depth_step :
    let after := PortfolioSnapshot.tick BranchingTemporal.Starvation.system
      depthBreadthDisciplines depthBreadthPortfolioInitial
    after.frontier.queues 0 =
        [BranchingTemporal.Starvation.Node.loop,
          BranchingTemporal.Starvation.Node.answer] ∧
      after.frontier.queues 1 =
        [BranchingTemporal.Starvation.Node.answer,
          BranchingTemporal.Starvation.Node.loop] := by
  decide

/-- Negative control: one mutable frontier list cannot simultaneously be the
two independent queue orders required after the first portfolio step. -/
theorem no_single_list_represents_independent_queues :
    let after := PortfolioSnapshot.tick BranchingTemporal.Starvation.system
      depthBreadthDisciplines depthBreadthPortfolioInitial
    ¬ ∃ shared : List BranchingTemporal.Starvation.Node,
      shared = after.frontier.queues 0 ∧
      shared = after.frontier.queues 1 := by
  simp [PortfolioSnapshot.tick, depthBreadthPortfolioInitial,
    PortfolioSnapshot.initial, PortfolioFrontier.initial,
    PortfolioFrontier.selected, PortfolioFrontier.advance,
    depthBreadthDisciplines, QueueDiscipline.depthFirst,
    QueueDiscipline.breadthFirst, BranchingTemporal.Starvation.roots,
    BranchingTemporal.Starvation.system]

/-- The independent BFS lane reaches the live answer on its first turn,
without waiting for a later scheduler to repair a shared frontier order. -/
theorem independent_depth_breadth_reaches_answer :
    (⟨BranchingTemporal.Starvation.Node.answer, 42⟩ :
        Emission BranchingTemporal.Starvation.Node Nat) ∈
      (PortfolioSnapshot.run BranchingTemporal.Starvation.system
        depthBreadthDisciplines 2 depthBreadthPortfolioInitial).events := by
  decide

theorem depth_breadth_portfolio_reaches_answer :
    (⟨BranchingTemporal.Starvation.Node.answer, 42⟩ :
        Emission BranchingTemporal.Starvation.Node Nat) ∈
      (Snapshot.run BranchingTemporal.Starvation.system depthBreadthController 3
        (Snapshot.initial depthBreadthController
          BranchingTemporal.Starvation.roots)).search.events := by
  decide

/-- A pure DFS member still carries the established starvation behavior; a
portfolio does not become fair merely because its interface can host a fair
member. -/
theorem depth_first_still_starves (fuel : Nat) :
    (⟨BranchingTemporal.Starvation.Node.answer, 42⟩ :
        Emission BranchingTemporal.Starvation.Node Nat) ∉
      (Snapshot.run BranchingTemporal.Starvation.system
        (Controller.fixed Scheduler.depthFirst) fuel
        (Snapshot.initial (Controller.fixed Scheduler.depthFirst)
          BranchingTemporal.Starvation.roots)).search.events := by
  change
    (⟨BranchingTemporal.Starvation.Node.answer, 42⟩ :
        Emission BranchingTemporal.Starvation.Node Nat) ∉
      (Snapshot.run BranchingTemporal.Starvation.system
        (Controller.fixed Scheduler.depthFirst) fuel
        { search := BranchingTemporal.initial BranchingTemporal.Starvation.roots,
          memory := () }).search.events
  rw [Snapshot.fixed_run_search]
  exact BranchingTemporal.Starvation.depthFirst_starves_answer fuel

end Canaries

#print axioms completed_controllers_weighted_bag_agree
#print axioms completed_controllers_answerWeight_agree
#print axioms roundRobin_run_sound
#print axioms PortfolioFrontier.selected_mem
#print axioms PortfolioSnapshot.events_prefix_tick
#print axioms PortfolioSnapshot.account_tick
#print axioms PortfolioSnapshot.completed_run_denotation
#print axioms Canaries.counted_projection_forgets_weight
#print axioms Canaries.answerWeight_forgets_occurrence
#print axioms Canaries.independent_queues_diverge_after_depth_step
#print axioms Canaries.no_single_list_represents_independent_queues
#print axioms Canaries.independent_depth_breadth_reaches_answer
#print axioms Canaries.depth_breadth_portfolio_reaches_answer
#print axioms Canaries.depth_first_still_starves

end Mettapedia.GSLT.Core.WeightedOccurrenceControl
