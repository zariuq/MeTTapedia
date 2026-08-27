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

theorem nextIndex_eq_add_one {count : Nat} [NeZero count]
    (index : Fin count) : nextIndex index = index + 1 := by
  apply Fin.ext
  simp [nextIndex, Fin.val_add]

private theorem finOfNat_succ {count : Nat} [NeZero count] (fuel : Nat) :
    Fin.ofNat count (fuel + 1) = Fin.ofNat count fuel + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem iterate_nextIndex {count : Nat} [NeZero count]
    (index : Fin count) (fuel : Nat) :
    (nextIndex^[fuel]) index = index + Fin.ofNat count fuel := by
  induction fuel generalizing index with
  | zero => simp [Fin.ofNat]
  | succ fuel inductionHypothesis =>
      rw [Function.iterate_succ_apply, nextIndex_eq_add_one,
        inductionHypothesis, finOfNat_succ]
      abel

/-- A finite round-robin cursor reaches every lane from every starting lane. -/
theorem nextIndex_reaches {count : Nat} [NeZero count]
    (start target : Fin count) :
    ∃ fuel, (nextIndex^[fuel]) start = target := by
  let delta : Fin count := target - start
  refine ⟨delta.val, ?_⟩
  rw [iterate_nextIndex]
  have castDelta : Fin.ofNat count delta.val = delta := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt delta.isLt]
  rw [castDelta]
  dsimp [delta]
  abel

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

/-- The number of pending occurrences preceding a target in one queue.  It is
meaningful as an age measure only while the target remains in the queue. -/
def ageDebt [DecidableEq Node] (pending : List Node) (target : Node) : Nat :=
  pending.idxOf target

/-- Removing a different live occurrence cannot increase a target's age debt.
This is the local fact needed when another portfolio lane wins a turn. -/
theorem ageDebt_erase_le [DecidableEq Node]
    (pending : List Node) {selected target : Node}
    (different : selected ≠ target) :
    ageDebt (pending.erase selected) target ≤ ageDebt pending target := by
  induction pending with
  | nil => simp [ageDebt]
  | cons head tail inductionHypothesis =>
      by_cases headSelected : head = selected
      · subst head
        simp [ageDebt, different]
      · by_cases headTarget : head = target
        · subst head
          simp [ageDebt, headSelected]
        · simp only [List.erase_cons, beq_iff_eq, headSelected,
            if_false, ageDebt, List.idxOf_cons_ne _ headTarget]
          exact Nat.succ_le_succ inductionHypothesis

/-- FIFO integration appends newly generated work after every occurrence that
was already pending.  Consequently another lane's selection cannot make an
existing target younger in the wrong direction. -/
theorem breadthFirst_ageDebt_nonincreasing [DecidableEq Node]
    (pending generated : List Node) {selected target : Node}
    (targetPending : target ∈ pending)
    (different : selected ≠ target) :
    ageDebt
        (breadthFirst.integrate (pending.erase selected) generated)
        target ≤ ageDebt pending target := by
  have targetRemains : target ∈ pending.erase selected := by
    exact (List.mem_erase_of_ne (Ne.symm different)).2 targetPending
  rw [breadthFirst, ageDebt, List.idxOf_append_of_mem targetRemains]
  exact ageDebt_erase_le pending different

/-- On an age/FIFO turn, selecting an older head decreases a surviving
target's debt by exactly one; generated work is appended behind it. -/
theorem breadthFirst_ageDebt_head_step [DecidableEq Node]
    (head target : Node) (pending generated : List Node)
    (different : head ≠ target) (targetPending : target ∈ pending) :
    ageDebt (breadthFirst.integrate pending generated) target + 1 =
      ageDebt (head :: pending) target := by
  change (pending ++ generated).idxOf target + 1 =
    (head :: pending).idxOf target
  rw [List.idxOf_append_of_mem targetPending,
    List.idxOf_cons_ne pending different]

/-- Negative control: a depth-first lane may put fresh work before an existing
target, so it cannot serve as the portfolio's age floor. -/
theorem depthFirst_can_increase_ageDebt :
    ageDebt (depthFirst.integrate [1] [2]) (1 : Nat) >
      ageDebt [1] 1 := by
  decide

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

/-- Events, exact selection receipts, the independent portfolio frontier, and
the selected lane advance together.  The controller cursor is resumable
state, not answer data. -/
structure PortfolioSnapshot (Node Answer : Type*) (count : Nat) where
  events : List (Emission Node Answer)
  selections : List Node
  frontier : PortfolioFrontier Node count
  cursor : Fin count

namespace PortfolioSnapshot

variable {Node Answer : Type*} {count : Nat}

def initial [NeZero count]
    (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) :
    PortfolioSnapshot Node Answer count :=
  ⟨[], [], PortfolioFrontier.initial disciplines roots, start⟩

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
        selections := snapshot.selections ++ [node]
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

theorem run_add [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (left right : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    run system disciplines (left + right) snapshot =
      run system disciplines right (run system disciplines left snapshot) := by
  induction right with
  | zero => rw [Nat.add_zero]; rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      simp only [run]
      rw [inductionHypothesis]

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

theorem selections_prefix_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count) :
    snapshot.selections.IsPrefix
      (tick system disciplines snapshot).selections := by
  cases selection : snapshot.frontier.selected snapshot.cursor with
  | none => simp [tick, selection]
  | some node => simp [tick, selection]

theorem selections_prefix_run [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    snapshot.selections.IsPrefix
      (run system disciplines fuel snapshot).selections := by
  induction fuel with
  | zero => simp [run]
  | succ fuel inductionHypothesis =>
      simp only [run]
      exact inductionHypothesis.trans
        (selections_prefix_tick system disciplines _)

/-- A nonempty live occurrence store always yields a selection from every
complete lane queue. -/
theorem selected_of_live [NeZero count] [DecidableEq Node]
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ selected,
      snapshot.frontier.selected snapshot.cursor = some selected := by
  have queueLive : target ∈ snapshot.frontier.queues snapshot.cursor :=
    (snapshot.frontier.queue_complete snapshot.cursor).mem_iff.mpr live
  cases queueEq : snapshot.frontier.queues snapshot.cursor with
  | nil => simp [queueEq] at queueLive
  | cons head tail =>
      exact ⟨head, by simp [PortfolioFrontier.selected, queueEq]⟩

/-- Every successful portfolio step records the exact selected occurrence. -/
theorem selection_receipt_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    {node : Node}
    (selection : snapshot.frontier.selected snapshot.cursor = some node) :
    (tick system disciplines snapshot).selections =
      snapshot.selections ++ [node] := by
  simp [tick, selection]

/-- If a live target is not selected at this step, it remains live.  Thus a
controller cannot silently consume an occurrence without a receipt. -/
theorem live_or_selected_after_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    target ∈ (tick system disciplines snapshot).frontier.live ∨
      (tick system disciplines snapshot).selections =
        snapshot.selections ++ [target] := by
  obtain ⟨selected, selection⟩ := selected_of_live snapshot live
  by_cases selectedTarget : selected = target
  · right
    subst selected
    exact selection_receipt_tick system disciplines snapshot selection
  · left
    have targetRemains :
        target ∈ snapshot.frontier.live.erase selected :=
      (List.mem_erase_of_ne (Ne.symm selectedTarget)).2 live
    simp [tick, selection, PortfolioFrontier.advance, targetRemains]

/-- After any finite portfolio prefix, an initially live occurrence is still
live or its exact identity appears in the selection receipts. -/
theorem live_or_selected_after_run [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    target ∈ (run system disciplines fuel snapshot).frontier.live ∨
      target ∈ (run system disciplines fuel snapshot).selections := by
  induction fuel with
  | zero => exact Or.inl live
  | succ fuel inductionHypothesis =>
      simp only [run]
      rcases inductionHypothesis with targetLive | targetSelected
      · rcases live_or_selected_after_tick system disciplines _ targetLive with
        targetLiveNext | targetReceipt
        · exact Or.inl targetLiveNext
        · exact Or.inr (by simp [targetReceipt])
      · exact Or.inr <|
          List.IsPrefix.mem targetSelected
            (selections_prefix_tick system disciplines _)

/-- While a live target has no receipt, every step is successful and the
portfolio cursor follows the declared finite round-robin clock exactly. -/
theorem cursor_run_of_live_unselected [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live)
    (unselected :
      target ∉ (run system disciplines fuel snapshot).selections) :
    (run system disciplines fuel snapshot).cursor =
      (nextIndex^[fuel]) snapshot.cursor := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      let previous := run system disciplines fuel snapshot
      have previousPrefix : previous.selections.IsPrefix
          (tick system disciplines previous).selections :=
        selections_prefix_tick system disciplines previous
      have unselectedPrevious : target ∉ previous.selections := by
        intro selectedPrevious
        exact unselected
          (List.IsPrefix.mem selectedPrevious previousPrefix)
      have targetLive : target ∈ previous.frontier.live := by
        rcases live_or_selected_after_run system disciplines fuel snapshot live with
          livePrevious | selectedPrevious
        · exact livePrevious
        · exact False.elim (unselectedPrevious selectedPrevious)
      obtain ⟨selected, selection⟩ := selected_of_live previous targetLive
      have previousCursor : previous.cursor =
          (nextIndex^[fuel]) snapshot.cursor :=
        inductionHypothesis unselectedPrevious
      simp only [run]
      change (tick system disciplines previous).cursor =
        (nextIndex^[fuel + 1]) snapshot.cursor
      simp only [tick, selection]
      rw [previousCursor]
      simpa only [Nat.add_comm] using
        (Function.iterate_succ_apply' nextIndex fuel snapshot.cursor).symm

/-- From any cursor, finite round-robin either selects a live target first or
reaches the requested lane with the target still live and unselected. -/
theorem reaches_lane_or_selects [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    (lane : Fin count) {target : Node}
    (live : target ∈ snapshot.frontier.live) :
    ∃ fuel,
      target ∈ (run system disciplines fuel snapshot).selections ∨
        (target ∈ (run system disciplines fuel snapshot).frontier.live ∧
          target ∉ (run system disciplines fuel snapshot).selections ∧
          (run system disciplines fuel snapshot).cursor = lane) := by
  obtain ⟨fuel, reaches⟩ := nextIndex_reaches snapshot.cursor lane
  refine ⟨fuel, ?_⟩
  by_cases selected :
      target ∈ (run system disciplines fuel snapshot).selections
  · exact Or.inl selected
  · right
    have targetLive :
        target ∈ (run system disciplines fuel snapshot).frontier.live :=
      (live_or_selected_after_run system disciplines fuel snapshot live).resolve_right
        selected
    refine ⟨targetLive, selected, ?_⟩
    exact (cursor_run_of_live_unselected system disciplines fuel snapshot
      live selected).trans reaches

/-- A turn of a FIFO age lane either selects the target or decreases its
predecessor debt exactly once while retaining it in the live store. -/
theorem breadthFirst_turn_progress [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    (ageLane : Fin count)
    (atAgeLane : snapshot.cursor = ageLane)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    (tick system disciplines snapshot).selections =
        snapshot.selections ++ [target] ∨
      (target ∈ (tick system disciplines snapshot).frontier.live ∧
        QueueDiscipline.ageDebt
              ((tick system disciplines snapshot).frontier.queues ageLane)
              target + 1 =
          QueueDiscipline.ageDebt
            (snapshot.frontier.queues ageLane) target) := by
  have targetQueued : target ∈ snapshot.frontier.queues ageLane :=
    (snapshot.frontier.queue_complete ageLane).mem_iff.mpr live
  cases queueEq : snapshot.frontier.queues ageLane with
  | nil => simp [queueEq] at targetQueued
  | cons head pending =>
      have selection :
          snapshot.frontier.selected snapshot.cursor = some head := by
        simp [PortfolioFrontier.selected, atAgeLane, queueEq]
      by_cases headTarget : head = target
      · left
        subst head
        exact selection_receipt_tick system disciplines snapshot selection
      · right
        have targetPending : target ∈ pending := by
          rw [queueEq] at targetQueued
          simp only [List.mem_cons] at targetQueued
          exact targetQueued.resolve_left (Ne.symm headTarget)
        have targetRemains : target ∈ snapshot.frontier.live.erase head :=
          (List.mem_erase_of_ne (Ne.symm headTarget)).2 live
        constructor
        · simp [tick, selection, PortfolioFrontier.advance, targetRemains]
        · simp only [tick, selection, PortfolioFrontier.advance]
          rw [ageDiscipline, queueEq]
          simp only [List.erase_cons_head,
            QueueDiscipline.breadthFirst]
          exact QueueDiscipline.breadthFirst_ageDebt_head_step
            head target pending (system.successors head)
            headTarget targetPending

/-- A non-age turn either selects the target itself or leaves the FIFO age
lane's debt nonincreasing. -/
theorem breadthFirst_other_turn_progress [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (snapshot : PortfolioSnapshot Node Answer count)
    (ageLane : Fin count)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    (tick system disciplines snapshot).selections =
        snapshot.selections ++ [target] ∨
      (target ∈ (tick system disciplines snapshot).frontier.live ∧
        QueueDiscipline.ageDebt
            ((tick system disciplines snapshot).frontier.queues ageLane)
            target ≤
          QueueDiscipline.ageDebt
            (snapshot.frontier.queues ageLane) target) := by
  obtain ⟨selected, selection⟩ := selected_of_live snapshot live
  by_cases selectedTarget : selected = target
  · left
    subst selected
    exact selection_receipt_tick system disciplines snapshot selection
  · right
    have targetQueued : target ∈ snapshot.frontier.queues ageLane :=
      (snapshot.frontier.queue_complete ageLane).mem_iff.mpr live
    have targetRemains : target ∈ snapshot.frontier.live.erase selected :=
      (List.mem_erase_of_ne (Ne.symm selectedTarget)).2 live
    constructor
    · simp [tick, selection, PortfolioFrontier.advance, targetRemains]
    · simp only [tick, selection, PortfolioFrontier.advance]
      rw [ageDiscipline]
      exact QueueDiscipline.breadthFirst_ageDebt_nonincreasing
        (snapshot.frontier.queues ageLane) (system.successors selected)
        targetQueued selectedTarget

/-- Until a target receives a selection receipt, no finite prefix can
increase its debt in a designated FIFO age lane. -/
theorem breadthFirst_ageDebt_run_nonincreasing
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (ageLane : Fin count)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live)
    (unselected :
      target ∉ (run system disciplines fuel snapshot).selections) :
    target ∈ (run system disciplines fuel snapshot).frontier.live ∧
      QueueDiscipline.ageDebt
          ((run system disciplines fuel snapshot).frontier.queues ageLane)
          target ≤
        QueueDiscipline.ageDebt
          (snapshot.frontier.queues ageLane) target := by
  induction fuel with
  | zero => exact ⟨live, Nat.le_refl _⟩
  | succ fuel inductionHypothesis =>
      let previous := run system disciplines fuel snapshot
      have previousPrefix : previous.selections.IsPrefix
          (tick system disciplines previous).selections :=
        selections_prefix_tick system disciplines previous
      have unselectedPrevious : target ∉ previous.selections := by
        intro selectedPrevious
        exact unselected
          (List.IsPrefix.mem selectedPrevious previousPrefix)
      obtain ⟨targetLive, previousDebt⟩ :=
        inductionHypothesis unselectedPrevious
      rcases breadthFirst_other_turn_progress system disciplines previous
          ageLane ageDiscipline targetLive with
        targetReceipt | ⟨targetLiveNext, nextDebt⟩
      · exfalso
        apply unselected
        simp only [run]
        rw [targetReceipt]
        simp
      · exact ⟨targetLiveNext, nextDebt.trans previousDebt⟩

/-- One finite round-robin cycle to a FIFO age lane either selects a live
target or strictly decreases its finite predecessor debt. -/
theorem breadthFirst_cycle_progress [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (ageLane : Fin count)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ fuel,
      target ∈ (run system disciplines fuel snapshot).selections ∨
        (target ∈ (run system disciplines fuel snapshot).frontier.live ∧
          QueueDiscipline.ageDebt
              ((run system disciplines fuel snapshot).frontier.queues ageLane)
              target <
            QueueDiscipline.ageDebt
              (snapshot.frontier.queues ageLane) target) := by
  obtain ⟨toAgeFuel, selected | ⟨targetLive, unselected, atAgeLane⟩⟩ :=
    reaches_lane_or_selects system disciplines snapshot ageLane live
  · exact ⟨toAgeFuel, Or.inl selected⟩
  · let atAge := run system disciplines toAgeFuel snapshot
    obtain ⟨_, debtBefore⟩ :=
      breadthFirst_ageDebt_run_nonincreasing system disciplines ageLane
        ageDiscipline toAgeFuel snapshot live unselected
    rcases breadthFirst_turn_progress system disciplines atAge ageLane
        atAgeLane ageDiscipline targetLive with
      targetReceipt | ⟨targetLiveNext, debtStep⟩
    · refine ⟨toAgeFuel + 1, Or.inl ?_⟩
      simp only [run]
      rw [targetReceipt]
      simp
    · refine ⟨toAgeFuel + 1, Or.inr ⟨?_, ?_⟩⟩
      · simpa only [run] using targetLiveNext
      · simp only [run]
        dsimp [atAge] at debtStep
        omega

/-- From an arbitrary resumable snapshot, any live occurrence remains covered
by the cumulative selection history under a finite round-robin clock with a
FIFO age lane. -/
theorem roundRobin_with_breadthFirst_fair_from_snapshot
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (ageLane : Fin count)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    (snapshot : PortfolioSnapshot Node Answer count)
    {target : Node} (live : target ∈ snapshot.frontier.live) :
    ∃ fuel, target ∈ (run system disciplines fuel snapshot).selections := by
  induction debtEq : QueueDiscipline.ageDebt
      (snapshot.frontier.queues ageLane) target using
      Nat.strong_induction_on generalizing snapshot with
  | h debtEq inductionHypothesis =>
      obtain ⟨fuel, selected | ⟨targetLive, debtDecreases⟩⟩ :=
        breadthFirst_cycle_progress system disciplines ageLane ageDiscipline
          snapshot live
      · exact ⟨fuel, selected⟩
      · let next := run system disciplines fuel snapshot
        obtain ⟨extraFuel, selectedLater⟩ := inductionHypothesis _
          (by simpa only [debtEq] using debtDecreases)
          next targetLive rfl
        refine ⟨fuel + extraFuel, ?_⟩
        rw [run_add]
        exact selectedLater

/-- Any independent scorer portfolio containing a FIFO age lane is fair from
its initial frontier.  Other lanes may use DFS, KBO, valuations, or learned
complete permutations; they cannot starve work protected by the age lane. -/
theorem roundRobin_with_breadthFirst_fair
    [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node)
    (ageLane start : Fin count)
    (ageDiscipline : disciplines ageLane = QueueDiscipline.breadthFirst)
    (roots : List Node) {target : Node} (root : target ∈ roots) :
    ∃ fuel,
      target ∈ (run system disciplines fuel
        (initial disciplines roots start)).selections := by
  apply roundRobin_with_breadthFirst_fair_from_snapshot
    system disciplines ageLane ageDiscipline
  simpa [initial, PortfolioFrontier.initial] using root

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

/-- Selection receipts expose the exact occurrence order independently of
whether either occurrence emitted an answer. -/
theorem independent_depth_breadth_selection_receipts :
    (PortfolioSnapshot.run BranchingTemporal.Starvation.system
      depthBreadthDisciplines 2
      depthBreadthPortfolioInitial).selections =
        [BranchingTemporal.Starvation.Node.loop,
          BranchingTemporal.Starvation.Node.answer] := by
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
#print axioms nextIndex_reaches
#print axioms QueueDiscipline.ageDebt_erase_le
#print axioms QueueDiscipline.breadthFirst_ageDebt_nonincreasing
#print axioms QueueDiscipline.breadthFirst_ageDebt_head_step
#print axioms QueueDiscipline.depthFirst_can_increase_ageDebt
#print axioms roundRobin_run_sound
#print axioms PortfolioFrontier.selected_mem
#print axioms PortfolioSnapshot.events_prefix_tick
#print axioms PortfolioSnapshot.selections_prefix_tick
#print axioms PortfolioSnapshot.selections_prefix_run
#print axioms PortfolioSnapshot.selected_of_live
#print axioms PortfolioSnapshot.selection_receipt_tick
#print axioms PortfolioSnapshot.live_or_selected_after_tick
#print axioms PortfolioSnapshot.live_or_selected_after_run
#print axioms PortfolioSnapshot.cursor_run_of_live_unselected
#print axioms PortfolioSnapshot.reaches_lane_or_selects
#print axioms PortfolioSnapshot.breadthFirst_turn_progress
#print axioms PortfolioSnapshot.breadthFirst_other_turn_progress
#print axioms PortfolioSnapshot.breadthFirst_ageDebt_run_nonincreasing
#print axioms PortfolioSnapshot.breadthFirst_cycle_progress
#print axioms PortfolioSnapshot.roundRobin_with_breadthFirst_fair_from_snapshot
#print axioms PortfolioSnapshot.roundRobin_with_breadthFirst_fair
#print axioms PortfolioSnapshot.account_tick
#print axioms PortfolioSnapshot.completed_run_denotation
#print axioms Canaries.counted_projection_forgets_weight
#print axioms Canaries.answerWeight_forgets_occurrence
#print axioms Canaries.independent_queues_diverge_after_depth_step
#print axioms Canaries.no_single_list_represents_independent_queues
#print axioms Canaries.independent_depth_breadth_reaches_answer
#print axioms Canaries.independent_depth_breadth_selection_receipts
#print axioms Canaries.depth_breadth_portfolio_reaches_answer
#print axioms Canaries.depth_first_still_starves

end Mettapedia.GSLT.Core.WeightedOccurrenceControl
