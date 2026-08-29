import Mettapedia.GSLT.Core.AgePrioritySchedule

/-!
# Given-clause control over an occurrence-preserving frontier

The given-clause loop separates two semantic collections:

* `passive` contains authorized work which may still be selected;
* `processed` contains the exact sequence of selected given occurrences.

One step selects a given occurrence from the passive store, observes it in the
current processed context, activates it, and generates new passive occurrences
against that context.  Selection order is supplied independently by complete
queue disciplines.  Consequently the loop does not build in DFS, FIFO,
fairness, a scoring algebra, or a physical continuation representation.

The processed context is load-bearing.  An embedding theorem shows that an
ordinary history-independent branching system is a special case, while a
negative canary proves that processed-sensitive generation cannot in general
be flattened back to node-local successors.
-/

namespace Mettapedia.GSLT.Core.GivenClauseLoop

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.GSLT.Core.AgePrioritySchedule

universe uNode uAnswer

/-- The transition authority of a given-clause loop.  The selected occurrence
and the already processed occurrences jointly determine observations and new
authorized work.  A scheduler never calls either operation itself. -/
structure System (Node : Type uNode) (Answer : Type uAnswer) where
  observe : Node -> List Node -> Option Answer
  generate : Node -> List Node -> List Node

/-- Exact operational state of a given-clause loop.  The passive occurrence
store is shared by every queue view; `processed` is semantic activation state,
not a scheduler-private cache. -/
structure Snapshot (Node : Type uNode) (Answer : Type uAnswer) (count : Nat)
    where
  events : List (Emission Node Answer)
  selections : List Node
  processed : List Node
  passive : PortfolioFrontier Node count
  cursor : Fin count

namespace Snapshot

variable {Node : Type uNode} {Answer : Type uAnswer} {count : Nat}

/-- Initialize one passive occurrence store and every complete selection view
from the same roots. -/
def initial [NeZero count]
    (disciplines : Fin count -> QueueDiscipline Node)
    (roots : List Node) (start : Fin count) : Snapshot Node Answer count :=
  { events := []
    selections := []
    processed := []
    passive := PortfolioFrontier.initial disciplines roots
    cursor := start }

private def eventFor (node : Node) : Option Answer -> List (Emission Node Answer)
  | none => []
  | some answer => [⟨node, answer⟩]

/-- One genuine given-clause step: select from `U`, observe and generate
against `P`, move the given occurrence to `P`, and integrate all generated
occurrences back into the single passive store. -/
def tick [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) : Snapshot Node Answer count :=
  match snapshot.passive.selected snapshot.cursor with
  | none => snapshot
  | some given =>
      { events := snapshot.events ++
          eventFor given (system.observe given snapshot.processed)
        selections := snapshot.selections ++ [given]
        processed := snapshot.processed ++ [given]
        passive := snapshot.passive.advance disciplines given
          (system.generate given snapshot.processed)
        cursor := nextIndex snapshot.cursor }

def run [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node) :
    Nat -> Snapshot Node Answer count -> Snapshot Node Answer count
  | 0, snapshot => snapshot
  | fuel + 1, snapshot =>
      tick system disciplines (run system disciplines fuel snapshot)

theorem run_add [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (left right : Nat) (snapshot : Snapshot Node Answer count) :
    run system disciplines (left + right) snapshot =
      run system disciplines right (run system disciplines left snapshot) := by
  induction right with
  | zero => rw [Nat.add_zero]; rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ]
      simp only [run]
      rw [inductionHypothesis]

/-- A mechanism-neutral fairness obligation for a concrete discipline family:
every occurrence which is live in an arbitrary resumable state receives a
finite selection receipt.  GCL itself does not require this property. -/
def PersistentSelectionDuty [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node) : Prop :=
  ∀ (snapshot : Snapshot Node Answer count) (target : Node),
    target ∈ snapshot.passive.live ->
      ∃ fuel,
        target ∈ (run system disciplines fuel snapshot).selections

/-- Strict FIFO is the first concrete selection-duty witness.  Other
mechanisms may discharge the same property without sharing its queue layout. -/
def breadthOnly : Fin 1 -> QueueDiscipline Node :=
  fun _ => QueueDiscipline.breadthFirst

/-- FIFO over the passive store satisfies the persistent-selection duty even
when generation depends on the processed set.  The proof uses only finite
predecessor debt; it does not inspect or restrict generated occurrences. -/
theorem breadthOnly_discharges_duty [DecidableEq Node]
    (system : System Node Answer) :
    PersistentSelectionDuty system (breadthOnly (Node := Node)) := by
  intro snapshot target live
  by_cases alreadySelected : target ∈ snapshot.selections
  · exact ⟨0, alreadySelected⟩
  have targetQueued : target ∈ snapshot.passive.queues 0 :=
    (snapshot.passive.queue_complete 0).mem_iff.mpr live
  induction debtEq : QueueDiscipline.ageDebt
      (snapshot.passive.queues 0) target using
      Nat.strong_induction_on generalizing snapshot with
  | h debtEq inductionHypothesis =>
      cases queueEq : snapshot.passive.queues 0 with
      | nil => simp [queueEq] at targetQueued
      | cons given pending =>
          have selection : snapshot.passive.selected snapshot.cursor =
              some given := by
            have cursorZero : snapshot.cursor = 0 := Subsingleton.elim _ _
            simp [PortfolioFrontier.selected, cursorZero, queueEq]
          by_cases givenTarget : given = target
          · subst given
            refine ⟨1, ?_⟩
            simp [run, tick, selection]
          · have targetPending : target ∈ pending := by
              rw [queueEq] at targetQueued
              simp only [List.mem_cons] at targetQueued
              exact targetQueued.resolve_left (Ne.symm givenTarget)
            let next := tick system (breadthOnly (Node := Node)) snapshot
            have targetRemains :
                target ∈ snapshot.passive.live.erase given :=
              (List.mem_erase_of_ne (Ne.symm givenTarget)).2 live
            have nextLive : target ∈ next.passive.live := by
              simp [next, tick, selection, PortfolioFrontier.advance,
                targetRemains]
            have nextQueued : target ∈ next.passive.queues 0 :=
              (next.passive.queue_complete 0).mem_iff.mpr nextLive
            have debtStep :
                QueueDiscipline.ageDebt (next.passive.queues 0) target + 1 =
                  QueueDiscipline.ageDebt
                    (snapshot.passive.queues 0) target := by
              simp only [next, tick, selection, PortfolioFrontier.advance]
              rw [queueEq]
              simp only [breadthOnly, List.erase_cons_head,
                QueueDiscipline.breadthFirst]
              exact QueueDiscipline.breadthFirst_ageDebt_head_step
                given target pending
                  (system.generate given snapshot.processed)
                  givenTarget targetPending
            have decreases :
                QueueDiscipline.ageDebt (next.passive.queues 0) target <
                  QueueDiscipline.ageDebt
                    (snapshot.passive.queues 0) target := by
              omega
            have notSelectedNext : target ∉ next.selections := by
              have targetGiven : target ≠ given := Ne.symm givenTarget
              simp [next, tick, selection, alreadySelected, targetGiven]
            obtain ⟨extraFuel, selectedLater⟩ :=
              inductionHypothesis _
                (by simpa only [debtEq] using decreases)
                next nextLive notSelectedNext nextQueued rfl
            refine ⟨1 + extraFuel, ?_⟩
            rw [run_add]
            simpa [run, next] using selectedLater

/-- A successful step records the selected given occurrence in both the exact
selection receipt and the processed sequence. -/
theorem activation_receipt [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) {given : Node}
    (selection : snapshot.passive.selected snapshot.cursor = some given) :
    (tick system disciplines snapshot).selections =
        snapshot.selections ++ [given] /\
      (tick system disciplines snapshot).processed =
        snapshot.processed ++ [given] := by
  simp [tick, selection]

/-- Generated work enters the shared passive occurrence store, independently
of which complete queue discipline selected the given occurrence. -/
theorem generated_mem_passive [NeZero count] [DecidableEq Node]
    (system : System Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) {given generated : Node}
    (selection : snapshot.passive.selected snapshot.cursor = some given)
    (member : generated ∈ system.generate given snapshot.processed) :
    generated ∈ (tick system disciplines snapshot).passive.live := by
  simp only [tick, selection, PortfolioFrontier.advance]
  exact List.mem_append_right _ member

/-- Empty passive work is exactly the operational saturation boundary.  The
definition deliberately says nothing about whether the chosen observation
licenses treating this closure as a complete semantic result. -/
def Saturated (snapshot : Snapshot Node Answer count) : Prop :=
  snapshot.passive.live = []

end Snapshot

/-! ## History-independent systems embed exactly -/

namespace System

variable {Node : Type uNode} {Answer : Type uAnswer}

/-- Ordinary node-local branching is the processed-insensitive fragment of
the given-clause transition authority. -/
def ofBranchingSystem (system : BranchingSystem Node Answer) :
    System Node Answer where
  observe node _ := system.emit node
  generate node _ := system.successors node

end System

/-- Forget only the processed activation sequence.  Events, exact selection
receipts, the shared passive store, and the controller cursor remain intact. -/
def eraseProcessed
    (snapshot : Snapshot Node Answer count) :
    PortfolioSnapshot Node Answer count where
  events := snapshot.events
  selections := snapshot.selections
  frontier := snapshot.passive
  cursor := snapshot.cursor

@[simp] theorem eraseProcessed_initial [NeZero count]
    (disciplines : Fin count -> QueueDiscipline Node)
    (roots : List Node) (start : Fin count) :
    eraseProcessed
        (Snapshot.initial (Answer := Answer) disciplines roots start) =
      PortfolioSnapshot.initial disciplines roots start :=
  rfl

/-- One history-independent given-clause step is exactly the existing shared-
frontier portfolio step after forgetting the processed sequence. -/
theorem eraseProcessed_tick [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (snapshot : Snapshot Node Answer count) :
    eraseProcessed
        (Snapshot.tick (System.ofBranchingSystem system) disciplines snapshot) =
      PortfolioSnapshot.tick system disciplines (eraseProcessed snapshot) := by
  cases selection : snapshot.passive.selected snapshot.cursor with
  | none => simp [Snapshot.tick, PortfolioSnapshot.tick, eraseProcessed,
      selection]
  | some given =>
      cases emitted : system.emit given <;>
        simp [Snapshot.tick, PortfolioSnapshot.tick, eraseProcessed,
          selection, System.ofBranchingSystem, Snapshot.eventFor, emitted] <;>
        rfl

/-- Every finite history-independent run commutes exactly with erasing the
processed sequence.  This is an equality of event order, occurrence receipts,
passive store, every queue view, and cursor—not only a completed bag theorem. -/
theorem eraseProcessed_run [NeZero count] [DecidableEq Node]
    (system : BranchingSystem Node Answer)
    (disciplines : Fin count -> QueueDiscipline Node)
    (fuel : Nat) (snapshot : Snapshot Node Answer count) :
    eraseProcessed
        (Snapshot.run (System.ofBranchingSystem system) disciplines fuel snapshot) =
      PortfolioSnapshot.run system disciplines fuel
        (eraseProcessed snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [Snapshot.run, PortfolioSnapshot.run]
      rw [eraseProcessed_tick, inductionHypothesis]

/-! ## Age-priority schedules are inhabitants, not the core -/

/-- Execute a given-clause loop under an age-priority schedule.  This
definition does not make priority or age protection part of `System`; it
merely supplies one lawful family of selection disciplines. -/
def runAgePriority [NeZero count] [DecidableEq Node]
    (schedule : AgePrioritySchedule.Spec Node count)
    (system : System Node Answer) (fuel : Nat)
    (snapshot : Snapshot Node Answer count) : Snapshot Node Answer count :=
  Snapshot.run system schedule.schedule.disciplines fuel snapshot

/-! ## Positive and negative canaries -/

namespace Canaries

/-- Generation genuinely consults the processed set: the same selected clause
creates different passive work before and after another occurrence is active. -/
def processedSensitive : System Nat Unit where
  observe _ _ := none
  generate node processed :=
    if node = 0 then
      if processed = [] then [1] else [2]
    else []

theorem processed_context_changes_generation :
    processedSensitive.generate 0 [] = [1] /\
      processedSensitive.generate 0 [9] = [2] := by
  decide

/-- Negative boundary: no node-local branching system can flatten this
processed-sensitive transition authority for every active context. -/
theorem processed_sensitive_not_node_local :
    ¬ ∃ system : BranchingSystem Nat Unit,
        ∀ node processed,
          system.successors node =
            processedSensitive.generate node processed := by
  rintro ⟨system, agrees⟩
  have emptyAgreement := agrees 0 []
  have activeAgreement := agrees 0 [9]
  have impossible : ([1] : List Nat) = [2] := by
    calc
      [1] = system.successors 0 := by
        simpa [processedSensitive] using emptyAgreement.symm
      _ = [2] := by
        simpa [processedSensitive] using activeAgreement
  exact (by decide : ([1] : List Nat) ≠ [2]) impossible

def initialProcessedSensitive : Snapshot Nat Unit 1 :=
  Snapshot.initial Snapshot.breadthOnly [0, 9] 0

/-- Concrete `U | P` canary: the first given clause activates, generates one
new passive occurrence, and leaves the older sibling ahead of it. -/
theorem first_given_clause_step :
    let next := Snapshot.run processedSensitive Snapshot.breadthOnly 1
      initialProcessedSensitive
    next.processed = [0] /\
      next.selections = [0] /\
      next.passive.live = [9, 1] := by
  decide

/-- The second step activates the pre-existing sibling; generated work remains
passive.  Thus processed and passive are observably distinct coordinates. -/
theorem second_given_clause_step :
    let next := Snapshot.run processedSensitive Snapshot.breadthOnly 2
      initialProcessedSensitive
    next.processed = [0, 9] /\
      next.selections = [0, 9] /\
      next.passive.live = [1] := by
  decide

end Canaries

#print axioms Snapshot.activation_receipt
#print axioms Snapshot.generated_mem_passive
#print axioms Snapshot.breadthOnly_discharges_duty
#print axioms eraseProcessed_tick
#print axioms eraseProcessed_run
#print axioms Canaries.processed_context_changes_generation
#print axioms Canaries.processed_sensitive_not_node_local
#print axioms Canaries.first_given_clause_step
#print axioms Canaries.second_given_clause_step

end Mettapedia.GSLT.Core.GivenClauseLoop
