import Mettapedia.GSLT.Core.AgeProtectedSchedule
import Mettapedia.GSLT.Core.DemandExecution

/-!
# Independent queue views inside a resumable controller

The controller retains the existing portfolio's independent queues and lane
cursor.  Its operational projection is proved step by step.  In particular,
priority sorting never rewrites the age queue, and demand resumption retains
the whole portfolio rather than reconstructing age from the latest sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.PortfolioController

open BranchingTemporal WeightedOccurrenceControl
open InferenceControl (Controller)

variable {Node Answer : Type*} {count : Nat} [NeZero count] [DecidableEq Node]

abbrev Memory (Node : Type*) (count : Nat) := PortfolioFrontier Node count × Fin count

/-- Move one authorized occurrence to the front.  The fallback makes the
scheduler lawful even on a snapshot unrelated to its retained queue views. -/
def bringFront (choice : Option Node) (frontier : List Node) : List Node :=
  match choice with
  | none => frontier
  | some node => if node ∈ frontier then node :: frontier.erase node else frontier

theorem bringFront_perm (choice : Option Node) (frontier : List Node) :
    (bringFront choice frontier).Perm frontier := by
  cases choice with
  | none => exact .refl _
  | some node =>
      by_cases member : node ∈ frontier
      · simpa [bringFront, member] using (List.perm_cons_erase member).symm
      · simp [bringFront, member]

def selectScheduler (memory : Memory Node count) : Scheduler Node where
  reorder := bringFront (memory.1.selected memory.2)
  reorder_complete := bringFront_perm _
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := .refl _

def controller (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) : Controller Node Answer (Memory Node count) where
  initialMemory := ⟨PortfolioFrontier.initial disciplines roots, start⟩
  scheduler := selectScheduler
  advance memory node _ generated :=
    ⟨memory.1.advance disciplines node generated, nextIndex memory.2⟩

def project (snapshot : PortfolioSnapshot Node Answer count) :
    InferenceControl.Snapshot Node Answer (Memory Node count) :=
  ⟨⟨snapshot.events, snapshot.frontier.live⟩, ⟨snapshot.frontier, snapshot.cursor⟩⟩

omit [NeZero count] [DecidableEq Node] in
theorem live_empty_of_no_selection (frontier : PortfolioFrontier Node count)
    (lane : Fin count) (empty : frontier.selected lane = none) : frontier.live = [] := by
  have queueEmpty : frontier.queues lane = [] := by
    simpa [PortfolioFrontier.selected] using empty
  have perm := frontier.queue_complete lane
  rw [queueEmpty] at perm
  exact (List.Perm.nil_eq perm).symm

theorem selection_projects (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) (snapshot : PortfolioSnapshot Node Answer count) :
    InferenceControl.Snapshot.selected (controller disciplines roots start) (project snapshot) =
      snapshot.frontier.selected snapshot.cursor := by
  cases selected : snapshot.frontier.selected snapshot.cursor with
  | none =>
      have empty := live_empty_of_no_selection snapshot.frontier snapshot.cursor selected
      simp [InferenceControl.Snapshot.selected, BranchingTemporal.selected,
        controller, selectScheduler, project, bringFront, selected, empty]
  | some node =>
      have member := PortfolioFrontier.selected_mem selected
      simp [InferenceControl.Snapshot.selected, BranchingTemporal.selected,
        controller, selectScheduler, project, bringFront, selected, member]

/-- Both machines update the actual live store, every queue view, events and
the retained lane cursor in the same way. -/
theorem tick_projects (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node) (roots : List Node) (start : Fin count)
    (snapshot : PortfolioSnapshot Node Answer count) :
    InferenceControl.Snapshot.tick system (controller disciplines roots start) (project snapshot) =
      project (PortfolioSnapshot.tick system disciplines snapshot) := by
  cases selected : snapshot.frontier.selected snapshot.cursor with
  | none =>
      have empty := live_empty_of_no_selection snapshot.frontier snapshot.cursor selected
      simp [InferenceControl.Snapshot.tick, BranchingTemporal.tick, PortfolioSnapshot.tick,
        controller, selectScheduler, project, bringFront, selected, empty]
  | some node =>
      have member := PortfolioFrontier.selected_mem selected
      cases emitted : system.emit node <;>
        simp [InferenceControl.Snapshot.tick, BranchingTemporal.tick, PortfolioSnapshot.tick,
          controller, selectScheduler, project, bringFront, selected, member,
          PortfolioFrontier.advance, emitted] <;> rfl

theorem run_projects (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node) (roots : List Node) (start : Fin count)
    (fuel : Nat) (snapshot : PortfolioSnapshot Node Answer count) :
    InferenceControl.Snapshot.run system (controller disciplines roots start) fuel
        (project snapshot) =
      project (PortfolioSnapshot.run system disciplines fuel snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [InferenceControl.Snapshot.run, PortfolioSnapshot.run, ih]
      exact tick_projects system disciplines roots start _

@[simp] theorem initial_projects (disciplines : Fin count → QueueDiscipline Node)
    (roots : List Node) (start : Fin count) :
    project (PortfolioSnapshot.initial disciplines roots start :
      PortfolioSnapshot Node Answer count) =
      InferenceControl.Snapshot.initial (controller disciplines roots start) roots := rfl

/-- A recorded selection comes from an actual earlier queue selection. -/
theorem selection_receipt_has_step (system : BranchingSystem Node Answer)
    (disciplines : Fin count → QueueDiscipline Node) (roots : List Node) (start : Fin count)
    (fuel : Nat) {node : Node}
    (recorded : node ∈ (PortfolioSnapshot.run system disciplines fuel
      (PortfolioSnapshot.initial disciplines roots start)).selections) :
    ∃ earlier < fuel, (PortfolioSnapshot.run system disciplines earlier
      (PortfolioSnapshot.initial disciplines roots start)).frontier.selected
        (PortfolioSnapshot.run system disciplines earlier
          (PortfolioSnapshot.initial disciplines roots start)).cursor = some node := by
  induction fuel with
  | zero => simp [PortfolioSnapshot.run, PortfolioSnapshot.initial] at recorded
  | succ fuel ih =>
      let snapshot := PortfolioSnapshot.run system disciplines fuel
        (PortfolioSnapshot.initial disciplines roots start)
      change node ∈ (PortfolioSnapshot.tick system disciplines snapshot).selections at recorded
      cases selected : snapshot.frontier.selected snapshot.cursor with
      | none =>
          have prior : node ∈ snapshot.selections := by
            simpa [PortfolioSnapshot.tick, selected] using recorded
          obtain ⟨earlier, before, selection⟩ := ih prior
          exact ⟨earlier, Nat.lt_succ_of_lt before, selection⟩
      | some picked =>
          have casesRecord : node ∈ snapshot.selections ∨ node = picked := by
            simpa [PortfolioSnapshot.tick, selected] using recorded
          rcases casesRecord with prior | same
          · obtain ⟨earlier, before, selection⟩ := ih prior
            exact ⟨earlier, Nat.lt_succ_of_lt before, selection⟩
          · exact ⟨fuel, Nat.lt_succ_self fuel, same ▸ selected⟩

/-- Protected queue fairness now satisfies the demand executor's exact
controller contract, for all occurrences that become live later as well as
the initial roots. -/
theorem protected_fair (schedule : AgeProtectedSchedule.Spec Node count)
    (system : BranchingSystem Node Answer) (roots : List Node) (start : Fin count) :
    InferenceControl.Snapshot.FairFrom system
      (controller schedule.disciplines roots start) roots := by
  intro node ⟨fuel, live⟩
  have projected := run_projects system schedule.disciplines roots start fuel
    (PortfolioSnapshot.initial schedule.disciplines roots start)
  rw [initial_projects] at projected
  rw [projected] at live
  obtain ⟨later, recorded⟩ := schedule.eventually_selects_live system _ live
  rw [← PortfolioSnapshot.run_add] at recorded
  obtain ⟨earlier, _, selection⟩ := selection_receipt_has_step system
    schedule.disciplines roots start (fuel + later) recorded
  refine ⟨earlier, ?_⟩
  rw [← initial_projects, run_projects, selection_projects]
  exact selection

/-- Count demand inherits finite-witness liveness without materializing a
complete answer bag or changing either queue's ordering discipline. -/
theorem protected_anyK (schedule : AgeProtectedSchedule.Spec Node count)
    (system : BranchingSystem Node Answer) (roots : List Node) (start : Fin count)
    (requested : Nat) (witnesses : List (Emission Node Answer))
    (distinct : witnesses.Nodup) (many : requested ≤ witnesses.length)
    (valid : ∀ event ∈ witnesses, EventValid system roots event) :
    ∃ fuel, DemandExecution.satisfied (DemandExecution.atLeast requested)
      (DemandExecution.run system (controller schedule.disciplines roots start)
        (DemandExecution.atLeast requested) fuel
        (InferenceControl.Snapshot.initial (controller schedule.disciplines roots start) roots))
        = true :=
  DemandExecution.fair_atLeast_liveness system _ roots
    (protected_fair schedule system roots start) requested witnesses distinct many valid

end Mettapedia.GSLT.Core.PortfolioController
