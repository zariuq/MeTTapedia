import Mettapedia.Machines.ObserverLicence.HEPortfolio

/-!
# Success erasure transfers deepening liveness without erasing error replies

The projection removes error values only from the mathematical success-search
view. The real strategy keeps its original error journal for uncut fallback.
Expansion and readiness commute with the projection, including dead error
leaves. The existing deepening existence theorem therefore applies to the HE
control whenever a depth settles its preferred demand.

The work unit is a control expansion or depth change. Native maintenance of
the preferred-count metadata is a separate cost/refinement obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open BoundedSearchPortfolio (Cursor Status Iteration)
open RuntimePlumbing

universe u
variable {S : Type u} {Reply : Type}

def successSpace (space : Space S Reply) (isError : Reply → Bool) : Space S Reply where
  expand state :=
    match space.expand state with
    | .answer value => if isError value then .branch [] else .answer value
    | .branch children => .branch children

def successCursor (isError : Reply → Bool) (cursor : Cursor S Reply) : Cursor S Reply :=
  {cursor with reversed := cursor.reversed.filter (fun value => !isError value)}

def successIteration (isError : Reply → Bool) (iteration : Iteration S Reply) : Iteration S Reply :=
  {iteration with cursor := successCursor isError iteration.cursor}

theorem projected_status (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply) :
    BoundedSearchPortfolio.status demand (successCursor isError cursor) = status isError demand cursor := by
  simp [BoundedSearchPortfolio.status, status, successCursor, Cursor.answers,
    SuccessPriority.successes, List.filter_reverse]
  split_ifs <;> simp_all

theorem projected_expansion (space : Space S Reply) (isError : Reply → Bool) (cursor : Cursor S Reply) :
    successCursor isError (BoundedSearchPortfolio.expandOne space cursor) =
      BoundedSearchPortfolio.expandOne (successSpace space isError) (successCursor isError cursor) := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨state, depth⟩
      cases expansion : space.expand state with
      | answer value =>
          cases flag : isError value <;> cases depth <;>
            simp [successCursor, BoundedSearchPortfolio.expandOne, successSpace, expansion, flag,
              BoundedSearchPortfolio.children]
      | branch children =>
          cases depth <;>
            simp [successCursor, BoundedSearchPortfolio.expandOne, successSpace, expansion]

theorem projected_bounded (space : Space S Reply) (isError : Reply → Bool) (depth : Nat) (root : S) :
    bounded (successSpace space isError) depth root =
      (SuccessPriority.successes isError (bounded space depth root).1, (bounded space depth root).2) := by
  induction depth generalizing root with
  | zero =>
      cases expansion : space.expand root with
      | answer value => cases flag : isError value <;> simp [bounded, successSpace, expansion, flag, SuccessPriority.successes]
      | branch children => simp [bounded, successSpace, expansion, SuccessPriority.successes]
  | succ depth ih =>
      cases expansion : space.expand root with
      | answer value => cases flag : isError value <;> simp [bounded, successSpace, expansion, flag, SuccessPriority.successes]
      | branch children =>
          have childrenProjected : children.map (bounded (successSpace space isError) depth) =
              children.map (fun child => (SuccessPriority.successes isError (bounded space depth child).1,
                (bounded space depth child).2)) := by
            apply List.map_congr_left
            intro child _
            exact ih child
          have move : (successSpace space isError).expand root = .branch children := by
            simp [successSpace, expansion]
          rw [bounded_succ_branch _ move, bounded_succ_branch _ expansion, childrenProjected]
          simp [List.flatMap_map, List.filter_flatMap, List.any_map, SuccessPriority.successes, Function.comp_def]

def deepenStep (space : Space S Reply) (isError : Reply → Bool) (root : S) (demand : Nat)
    (iteration : Iteration S Reply) : Iteration S Reply :=
  match status isError demand iteration.cursor with
  | .cutoff => BoundedSearchPortfolio.nextIteration root iteration
  | _ => {iteration with cursor := BoundedSearchPortfolio.expandOne space iteration.cursor}

theorem projected_deepening_step (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand : Nat) (iteration : Iteration S Reply) :
    successIteration isError (deepenStep space isError root demand iteration) =
      PortfolioReach.deepenOne (successSpace space isError) root demand (successIteration isError iteration) := by
  unfold deepenStep PortfolioReach.deepenOne
  rw [show (successIteration isError iteration).cursor = successCursor isError iteration.cursor from rfl,
    projected_status]
  cases outcome : status isError demand iteration.cursor with
  | cutoff => rfl
  | paused | full | exhausted =>
      exact congrArg (fun cursor : Cursor S Reply => ({iteration with cursor := cursor} : Iteration S Reply))
        (projected_expansion space isError iteration.cursor)

theorem projected_deepening_run (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand steps : Nat) (iteration : Iteration S Reply) :
    successIteration isError ((deepenStep space isError root demand)^[steps] iteration) =
      (PortfolioReach.deepenOne (successSpace space isError) root demand)^[steps]
        (successIteration isError iteration) := by
  induction steps generalizing iteration with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, ih, projected_deepening_step, Function.iterate_succ_apply]

theorem deepening_eventually_ready (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand target : Nat) (settled : Decides space isError demand target root) :
    ∃ units, units ≤ idWork (successSpace space isError) root 0 target + target ∧
      BoundedSearchPortfolio.ready (status isError demand
        (((deepenStep space isError root demand)^[units]
          (BoundedSearchPortfolio.beginIteration root 0)).cursor)) = true := by
  have settles : PortfolioReach.Decides (successSpace space isError) root demand target := by
    unfold PortfolioReach.Decides
    rw [projected_bounded]
    exact settled
  obtain ⟨units, bounded, ready⟩ := PortfolioReach.deepen_need (successSpace space isError) root demand target settles
  refine ⟨units, bounded, ?_⟩
  have moved := projected_deepening_run space isError root demand units (BoundedSearchPortfolio.beginIteration root 0)
  have start : successIteration isError (BoundedSearchPortfolio.beginIteration root 0) =
      BoundedSearchPortfolio.beginIteration root 0 := rfl
  rw [start] at moved
  change BoundedSearchPortfolio.ready (BoundedSearchPortfolio.status demand
    ((PortfolioReach.deepenOne (successSpace space isError) root demand)^[units]
      (BoundedSearchPortfolio.beginIteration root 0)).cursor) = true at ready
  rw [← moved] at ready
  change BoundedSearchPortfolio.ready (BoundedSearchPortfolio.status demand (successCursor isError _)) = true at ready
  rwa [projected_status] at ready

end Mettapedia.Machines.ObserverLicence.HEWitness
