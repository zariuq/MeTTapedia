import Mettapedia.Machines.ObserverLicence.HEWitnessRuns
import Mettapedia.Machines.PortfolioReach.Embedding

/-!
# Distinct DFS and deepening strategies for a success-priority boundary

The DFS state is an unbounded pending-state stack; the deepening state has
depth-tagged tasks and discards cut-off rounds. They share the existing
single-publication coordinator through a tagged control type, not by running
the same bounded algorithm twice. Both retain error values privately until
success or uncut exhaustion decides their boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open BoundedSearchPortfolio (Cursor Status Iteration)
open RuntimePlumbing

universe u w
variable {S : Type u} {Reply : Type}

def walkStatus (isError : Reply → Bool) (demand : Nat) (walk : PortfolioReach.Walk S Reply) : Status :=
  if demand ≤ (SuccessPriority.successes isError walk.reversed.reverse).length then .full
  else if walk.stack.isEmpty then .exhausted else .paused

def WalkValid (space : Space S Reply) (root : S) (walk : PortfolioReach.Walk S Reply) : Prop :=
  ∀ floor, ∃ iteration : Iteration S Reply,
    Valid space root iteration ∧ PortfolioReach.Shadows floor walk iteration.cursor

theorem walk_begin_valid (space : Space S Reply) (root : S) :
    WalkValid space root (⟨[root], []⟩ : PortfolioReach.Walk S Reply) := by
  intro floor
  exact ⟨BoundedSearchPortfolio.beginIteration root floor, begin_valid space root floor,
    rfl, rfl, rfl, by simp [BoundedSearchPortfolio.beginIteration, BoundedSearchPortfolio.start]⟩

theorem shadow_status {floor : Nat} {walk : PortfolioReach.Walk S Reply} {cursor : Cursor S Reply}
    (shadows : PortfolioReach.Shadows floor walk cursor) (isError : Reply → Bool) (demand : Nat) :
    status isError demand cursor = walkStatus isError demand walk := by
  obtain ⟨stack, reversed, uncut, _⟩ := shadows
  unfold status walkStatus
  rw [Cursor.answers, ← reversed, stack, uncut]
  cases cursor.frontier <;> simp

theorem walk_step_valid (space : Space S Reply) (root : S) (walk : PortfolioReach.Walk S Reply)
    (valid : WalkValid space root walk) : WalkValid space root (PortfolioReach.walkOne space walk) := by
  intro floor
  obtain ⟨iteration, validIteration, shadow⟩ := valid (floor + 1)
  refine ⟨{iteration with cursor := BoundedSearchPortfolio.expandOne space iteration.cursor}, ?_, shadow.step space⟩
  exact ⟨(BoundedSearchPortfolio.expandOne_answers space iteration.cursor).trans validIteration.1,
    (BoundedSearchPortfolio.expandOne_cut space iteration.cursor).trans validIteration.2⟩

theorem walk_ready_law (space : Space S Reply) (root : S) (isError : Reply → Bool)
    (demand : Nat) (walk : PortfolioReach.Walk S Reply) (valid : WalkValid space root walk)
    (ready : BoundedSearchPortfolio.ready (walkStatus isError demand walk) = true) :
    BatchMeaning space root isError demand
      ((SuccessPriority.select isError walk.reversed.reverse).take demand) := by
  obtain ⟨iteration, validIteration, shadow⟩ := valid 0
  have cursorReady : BoundedSearchPortfolio.ready (status isError demand iteration.cursor) = true := by
    rw [shadow_status shadow]
    exact ready
  have meaning := cursor_ready_meaning space isError demand iteration.depth root iteration.cursor
    validIteration.1 validIteration.2 cursorReady
  simpa only [batch, Cursor.answers, ← shadow.2.1] using meaning

inductive StrategyState (space : Space S Reply) (root : S) where
  | dfs (walk : {walk : PortfolioReach.Walk S Reply // WalkValid space root walk})
  | idd (iteration : {iteration : Iteration S Reply // Valid space root iteration})

def strategyEngine (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) : BoundedSearchPortfolio.Engine (StrategyState space root) Reply E where
  inspect
    | .dfs walk => walkStatus isError demand walk.val
    | .idd iteration => status isError demand iteration.val.cursor
  batch
    | .dfs walk => (SuccessPriority.select isError walk.val.reversed.reverse).take demand
    | .idd iteration => batch isError demand iteration.val.cursor
  progress
    | .dfs walk =>
        (.dfs ⟨PortfolioReach.walkOne space walk.val, walk_step_valid space root walk.val walk.property⟩, [])
    | .idd iteration =>
        (.idd ⟨{iteration.val with cursor := tick space isError demand iteration.val.cursor},
          tick_valid space isError root demand iteration.val iteration.property⟩, [])
  deepen
    | .dfs walk => (.dfs walk, [])
    | .idd iteration =>
        (.idd ⟨BoundedSearchPortfolio.nextIteration root iteration.val,
          begin_valid space root (iteration.val.depth + 1)⟩, [])

theorem dfs_never_requests_deepening (isError : Reply → Bool) (demand : Nat)
    (walk : PortfolioReach.Walk S Reply) : walkStatus isError demand walk ≠ .cutoff := by
  unfold walkStatus
  split <;> simp_all
  split <;> simp_all

theorem strategy_pure (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) : (strategyEngine space isError root demand E).Pure := by
  intro state
  cases state <;> exact ⟨rfl, rfl⟩

theorem strategy_ready_law (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) (state : StrategyState space root)
    (ready : BoundedSearchPortfolio.ready ((strategyEngine space isError root demand E).inspect state) = true) :
    BatchMeaning space root isError demand ((strategyEngine space isError root demand E).batch state) := by
  cases state with
  | dfs walk => exact walk_ready_law space root isError demand walk.val walk.property ready
  | idd iteration =>
      exact cursor_ready_meaning space isError demand iteration.val.depth root
        iteration.val.cursor iteration.property.1 iteration.property.2 ready

def initialPortfolio (space : Space S Reply) (root : S) (E : Type w) (budget : Nat) :
    BoundedSearchPortfolio.Portfolio (StrategyState space root) Reply E :=
  ⟨.dfs ⟨⟨[root], []⟩, walk_begin_valid space root⟩,
    .idd ⟨BoundedSearchPortfolio.beginIteration root 0, begin_valid space root 0⟩,
    budget, 0, [], none⟩

theorem mixed_portfolio_publication_law (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand : Nat) (E : Type w) (budget : Nat) (schedule : List BoundedSearchPortfolio.Origin) :
    ∀ origin answers,
      (BoundedSearchPortfolio.execute (strategyEngine space isError root demand E)
        (strategyEngine space isError root demand E) schedule
          (initialPortfolio space root E budget)).published = some (origin, answers) →
      BatchMeaning space root isError demand answers := by
  apply BoundedSearchPortfolio.execute_publication_law _ _ (BatchMeaning space root isError demand)
    (strategy_ready_law space isError root demand E) (strategy_ready_law space isError root demand E)
  intro origin answers impossible
  contradiction

namespace PortfolioControls

open Mettapedia.Machines.ObserverLicence.HEWitness.Controls (Sample isError fan)

theorem two_strategies_do_not_publish_the_provisional_error :
    (BoundedSearchPortfolio.execute (strategyEngine (fan [.error 3, .ok 7]) isError none 1 Nat)
      (strategyEngine (fan [.error 3, .ok 7]) isError none 1 Nat)
        [.left, .right, .left, .right, .left, .right, .left, .right]
        (initialPortfolio (fan [.error 3, .ok 7]) none Nat 20)).published = some (.left, [.ok 7]) := by decide

def looping : Space Nat Sample where
  expand
    | 0 => .branch [1, 2]
    | 1 => .branch [1]
    | 2 => .answer (.ok 7)
    | _ => .branch []

theorem deepening_wins_beside_an_infinite_dfs_branch :
    (BoundedSearchPortfolio.execute (strategyEngine looping isError 0 1 Nat)
      (strategyEngine looping isError 0 1 Nat)
        [.left, .right, .left, .right, .left, .right, .left, .right, .left, .right, .left, .right]
        (initialPortfolio looping 0 Nat 30)).published = some (.right, [.ok 7]) := by decide

end PortfolioControls

end Mettapedia.Machines.ObserverLicence.HEWitness
