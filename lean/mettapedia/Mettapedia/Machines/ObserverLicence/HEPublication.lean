import Mettapedia.Machines.ObserverLicence.HEProjection

/-!
# A budgeted coordinator execution really publishes a preferred batch

The deepening readiness witness is realized by an actual sequence of right
services in the single-publication coordinator. Earlier readiness shortens
the constructed schedule; ready publication spends no expansion unit. This
supplies execution existence alongside the arbitrary-schedule safety law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open BoundedSearchPortfolio (Cursor Status Iteration)

universe u w
variable {S : Type u} {Reply : Type}

theorem deepenStep_valid (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (iteration : Iteration S Reply) (valid : Valid space root iteration) :
    Valid space root (deepenStep space isError root demand iteration) := by
  unfold deepenStep
  split
  · exact begin_valid space root (iteration.depth + 1)
  · exact ⟨(BoundedSearchPortfolio.expandOne_answers space iteration.cursor).trans valid.1,
      (BoundedSearchPortfolio.expandOne_cut space iteration.cursor).trans valid.2⟩

theorem right_services_publish (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) (units : Nat)
    (iteration : Iteration S Reply) (valid : Valid space root iteration)
    (portfolio : BoundedSearchPortfolio.Portfolio (StrategyState space root) Reply E)
    (atRight : portfolio.right = .idd ⟨iteration, valid⟩)
    (budget : units ≤ portfolio.remaining)
    (eventual : BoundedSearchPortfolio.ready (status isError demand
      (((deepenStep space isError root demand)^[units] iteration).cursor)) = true) :
    ∃ schedule : List BoundedSearchPortfolio.Origin, schedule.length ≤ units + 1 ∧
      (BoundedSearchPortfolio.execute (strategyEngine space isError root demand E)
        (strategyEngine space isError root demand E) schedule portfolio).published.isSome = true := by
  induction units generalizing iteration valid portfolio with
  | zero =>
      cases published : portfolio.published with
      | some old => exact ⟨[], by simp, by simp [BoundedSearchPortfolio.execute, published]⟩
      | none =>
          cases stage : status isError demand iteration.cursor <;>
            simp only [stage, Function.iterate_zero, id_eq, BoundedSearchPortfolio.ready] at eventual
          case paused => contradiction
          case cutoff => contradiction
          all_goals
            refine ⟨[.right], by simp, ?_⟩
            simp [BoundedSearchPortfolio.execute, BoundedSearchPortfolio.turn,
              BoundedSearchPortfolio.serve, published, BoundedSearchPortfolio.Portfolio.privateState,
              atRight, strategyEngine, stage]
  | succ units ih =>
      cases published : portfolio.published with
      | some old => exact ⟨[], by simp, by simp [BoundedSearchPortfolio.execute, published]⟩
      | none =>
          cases stage : status isError demand iteration.cursor with
          | full | exhausted =>
              refine ⟨[.right], by simp, ?_⟩
              simp [BoundedSearchPortfolio.execute, BoundedSearchPortfolio.turn,
                BoundedSearchPortfolio.serve, published, BoundedSearchPortfolio.Portfolio.privateState,
                atRight, strategyEngine, stage]
          | paused | cutoff =>
              let moved := deepenStep space isError root demand iteration
              have movedValid := deepenStep_valid space isError root demand iteration valid
              let next := BoundedSearchPortfolio.serve (strategyEngine space isError root demand E) .right portfolio
              have positive : portfolio.remaining ≠ 0 := by omega
              have nextRight : next.right = .idd ⟨moved, movedValid⟩ := by
                simp [next, BoundedSearchPortfolio.serve, published,
                  BoundedSearchPortfolio.Portfolio.privateState, atRight, strategyEngine,
                  BoundedSearchPortfolio.pay, positive, BoundedSearchPortfolio.Portfolio.replace,
                  moved, deepenStep, tick, stage]
              have nextBudget : units ≤ next.remaining := by
                simp only [next, BoundedSearchPortfolio.serve, published, Option.isSome_none,
                  Bool.false_eq_true, ↓reduceIte, BoundedSearchPortfolio.Portfolio.privateState,
                  atRight, strategyEngine, stage, BoundedSearchPortfolio.pay, positive,
                  BoundedSearchPortfolio.Portfolio.replace]
                omega
              have movedReady : BoundedSearchPortfolio.ready (status isError demand
                  (((deepenStep space isError root demand)^[units] moved).cursor)) = true := by
                simpa only [Function.iterate_succ_apply, moved] using eventual
              obtain ⟨schedule, length, ready⟩ := ih moved movedValid next nextRight nextBudget movedReady
              refine ⟨.right :: schedule, by simp only [List.length_cons]; omega, ?_⟩
              exact ready

theorem mixed_portfolio_has_a_lawful_publication (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand target : Nat) (E : Type w)
    (settled : Decides space isError demand target root) :
    ∃ budget schedule origin answers,
      (BoundedSearchPortfolio.execute (strategyEngine space isError root demand E)
        (strategyEngine space isError root demand E) schedule
          (initialPortfolio space root E budget)).published = some (origin, answers) ∧
      BatchMeaning space root isError demand answers := by
  obtain ⟨units, _, eventually⟩ := deepening_eventually_ready space isError root demand target settled
  obtain ⟨schedule, _, published⟩ := right_services_publish space isError root demand E units
    (BoundedSearchPortfolio.beginIteration root 0) (begin_valid space root 0)
    (initialPortfolio space root E units) rfl (Nat.le_refl _) eventually
  cases answer : (BoundedSearchPortfolio.execute (strategyEngine space isError root demand E)
      (strategyEngine space isError root demand E) schedule (initialPortfolio space root E units)).published with
  | none => simp [answer] at published
  | some publication =>
      exact ⟨units, schedule, publication.1, publication.2, answer,
        mixed_portfolio_publication_law space isError root demand E units schedule publication.1 publication.2 answer⟩

end Mettapedia.Machines.ObserverLicence.HEWitness
