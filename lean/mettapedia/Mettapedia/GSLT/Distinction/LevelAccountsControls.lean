import Mettapedia.GSLT.Distinction.LevelAccounts
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls

/-!
# Controls for level-indexed accounts and qualified replay

* **Replay on the two routes of one tile** (`grid_work_replay_qualified`,
  `grid_state_cost_replay_not_qualified`, `grid_ordered_replay_not_qualified`,
  `erasure_qualifies_what_full_does_not`).  The two routes have the same
  endpoints and the same trace.  Replaying one for the other is qualified for
  work, not for a state-dependent host cost, and not for an ordered account,
  the shape of a noncommutative Need account; erasing the ordered account to
  its length qualifies the replay, so an erasure must be declared.
* **Checked bounds** (`state_cost_checked_bound`, `state_cost_unbounded_by_work`).
  The state-dependent cost is at most five times the work on every path,
  checked on occurrences; it is not bounded by the work itself.
* **An optimization cuts host work and keeps the reference reading**
  (`optimization_cuts_work`).  The one-step checker and the three-step
  interpreter have the same final observation; the checker spends two units,
  the interpreter four.
* **A read component is observed** (`read_account_not_in_observation`).  Two
  states with equal observations and different accounts: a program that reads
  its account separates them, so the account belongs to its observation.
* **Exactness** (`exact_cost_replays_by_endpoints`, `cycle_work_not_by_endpoints`).
  On the three-cycle with fork and erasure, an exact real cost gives the
  fork-and-erase loop and the evolution cycle cost zero, like the empty
  history; one unit per event gives them `2` and `3`, and is not exact.
* **Machine runs as occurrence paths** (`checker_segment_account`,
  `finishing_charge_off_trace`).  On a segment the account of a machine run is
  the run account of its trace; the transition that ends a complete run is
  charged off the trace.
* **Whole-parent suspension** (`whole_parent_control`, `child_only_control`,
  `restart_control`).  Pausing a parent inside its child and resuming the whole
  residual keeps every event and the full account; resuming the child alone
  loses the parent's continuation; restarting charges the paid prefix again.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.LevelAccounts.Controls

open Mettapedia.Effects
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.Mazurkiewicz
open Mettapedia.GSLT.Causality.TraceCostValuation
open Mettapedia.GSLT.Core.NonFactorization

/-! ## Replay on the two routes of one tile -/

/-- **Work: replay qualified.** -/
theorem grid_work_replay_qualified :
    QualifiedReplay (pathAccount (workValuation gridPresentation)) gridTile.path gridTile.pathSwap' := by
  unfold QualifiedReplay
  change Multiplicative.ofAdd ((workValuation gridPresentation).onPath gridTile.path) =
    Multiplicative.ofAdd ((workValuation gridPresentation).onPath gridTile.pathSwap')
  rw [grid_work_both_routes.1, grid_work_both_routes.2]

/-- **A state-dependent host cost: replay not qualified**, with the same
endpoints and trace. -/
theorem grid_state_cost_replay_not_qualified :
    ¬ QualifiedReplay (pathAccount gridStateCost) gridTile.path gridTile.pathSwap' := by
  intro qualified
  have costs : gridStateCost.onPath gridTile.path = gridStateCost.onPath gridTile.pathSwap' :=
    Multiplicative.ofAdd.injective qualified
  revert costs
  decide

/-- **An ordered account: replay not qualified.** -/
theorem grid_ordered_replay_not_qualified :
    ¬ QualifiedReplay (pathAccount (siteListValuation (P := gridPresentation)))
      gridTile.path gridTile.pathSwap' := by
  intro qualified
  have words : (siteListValuation (P := gridPresentation)).onPath gridTile.path =
      (siteListValuation (P := gridPresentation)).onPath gridTile.pathSwap' :=
    Multiplicative.ofAdd.injective qualified
  have sites := congrArg SiteWord.toList words
  rw [siteListValuation_onPath, siteListValuation_onPath] at sites
  exact grid_not_tile_invariant_sites sites

/-- The length of an ordered site word. -/
def wordLength (α : Type) : SiteWord α →+ ℕ where
  toFun word := word.toList.length
  map_zero' := rfl
  map_add' first second := by simp

/-- **Erasure is lossy**: the length of the ordered account qualifies the
replay that the ordered account refuses. -/
theorem erasure_qualifies_what_full_does_not :
    QualifiedReplay ((pathAccount (siteListValuation (P := gridPresentation))).map
        (wordLength GridSite).toMultiplicative) gridTile.path gridTile.pathSwap' ∧
      ¬ QualifiedReplay (pathAccount (siteListValuation (P := gridPresentation)))
        gridTile.path gridTile.pathSwap' := by
  refine ⟨?_, grid_ordered_replay_not_qualified⟩
  unfold QualifiedReplay
  change Multiplicative.ofAdd ((wordLength GridSite) ((siteListValuation (P := gridPresentation)).onPath
      gridTile.path)) =
    Multiplicative.ofAdd ((wordLength GridSite) ((siteListValuation (P := gridPresentation)).onPath
      gridTile.pathSwap'))
  simp only [wordLength, AddMonoidHom.coe_mk, ZeroHom.coe_mk, siteListValuation_onPath]
  rw [gridTile.sites_pathSwap']
  rfl

/-! ## Checked bounds -/

/-- **The state-dependent cost is at most five times the work on every path**,
checked on its occurrences. -/
theorem state_cost_checked_bound : CheckedBound (workValuation gridPresentation) gridStateCost 5 := by
  apply CheckedBound.of_occurrences
  intro s t occurrence
  obtain ⟨site, evidence⟩ := occurrence
  cases site
  · show (if s.2 then 5 else 1) ≤ 5 * 1
    split <;> omega
  · show 1 ≤ 5 * 1
    omega

/-- It is not bounded by the work itself. -/
theorem state_cost_unbounded_by_work : ¬ CheckedBound (workValuation gridPresentation) gridStateCost 1 := by
  intro bound
  have swapped := bound gridTile.pathSwap'
  revert swapped
  decide

/-! ## An optimization cuts host work -/

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks.Controls (checker interpreter check_interpret_final
  paceMachine Pace)

/-- **The checker and the interpreter have the same final observation; the
checker spends half the host work.** -/
theorem optimization_cuts_work :
    checker.observe 2 .start = interpreter.observe 4 .start ∧
      checker.spent (fun _ => 1) 2 .start = 2 ∧ interpreter.spent (fun _ => 1) 4 .start = 4 :=
  ⟨check_interpret_final.1, rfl, rfl⟩

/-- **A component the program reads is observed**: equal observations,
different accounts.  A program that reads its account tells the two states
apart, so the account belongs to its observation. -/
def read_account_not_in_observation :
    NonTrivialFiber (fun state : Pace => paceMachine.observe 2 state)
      (fun state => paceMachine.spent (fun _ => 1) 2 state) where
  left := .slow
  right := .fast
  sameShadow := rfl
  differentValue := by decide

/-! ## Machine runs as occurrence paths -/

/-- **Positive: on a segment the machine's account is the run account of its
trace.**  The checker's first step publishes and leaves its residual. -/
theorem checker_segment_account :
    (pathAccount (checker.priceValuation fun _ => 1)).of (checker.trace 1 .start).2 =
      Multiplicative.ofAdd 1 :=
  checker.spent_eq_pathAccount (fun _ => 1) (events := [.answer 1]) (residual := .verdict) rfl

/-- **Negative: the transition that ends a run is not on its trace.**  The
checker's complete run is charged two units; its trace carries one, and the
finishing transition the other. -/
theorem finishing_charge_off_trace :
    checker.spent (fun _ => 1) 2 .start = 2 ∧
      (checker.priceValuation fun _ => 1).onPath (checker.trace 2 .start).2 = 1 ∧
      checker.endCharge (fun _ => 1) 2 .start = 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Exactness on the three-cycle -/

open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.Cybernetics.DistinctionCalculus.History (Event)

/-- A potential on the three-cycle. -/
noncomputable def cyclePotential : Fin 3 → ℝ := fun x => (x.val : ℝ) + 1

/-- The differential of that potential. -/
noncomputable def exactCost : Event (Fin 3) → ℝ
  | .evolve x => cyclePotential (cycleGrammar.evolve x) - cyclePotential x
  | .fork x => cyclePotential x
  | .erase x => -cyclePotential x
  | .merge x y => cyclePotential (cycleGrammar.merge x y) - cyclePotential x - cyclePotential y

theorem exactCost_exact : Exact cycleGrammar exactCost :=
  ⟨cyclePotential, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The evolution cycle from `{0}` back to `{0}`. -/
theorem cycle_path : LabelledPath cycleGrammar {0} [.evolve 0, .evolve 1, .evolve 2] {0} :=
  (cycle_control).2.2.1

/-- **An exact cost replays by endpoints**: the evolution cycle costs what the
empty history costs. -/
theorem exact_cost_replays_by_endpoints :
    (([.evolve 0, .evolve 1, .evolve 2] : List (Event (Fin 3))).map exactCost).sum =
      (([] : List (Event (Fin 3))).map exactCost).sum :=
  exact_replay cycleGrammar exactCost_exact cycle_path (.nil _)

/-- **One unit per event does not replay by endpoints**: the fork-and-erase
loop and the cycle cost `2` and `3`, the empty history `0`; and it is not
exact. -/
theorem cycle_work_not_by_endpoints :
    (([.fork 0, .erase 0] : List (Event (Fin 3))).map unitWork).sum = 2 ∧
      (([.evolve 0, .evolve 1, .evolve 2] : List (Event (Fin 3))).map unitWork).sum = 3 ∧
      LabelledPath cycleGrammar {0} [.fork 0, .erase 0] {0} ∧
      ¬ Exact cycleGrammar (unitWork (V := Fin 3)) := by
  obtain ⟨_, loop, _, two⟩ := work_replay_not_by_endpoints cycleGrammar (0 : Fin 3)
  exact ⟨two, by norm_num [unitWork], loop, unit_work_not_exact cycleGrammar⟩

/-! ## Whole-parent suspension -/

/-- A parent that runs a child, then finishes its own work. -/
inductive Family where
  | parentStart
  | childFirst
  | childSecond
  | parentAfter
  | finished
  deriving DecidableEq

abbrev FamilyEvent := Mettapedia.GSLT.Dynamics.OrderedDemand.Event ℕ Unit Unit

/-- The parent enters the child, the child publishes `1` and `2`, the parent
publishes `9` and finishes. -/
def parent : ProductiveBlocks.Machine Family FamilyEvent Unit Empty where
  step
    | .parentStart => some (.silent .childFirst)
    | .childFirst => some (.publish [.answer 1] .childSecond)
    | .childSecond => some (.publish [.answer 2] .parentAfter)
    | .parentAfter => some (.publish [.answer 9] .finished)
    | .finished => some (.finish ())

/-- The child alone: after its second publication it finishes. -/
def childOnly : ProductiveBlocks.Machine Family FamilyEvent Unit Empty where
  step
    | .childFirst => some (.publish [.answer 1] .childSecond)
    | .childSecond => some (.publish [.answer 2] .finished)
    | _ => some (.finish ())

/-- Paused inside the child, after its first publication. -/
theorem paused_in_child : parent.run 2 .parentStart = ([.answer 1], .exhausted .childSecond) :=
  rfl

/-- **Resuming the whole residual keeps every event and the full account.** -/
theorem whole_parent_control :
    (parent.run 2 .parentStart).1 ++ (parent.run 3 .childSecond).1 = [.answer 1, .answer 2, .answer 9] ∧
      parent.spent (fun _ => 1) 2 .parentStart + parent.spent (fun _ => 1) 3 .childSecond =
        parent.spent (fun _ => 1) 5 .parentStart := by
  obtain ⟨_, accounts⟩ := Machine.whole_parent_resumption parent (fun (_ : Unit) _ => 1) 2 3
    paused_in_child
  exact ⟨rfl, (accounts ()).symm⟩

/-- **Resuming the child alone loses the parent's continuation.** -/
theorem child_only_control :
    (parent.run 2 .parentStart).1 ++ (childOnly.run 3 .childSecond).1 = [.answer 1, .answer 2] ∧
      (parent.run 5 .parentStart).1 = [.answer 1, .answer 2, .answer 9] :=
  ⟨rfl, rfl⟩

/-- **Restarting charges the paid prefix again.** -/
theorem restart_control :
    parent.spent (fun _ => 1) 2 .parentStart + parent.spent (fun _ => 1) 5 .parentStart = 7 ∧
      parent.spent (fun _ => 1) 5 .parentStart = 5 :=
  ⟨rfl, rfl⟩

end Mettapedia.GSLT.Distinction.LevelAccounts.Controls
