import Mettapedia.OSLF.Framework.InfiniteChainInspection
import Mettapedia.OSLF.Framework.FundedNuInstructionAssays

/-!
# A proved observational ceiling for funded unfolding tests

The observation retains the actual public answer and spent instruction count.
At every purse no larger than a fixed bound, all unfolding questions give the
same observation for a sufficiently long finite chain and a persistent loop.
Their original greatest-fixed-point predicates differ. Consequently that
predicate cannot descend to this bounded observation profile.

This is the declared continuation-unfolding observer class. It is not a claim
about all HML formulas, unrestricted contexts, raw instruction inspection or
structural access to the supplied state. Compilation and physical time have
their own accounts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuBudgetSeparation

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding StackInspection
open FundedNuAssays
open FundedNuAssayControls (continuation)
open NuInfiniteUnfoldingControls InfiniteChainInspection

def receipt (budget index : Nat) (state : Option Nat) :=
  Funded.attempt infiniteChains (continuation.atStage index)
    (continuation.stage_admitted index) emptyEnvironment state [] budget

def observation (budget index : Nat) (state : Option Nat) : Option Bool × Nat :=
  (Funded.publicAnswer (receipt budget index state).endpoint, (receipt budget index state).endpoint.spent)

def view (budget : Nat) (state : Option Nat) : Nat → Option Bool × Nat :=
  fun index => observation budget index state

theorem loop_observation (budget index : Nat) :
    observation budget index none =
      (if index + 1 ≤ budget then some true else none, min budget (index + 1)) := by
  unfold observation receipt
  rw [Funded.attempt_answer, Funded.attempt_spent, persistent_loop_inspection]

theorem chain_observation (budget index length : Nat) :
    observation budget index (some length) =
      (if min (index + 1) (length + 1) ≤ budget then some (decide (index ≤ length)) else none,
        min budget (min (index + 1) (length + 1))) := by
  unfold observation receipt
  rw [Funded.attempt_answer, Funded.attempt_spent, finite_chain_inspection]

theorem bounded_observations_agree (bound budget index : Nat) (within : budget ≤ bound) :
    observation budget index (some bound) = observation budget index none := by
  rw [chain_observation, loop_observation]
  by_cases affordable : index + 1 ≤ budget
  · have reaches : index ≤ bound := by omega
    have price : min (index + 1) (bound + 1) = index + 1 := by omega
    simp only [price, if_pos affordable, reaches, decide_true]
  · have unavailable : ¬ min (index + 1) (bound + 1) ≤ budget := by omega
    simp only [if_neg affordable, if_neg unavailable]
    congr 1
    omega

theorem bounded_views_agree (bound budget : Nat) (within : budget ≤ bound) :
    view budget (some bound) = view budget none := by
  funext index
  exact bounded_observations_agree bound budget index within

/-- Every state in this actual family admits a complete test when the
supplied purse covers the unfolding depth and its final observation. -/
theorem stage_uniformly_affordable (budget index : Nat) (enough : index + 1 ≤ budget)
    (state : Option Nat) :
    (inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
      emptyEnvironment state).2 ≤ budget := by
  cases state with
  | none => simpa only [persistent_loop_inspection] using enough
  | some length =>
      rw [finite_chain_inspection]
      exact le_trans (Nat.min_le_left _ _) enough

theorem affordable_stage_classified (budget index : Nat) (enough : index + 1 ≤ budget)
    (state : Option Nat) :
    (view budget state index).1 = some true ↔
      satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) state := by
  change Funded.publicAnswer (receipt budget index state).endpoint = some true ↔ _
  unfold receipt
  rw [Funded.attempt_answer, if_pos (stage_uniformly_affordable budget index enough state)]
  rw [Option.some.injEq]
  exact test_truth infiniteChains (fun _ _ => 0) (continuation, index) state

theorem affordable_stage_descends (budget index : Nat) (enough : index + 1 ≤ budget) :
    ∃ classify : (Nat → Option Bool × Nat) → Prop, ∀ state : Option Nat,
      classify (view budget state) ↔
        satisfies infiniteChains.toLTS Env.empty (continuation.atStage index) state :=
  ⟨fun profile => (profile index).1 = some true, affordable_stage_classified budget index enough⟩

theorem bounded_profile_does_not_classify_limit (budget : Nat) :
    ¬ ∃ classify : (Nat → Option Bool × Nat) → Prop, ∀ state : Option Nat,
      classify (view budget state) ↔
        satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) state := by
  rintro ⟨classify, correct⟩
  have atLoop := (correct none).2 infinite_loop_original
  have same := bounded_views_agree budget budget le_rfl
  have atChain : classify (view budget (some budget)) := by
    rw [same]
    exact atLoop
  exact finite_chain_original_refuted budget ((correct (some budget)).1 atChain)

theorem one_more_cell_earns_refutation (bound : Nat) :
    observation (bound + 1) (bound + 1) (some bound) = (some false, bound + 1) := by
  rw [chain_observation]
  have price : min (bound + 1 + 1) (bound + 1) = bound + 1 := by omega
  simp only [price, le_refl, if_true, Nat.not_succ_le_self, decide_false, Nat.min_self]

theorem persistent_loop_still_waits (bound : Nat) :
    observation (bound + 1) (bound + 1) none = (none, bound + 1) := by
  rw [loop_observation]
  have insufficient : ¬ bound + 1 + 1 ≤ bound + 1 := by omega
  simp only [if_neg insufficient, Nat.min_eq_left (by omega : bound + 1 ≤ bound + 1 + 1)]

end Mettapedia.OSLF.Framework.FundedNuBudgetSeparation
