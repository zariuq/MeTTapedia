import Mettapedia.OSLF.Framework.NuInfiniteUnfoldingControls

/-!
# Exact inspection prices for finite chains and a persistent loop

Every successor list in this infinite state family has at most one member.
The complete finite-unfolding inspector has an independently earned answer
and price: a chain either reaches the unfolding depth or first stops at its
actual blocked endpoint. A persistent loop must inspect the whole depth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.InfiniteChainInspection

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding
open FundedNuAssays
open FundedNuAssayControls (continuation)
open NuInfiniteUnfoldingControls

theorem chain_successor_inspection (index length : Nat) :
    inspect infiniteChains (continuation.atStage (index + 1)) (continuation.stage_admitted (index + 1))
      emptyEnvironment (some (length + 1)) =
        ((inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
          emptyEnvironment (some length)).1,
          1 + (inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
            emptyEnvironment (some length)).2) := by
  simp only [atStage_successor, inspect, infiniteChains, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, Bool.or_false, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem loop_successor_inspection (index : Nat) :
    inspect infiniteChains (continuation.atStage (index + 1)) (continuation.stage_admitted (index + 1))
      emptyEnvironment none =
        ((inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
          emptyEnvironment none).1,
          1 + (inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
            emptyEnvironment none).2) := by
  simp only [atStage_successor, inspect, infiniteChains, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, Bool.or_false, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem finite_chain_inspection (index length : Nat) :
    inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
      emptyEnvironment (some length) = (decide (index ≤ length), min (index + 1) (length + 1)) := by
  induction index generalizing length with
  | zero => simp [PositiveHMLBody.atStage, nuUnfolding, inspect]
  | succ index inductionHypothesis =>
      cases length with
      | zero => simp [atStage_successor, inspect, infiniteChains]
      | succ length =>
          rw [chain_successor_inspection, inductionHypothesis]
          simp only [Nat.succ_le_succ_iff]
          congr 1
          omega

theorem persistent_loop_inspection (index : Nat) :
    inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
      emptyEnvironment none = (true, index + 1) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [loop_successor_inspection, inductionHypothesis]
      congr 1
      omega

theorem first_refuting_stage (length index : Nat) :
    (inspect infiniteChains (continuation.atStage index) (continuation.stage_admitted index)
      emptyEnvironment (some length)).1 = false ↔ length < index := by
  rw [finite_chain_inspection]
  simp only [decide_eq_false_iff_not, Nat.not_le]

theorem first_refutation_price (length : Nat) :
    inspect infiniteChains (continuation.atStage (length + 1))
      (continuation.stage_admitted (length + 1)) emptyEnvironment (some length) =
        (false, length + 1) := by
  rw [finite_chain_inspection]
  simp only [Nat.not_succ_le_self, decide_false, Nat.min_eq_right (by omega : length + 1 ≤ length + 1 + 1)]

end Mettapedia.OSLF.Framework.InfiniteChainInspection
