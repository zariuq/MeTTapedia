import Mettapedia.Machines.Order.RentOrBuy
import Mettapedia.Machines.PortfolioReach.Race
import Mettapedia.Machines.OrderedRead.Sequences

/-!
# Ordered demand: prepaid acquisition and resumable prefix racing

Rent-or-buy retains its factor two when the purchase price includes the work
needed to make all later ordered replies available. A common delivery charge
can be added to both plans. Incremental heap delivery is not free after the
purchase; ignoring it destroys that ratio.

For genuinely incremental alternatives, the existing pure resumable race
gives a prefix-cost bound. Both providers must certify the same ordered
occurrence prefix; that condition also makes changing winners at successive
demands coherent. Costs count the declared provider work units, not native
instructions or scheduling overhead.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead

open Order.RentOrBuy

def prepaidOrdered (walk purchase commonDelivery : Nat) : Nat :=
  breakEven walk purchase purchase + commonDelivery

def orderedOpt (walk purchase commonDelivery : Nat) : Nat :=
  min (walk + commonDelivery) (purchase + commonDelivery)

theorem prepaid_ordered_two_competitive (walk purchase commonDelivery : Nat) :
    prepaidOrdered walk purchase commonDelivery ≤ 2 * orderedOpt walk purchase commonDelivery := by
  have bound := breakEven_le_two_opt walk purchase
  unfold opt at bound
  unfold prepaidOrdered orderedOpt
  rcases le_total walk purchase with smaller | smaller
  · rw [Nat.min_eq_left (by omega)]
    rw [Nat.min_eq_left smaller] at bound
    omega
  · rw [Nat.min_eq_right (by omega)]
    rw [Nat.min_eq_right smaller] at bound
    omega

theorem every_ordered_demand (walk : Nat → Nat) (purchase : Nat) (delivery : Nat → Nat) :
    ∀ demand, prepaidOrdered (walk demand) purchase (delivery demand) ≤
      2 * orderedOpt (walk demand) purchase (delivery demand) :=
  fun demand => prepaid_ordered_two_competitive (walk demand) purchase (delivery demand)

def naiveDeferred (walk purchase delivered demand height : Nat) : Nat :=
  if walk ≤ purchase then walk else purchase + purchase + (demand - delivered) * height

def deferredOpt (walk purchase demand height : Nat) : Nat :=
  min walk (purchase + demand * height)

theorem ignoring_heap_delivery_is_not_two_competitive :
    naiveDeferred 1536 1024 512 1024 10 = 7168 ∧
      deferredOpt 1536 1024 1024 10 = 1536 ∧
      2 * deferredOpt 1536 1024 1024 10 < naiveDeferred 1536 1024 512 1024 10 := by decide

/-- A power-of-two candidate population has the indicated heap height. The
first two thirds of the walk include half its matches; the remaining matches
are dense. Buying at the posted candidate count can be arbitrarily worse. -/
theorem naive_deferred_has_no_constant_ratio (ratio : Nat) :
    ∃ half height, 0 < half ∧ 2 * half = 2 ^ height ∧
      ratio * deferredOpt (3 * half) (2 * half) (2 * half) height <
        naiveDeferred (3 * half) (2 * half) half (2 * half) height := by
  let height := 3 * ratio + 2
  let half := 2 ^ (3 * ratio + 1)
  have positive : 0 < half := by dsimp [half]; positivity
  have population : 2 * half = 2 ^ height := by
    dsimp [half, height]
    rw [show 3 * ratio + 2 = (3 * ratio + 1) + 1 by omega, pow_succ]
    omega
  have heightPositive : 1 ≤ height := by dsimp [height]; omega
  have best : deferredOpt (3 * half) (2 * half) (2 * half) height = 3 * half := by
    unfold deferredOpt
    apply Nat.min_eq_left
    nlinarith
  have after : ¬ 3 * half ≤ 2 * half := by omega
  refine ⟨half, height, positive, population, ?_⟩
  rw [best, naiveDeferred, if_neg after]
  have remaining : 2 * half - half = half := by omega
  rw [remaining]
  dsimp [height]
  nlinarith

section Race

open PortfolioReach

universe u v w
variable {T : Type u} {U : Type v} {W : Type w}

/-- A prefix demand is an outcome of each provider, measured from its actual
retained start state. No restart or cost defined from an oracle is used. -/
theorem ordered_prefix_race_cost (walk : Resumable T) (indexed : Resumable U)
    (world : W) (walkStart : T) (indexStart : U) (walkNeed indexNeed : Nat)
    (walkReady : walk.ready (walk.step^[walkNeed] walkStart) = true)
    (indexReady : indexed.ready (indexed.step^[indexNeed] indexStart) = true) :
    ∃ rounds,
      (race walk indexed (fun _ => 1) world walkStart indexStart rounds).published.isSome = true ∧
      (race walk indexed (fun _ => 1) world walkStart indexStart rounds).spent ≤
        2 * min walkNeed indexNeed + 1 := by
  have publishes := race_publishes_first walk indexed (fun _ => 1) world walkStart indexStart
    (fun _ => by decide) walkReady
  let rounds := walkNeed + 1
  refine ⟨rounds, publishes, ?_⟩
  have first := race_first_cost walk indexed (fun _ => 1) world walkStart indexStart publishes walkReady
  have second := uniform_second_cost walk indexed 1 world walkStart indexStart publishes indexReady
  dsimp only [rounds]
  rcases le_total walkNeed indexNeed with smaller | smaller
  · rw [Nat.min_eq_left smaller]
    omega
  · rw [Nat.min_eq_right smaller]
    exact second

end Race

theorem successive_prefix_winners_cohere {α : Type} (ordered : List α)
    (first second : List α) (early later : Nat) (grows : early ≤ later)
    (firstExact : first = ordered.take early) (secondExact : second = ordered.take later) :
    second.take early = first := by
  rw [firstExact, secondExact, List.take_take, Nat.min_eq_left grows]

theorem switch_keeps_exact_residual {α : Type} (ordered : List α) (position : Nat) :
    ordered.take position ++ ordered.drop position = ordered :=
  List.take_append_drop position ordered

namespace Controls

theorem two_correct_bag_providers_need_not_agree_on_a_prefix :
    ([1, 2, 3] : List Nat).Perm [2, 1, 3] ∧
      ([1, 2, 3] : List Nat).take 1 ≠ [2, 1, 3].take 1 := by
  exact ⟨List.Perm.swap _ _ [3], by decide⟩

theorem ordered_walk_and_index_may_switch_winners :
    ([1, 2, 3] : List Nat).take 2 = [1, 2] ∧
      (([1, 2, 3] : List Nat).take 3).take 2 = [1, 2] := by decide

end Controls

end Mettapedia.Machines.OrderedRead
