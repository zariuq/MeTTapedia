import Mettapedia.Machines.RelationHoldReceipts
import Mettapedia.Machines.RelationNumberingCost
import Mettapedia.Machines.RelationBagTransfer
import Mettapedia.Machines.RelationTransferCost
import Mathlib.Data.Finset.Card

/-!
# Semantic budgets for relation numbering costs

Fresh and revived holds are calculated from the actual zero-crossing receipt,
not freely chosen counters. Their sum is bounded by the inserted row's arity,
and revival is bounded by the cache's dead entries. Those facts make the
existing cost model's insertion clamps identities. Removal callbacks are
similarly bounded by row arity and live ownership.

This is a local semantic-to-cost interface. Allocation-room policy, failed
reservation metadata, native word ranges and the complete C scheduling trace
still need their representation correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationOwnershipCostBridge

open RelationColumnOwnership RelationHoldReceipts
variable {Id : Type} [DecidableEq Id]

def fresh (dictionary : List Id) (events : List Id) : List Id :=
  events.filter (fun id => decide (id ∉ dictionary))

def revived (dictionary : List Id) (events : List Id) : List Id :=
  events.filter (fun id => decide (id ∈ dictionary))

theorem receipt_partition (dictionary events : List Id) :
    (fresh dictionary events).length + (revived dictionary events).length = events.length := by
  induction events with
  | nil => simp [fresh, revived]
  | cons id rest ih =>
      by_cases member : id ∈ dictionary <;> simp [fresh, revived, member] at ih ⊢ <;> omega

theorem insertion_budget (dictionary : List Id) (state : Counters Id) (row : List Id) :
    (fresh dictionary (acquired state row)).length + (revived dictionary (acquired state row)).length ≤ row.length := by
  rw [receipt_partition]
  exact (acquired_sublist state row).length_le

theorem revival_budget (dictionary : List Id) (state : Counters Id) (valid : state.Valid) (row : List Id) :
    (revived dictionary (acquired state row)).length ≤ (dictionary.toFinset \ state.owned).card := by
  have distinct := (acquired_nodup state row).filter (fun id => decide (id ∈ dictionary))
  change (List.filter (fun id => decide (id ∈ dictionary)) (acquired state row)).length ≤ _
  rw [← List.toFinset_card_of_nodup distinct]
  apply Finset.card_le_card
  intro id member
  have fields : id ∈ acquired state row ∧ id ∈ dictionary := by simpa [revived] using member
  have zero := ((acquired_mem state row id).mp fields.1).2
  apply Finset.mem_sdiff.mpr
  refine ⟨by simpa using fields.2, ?_⟩
  rw [valid id, zero]
  simp

theorem numbering_add_clamps_are_exact (dictionary : List Id) (state : Counters Id)
    (valid : state.Valid) (row : List Id) (cost : RelationNumberingCost.St)
    (dead : cost.dead = (dictionary.toFinset \ state.owned).card) :
    RelationNumberingCost.revives row.length cost (revived dictionary (acquired state row)).length =
      (revived dictionary (acquired state row)).length ∧
    RelationNumberingCost.makes row.length cost (fresh dictionary (acquired state row)).length
      (revived dictionary (acquired state row)).length = (fresh dictionary (acquired state row)).length := by
  have together := insertion_budget dictionary state row
  have cached := revival_budget dictionary state valid row
  rw [← dead] at cached
  have arity : (revived dictionary (acquired state row)).length ≤ row.length := by omega
  have exactRevive : RelationNumberingCost.revives row.length cost (revived dictionary (acquired state row)).length =
      (revived dictionary (acquired state row)).length := by
    simp [RelationNumberingCost.revives, Nat.min_eq_left arity, Nat.min_eq_left cached]
  refine ⟨exactRevive, ?_⟩
  unfold RelationNumberingCost.makes
  rw [exactRevive]
  apply Nat.min_eq_left
  omega

theorem removal_budget (state : Counters Id) (valid : state.Valid) (row : List Id)
    (enough : ∀ id, row.count id ≤ state.uses id) :
    (released state row).length ≤ row.length ∧ (released state row).length ≤ state.owned.card := by
  refine ⟨(released_sublist state row).length_le, ?_⟩
  rw [← List.toFinset_card_of_nodup (released_nodup state row enough)]
  apply Finset.card_le_card
  intro id member
  have emitted : id ∈ released state row := by simpa using member
  exact ((release_iff_lost_owner state valid row id enough).mp emitted).1

/-- A pending estimate must cover eligible source candidates. The actual
successful movement count then needs no clamping in the cost rule. -/
theorem transfer_cost_uses_actual_moves {Fact : Type} [DecidableEq Fact]
    (choose : Nat → Fact → RelationBagTransfer.Action) (rows : List Fact)
    (target : RelationBagTransfer.Target Fact) (cost : RelationTransferCost.St)
    (covered : RelationBagTransfer.candidates choose 0 rows ≤ cost.pending) :
    let moved := (RelationBagTransfer.plan choose 0 rows target).2.count true
    RelationTransferCost.pass cost moved =
      if cost.pending ≠ 0 ∧ cost.rows ≤ 2 * cost.pending then
        ⟨cost.rows - moved, 0, cost.counted, cost.work + cost.rows + moved + cost.rows⟩
      else cost := by
  have bounded := (RelationBagTransfer.moved_le_candidates choose 0 rows target).trans covered
  simp [RelationTransferCost.pass, Nat.min_eq_left bounded]

omit [DecidableEq Id] in
theorem transfer_rows_measure {Fact : Type} [DecidableEq Fact]
    (choose : Nat → Fact → RelationBagTransfer.Action) (rows : List Fact)
    (target : RelationBagTransfer.Target Fact) :
    (RelationBagTransfer.retained rows (RelationBagTransfer.plan choose 0 rows target).2).length =
      rows.length - (RelationBagTransfer.plan choose 0 rows target).2.count true := by
  have conserved := RelationBagTransfer.retained_length rows _ (RelationBagTransfer.plan_length choose 0 rows target)
  omega

namespace Controls

def state : Counters Nat := ⟨fun id => if id = 1 then 2 else 0, {1}⟩

theorem repeated_new_id_uses_one_number :
    fresh [1, 2] (acquired state [2, 3, 3]) = [3] ∧
    revived [1, 2] (acquired state [2, 3, 3]) = [2] := by decide

end Controls
end Mettapedia.Machines.RelationOwnershipCostBridge
