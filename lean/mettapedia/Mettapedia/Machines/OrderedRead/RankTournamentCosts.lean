import Mettapedia.Machines.OrderedRead.RankTournament

/-!
# Rank acquisition, residual resumption and logarithmic delivery charges

The preparation reads each posted rank once. Padding contains no rank reads.
With a power-of-two capacity below twice the posted population, preparation
has linear node work; a pop pays at most two comparison charges per level.
The account excludes native allocation, payload decoding and maintenance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead.RankTournament

theorem filter_range_below (capacity count : Nat) :
    (List.range capacity).filter (fun index => index < count) = List.range (min capacity count) := by
  induction capacity with
  | zero => simp
  | succ capacity ih =>
      by_cases below : capacity < count
      · simp [List.range_succ, List.filter_append, below, ih,
          Nat.min_eq_left (show capacity ≤ count by omega)]
      · simp [List.range_succ, List.filter_append, below, ih,
          Nat.min_eq_right (show count ≤ capacity by omega),
          Nat.min_eq_right (show count ≤ capacity + 1 by omega)]

def capacityHeight (count : Nat) : Nat := if count = 0 then 0 else Nat.log 2 count + 1

theorem capacity_covers (count : Nat) : count ≤ 2 ^ capacityHeight count := by
  by_cases zero : count = 0
  · simp [capacityHeight, zero]
  · simpa [capacityHeight, zero] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) count).le

theorem capacity_is_linear (count : Nat) (positive : 0 < count) :
    2 ^ capacityHeight count ≤ 2 * count := by
  have bounded := Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt positive)
  simp only [capacityHeight, Nat.ne_zero_of_lt positive, ↓reduceIte, pow_succ]
  omega

theorem preparation_reads_posted_ranks_once (count : Nat) (rankAt : Nat → Nat) :
    (build count rankAt (capacityHeight count) 0).2.1 = count ∧
      ranks (build count rankAt (capacityHeight count) 0).1 =
        ((List.range count).map rankAt : Multiset Nat) := by
  obtain ⟨contents, reads⟩ := build_contents count rankAt (capacityHeight count) 0
  have cover := capacity_covers count
  simp only [← List.range_eq_range', filter_range_below, Nat.min_eq_right cover,
    List.length_range] at contents reads
  exact ⟨reads, contents⟩

theorem preparation_comparison_charge_linear (count : Nat) (rankAt : Nat → Nat) (positive : 0 < count) :
    (build count rankAt (capacityHeight count) 0).2.2 < 2 * count := by
  have exactCharge := build_comparisons count rankAt (capacityHeight count) 0
  have cap := capacity_is_linear count positive
  omega

theorem prepared_pop_logarithmic (count : Nat) (rankAt : Nat → Nat) (positive : 0 < count) :
    (pop (build count rankAt (capacityHeight count) 0).1).2.2 ≤ 2 * (Nat.log 2 count + 1) := by
  have cost := (pop_correct _ (build_valid count rankAt (capacityHeight count) 0)).2.2.2
  simpa [capacityHeight, Nat.ne_zero_of_lt positive] using cost

theorem pop_empty {height : Nat} (heap : Heap height) (empty : root heap = none) :
    pop heap = (none, heap, 0) := by
  cases heap with
  | leaf rank =>
      change rank = none at empty
      subst rank
      rfl
  | branch cached left right =>
      change cached = none at empty
      simp [pop, empty]

theorem drain_empty {height : Nat} (fuel : Nat) (heap : Heap height) (empty : root heap = none) :
    drain fuel heap = ([], heap, 0) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [drain, pop_empty heap empty]

theorem drain_append {height : Nat} (first second : Nat) (heap : Heap height) (valid : Valid heap) :
    drain (first + second) heap =
      let front := drain first heap
      let back := drain second front.2.1
      (front.1 ++ back.1, back.2.1, front.2.2 + back.2.2) := by
  induction first generalizing heap with
  | zero => simp [drain]
  | succ first ih =>
      obtain ⟨top, newValid, _, _⟩ := pop_correct heap valid
      cases found : (pop heap).1 with
      | none =>
          have empty := top.symm.trans found
          simp [drain_empty _ heap empty]
      | some value =>
          simp [Nat.succ_add, drain, found, ih (pop heap).2.1 newValid, Nat.add_assoc]

theorem drain_length {height : Nat} (fuel : Nat) (heap : Heap height) (valid : Valid heap) :
    (drain fuel heap).1.length = min fuel (ranks heap).card := by
  induction fuel generalizing heap with
  | zero => simp [drain]
  | succ fuel ih =>
      obtain ⟨top, newValid, contents, _⟩ := pop_correct heap valid
      cases found : (pop heap).1 with
      | none =>
          have empty := (root_none_iff heap valid).mp (top.symm.trans found)
          simp [drain, found, empty]
      | some value =>
          have sizes := congrArg Multiset.card contents
          simp only [found, Option.toList_some, Multiset.coe_singleton, Multiset.card_add,
            Multiset.card_singleton] at sizes
          simp only [drain, found, List.length_cons, ih _ newValid]
          omega

theorem bounded_delivery_is_the_ordered_prefix {height : Nat} (fuel : Nat)
    (heap : Heap height) (valid : Valid heap) (within : fuel ≤ (ranks heap).card) :
    (drain fuel heap).1 = ((ranks heap).sort (· ≤ ·)).take fuel := by
  have split := congrArg (fun result : List Nat × Heap height × Nat => result.1)
    (drain_append fuel ((ranks heap).card - fuel) heap valid)
  simp only at split
  rw [Nat.add_sub_of_le within, complete_delivery_is_sorted_bag heap valid] at split
  have size := drain_length fuel heap valid
  rw [Nat.min_eq_left within] at size
  have prefixTake := congrArg (List.take fuel) split
  rw [List.take_append_of_le_length (show fuel ≤ (drain fuel heap).1.length by omega)] at prefixTake
  rw [List.take_of_length_le (show (drain fuel heap).1.length ≤ fuel by omega)] at prefixTake
  exact prefixTake.symm

theorem prepared_complete_delivery (count : Nat) (rankAt : Nat → Nat) :
    (drain count (build count rankAt (capacityHeight count) 0).1).1 =
      ((List.range count).map rankAt : Multiset Nat).sort (· ≤ ·) := by
  have contents := (preparation_reads_posted_ranks_once count rankAt).2
  have size := congrArg Multiset.card contents
  simp only [Multiset.coe_card, List.length_map, List.length_range] at size
  have exactDelivery := complete_delivery_is_sorted_bag (build count rankAt (capacityHeight count) 0).1
    (build_valid count rankAt (capacityHeight count) 0)
  rw [size, contents] at exactDelivery
  exact exactDelivery

end Mettapedia.Machines.OrderedRead.RankTournament
