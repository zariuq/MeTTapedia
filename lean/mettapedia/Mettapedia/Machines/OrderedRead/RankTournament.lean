import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A cached rank tournament for ordered delivery

Leaves hold occurrence ranks, not payload values. Internal nodes cache the
lesser live rank. Removing a winner rebuilds exactly one root-to-leaf path;
the fixed perfect shape bounds that path by the initial capacity's height.
Empty leaves are retained, so deletions do not require rebalancing.

This is a concrete pure ordered-provider implementation. It is not a claim
that a native array heap has already been refined to this representation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead.RankTournament

inductive Heap : Nat → Type
  | leaf (rank : Option Nat) : Heap 0
  | branch {height : Nat} (winner : Option Nat) (left right : Heap height) : Heap (height + 1)
  deriving Repr, DecidableEq

def root {height : Nat} : Heap height → Option Nat
  | .leaf rank => rank
  | .branch winner _ _ => winner

def ranks {height : Nat} : Heap height → Multiset Nat
  | .leaf rank => rank.toList
  | .branch _ left right => ranks left + ranks right

def winner : Option Nat → Option Nat → Option Nat
  | none, right => right
  | left, none => left
  | some left, some right => some (min left right)

def leftWins : Option Nat → Option Nat → Bool
  | none, _ => false
  | some _, none => true
  | some left, some right => decide (left ≤ right)

theorem winner_selects (left right : Option Nat) :
    winner left right = if leftWins left right then left else right := by
  cases left <;> cases right <;> simp [winner, leftWins, Nat.min_def]
  split <;> rfl

theorem winner_none_iff (left right : Option Nat) :
    winner left right = none ↔ left = none ∧ right = none := by
  cases left <;> cases right <;> simp [winner]

theorem winner_le_left (value : Nat) (right : Option Nat) :
    ∃ top, winner (some value) right = some top ∧ top ≤ value := by
  cases right with
  | none => exact ⟨value, rfl, le_rfl⟩
  | some other => exact ⟨min value other, rfl, Nat.min_le_left _ _⟩

theorem winner_le_right (left : Option Nat) (value : Nat) :
    ∃ top, winner left (some value) = some top ∧ top ≤ value := by
  cases left with
  | none => exact ⟨value, rfl, le_rfl⟩
  | some other => exact ⟨min other value, rfl, Nat.min_le_right _ _⟩

def make {height : Nat} (left right : Heap height) : Heap (height + 1) :=
  .branch (winner (root left) (root right)) left right

def Valid : {height : Nat} → Heap height → Prop
  | _, .leaf _ => True
  | _, .branch cached left right =>
      Valid left ∧ Valid right ∧ cached = winner (root left) (root right)

theorem make_valid {height : Nat} (left right : Heap height)
    (validLeft : Valid left) (validRight : Valid right) : Valid (make left right) :=
  ⟨validLeft, validRight, rfl⟩

theorem root_bounds {height : Nat} (heap : Heap height) (valid : Valid heap) :
    (∀ value, root heap = some value → value ∈ ranks heap) ∧
      (∀ value ∈ ranks heap, ∃ top, root heap = some top ∧ top ≤ value) := by
  induction heap with
  | leaf rank =>
      cases rank <;> simp [root, ranks]
  | @branch height cached left right ihLeft ihRight =>
      obtain ⟨validLeft, validRight, cache⟩ := valid
      obtain ⟨leftMember, leftBound⟩ := ihLeft validLeft
      obtain ⟨rightMember, rightBound⟩ := ihRight validRight
      constructor
      · intro value top
        change cached = some value at top
        rw [cache, winner_selects] at top
        split at top
        · exact Multiset.mem_add.mpr (Or.inl (leftMember value top))
        · exact Multiset.mem_add.mpr (Or.inr (rightMember value top))
      · intro value member
        rcases Multiset.mem_add.mp member with inLeft | inRight
        · obtain ⟨leftTop, present, below⟩ := leftBound value inLeft
          obtain ⟨top, chosen, leLeft⟩ := winner_le_left leftTop (root right)
          refine ⟨top, ?_, leLeft.trans below⟩
          change cached = some top
          rw [cache, present]
          exact chosen
        · obtain ⟨rightTop, present, below⟩ := rightBound value inRight
          obtain ⟨top, chosen, leRight⟩ := winner_le_right (root left) rightTop
          refine ⟨top, ?_, leRight.trans below⟩
          change cached = some top
          rw [cache, present]
          exact chosen

theorem root_none_iff {height : Nat} (heap : Heap height) (valid : Valid heap) :
    root heap = none ↔ ranks heap = 0 := by
  obtain ⟨member, bounded⟩ := root_bounds heap valid
  constructor
  · intro empty
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro value present
    obtain ⟨top, some, _⟩ := bounded value present
    rw [empty] at some
    contradiction
  · intro empty
    cases found : root heap with
    | none => rfl
    | some value =>
        have present := member value found
        rw [empty] at present
        contradiction

def pop : {height : Nat} → Heap height → Option Nat × Heap height × Nat
  | _, .leaf rank => (rank, .leaf none, 0)
  | _, .branch cached left right =>
      if cached = none then (none, .branch cached left right, 0) else
        if leftWins (root left) (root right) then
          let next := pop left
          (next.1, make next.2.1 right, next.2.2 + 2)
        else
          let next := pop right
          (next.1, make left next.2.1, next.2.2 + 2)

theorem pop_correct {height : Nat} (heap : Heap height) (valid : Valid heap) :
    (pop heap).1 = root heap ∧ Valid (pop heap).2.1 ∧
      ranks heap = ((pop heap).1.toList : Multiset Nat) + ranks (pop heap).2.1 ∧
      (pop heap).2.2 ≤ 2 * height := by
  induction heap with
  | leaf rank =>
      cases rank <;> simp [pop, root, ranks, Valid]
  | @branch height cached left right ihLeft ihRight =>
      obtain ⟨validLeft, validRight, cache⟩ := valid
      by_cases empty : cached = none
      · simp only [pop, if_pos empty]
        exact ⟨empty.symm, ⟨validLeft, validRight, cache⟩, by simp, by omega⟩
      · simp only [pop, if_neg empty]
        cases choose : leftWins (root left) (root right) with
        | true =>
            obtain ⟨top, leftValid, bag, cost⟩ := ihLeft validLeft
            simp only [↓reduceIte]
            refine ⟨?_, make_valid _ _ leftValid validRight, ?_, by omega⟩
            · change (pop left).1 = cached
              rw [top, cache, winner_selects, choose]
              rfl
            · change ranks left + ranks right = _ + (ranks (pop left).2.1 + ranks right)
              rw [bag, add_assoc]
        | false =>
            obtain ⟨top, rightValid, bag, cost⟩ := ihRight validRight
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, make_valid _ _ validLeft rightValid, ?_, by omega⟩
            · change (pop right).1 = cached
              rw [top, cache, winner_selects, choose]
              rfl
            · change ranks left + ranks right = _ + (ranks left + ranks (pop right).2.1)
              rw [bag]
              ac_rfl

def build (count : Nat) (rankAt : Nat → Nat) :
    (height : Nat) → Nat → Heap height × Nat × Nat
  | 0, position =>
      if position < count then (.leaf (some (rankAt position)), 1, 0)
      else (.leaf none, 0, 0)
  | height + 1, position =>
      let left := build count rankAt height position
      let right := build count rankAt height (position + 2 ^ height)
      (make left.1 right.1, left.2.1 + right.2.1, left.2.2 + right.2.2 + 1)

theorem build_valid (count : Nat) (rankAt : Nat → Nat) (height position : Nat) :
    Valid (build count rankAt height position).1 := by
  induction height generalizing position with
  | zero => simp [build]; split <;> trivial
  | succ height ih => exact make_valid _ _ (ih position) (ih (position + 2 ^ height))

theorem build_comparisons (count : Nat) (rankAt : Nat → Nat) (height position : Nat) :
    (build count rankAt height position).2.2 + 1 = 2 ^ height := by
  induction height generalizing position with
  | zero => simp [build]; split <;> rfl
  | succ height ih =>
      have left := ih position
      have right := ih (position + 2 ^ height)
      simp only [build, pow_succ]
      omega

@[simp] theorem ranks_make {height : Nat} (left right : Heap height) :
    ranks (make left right) = ranks left + ranks right := rfl

theorem build_contents (count : Nat) (rankAt : Nat → Nat) (height position : Nat) :
    ranks (build count rankAt height position).1 =
      (((List.range' position (2 ^ height)).filter (fun index => index < count)).map rankAt : Multiset Nat) ∧
    (build count rankAt height position).2.1 =
      ((List.range' position (2 ^ height)).filter (fun index => index < count)).length := by
  induction height generalizing position with
  | zero =>
      by_cases inside : position < count <;> simp [build, inside, ranks]
  | succ height ih =>
      obtain ⟨leftRanks, leftReads⟩ := ih position
      obtain ⟨rightRanks, rightReads⟩ := ih (position + 2 ^ height)
      rw [pow_succ, Nat.mul_two, ← List.range'_append_1]
      simp only [build, ranks_make, leftRanks, leftReads, rightRanks, rightReads,
        List.filter_append, List.map_append, List.length_append, Multiset.coe_add]
      constructor <;> trivial

def drain {height : Nat} : Nat → Heap height → List Nat × Heap height × Nat
  | 0, heap => ([], heap, 0)
  | count + 1, heap =>
      let next := pop heap
      match next.1 with
      | none => ([], next.2.1, next.2.2)
      | some value =>
          let later := drain count next.2.1
          (value :: later.1, later.2.1, next.2.2 + later.2.2)

theorem drain_correct {height : Nat} (fuel : Nat) (heap : Heap height) (valid : Valid heap) :
    Valid (drain fuel heap).2.1 ∧
      ranks heap = ((drain fuel heap).1 : Multiset Nat) + ranks (drain fuel heap).2.1 ∧
      (drain fuel heap).2.2 ≤ fuel * (2 * height) := by
  induction fuel generalizing heap with
  | zero => simp [drain, valid]
  | succ fuel ih =>
      obtain ⟨top, newValid, bag, cost⟩ := pop_correct heap valid
      cases found : (pop heap).1 with
      | none => simpa [drain, found, Nat.succ_mul] using
          (show Valid (pop heap).2.1 ∧ ranks heap = ranks (pop heap).2.1 ∧
            (pop heap).2.2 ≤ (fuel + 1) * (2 * height) from
              ⟨newValid, by simpa [found] using bag, by nlinarith⟩)
      | some value =>
          obtain ⟨lastValid, restBag, restCost⟩ := ih (pop heap).2.1 newValid
          simp only [drain, found]
          refine ⟨lastValid, ?_, ?_⟩
          · rw [found] at bag
            simp only [Option.toList_some, Multiset.coe_singleton] at bag
            rw [bag, restBag, ← add_assoc]
            rfl
          · rw [Nat.succ_mul]
            omega

theorem drain_sorted {height : Nat} (fuel : Nat) (heap : Heap height) (valid : Valid heap) :
    (drain fuel heap).1.Pairwise (· ≤ ·) := by
  induction fuel generalizing heap with
  | zero => simp [drain]
  | succ fuel ih =>
      obtain ⟨top, newValid, bag, _⟩ := pop_correct heap valid
      cases found : (pop heap).1 with
      | none => simp [drain, found]
      | some value =>
          simp only [drain, found]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih (pop heap).2.1 newValid⟩
          intro later member
          have remaining := (drain_correct fuel (pop heap).2.1 newValid).2.1
          have inNew : later ∈ ranks (pop heap).2.1 := by
            rw [remaining]
            exact Multiset.mem_add.mpr (Or.inl member)
          have inOld : later ∈ ranks heap := by
            rw [bag]
            exact Multiset.mem_add.mpr (Or.inr inNew)
          obtain ⟨least, chosen, bound⟩ := (root_bounds heap valid).2 later inOld
          rw [← top, found] at chosen
          have same : value = least := Option.some.inj chosen
          simpa only [same] using bound

theorem drain_exhausts {height : Nat} (fuel : Nat) (heap : Heap height) (valid : Valid heap)
    (enough : (ranks heap).card ≤ fuel) : ranks (drain fuel heap).2.1 = 0 := by
  induction fuel generalizing heap with
  | zero =>
      change ranks heap = 0
      exact Multiset.card_eq_zero.mp (by simpa using enough)
  | succ fuel ih =>
      obtain ⟨top, newValid, bag, _⟩ := pop_correct heap valid
      cases found : (pop heap).1 with
      | none =>
          have empty : ranks heap = 0 := (root_none_iff heap valid).mp (top.symm.trans found)
          simp only [found, Option.toList_none, Multiset.coe_nil, zero_add] at bag
          simpa [drain, found] using bag.symm.trans empty
      | some value =>
          have sizes := congrArg Multiset.card bag
          simp only [found, Option.toList_some, Multiset.coe_singleton, Multiset.card_add,
            Multiset.card_singleton] at sizes
          simpa [drain, found] using ih (pop heap).2.1 newValid (by omega)

theorem complete_delivery_is_sorted_bag {height : Nat} (heap : Heap height) (valid : Valid heap) :
    (drain (ranks heap).card heap).1 = (ranks heap).sort (· ≤ ·) := by
  have contents := (drain_correct (ranks heap).card heap valid).2.1
  rw [drain_exhausts _ heap valid (le_refl _), add_zero] at contents
  have permutation : ((drain (ranks heap).card heap).1).Perm ((ranks heap).sort (· ≤ ·)) :=
    Multiset.coe_eq_coe.mp (contents.symm.trans (Multiset.sort_eq _ _).symm)
  exact permutation.eq_of_pairwise' (drain_sorted _ heap valid) (Multiset.pairwise_sort _ _)

namespace Controls

def sample : Heap 2 := (build 3 (fun index => if index = 0 then 2 else if index = 1 then 0 else 1) 2 0).1

theorem build_reads_each_present_rank_once :
    (build 3 (fun index => index) 2 0).2.1 = 3 ∧
      (build 3 (fun index => index) 2 0).2.2 = 3 := by decide

theorem ordered_delivery_preserves_all_ranks :
    (drain 3 sample).1 = [0, 1, 2] ∧ root (drain 3 sample).2.1 = none ∧
      (drain 3 sample).2.2 = 12 := by decide

theorem stale_winner_is_not_a_valid_heap :
    ¬ Valid (Heap.branch (some 9) (.leaf (some 1)) (.leaf (some 2))) := by
  simp [Valid, root, winner]

end Controls

end Mettapedia.Machines.OrderedRead.RankTournament
