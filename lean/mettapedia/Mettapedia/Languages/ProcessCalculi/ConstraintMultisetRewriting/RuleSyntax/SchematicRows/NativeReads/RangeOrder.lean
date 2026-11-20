import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.HeadRanges
import Mathlib.Data.List.Sort

/-! # The two binary bands enumerate each candidate exactly once in view order -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RangeOrder

open HeadRanges

theorem interval_ordered (low high : Nat) : (interval low high).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  exact List.pairwise_lt_range.imp (fun less => Nat.add_lt_add_left less low)

theorem two_runs_ordered (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size)
    (head arity : Nat) (rigid : 0 < head) : (twoRuns keys size head arity).Pairwise (· < ·) := by
  have keysOrdered : (toLex (1, 0) : HeadKey) ≤ toLex (head, arity) := by
    rw [Prod.Lex.toLex_le_toLex]
    by_cases one : head = 1
    · exact Or.inr ⟨one.symm, Nat.zero_le _⟩
    · exact Or.inl (by omega)
  have disjoint := lower_mono keys size sorted _ _ keysOrdered
  apply List.pairwise_append.mpr
  refine ⟨interval_ordered _ _, interval_ordered _ _, ?_⟩
  intro first a second b
  have left := (mem_interval _ _ _).mp a
  have right := (mem_interval _ _ _).mp b
  omega

def selected (keys : Nat → HeadKey) (size head arity : Nat) : List Nat :=
  if head = 0 then List.range size else twoRuns keys size head arity

theorem selected_ordered (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size) (head arity : Nat) :
    (selected keys size head arity).Pairwise (· < ·) := by
  by_cases openHead : head = 0
  · simpa only [selected, if_pos openHead] using List.pairwise_lt_range (n := size)
  · simpa only [selected, if_neg openHead] using two_runs_ordered keys size sorted head arity (by omega)

theorem selected_inside (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size)
    (head arity i : Nat) (member : i ∈ selected keys size head arity) : i < size := by
  by_cases openHead : head = 0
  · simpa only [selected, if_pos openHead, List.mem_range] using member
  · simp only [selected, if_neg openHead, twoRuns, List.mem_append, mem_interval] at member
    rcases member with unknown | rigid
    · exact unknown.2.trans_le (lower_bound keys size sorted _)
    · exact rigid.2.trans_le (upper_bound keys size sorted _)

theorem selected_exact_word (keys : Nat → HeadKey) (size : Nat) (sorted : Sorted keys size) (head arity : Nat) :
    selected keys size head arity = (List.range size).filter
      (fun i => decide (head = 0 ∨ (ofLex (keys i)).1 = 0 ∨ keys i = toLex (head, arity))) := by
  apply List.Pairwise.eq_of_mem_iff (selected_ordered keys size sorted head arity)
    (List.pairwise_lt_range.filter _)
  intro i
  constructor
  · intro member
    have inside := selected_inside keys size sorted head arity i member
    refine List.mem_filter.mpr ⟨List.mem_range.mpr inside, ?_⟩
    exact decide_eq_true ((selected_range_is_complete keys size sorted head arity i inside).mp member)
  · intro member
    obtain ⟨inside, accepted⟩ := List.mem_filter.mp member
    exact (selected_range_is_complete keys size sorted head arity i (List.mem_range.mp inside)).mpr
      (of_decide_eq_true accepted)

#print axioms two_runs_ordered
#print axioms selected_exact_word

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.RangeOrder
