import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGround

/-!
# The literal ordering is the Bachmair–Ganzinger multiset ordering

Bachmair and Ganzinger compare literals through multisets of terms: `s ≈ t` is `{s, t}` and
`s ≉ t` is `{s, s, t, t}`, ordered by the Dershowitz–Manna extension of the term ordering. On
oriented literals this is exactly the lexicographic ordering of `Lit` (larger side, then sign, then
smaller side): `lt_iff_multiset`. The clause ordering `ClauseLT`, the multiset extension of the
literal ordering, is therefore their clause ordering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

namespace Lit

variable {T : Type*} [LinearOrder T]

/-- **The Bachmair–Ganzinger multiset of a literal.** -/
def multiset (L : Lit T) : Multiset T :=
  if L.negative = true then L.lhs ::ₘ L.lhs ::ₘ L.rhs ::ₘ L.rhs ::ₘ 0 else L.lhs ::ₘ L.rhs ::ₘ 0

theorem multiset_of_negative {L : Lit T} (negative : L.negative = true) :
    L.multiset = L.lhs ::ₘ L.lhs ::ₘ L.rhs ::ₘ L.rhs ::ₘ 0 := if_pos negative

theorem multiset_of_positive {L : Lit T} (positive : L.negative = false) :
    L.multiset = L.lhs ::ₘ L.rhs ::ₘ 0 := if_neg (by rw [positive]; decide)

theorem mem_multiset {L : Lit T} {y : T} (member : y ∈ L.multiset) : y = L.lhs ∨ y = L.rhs := by
  unfold multiset at member
  split_ifs at member <;> simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member <;>
    tauto

theorem lhs_mem_multiset (L : Lit T) : L.lhs ∈ L.multiset := by
  unfold multiset
  split_ifs <;> exact Multiset.mem_cons_self _ _

theorem multiset_ne_zero (L : Lit T) : L.multiset ≠ 0 :=
  fun zero => Multiset.notMem_zero _ (zero ▸ lhs_mem_multiset L)

/-- A literal below another lies below it in the multiset ordering. -/
theorem dm_of_lt {L M : Lit T} (lt : L < M) : L.multiset.IsDershowitzMannaLT M.multiset := by
  rcases lt_iff.mp lt with larger | ⟨same, sign | ⟨sign, smaller⟩⟩
  · refine dm_of_all_below _ _ (multiset_ne_zero M) fun y member => ⟨M.lhs, lhs_mem_multiset M, ?_⟩
    rcases mem_multiset member with rfl | rfl
    · exact larger
    · exact L.oriented.trans_lt larger
  · obtain ⟨positive, negative⟩ := bool_lt_iff.mp sign
    rw [multiset_of_positive positive, multiset_of_negative negative, same]
    rcases L.oriented.lt_or_eq with below | equal
    · have step := dm_intro (M.lhs ::ₘ 0) (L.rhs ::ₘ 0) (M.lhs ::ₘ M.rhs ::ₘ M.rhs ::ₘ 0)
        Multiset.cons_ne_zero fun y member => ⟨M.lhs, Multiset.mem_cons_self _ _, by
          rw [Multiset.mem_singleton.mp member, ← same]
          exact below⟩
      simpa only [Multiset.cons_add, zero_add] using step
    · have step := dm_intro (M.lhs ::ₘ M.lhs ::ₘ 0) 0 (M.rhs ::ₘ M.rhs ::ₘ 0) Multiset.cons_ne_zero
        fun y member => absurd member (Multiset.notMem_zero y)
      rw [equal, same]
      simpa only [Multiset.cons_add, zero_add, add_zero] using step
  · cases signL : L.negative
    · have signM : M.negative = false := sign ▸ signL
      rw [multiset_of_positive signL, multiset_of_positive signM, same]
      have step := dm_intro (M.lhs ::ₘ 0) (L.rhs ::ₘ 0) (M.rhs ::ₘ 0) Multiset.cons_ne_zero
        fun y member => ⟨M.rhs, Multiset.mem_cons_self _ _, by rw [Multiset.mem_singleton.mp member]; exact smaller⟩
      simpa only [Multiset.cons_add, zero_add] using step
    · have signM : M.negative = true := sign ▸ signL
      rw [multiset_of_negative signL, multiset_of_negative signM, same]
      have step := dm_intro (M.lhs ::ₘ M.lhs ::ₘ 0) (L.rhs ::ₘ L.rhs ::ₘ 0) (M.rhs ::ₘ M.rhs ::ₘ 0)
        Multiset.cons_ne_zero fun y member => ⟨M.rhs, Multiset.mem_cons_self _ _, by
          rcases Multiset.mem_cons.mp member with rfl | rest
          · exact smaller
          · rw [Multiset.mem_singleton.mp rest]
            exact smaller⟩
      simpa only [Multiset.cons_add, zero_add] using step

/-- **The literal ordering is the Bachmair–Ganzinger multiset ordering.** -/
theorem lt_iff_multiset [WellFoundedLT T] (L M : Lit T) :
    L < M ↔ L.multiset.IsDershowitzMannaLT M.multiset := by
  refine ⟨dm_of_lt, fun dm => ?_⟩
  rcases lt_trichotomy L M with lt | rfl | gt
  · exact lt
  · exact absurd dm (dm_irrefl _)
  · exact absurd ((dm_of_lt gt).trans dm) (dm_irrefl _)

end Lit

#print axioms Lit.mem_multiset
#print axioms Lit.dm_of_lt
#print axioms Lit.lt_iff_multiset

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
