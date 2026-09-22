import Mettapedia.Logic.HOL.Embedding.ZFSetList
import Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure

/-!
# Actual list codes inside naturally indexed closed universes

Finite constructor stages collect to exactly the independently encoded list
set. Replacement over a natural-index code places that set in the same
closed universe. A concrete seeded least universe supplies the premises.
The hereditarily finite universe supplies the negative control: it contains
the singleton element type and each finite list, but not its list type.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetListClosure

open ZFSetList ZFSetDependentProducts ZFSetUniverseClosure ZFSetIndexedClosure
open scoped ZFSet Ordinal

universe u

noncomputable def stage (a : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => {∅}
  | n + 1 => {∅} ∪ ZFSet.prod a (stage a n)

theorem stage_mem {U a : ZFSet.{u}} (closed : Closed U) (member : a ∈ U) :
    ∀ n, stage a n ∈ U := by
  intro n
  induction n with
  | zero => exact closed.singleton_mem (closed.empty_mem member)
  | succ n ih =>
      exact closed.binaryUnion_mem
        (closed.singleton_mem (closed.empty_mem member)) (closed.product_mem member ih)

theorem encode_mem_stage {a : ZFSet.{u}} (xs : List (Elements a)) :
    encode xs ∈ stage a xs.length := by
  induction xs with
  | nil => exact ZFSet.mem_singleton.mpr rfl
  | cons x xs ih =>
      exact ZFSet.mem_union.mpr (Or.inr (ZFSet.pair_mem_prod.mpr ⟨x.2, ih⟩))

theorem stage_subset_listCode (a : ZFSet.{u}) : ∀ n, stage a n ⊆ listCode a := by
  intro n
  induction n with
  | zero =>
      intro x member
      have equal := ZFSet.mem_singleton.mp member
      exact mem_listCode.mpr ⟨[], equal.symm⟩
  | succ n ih =>
      intro x member
      rcases ZFSet.mem_union.mp member with zero | cell
      · exact mem_listCode.mpr ⟨[], (ZFSet.mem_singleton.mp zero).symm⟩
      · obtain ⟨head, headMember, tail, tailMember, rfl⟩ := ZFSet.mem_prod.mp cell
        exact pair_mem_listCode.mpr ⟨headMember, ih tailMember⟩

theorem listCode_eq_union_stages (a : ZFSet.{u}) :
    listCode a = ZFSet.sUnion (ZFSet.range (stage a)) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨xs, rfl⟩ := mem_listCode.mp member
    exact ZFSet.mem_sUnion.mpr
      ⟨stage a xs.length, ZFSet.mem_range_self (f := stage a) xs.length, encode_mem_stage xs⟩
  · intro member
    obtain ⟨s, stageMember, inStage⟩ := ZFSet.mem_sUnion.mp member
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp stageMember
    exact stage_subset_listCode a n inStage

theorem listCode_mem {U a : ZFSet.{u}} (closed : Closed U) (member : a ∈ U)
    (indices : finiteRankIndex ∈ U) : listCode a ∈ U := by
  rw [listCode_eq_union_stages]
  exact nat_union_mem closed indices (stage a) (stage_mem closed member)

theorem listCode_mem_seeded_universe (h : CofinalInaccessibles.{u}) (a : ZFSet.{u}) :
    listCode a ∈ univOf h (seed a) :=
  listCode_mem (univOf_closed h (seed a)) (seed_contains_parameter h a)
    (seed_contains_indices h a)

/-! ## Finite closure alone does not admit the collecting datatype -/

private theorem tail_rank_lt_pair (head tail : ZFSet.{u}) :
    tail.rank < (ZFSet.pair head tail).rank :=
  (ZFSet.rank_lt_of_mem (show tail ∈ ({head, tail} : ZFSet.{u}) from
    ZFSet.mem_pair.mpr (Or.inr rfl))).trans
    (ZFSet.rank_lt_of_mem (show ({head, tail} : ZFSet.{u}) ∈ ZFSet.pair head tail from
      ZFSet.mem_pair.mpr (Or.inr rfl)))

noncomputable def zeroList : Nat → Elements (listCode ({∅} : ZFSet.{u}))
  | 0 => nil {∅}
  | n + 1 => cons ⟨∅, ZFSet.mem_singleton.mpr rfl⟩ (zeroList n)

theorem zeroList_rank (n : Nat) : (n : Ordinal.{u}) ≤ (zeroList n).1.rank := by
  induction n with
  | zero => exact zero_le
  | succ n ih =>
      exact (Order.succ_le_succ ih).trans
        (Order.succ_le_of_lt (tail_rank_lt_pair ∅ (zeroList n).1))

theorem singleton_mem_finite_universe :
    ({∅} : ZFSet.{u}) ∈ V_ (ω : Ordinal.{u}) :=
  finite_universe_closed.singleton_mem
    (by simpa only [finiteRank, Nat.cast_zero, ZFSet.vonNeumann_zero]
      using finiteRank_mem_finite_universe.{u} 0)

theorem singleton_listCode_not_mem_finite_universe :
    listCode ({∅} : ZFSet.{u}) ∉ V_ (ω : Ordinal.{u}) := by
  intro member
  obtain ⟨n, equal⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp member)
  have rankLess := ZFSet.rank_lt_of_mem (zeroList.{u} n).2
  rw [equal] at rankLess
  exact (not_lt_of_ge (zeroList_rank n)) rankLess

theorem closed_does_not_imply_list_closed :
    ∃ U a : ZFSet.{u}, Closed U ∧ a ∈ U ∧ listCode a ⊆ U ∧ listCode a ∉ U :=
  ⟨V_ (ω : Ordinal.{u}), {∅}, finite_universe_closed, singleton_mem_finite_universe,
    listCode_subset finite_universe_closed singleton_mem_finite_universe,
    singleton_listCode_not_mem_finite_universe⟩

#print axioms listCode_eq_union_stages
#print axioms listCode_mem
#print axioms listCode_mem_seeded_universe
#print axioms zeroList_rank
#print axioms closed_does_not_imply_list_closed

end Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
