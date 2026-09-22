import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts

/-!
# Indexed closure inside actual set universes

Replacement closes a universe under a small family when the index type has
an injective set coding whose range belongs to that universe. Finite rank
segments provide a concrete coding of natural indices. Its code can be
included in a universe seed independently of any later inductive datatype.
No closure under arbitrary externally small families is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts
open scoped ZFSet Cardinal Ordinal

universe u v

theorem range_mem_of_index {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} (closed : Closed U)
    (index : I → ZFSet.{u}) (injective : Function.Injective index)
    (indices : ZFSet.range index ∈ U)
    (f : I → ZFSet.{u}) (members : ∀ i, f i ∈ U) : ZFSet.range f ∈ U := by
  classical
  let decode : ZFSet.{u} → ZFSet.{u} := fun x =>
    if present : ∃ i, index i = x then f present.choose else ∅
  have atIndex (i : I) : decode (index i) = f i := by
    dsimp only [decode]
    rw [dif_pos ⟨i, rfl⟩]
    congr 1
    exact injective (Exists.choose_spec (show ∃ j, index j = index i from ⟨i, rfl⟩))
  have equality : replacement (ZFSet.range index) decode = ZFSet.range f := by
    apply ZFSet.ext
    intro x
    rw [mem_replacement, ZFSet.mem_range]
    constructor
    · rintro ⟨y, hy, equal⟩
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hy
      exact ⟨i, (atIndex i).symm.trans equal⟩
    · rintro ⟨i, rfl⟩
      exact ⟨index i, ZFSet.mem_range_self i, atIndex i⟩
  rw [← equality]
  apply closed.replacement_mem indices decode
  intro x hx
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hx
  rw [atIndex]
  exact members i

noncomputable def finiteRank (n : Nat) : ZFSet.{u} := V_ (n : Ordinal.{u})

theorem finiteRank_injective : Function.Injective finiteRank.{u} := by
  intro n m equal
  exact_mod_cast ZFSet.vonNeumann_injective equal

noncomputable def finiteRankIndex : ZFSet.{u} := ZFSet.range finiteRank

theorem nat_range_mem {U : ZFSet.{u}} (closed : Closed U)
    (indices : finiteRankIndex ∈ U) (f : Nat → ZFSet.{u})
    (members : ∀ n, f n ∈ U) : ZFSet.range f ∈ U :=
  range_mem_of_index closed finiteRank finiteRank_injective indices f members

theorem nat_union_mem {U : ZFSet.{u}} (closed : Closed U)
    (indices : finiteRankIndex ∈ U) (f : Nat → ZFSet.{u})
    (members : ∀ n, f n ∈ U) : ZFSet.sUnion (ZFSet.range f) ∈ U :=
  closed.union_mem (nat_range_mem closed indices f members)

/-- A concrete seed supports natural-indexed constructions. It does not
contain the datatype or recursively generated family that will be built. -/
noncomputable def seed (a : ZFSet.{u}) : ZFSet.{u} := {a, finiteRankIndex}

theorem seed_contains_parameter (h : CofinalInaccessibles.{u}) (a : ZFSet.{u}) :
    a ∈ univOf h (seed a) :=
  (univOf_closed h (seed a)).transitive _ (mem_univOf h (seed a))
    (ZFSet.mem_pair.mpr (Or.inl rfl))

theorem seed_contains_indices (h : CofinalInaccessibles.{u}) (a : ZFSet.{u}) :
    finiteRankIndex ∈ univOf h (seed a) :=
  (univOf_closed h (seed a)).transitive _ (mem_univOf h (seed a))
    (ZFSet.mem_pair.mpr (Or.inr rfl))

theorem seeded_nat_range_mem (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (f : Nat → ZFSet.{u}) (members : ∀ n, f n ∈ univOf h (seed a)) :
    ZFSet.range f ∈ univOf h (seed a) :=
  nat_range_mem (univOf_closed h (seed a)) (seed_contains_indices h a) f members

/-! ## Finite closure does not supply the natural index set -/

private theorem replacement_range (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    replacement a f = ZFSet.range
      (fun i : Shrink a => f ((equivShrink a).symm i).1) := by
  apply ZFSet.ext
  intro y
  rw [mem_replacement, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx, equal⟩
    refine ⟨equivShrink a ⟨x, hx⟩, ?_⟩
    simpa using equal
  · rintro ⟨i, equal⟩
    exact ⟨((equivShrink a).symm i).1, ((equivShrink a).symm i).2, equal⟩

private theorem finite_card {a : ZFSet.{u}} (member : a ∈ V_ (ω : Ordinal.{u})) :
    a.card < ℵ₀ := by
  calc
    a.card ≤ (V_ a.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self a)
    _ = Cardinal.preBeth a.rank := ZFSet.card_vonNeumann _
    _ < Cardinal.preBeth ω := Cardinal.preBeth_strictMono (ZFSet.mem_vonNeumann.mp member)
    _ = ℵ₀ := Cardinal.preBeth_omega

/-- Hereditarily finite sets satisfy exactly the existing closure record.
The record intentionally does not add an infinity axiom. -/
theorem finite_universe_closed : Closed (V_ (ω : Ordinal.{u})) where
  transitive := ZFSet.isTransitive_vonNeumann _
  union_mem member := ZFSet.mem_vonNeumann.mpr
    ((ZFSet.rank_sUnion_le _).trans_lt (ZFSet.mem_vonNeumann.mp member))
  power_mem member := by
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    exact Ordinal.isSuccLimit_omega0.succ_lt (ZFSet.mem_vonNeumann.mp member)
  replacement_mem member f values := by
    rw [ZFSet.mem_vonNeumann, replacement_range, ZFSet.rank_range]
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [← Cardinal.ord_aleph0, Cardinal.isRegular_aleph0.cof_ord]
      exact finite_card member
    · intro i
      exact Ordinal.isSuccLimit_omega0.succ_lt
        (ZFSet.mem_vonNeumann.mp (values _ ((equivShrink _).symm i).2))

theorem finiteRank_mem_finite_universe (n : Nat) :
    finiteRank.{u} n ∈ V_ (ω : Ordinal.{u}) :=
  ZFSet.vonNeumann_mem_of_lt (Ordinal.natCast_lt_omega0 n)

theorem finiteRankIndex_not_mem_finite_universe :
    finiteRankIndex.{u} ∉ V_ (ω : Ordinal.{u}) := by
  intro member
  obtain ⟨n, equal⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp member)
  have rankLess := ZFSet.rank_lt_of_mem
    (ZFSet.mem_range_self (f := finiteRank.{u}) n)
  rw [show (ZFSet.range finiteRank.{u}).rank = n from equal] at rankLess
  exact (lt_irrefl (n : Ordinal.{u}))
    (by simpa only [finiteRank, ZFSet.rank_vonNeumann] using rankLess)

/-- A closed universe contains every stage, but not their indexed range.
This is a counterexample to dropping the index-membership premise. -/
theorem indexed_closure_requires_more_than_Closed :
    ∃ U : ZFSet.{u}, Closed U ∧ (∀ n, finiteRank n ∈ U) ∧ finiteRankIndex ∉ U :=
  ⟨V_ (ω : Ordinal.{u}), finite_universe_closed, finiteRank_mem_finite_universe,
    finiteRankIndex_not_mem_finite_universe⟩

/-- Externally small indexing does not entail closure of an arbitrary set:
the singleton containing the empty set cannot contain this injective range. -/
theorem finiteRankIndex_not_in_singleton_empty :
    finiteRankIndex.{u} ∉ ({∅} : ZFSet.{u}) := by
  intro member
  have equal := ZFSet.mem_singleton.mp member
  have zero : finiteRank 0 ∈ finiteRankIndex.{u} := ZFSet.mem_range_self 0
  rw [equal] at zero
  exact ZFSet.notMem_empty _ zero

#print axioms range_mem_of_index
#print axioms finiteRank_injective
#print axioms nat_range_mem
#print axioms nat_union_mem
#print axioms seed_contains_parameter
#print axioms seed_contains_indices
#print axioms seeded_nat_range_mem
#print axioms finite_universe_closed
#print axioms finiteRankIndex_not_mem_finite_universe
#print axioms indexed_closure_requires_more_than_Closed
#print axioms finiteRankIndex_not_in_singleton_empty

end Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure
