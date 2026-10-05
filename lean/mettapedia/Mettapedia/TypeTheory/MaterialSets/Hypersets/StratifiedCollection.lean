import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLiftCoherence

/-!
# Constructed relational collection at explicit universe bounds

Collecting every witness of a relation requires no choice of one witness per
argument. At the successor graph bound, the complete smaller material carrier
has a uniform presentation. We use it to construct all-witness collection for
arbitrary smaller-valued relations, including relations whose values have no
supplied common bound. Functional replacement is a special case.

When an original material bound is available, separation constructs collection
at that original level, and its lift agrees with the successor construction.
The unrestricted construction returns a larger material set. It is not a proof
of a fixed-level collection schema. The unrestricted true relation illustrates
the distinction: its all-witness collection is the complete smaller carrier,
which cannot be a lifted smaller set.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

universe u

/-- All witnesses are collected from an actual uniform presentation. No
relation witness or presentation selector is an input to the construction. -/
def collectionUp {I : Type (u + 1)} (relation : I → HSet.{u} → Prop) :
    HSet.{u + 1} :=
  imageUp (fun witness : Σ index : I, {y : HSet.{u} // relation index y} =>
    witness.2.val)

theorem mem_collectionUp_iff {I : Type (u + 1)}
    {relation : I → HSet.{u} → Prop} {z : HSet.{u + 1}} :
    z ∈ collectionUp relation ↔ ∃ index y, relation index y ∧ lift y = z := by
  rw [collectionUp, mem_imageUp_iff]
  constructor
  · rintro ⟨⟨index, y, related⟩, same⟩
    exact ⟨index, y, related, same⟩
  · rintro ⟨index, y, related, same⟩
    exact ⟨⟨index, y, related⟩, same⟩

@[simp] theorem lift_mem_collectionUp_iff {I : Type (u + 1)}
    {relation : I → HSet.{u} → Prop} {y : HSet.{u}} :
    lift y ∈ collectionUp relation ↔ ∃ index, relation index y := by
  rw [mem_collectionUp_iff]
  constructor
  · rintro ⟨index, z, related, same⟩
    exact ⟨index, lift_injective same ▸ related⟩
  · rintro ⟨index, related⟩
    exact ⟨index, y, related, rfl⟩

/-- Both clauses of strong collection hold for the actual constructed set.
The totality premise is the relation's hypothesis, not construction data. -/
theorem strong_collection_at_successor {I : Type (u + 1)}
    (relation : I → HSet.{u} → Prop)
    (total : ∀ index, ∃ y, relation index y) :
    (∀ index, ∃ y, relation index y ∧ lift y ∈ collectionUp relation) ∧
      (∀ z ∈ collectionUp relation,
        ∃ index y, relation index y ∧ lift y = z) := by
  constructor
  · intro index
    obtain ⟨y, related⟩ := total index
    exact ⟨y, related, lift_mem_collectionUp_iff.mpr ⟨index, related⟩⟩
  · intro z member
    exact mem_collectionUp_iff.mp member

theorem exists_strong_collection_at_successor {I : Type (u + 1)}
    (relation : I → HSet.{u} → Prop)
    (total : ∀ index, ∃ y, relation index y) :
    ∃ collected : HSet.{u + 1},
      (∀ index, ∃ y, relation index y ∧ lift y ∈ collected) ∧
      (∀ z ∈ collected, ∃ index y, relation index y ∧ lift y = z) :=
  ⟨collectionUp relation, strong_collection_at_successor relation total⟩

theorem collectionUp_subset_smallerCarrier {I : Type (u + 1)}
    (relation : I → HSet.{u} → Prop) :
    collectionUp relation ⊆ smallerCarrier.{u} := by
  intro z member
  obtain ⟨_, y, _, same⟩ := mem_collectionUp_iff.mp member
  exact mem_smallerCarrier_iff.mpr ⟨y, same⟩

theorem collectionUp_mono {I : Type (u + 1)}
    {first second : I → HSet.{u} → Prop}
    (implies : ∀ index y, first index y → second index y) :
    collectionUp first ⊆ collectionUp second := by
  intro z member
  obtain ⟨index, y, related, same⟩ := mem_collectionUp_iff.mp member
  exact mem_collectionUp_iff.mpr ⟨index, y, implies index y related, same⟩

/-- Collection after substitution has exactly the substituted index image. -/
theorem mem_collectionUp_reindex_iff {I J : Type (u + 1)}
    (relation : I → HSet.{u} → Prop) (σ : J → I) (z : HSet.{u + 1}) :
    z ∈ collectionUp (fun j => relation (σ j)) ↔
      ∃ j y, relation (σ j) y ∧ lift y = z := mem_collectionUp_iff

theorem collectionUp_reindex_subset {I J : Type (u + 1)}
    (relation : I → HSet.{u} → Prop) (σ : J → I) :
    collectionUp (fun j => relation (σ j)) ⊆ collectionUp relation := by
  intro z member
  obtain ⟨j, y, related, same⟩ := mem_collectionUp_iff.mp member
  exact mem_collectionUp_iff.mpr ⟨σ j, y, related, same⟩

theorem collectionUp_reindex_eq {I J : Type (u + 1)}
    (relation : I → HSet.{u} → Prop) (σ : J → I)
    (surjective : Function.Surjective σ) :
    collectionUp (fun j => relation (σ j)) = collectionUp relation := by
  ext z
  constructor
  · intro member
    exact collectionUp_reindex_subset relation σ member
  · intro member
    obtain ⟨i, y, related, same⟩ := mem_collectionUp_iff.mp member
    obtain ⟨j, mapped⟩ := surjective i
    exact mem_collectionUp_iff.mpr ⟨j, y, mapped.symm ▸ related, same⟩

/-- Replacement of an arbitrary actual smaller-valued function is an
instance of relational collection, with the very same constructed image. -/
theorem collectionUp_function_graph {I : Type (u + 1)} (family : I → HSet.{u}) :
    collectionUp (fun index y => y = family index) = imageUp family := by
  ext z
  rw [mem_collectionUp_iff, mem_imageUp_iff]
  constructor
  · rintro ⟨index, y, rfl, same⟩
    exact ⟨index, same⟩
  · rintro ⟨index, same⟩
    exact ⟨index, family index, rfl, same⟩

/-! ## Original-level collection below an actual material bound -/

def boundedCollection {I : Type (u + 1)} (bound : HSet.{u})
    (relation : I → HSet.{u} → Prop) : HSet.{u} :=
  HSet.sep (fun y => ∃ index, relation index y) bound

theorem mem_boundedCollection_iff {I : Type (u + 1)}
    {bound : HSet.{u}} {relation : I → HSet.{u} → Prop} {y : HSet.{u}} :
    y ∈ boundedCollection bound relation ↔ y ∈ bound ∧ ∃ index, relation index y :=
  mem_sep

theorem strong_bounded_collection {I : Type (u + 1)} (bound : HSet.{u})
    (relation : I → HSet.{u} → Prop)
    (total : ∀ index, ∃ y ∈ bound, relation index y) :
    (∀ index, ∃ y, relation index y ∧ y ∈ boundedCollection bound relation) ∧
      (∀ y ∈ boundedCollection bound relation, ∃ index, relation index y) := by
  constructor
  · intro index
    obtain ⟨y, member, related⟩ := total index
    exact ⟨y, related, mem_boundedCollection_iff.mpr ⟨member, index, related⟩⟩
  · intro y member
    exact (mem_boundedCollection_iff.mp member).2

/-- A proved original bound removes the universe increase. The original
set is constructed by separation; no collecting set is assumed. -/
theorem lift_boundedCollection_eq_collectionUp {I : Type (u + 1)}
    (bound : HSet.{u}) (relation : I → HSet.{u} → Prop)
    (bounded : ∀ index y, relation index y → y ∈ bound) :
    lift (boundedCollection bound relation) = collectionUp relation := by
  ext z
  rw [mem_lift_iff, mem_collectionUp_iff]
  constructor
  · rintro ⟨y, member, same⟩
    obtain ⟨_, index, related⟩ := mem_boundedCollection_iff.mp member
    exact ⟨index, y, related, same⟩
  · rintro ⟨index, y, related, same⟩
    exact ⟨y, mem_boundedCollection_iff.mpr ⟨bounded index y related, index, related⟩, same⟩

/-! ## A deterministic material witness operation for functional relations -/

/-- Union of the all-witness row is defined before existence or uniqueness
is proved. For an inhabited unique row it returns its lifted witness. -/
def uniqueWitnessUp (relation : HSet.{u} → Prop) : HSet.{u + 1} :=
  sUnion (imageUp (fun witness : {y : HSet.{u} // relation y} => witness.val))

theorem uniqueWitnessUp_eq_lift {relation : HSet.{u} → Prop} {witness : HSet.{u}}
    (related : relation witness)
    (unique : ∀ y, relation y → y = witness) :
    uniqueWitnessUp relation = lift witness := by
  have row : imageUp (fun y : {y : HSet.{u} // relation y} => y.val) = {lift witness} := by
    ext z
    rw [mem_imageUp_iff, mem_singleton]
    constructor
    · rintro ⟨⟨y, proof⟩, same⟩
      exact same.symm.trans (congrArg lift (unique y proof))
    · intro same
      exact ⟨⟨witness, related⟩, same.symm⟩
  rw [uniqueWitnessUp, row, sUnion_singleton]

/-- Unique relational witnesses become an actual larger-valued material
function; existence is used only in the proposition proving its correctness. -/
theorem uniqueWitnessUp_spec {I : Type (u + 1)}
    (relation : I → HSet.{u} → Prop)
    (total : ∀ index, ∃! y, relation index y) (index : I) :
    ∃ y, relation index y ∧ uniqueWitnessUp (relation index) = lift y := by
  obtain ⟨y, related, unique⟩ := total index
  exact ⟨y, related, uniqueWitnessUp_eq_lift related unique⟩

/-! ## Discriminating controls -/

namespace CollectionControls

theorem no_witnesses : collectionUp (fun (_ : ULift.{u + 1, 0} PUnit.{1}) (_ : HSet.{u}) => False) = ∅ := by
  apply eq_empty_iff.mpr
  intro z member
  obtain ⟨_, _, impossible, _⟩ := mem_collectionUp_iff.mp member
  exact impossible

/-- Unrestricted collection may need the displayed universe increase.
This is a counterexample about this all-witness construction, not an
impossibility assertion about every possible collecting subset. -/
theorem true_relation_collects_smallerCarrier :
    collectionUp (fun (_ : ULift.{u + 1, 0} PUnit.{1}) (_ : HSet.{u}) => True) =
      smallerCarrier.{u} := by
  ext z
  rw [mem_collectionUp_iff, mem_smallerCarrier_iff]
  exact ⟨fun ⟨_, y, _, same⟩ => ⟨y, same⟩,
    fun ⟨y, same⟩ => ⟨⟨PUnit.unit⟩, y, True.intro, same⟩⟩

theorem true_relation_collection_not_lifted :
    ¬ ∃ X : HSet.{u}, lift X =
      collectionUp (fun (_ : ULift.{u + 1, 0} PUnit.{1}) (_ : HSet.{u}) => True) := by
  rw [true_relation_collects_smallerCarrier]
  exact smallerCarrier_not_lifted

/-- A non-well-founded unique witness is recovered by the same operation. -/
theorem quine_witness : uniqueWitnessUp (fun y : HSet.{u} => y = quineAtom) =
    quineAtom.{u + 1} := by
  exact (uniqueWitnessUp_eq_lift (relation := fun y : HSet.{u} => y = quineAtom)
    rfl (fun _ same => same)).trans lift_quineAtom

end CollectionControls

#print axioms strong_collection_at_successor
#print axioms strong_bounded_collection
#print axioms lift_boundedCollection_eq_collectionUp
#print axioms uniqueWitnessUp_spec
#print axioms CollectionControls.true_relation_collection_not_lifted

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet
