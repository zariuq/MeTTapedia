import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassMembers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel

/-!
# Actual set-indexed anti-foundation at the original graph bound

Every relation on the members of any material set has a unique decoration
into the same hyperset carrier. The member type lives a level above the graph
bound, but a supplied graph's full nonempty observation fibres give an actual
small carrier and inverse member map. A presentation of the indexing set is
used only inside the proposition proving existence; no uniform presentation
selector or inverse of an arbitrary surjection is assumed.

This proves the set-indexed decoration principle, including its infinite
natural-set instance. It does not construct original-bound Collection for
arbitrary material-valued relations. Plain membership decoration also does
not retain an indexing state's identity or an undeclared observable label.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation

universe u v

def IsDecoration {Index : Type v} (relation : Index → Index → Prop)
    (reading : Index → HSet.{u}) : Prop :=
  ∀ parent value, value ∈ reading parent ↔
    ∃ child, relation parent child ∧ reading child = value

section Transport

variable {SmallIndex : Type u} {Index : Type v}
variable (comparison : SmallIndex ≃ Index) (relation : Index → Index → Prop)

def pulledRelation (first second : SmallIndex) : Prop :=
  relation (comparison first) (comparison second)

def transportedDecoration (index : Index) : HSet.{u} :=
  HSet.decorate (pulledRelation comparison relation) (comparison.symm index)

theorem transportedDecoration_law :
    IsDecoration relation (transportedDecoration comparison relation) := by
  intro parent value
  refine HSet.mem_decorate.trans ?_
  constructor
  · rintro ⟨child, connected, same⟩
    refine ⟨comparison child, ?_, ?_⟩
    · exact comparison.apply_symm_apply parent ▸ connected
    · change HSet.decorate (pulledRelation comparison relation)
        (comparison.symm (comparison child)) = value
      rw [comparison.symm_apply_apply]
      exact same
  · rintro ⟨child, connected, same⟩
    refine ⟨comparison.symm child, ?_, same⟩
    change relation (comparison (comparison.symm parent))
      (comparison (comparison.symm child))
    rw [comparison.apply_symm_apply, comparison.apply_symm_apply]
    exact connected

theorem transportedDecoration_unique {reading : Index → HSet.{u}}
    (decorates : IsDecoration relation reading) :
    reading = transportedDecoration comparison relation := by
  have smallLaw : HSet.IsDecoration (pulledRelation comparison relation)
      (fun index => reading (comparison index)) := by
    intro parent value
    refine (decorates (comparison parent) value).trans ?_
    constructor
    · rintro ⟨child, connected, same⟩
      refine ⟨comparison.symm child, ?_, ?_⟩
      · change relation (comparison parent) (comparison (comparison.symm child))
        rw [comparison.apply_symm_apply]
        exact connected
      · change reading (comparison (comparison.symm child)) = value
        rw [comparison.apply_symm_apply]
        exact same
    · rintro ⟨child, connected, same⟩
      exact ⟨comparison child, connected, same⟩
  funext index
  have actual := congrFun smallLaw.eq_decorate (comparison.symm index)
  rw [comparison.apply_symm_apply] at actual
  exact actual

include comparison in
theorem existsUnique_of_smallComparison :
    ∃! reading : Index → HSet.{u}, IsDecoration relation reading :=
  ⟨transportedDecoration comparison relation, transportedDecoration_law comparison relation,
    fun _ law => transportedDecoration_unique comparison relation law⟩

end Transport

def Members (domain : HSet.{u}) := {value : HSet.{u} // value ∈ domain}

/-- The complete set-indexed principle on the actual material carrier.
The collecting graph bound and the target hyperset bound are unchanged. -/
theorem existsUnique_setDecoration (domain : HSet.{u})
    (relation : Members domain → Members domain → Prop) :
    ∃! reading : Members domain → HSet.{u}, IsDecoration relation reading := by
  revert relation
  induction domain using HSet.ind with
  | mk graph =>
    rw [← AccessiblePointedGraph.picture_eq_mk graph]
    intro relation
    exact existsUnique_of_smallComparison (AccessiblePointedGraph.powerMemberEquiv graph) relation

/-- An actual infinite set-indexed relation needs no additional coalgebra
existence field or chosen small presentation. -/
theorem existsUnique_naturalDecoration
    (relation : Members NaturalOrdinalModel.naturals.{u} →
      Members NaturalOrdinalModel.naturals.{u} → Prop) :
    ∃! reading : Members NaturalOrdinalModel.naturals.{u} → HSet.{u},
      IsDecoration relation reading :=
  existsUnique_setDecoration NaturalOrdinalModel.naturals relation

namespace Controls

/-- No successors gives the empty value at every source, regardless of
which source member supplied its identity. -/
theorem childless (domain : HSet.{u}) :
    IsDecoration (fun _ _ : Members domain => False) (fun _ => (∅ : HSet.{u})) := by
  intro parent value
  constructor
  · exact fun belongs => (HSet.notMem_empty value belongs).elim
  · rintro ⟨child, impossible, _⟩
    exact impossible.elim

theorem selfLoops (domain : HSet.{u}) :
    IsDecoration (fun first second : Members domain => first = second)
      (fun _ => HSet.quineAtom.{u}) := by
  intro parent value
  refine HSet.mem_quineAtom.trans ?_
  constructor
  · intro same
    exact ⟨parent, rfl, same.symm⟩
  · rintro ⟨child, _, same⟩
    exact same.symm

def twoSources : HSet.{u} := {∅, {∅}}

def zeroSource : Members twoSources.{u} := ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩

def oneSource : Members twoSources.{u} := ⟨{∅}, HSet.mem_pair.mpr (Or.inr rfl)⟩

theorem source_identity_distinguished : zeroSource.{u} ≠ oneSource :=
  fun same => HSet.empty_ne_singleton_empty (congrArg Subtype.val same)

/-- Exact negative control for source-identity recovery from a plain
membership observation: distinct self-looping indices have equal values. -/
theorem source_identity_erased : ∃ reading : Members twoSources.{u} → HSet.{u},
    IsDecoration (fun first second => first = second) reading ∧
      zeroSource ≠ oneSource ∧ reading zeroSource = reading oneSource :=
  ⟨fun _ => HSet.quineAtom, selfLoops twoSources, source_identity_distinguished, rfl⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation
