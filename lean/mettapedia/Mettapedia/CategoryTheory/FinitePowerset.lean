import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Prod

/-!
# Actual finite powersets and deterministic successor inclusion

The map is direct image of the complete finite successor set. State maps may
identify successors, so cardinality and occurrence receipts are not preserved.
The categorical functor laws are derived from finite-set image laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowerset

open _root_.CategoryTheory

universe u v w

def map {X : Type u} {Y : Type v} (mapping : X → Y) (successors : Finset X) :
    Finset Y := by
  classical
  exact successors.image mapping

@[simp] theorem mem_map {X : Type u} {Y : Type v} (mapping : X → Y)
    (successors : Finset X) (value : Y) :
    value ∈ map mapping successors ↔ ∃ input ∈ successors, mapping input = value := by
  classical
  exact Finset.mem_image

@[simp] theorem map_identity {X : Type u} (successors : Finset X) :
    map id successors = successors := by
  classical
  exact Finset.image_id

theorem map_compose {X : Type u} {Y : Type v} {Z : Type w}
    (before : X → Y) (after : Y → Z) (successors : Finset X) :
    map after (map before successors) = map (after ∘ before) successors := by
  classical
  exact Finset.image_image

def functor : Type u ⥤ Type u where
  obj := Finset
  map mapping := TypeCat.ofHom (map mapping.hom)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact map_identity
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro successors
    exact (map_compose before.hom after.hom successors).symm

@[simp] theorem map_empty {X : Type u} {Y : Type v} (mapping : X → Y) :
    map mapping ∅ = ∅ := by
  classical
  change Finset.image mapping (∅ : Finset X) = ∅
  exact Finset.image_empty mapping

@[simp] theorem map_singleton {X : Type u} {Y : Type v} (mapping : X → Y) (value : X) :
    map mapping {value} = {mapping value} := by
  classical
  change Finset.image mapping {value} = {mapping value}
  exact Finset.image_singleton mapping value

theorem map_eq_empty_iff {X : Type u} {Y : Type v}
    (mapping : X → Y) (successors : Finset X) :
    map mapping successors = ∅ ↔ successors = ∅ := by
  classical
  exact Finset.image_eq_empty

theorem map_option {X : Type u} {Y : Type v} (mapping : X → Y) (value : Option X) :
    map mapping value.toFinset = (value.map mapping).toFinset := by
  cases value with
  | none => exact map_empty mapping
  | some value => exact map_singleton mapping value

theorem option_injective {X : Type u} :
    Function.Injective (Option.toFinset : Option X → Finset X) := by
  classical
  intro first second same
  cases first <;> cases second <;> simp_all

/-- Complete forward and backward coverage, retaining both sets. -/
def Related {X : Type u} {Y : Type v} (relation : X → Y → Prop)
    (first : Finset X) (second : Finset Y) : Prop :=
  (∀ value ∈ first, ∃ other ∈ second, relation value other) ∧
    (∀ other ∈ second, ∃ value ∈ first, relation value other)

theorem related_identity {X : Type u} (successors : Finset X) :
    Related Eq successors successors := by
  constructor <;> intro value member <;> exact ⟨value, member, rfl⟩

theorem related_compose {X : Type u} {Y : Type v} {Z : Type w}
    {before : X → Y → Prop} {after : Y → Z → Prop}
    {first : Finset X} {middle : Finset Y} {last : Finset Z}
    (earlier : Related before first middle) (later : Related after middle last) :
    Related (fun value result => ∃ other, before value other ∧ after other result)
      first last := by
  constructor
  · intro value member
    obtain ⟨other, inMiddle, relatedBefore⟩ := earlier.1 value member
    obtain ⟨result, inLast, relatedAfter⟩ := later.1 other inMiddle
    exact ⟨result, inLast, other, relatedBefore, relatedAfter⟩
  · intro result member
    obtain ⟨other, inMiddle, relatedAfter⟩ := later.2 result member
    obtain ⟨value, inFirst, relatedBefore⟩ := earlier.2 other inMiddle
    exact ⟨value, inFirst, other, relatedBefore, relatedAfter⟩

theorem related_graph_iff {X : Type u} {Y : Type v} (mapping : X → Y)
    (first : Finset X) (second : Finset Y) :
    Related (fun value other => mapping value = other) first second ↔
      map mapping first = second := by
  constructor
  · intro held
    apply Finset.ext
    intro other
    rw [mem_map]
    constructor
    · rintro ⟨value, inFirst, rfl⟩
      obtain ⟨result, inSecond, same⟩ := held.1 value inFirst
      simpa only [← same] using inSecond
    · intro inSecond
      exact held.2 other inSecond
  · intro same
    constructor
    · intro value inFirst
      refine ⟨mapping value, ?_, rfl⟩
      rw [← same, mem_map]
      exact ⟨value, inFirst, rfl⟩
    · intro other inSecond
      rw [← same, mem_map] at inSecond
      exact inSecond

end Mettapedia.CategoryTheory.FinitePowerset
