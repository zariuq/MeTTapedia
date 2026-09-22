import Mettapedia.GSLT.GraphTheory.PartialPair

/-!
# Projection-coding obstruction

The exact raw coding expression inside the unfinished `WeakProduct` discards
opposite-component supports. These controls isolate that expression from the
record's admitted injectivity field; they construct no graph model or web.
-/

namespace Mettapedia.GSLT.GraphTheory.WeakProductControls

open Mettapedia.GSLT.Core

private def projectionCode (D₁ D₂ : GraphModel) :
    Finset (D₁.Carrier ⊕ D₂.Carrier) × (D₁.Carrier ⊕ D₂.Carrier) →
      D₁.Carrier ⊕ D₂.Carrier :=
  fun ⟨a, d⟩ => match d with
    | .inl d₁ => .inl (D₁.coding.code (projectLeft a, d₁))
    | .inr d₂ => .inr (D₂.coding.code (projectRight a, d₂))

/-- Opposite-component singleton support is erased by the actual expression. -/
theorem left_support_collision (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    projectionCode D₁ D₂ (∅, .inl x) =
      projectionCode D₁ D₂ ({Sum.inr y}, .inl x) := by
  apply congrArg (fun support : Finset D₁.Carrier =>
    Sum.inl (D₁.coding.code (support, x)))
  rw [PartialPair.projectLeft_eq_toLeft, PartialPair.projectLeft_eq_toLeft]
  ext value
  simp

theorem right_support_collision (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    projectionCode D₁ D₂ (∅, .inr y) =
      projectionCode D₁ D₂ ({Sum.inl x}, .inr y) := by
  apply congrArg (fun support : Finset D₂.Carrier =>
    Sum.inr (D₂.coding.code (support, y)))
  rw [PartialPair.projectRight_eq_toRight, PartialPair.projectRight_eq_toRight]
  ext value
  simp

/-- The inputs producing the left collision really are distinct. -/
theorem left_collision_inputs_differ (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    ((∅, Sum.inl x) : Finset (D₁.Carrier ⊕ D₂.Carrier) × (D₁.Carrier ⊕ D₂.Carrier)) ≠
      (({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)), Sum.inl x) := by
  intro h
  have hSets := congrArg Prod.fst h
  exact Finset.empty_ne_singleton _ hSets

theorem projection_code_not_injective (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    ¬Function.Injective (projectionCode D₁ D₂) := by
  intro h
  exact left_collision_inputs_differ D₁ D₂ x y (h (left_support_collision D₁ D₂ x y))

/-- The correct source partial pair retains each pure factor code. -/
theorem pure_left_code_is_defined (D₁ D₂ : GraphModel)
    (support : Finset D₁.Carrier) (output : D₁.Carrier) :
    PartialPair.disjointUnionCode D₁ D₂
      (support.map Function.Embedding.inl, .inl output) =
      some (.inl (D₁.coding.code (support, output))) :=
  PartialPair.disjointUnionCode_left D₁ D₂ support output

/-- The formerly erased singleton is undefined, not the empty-support code. -/
theorem opposite_support_is_undefined (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    PartialPair.disjointUnionCode D₁ D₂ ({Sum.inr y}, .inl x) = none :=
  PartialPair.disjointUnionCode_inl_none_of_inr_mem D₁ D₂ _ x y
    (Finset.mem_singleton_self (Sum.inr y))

/-- Source-defined coding distinguishes the collided inputs by definedness. -/
theorem source_partial_code_distinguishes_collision (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    PartialPair.disjointUnionCode D₁ D₂ (∅, .inl x) ≠
      PartialPair.disjointUnionCode D₁ D₂ ({Sum.inr y}, .inl x) := by
  have hDefined := PartialPair.disjointUnionCode_left D₁ D₂ ∅ x
  simp only [Finset.map_empty] at hDefined
  rw [hDefined, opposite_support_is_undefined]
  intro h
  cases h

theorem source_union_is_proper (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    (PartialPair.disjointUnion D₁ D₂).Proper :=
  PartialPair.disjointUnion_proper D₁ D₂ x y

end Mettapedia.GSLT.GraphTheory.WeakProductControls
