import Mettapedia.GSLT.GraphTheory.WeakProduct
import Mettapedia.GSLT.Core.WebSemanticsControls

/-!
# Projection-coding obstruction

Projection-only coding discards opposite-component supports and is not
injective. The actual canonical weak product distinguishes those inputs,
codes mixed supports outside the original factors, and preserves the native
lambda identity's distinct arguments.
-/

namespace Mettapedia.GSLT.GraphTheory.WeakProductControls

open Mettapedia.GSLT.Core

noncomputable local instance (D₁ D₂ : GraphModel) : DecidableEq (D₁ ◇ D₂).Carrier :=
  Classical.decEq _

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

/-- The canonical completion preserves the support erased by projection coding. -/
theorem completed_mixed_support_distinguished (D₁ D₂ : GraphModel)
    (left : D₁.Carrier) (right : D₂.Carrier) :
    (D₁ ◇ D₂).code (∅ : Finset (D₁ ◇ D₂).Carrier) (WeakProduct.leftEmbedding D₁ D₂ left) ≠
      (D₁ ◇ D₂).code ({WeakProduct.rightEmbedding D₁ D₂ right} : Finset (D₁ ◇ D₂).Carrier)
        (WeakProduct.leftEmbedding D₁ D₂ left) := by
  intro equality
  have inputs := (D₁ ◇ D₂).coding.injective equality
  exact Finset.empty_ne_singleton _ (congrArg Prod.fst inputs)

/-- A mixed code does not collapse into the original left factor. -/
theorem completed_mixed_code_outside_left (D₁ D₂ : GraphModel)
    (left : D₁.Carrier) (right : D₂.Carrier) (token : D₁.Carrier) :
    (D₁ ◇ D₂).code ({WeakProduct.rightEmbedding D₁ D₂ right} : Finset (D₁ ◇ D₂).Carrier)
        (WeakProduct.leftEmbedding D₁ D₂ left) ≠ WeakProduct.leftEmbedding D₁ D₂ token := by
  intro equality
  obtain ⟨support, output, _, supports, _⟩ :=
    (WeakProduct.code_eq_left_iff D₁ D₂ _ _ token).mp equality
  have member : WeakProduct.rightEmbedding D₁ D₂ right ∈
      support.map (WeakProduct.leftEmbedding D₁ D₂) :=
    supports ▸ Finset.mem_singleton_self _
  obtain ⟨value, _, equal⟩ := Finset.mem_map.mp member
  exact WeakProduct.left_ne_right D₁ D₂ value right equal

/-- A mixed code does not collapse into the original right factor either. -/
theorem completed_mixed_code_outside_right (D₁ D₂ : GraphModel)
    (left : D₁.Carrier) (right : D₂.Carrier) (token : D₂.Carrier) :
    (D₁ ◇ D₂).code ({WeakProduct.rightEmbedding D₁ D₂ right} : Finset (D₁ ◇ D₂).Carrier)
        (WeakProduct.leftEmbedding D₁ D₂ left) ≠ WeakProduct.rightEmbedding D₁ D₂ token := by
  intro equality
  obtain ⟨_, output, _, _, outputs⟩ :=
    (WeakProduct.code_eq_right_iff D₁ D₂ _ _ token).mp equality
  exact WeakProduct.left_ne_right D₁ D₂ left output outputs

/-- The existing lambda interpreter, applied to identity, retains distinct
arguments from the actual completed factors. -/
theorem native_identity_distinguishes_factors (D₁ D₂ : GraphModel)
    (left : D₁.Carrier) (right : D₂.Carrier) (environment : Env (D₁ ◇ D₂)) :
    (D₁ ◇ D₂).apply (interpret (D₁ ◇ D₂) environment LambdaTerm.I)
        {WeakProduct.leftEmbedding D₁ D₂ left} ≠
      (D₁ ◇ D₂).apply (interpret (D₁ ◇ D₂) environment LambdaTerm.I)
        {WeakProduct.rightEmbedding D₁ D₂ right} := by
  rw [interpret_I]
  exact (D₁ ◇ D₂).identity_distinguishes_inputs _ _ (WeakProduct.left_ne_right D₁ D₂ left right)

end Mettapedia.GSLT.GraphTheory.WeakProductControls
