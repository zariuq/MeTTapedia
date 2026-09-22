import Mettapedia.GSLT.GraphTheory.PartialPairCompletionStep

/-!
# Canonical-successor controls

The source disjoint union supplies both defined pure inputs and undefined
mixed inputs. Its successor preserves the former and fills the latter with
distinct tokens carrying their entire old inputs. Further inputs using those
fresh tokens are still undefined.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStepControls

open Mettapedia.GSLT.Core CompletionStep

private def opposite (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    Missing (disjointUnion D₁ D₂) :=
  ⟨(({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)), Sum.inl x),
    disjointUnionCode_inl_none_of_inr_mem D₁ D₂ _ x y
      (Finset.mem_singleton_self (Sum.inr y))⟩

private def mixed (D₁ D₂ : GraphModel) (x : D₁.Carrier) (y : D₂.Carrier) :
    Missing (disjointUnion D₁ D₂) :=
  ⟨(({Sum.inl x, Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)), Sum.inl x),
    disjointUnionCode_inl_none_of_inr_mem D₁ D₂ _ x y (by simp)⟩

theorem pure_factor_code_preserved (D₁ D₂ : GraphModel)
    (support : Finset D₁.Carrier) (x : D₁.Carrier) :
    code (disjointUnion D₁ D₂)
      ((support.map Function.Embedding.inl).map Function.Embedding.inl,
        Sum.inl (Sum.inl x)) =
      some (.inl (.inl (D₁.coding.code (support, x)))) :=
  code_preserves_defined (disjointUnion D₁ D₂) _ _ _
    (disjointUnionCode_left D₁ D₂ support x)

theorem formerly_missing_input_filled (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    code (disjointUnion D₁ D₂)
      (({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map Function.Embedding.inl,
        Sum.inl (Sum.inl x)) = some (.inr (opposite D₁ D₂ x y)) :=
  code_fills_missing (disjointUnion D₁ D₂) _ _ (opposite D₁ D₂ x y).property

theorem mixed_full_input_filled (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    code (disjointUnion D₁ D₂)
      (({Sum.inl x, Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map
        Function.Embedding.inl, Sum.inl (Sum.inl x)) =
      some (.inr (mixed D₁ D₂ x y)) :=
  code_fills_missing (disjointUnion D₁ D₂) _ _ (mixed D₁ D₂ x y).property

/-- Two missing inputs with different full supports cannot share a fresh token. -/
theorem fresh_tokens_retain_full_support (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    (Sum.inr (opposite D₁ D₂ x y) : CompletionStep.Carrier (disjointUnion D₁ D₂)) ≠
      Sum.inr (mixed D₁ D₂ x y) := by
  intro h
  have hSupports := congrArg (fun input => input.val.1) (Sum.inr.inj h)
  change ({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)) = {Sum.inl x, Sum.inr y}
    at hSupports
  have hMember : Sum.inl x ∈ ({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)) := by
    rw [hSupports]
    simp
  have hTags := Finset.mem_singleton.mp hMember
  cases hTags

theorem mixed_codes_do_not_collapse (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    code (disjointUnion D₁ D₂)
      (({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map Function.Embedding.inl,
        Sum.inl (Sum.inl x)) ≠
    code (disjointUnion D₁ D₂)
      (({Sum.inl x, Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map
        Function.Embedding.inl, Sum.inl (Sum.inl x)) := by
  rw [formerly_missing_input_filled, mixed_full_input_filled]
  intro h
  exact fresh_tokens_retain_full_support D₁ D₂ x y (Option.some.inj h)

/-- Information invisible to one factor projection remains in the fresh code. -/
theorem equal_projection_distinct_fresh_codes (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y z : D₂.Carrier) (hDistinct : y ≠ z) :
    projectLeft ({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)) =
        projectLeft ({Sum.inr z} : Finset (D₁.Carrier ⊕ D₂.Carrier)) ∧
      code (disjointUnion D₁ D₂)
        (({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map Function.Embedding.inl,
          Sum.inl (Sum.inl x)) ≠
      code (disjointUnion D₁ D₂)
        (({Sum.inr z} : Finset (D₁.Carrier ⊕ D₂.Carrier)).map Function.Embedding.inl,
          Sum.inl (Sum.inl x)) := by
  constructor
  · rw [projectLeft_eq_toLeft, projectLeft_eq_toLeft]
    ext value
    simp
  · rw [formerly_missing_input_filled, formerly_missing_input_filled]
    intro h
    have hTokens := Sum.inr.inj (Option.some.inj h)
    have hSupports := congrArg (fun input => input.val.1) hTokens
    change ({Sum.inr y} : Finset (D₁.Carrier ⊕ D₂.Carrier)) = {Sum.inr z}
      at hSupports
    exact hDistinct (Sum.inr.inj (Finset.singleton_injective hSupports))

theorem fresh_token_differs_from_old_output (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) (old : (disjointUnion D₁ D₂).Carrier) :
    (Sum.inr (opposite D₁ D₂ x y) : CompletionStep.Carrier (disjointUnion D₁ D₂)) ≠
      Sum.inl old := by
  intro h
  cases h

theorem fresh_support_remains_undefined (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    code (disjointUnion D₁ D₂)
      ({Sum.inr (opposite D₁ D₂ x y)}, Sum.inl (Sum.inl x)) = none :=
  code_none_of_fresh_mem (disjointUnion D₁ D₂) _ _ _
    (Finset.mem_singleton_self (Sum.inr (opposite D₁ D₂ x y)))

theorem fresh_output_remains_undefined (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    code (disjointUnion D₁ D₂) (∅, Sum.inr (opposite D₁ D₂ x y)) = none := rfl

theorem successor_still_proper (D₁ D₂ : GraphModel)
    (x : D₁.Carrier) (y : D₂.Carrier) :
    (successor (disjointUnion D₁ D₂)).Proper :=
  successor_proper_of_missing (disjointUnion D₁ D₂) (opposite D₁ D₂ x y)

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStepControls
