import Mettapedia.GSLT.GraphTheory.PartialPairFactorEmbedding
import Mettapedia.GSLT.Core.WebSemanticsControls

/-! Concrete primitive factor selection and full-support isolation controls. -/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.FactorEmbeddingControls

open Mettapedia.GSLT.Core

private abbrev leftFactor := FactorEmbedding.left GraphModel.naturalModel GraphModel.naturalModel
private abbrev rightFactor := FactorEmbedding.right GraphModel.naturalModel GraphModel.naturalModel

theorem left_selects_actual_left_token :
    leftFactor.selector (Sum.inl (0 : Nat)) = some (0 : Nat) :=
  leftFactor.selector_embedding (0 : Nat)

theorem right_selects_actual_right_token :
    rightFactor.selector (Sum.inr (1 : Nat)) = some (1 : Nat) :=
  rightFactor.selector_embedding (1 : Nat)

theorem left_excludes_opposite_token : leftFactor.selector (Sum.inr (1 : Nat)) = none := by
  apply (leftFactor.selector_none_iff _).mpr
  rintro ⟨value, h⟩
  cases h

theorem right_excludes_opposite_token : rightFactor.selector (Sum.inl (0 : Nat)) = none := by
  apply (rightFactor.selector_none_iff _).mpr
  rintro ⟨value, h⟩
  cases h

theorem opposite_support_cannot_survive_left_coding :
    disjointUnionCode GraphModel.naturalModel GraphModel.naturalModel
      (({Sum.inr 1} : Finset (Nat ⊕ Nat)), Sum.inl (0 : Nat)) = none :=
  disjointUnionCode_inl_none_of_inr_mem GraphModel.naturalModel GraphModel.naturalModel
    _ (0 : Nat) (1 : Nat)
    (Finset.mem_singleton_self _)

theorem opposite_support_cannot_survive_right_coding :
    disjointUnionCode GraphModel.naturalModel GraphModel.naturalModel
      (({Sum.inl 0} : Finset (Nat ⊕ Nat)), Sum.inr (1 : Nat)) = none :=
  disjointUnionCode_inr_none_of_inl_mem GraphModel.naturalModel GraphModel.naturalModel
    _ (1 : Nat) (0 : Nat)
    (Finset.mem_singleton_self _)

end Mettapedia.GSLT.GraphTheory.PartialPair.FactorEmbeddingControls
