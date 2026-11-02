import Mettapedia.OSLF.Syntax.BindingScopeEqualizerFinite
import Mathlib.Data.Fintype.Card

/-!
# Different parameter maps strictly shrink their computed equalizer

The retained context has one position for each source position on which the
two maps agree. Its length is the cardinality of that table. A disagreement
therefore removes a position. Equal maps retain every position instead and
must be handled by reflexive-equation removal, not a claimed strict shrink.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopeEqualizer.Finite

open ContextPositions

variable {S : Signature} {Δ Γ : Ctx S} (left right : Ren S Δ Γ)

theorem context_length : (context left right).length = Fintype.card (Slot left right) := by
  simp only [context, ContextRows.context, List.length_map, rows, Finset.length_sort, Finset.card_univ]

theorem context_length_le : (context left right).length ≤ Δ.length := by
  rw [context_length]
  have bounded := Fintype.card_subtype_le (fun slot : Fin Δ.length =>
    CommonABT.index (left _ (ofSlot Δ slot)) = CommonABT.index (right _ (ofSlot Δ slot)))
  simpa only [Fintype.card_fin] using bounded

theorem context_length_same : (context left left).length = Δ.length := by
  rw [context_length]
  simp only [Slot, Fintype.card_subtype_true, Fintype.card_fin]

theorem context_length_lt_of_disagreement {sort : S.Srt} (position : Var Δ sort)
    (different : left sort position ≠ right sort position) : (context left right).length < Δ.length := by
  rw [context_length]
  have missing : ¬ (CommonABT.index (left _ (ofSlot Δ (toSlot position))) =
      CommonABT.index (right _ (ofSlot Δ (toSlot position)))) := by
    intro same
    apply different
    apply CommonABT.index_injective
    exact (map_index_ofSlot left position).symm.trans (same.trans (map_index_ofSlot right position))
  have strict := Fintype.card_subtype_lt (α := Fin Δ.length)
    (p := fun slot => CommonABT.index (left _ (ofSlot Δ slot)) =
      CommonABT.index (right _ (ofSlot Δ slot))) (x := toSlot position) missing
  simpa only [Fintype.card_fin] using strict

theorem context_length_lt (different : left ≠ right) : (context left right).length < Δ.length := by
  classical
  have disagreement : ∃ (sort : S.Srt) (position : Var Δ sort), left sort position ≠ right sort position := by
    by_contra none
    apply different
    funext sort position
    by_contra unequal
    exact none ⟨sort, position, unequal⟩
  obtain ⟨sort, position, unequal⟩ := disagreement
  exact context_length_lt_of_disagreement left right position unequal

end Mettapedia.OSLF.Binding.ScopeEqualizer.Finite
