import Mettapedia.Languages.MM0.Kernel.Conversion

/-! # Exact witness, congruence and fresh unfolding controls for MM0 conversion -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.ConversionControls

open Preterm ConvWitness

private def signature : TermSignature
  | 0 => some ⟨[.regular 1 ∅], 1, ∅⟩
  | 1 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 2 => some ⟨[.regular 1 ∅], 1, ∅⟩
  | 3 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 4 => some ⟨[], 1, ∅⟩
  | 5 => some ⟨[], 1, ∅⟩
  | 6 => some ⟨[], 1, ∅⟩
  | 7 => some ⟨[], 0, ∅⟩
  | _ => none

private def definitions : Definition.Signature
  | 2 => some ⟨[], .app (.term 0) (.var 0)⟩
  | 3 => some ⟨[0], .applyArgs (.term 1)
      [.var 2, .applyArgs (.term 1) [.var 0, .var 1]]⟩
  | 5 => some ⟨[], .term 4⟩
  | 6 => some ⟨[], .term 7⟩
  | _ => none

private def context : Context :=
  [.bound 0, .bound 0, .regular 1 {0}, .regular 1 ∅, .bound 0, .bound 0, .bound 1]

private def definedCall : Preterm := .app (.term 2) (.var 2)
private def expanded : Preterm := .app (.term 0) (.var 2)
private def aliasWitness : ConvWitness := .unfold 2 [.var 2] []

theorem typed_reflexivity_accepts :
    check signature definitions context (.refl (.var 2)) (.var 2) (.var 2) 1 = true := by decide +kernel

theorem primitive_constant_reflexivity_accepts :
    check signature definitions context (.refl (.term 4)) (.term 4) (.term 4) 1 = true := by decide +kernel

theorem direct_unfolding_computes_substitution :
    conversion? signature definitions context aliasWitness = some ⟨definedCall, expanded, 1⟩ := by decide +kernel

theorem folding_is_symmetric_conversion :
    check signature definitions context (.symm aliasWitness) expanded definedCall 1 = true := by decide +kernel

theorem transitivity_checks_shared_middle :
    check signature definitions context (.trans aliasWitness (.symm aliasWitness))
      definedCall definedCall 1 = true := by decide +kernel

theorem congruence_composes_actual_child_unfolding :
    check signature definitions context (.congruence 0 [aliasWitness])
      (.app (.term 0) definedCall) (.app (.term 0) expanded) 1 = true := by decide +kernel

theorem bound_slot_congruence_preserves_bound_images :
    check signature definitions context (.congruence 1 [.refl (.var 0), aliasWitness])
      (.applyArgs (.term 1) [.var 0, definedCall])
      (.applyArgs (.term 1) [.var 0, expanded]) 1 = true := by decide +kernel

theorem fresh_dummy_unfolding_accepts :
    check signature definitions context (.unfold 3 [.var 0, .var 2] [4])
      (.applyArgs (.term 3) [.var 0, .var 2])
      (.applyArgs (.term 1) [.var 4, .applyArgs (.term 1) [.var 0, .var 2]]) 1 = true := by decide +kernel

theorem other_fresh_dummy_changes_exact_result :
    check signature definitions context (.unfold 3 [.var 0, .var 2] [5])
      (.applyArgs (.term 3) [.var 0, .var 2])
      (.applyArgs (.term 1) [.var 5, .applyArgs (.term 1) [.var 0, .var 2]]) 1 = true := by decide +kernel

theorem fresh_dummy_cannot_be_relabelled_in_claim :
    check signature definitions context (.unfold 3 [.var 0, .var 2] [4])
      (.applyArgs (.term 3) [.var 0, .var 2])
      (.applyArgs (.term 1) [.var 5, .applyArgs (.term 1) [.var 0, .var 2]]) 1 = false := by decide +kernel

theorem capturing_dummy_rejected :
    conversion? signature definitions context (.unfold 3 [.var 0, .var 2] [0]) = none := by decide +kernel

theorem missing_dummy_rejected :
    conversion? signature definitions context (.unfold 3 [.var 0, .var 2] []) = none := by decide +kernel

theorem wrong_sort_dummy_rejected :
    conversion? signature definitions context (.unfold 3 [.var 0, .var 2] [6]) = none := by decide +kernel

theorem primitive_without_definition_rejected :
    conversion? signature definitions context (.unfold 4 [] []) = none := by decide +kernel

theorem declared_definition_with_wrong_result_sort_rejected :
    conversion? signature definitions context (.unfold 6 [] []) = none := by decide +kernel

theorem malformed_body_is_rejected_after_raw_unfolding :
    Definition.unfold? signature definitions context 6 [] [] = some (.term 7) ∧
      conversion? signature definitions context (.unfold 6 [] []) = none := by decide +kernel

theorem unrelated_middle_rejected :
    conversion? signature definitions context (.trans (.refl (.var 2)) (.refl (.var 3))) =
      none := by decide +kernel

theorem requested_wrong_sort_rejected :
    check signature definitions context aliasWitness definedCall expanded 0 = false := by decide +kernel

theorem requested_wrong_endpoint_rejected :
    check signature definitions context aliasWitness definedCall (.term 4) 1 = false := by decide +kernel

theorem requested_reversed_endpoints_rejected :
    check signature definitions context aliasWitness expanded definedCall 1 = false := by decide +kernel

theorem missing_congruence_child_rejected :
    conversion? signature definitions context (.congruence 1 [.refl (.var 0)]) = none := by decide +kernel

theorem extra_congruence_child_rejected :
    conversion? signature definitions context
      (.congruence 0 [.refl (.var 2), .refl (.var 3)]) = none := by decide +kernel

theorem reordered_congruence_children_rejected :
    conversion? signature definitions context
      (.congruence 1 [.refl (.var 2), .refl (.var 0)]) = none := by decide +kernel

theorem same_sort_constant_in_bound_slot_rejected :
    conversion? signature definitions context
      (.congruence 1 [.refl (.term 7), .refl (.var 2)]) = none := by decide +kernel

theorem unsaturated_reflexivity_rejected :
    conversion? signature definitions context (.refl (.term 1)) = none := by decide +kernel

theorem undefined_reflexivity_rejected :
    conversion? signature definitions context (.refl (.var 7)) = none := by decide +kernel

theorem undefined_congruence_head_rejected :
    conversion? signature definitions context (.congruence 8 []) = none := by decide +kernel

/-- An independent conversion does not validate a malformed submitted witness. -/
theorem provable_conversion_does_not_validate_unrelated_children :
    Converts signature definitions context (.var 2) (.var 2) 1 ∧
      check signature definitions context (.trans (.refl (.var 2)) (.refl (.var 3)))
        (.var 2) (.var 2) 1 = false := by
  refine ⟨.refl ?_, ?_⟩
  · exact (infer_eq_some_iff _ _ _ _ _).mp (by decide)
  · decide +kernel

theorem accepted_unfolding_has_independent_derivation :
    Converts signature definitions context definedCall expanded 1 :=
  ((conversion_eq_some_iff _ _ _ _ _ _ _).mp direct_unfolding_computes_substitution).derives

theorem rejected_capture_has_no_submitted_witness_meaning :
    ¬ ∃ left right sort,
      Checks signature definitions context (.unfold 3 [.var 0, .var 2] [0]) left right sort :=
  (conversion_none_iff _ _ _ _).mp capturing_dummy_rejected

end Mettapedia.Languages.MM0.Kernel.ConversionControls
