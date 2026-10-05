import Mettapedia.Languages.MM0.Kernel.Unfolding

/-! # Definition unfolding computes the body while rejecting captured dummy images -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.UnfoldingControls

private def signature : TermSignature
  | 0 => some ⟨[.bound 0], 1, {0}⟩
  | 1 => some ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
  | 2 => some ⟨[.regular 0 ∅, .regular 0 ∅], 1, ∅⟩
  | _ => none

private def definitions : Definition.Signature
  | 0 => some ⟨[0], .applyArgs (.term 1)
      [.var 1, .applyArgs (.term 2) [.var 0, .var 1]]⟩
  | _ => none

private def target : Context := [.bound 0, .bound 0]

theorem fresh_unfolding_computes_body :
    Definition.unfold? signature definitions target 0 [.var 0] [1] =
      some (.applyArgs (.term 1) [.var 1, .applyArgs (.term 2) [.var 0, .var 1]]) := by decide

theorem capturing_unfolding_refuses :
    Definition.unfold? signature definitions target 0 [.var 0] [0] = none := by decide

theorem reversed_fresh_names_compute_reversed_body :
    Definition.unfold? signature definitions target 0 [.var 1] [0] =
      some (.applyArgs (.term 1) [.var 0, .applyArgs (.term 2) [.var 1, .var 0]]) := by decide

theorem primitive_term_is_not_a_definition :
    Definition.unfold? signature definitions target 1 [.var 0, .var 0] [] = none := by decide

theorem missing_dummy_refuses :
    Definition.unfold? signature definitions target 0 [.var 0] [] = none := by decide

theorem wrong_requested_body_not_justified :
    ¬ Definition.Unfolds signature definitions target 0 [.var 0] [1] (.var 0) := by
  intro unfolded
  have computed := (Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mpr unfolded
  rw [fresh_unfolding_computes_body] at computed
  contradiction

end Mettapedia.Languages.MM0.Kernel.UnfoldingControls
