import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-! # Ordered theorem application, dependency and conversion proof controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.ProofControls

open Preterm ProofWitness

private def signature : TermSignature
  | 0 => some ⟨[.regular 1 ∅, .regular 1 ∅], 1, ∅⟩
  | 1 => some ⟨[.regular 1 ∅], 1, ∅⟩
  | 2 => some ⟨[], 1, ∅⟩
  | 3 => some ⟨[], 1, ∅⟩
  | 4 => some ⟨[.bound 0], 1, {0}⟩
  | 5 => some ⟨[], 0, ∅⟩
  | _ => none

private def definitions : Definition.Signature
  | 1 => some ⟨[], .var 0⟩
  | _ => none

private def context : Context :=
  [.regular 1 ∅, .regular 1 ∅, .bound 0, .regular 1 {2}, .bound 0]

private def implies (first second : Preterm) : Preterm :=
  applyArgs (.term 0) [first, second]

private def modusPonens : TheoremDecl :=
  ⟨[.regular 1 ∅, .regular 1 ∅], [.var 0, implies (.var 0) (.var 1)], .var 1⟩

private def theorems : TheoremSignature
  | 0 => some modusPonens
  | 1 => some ⟨[], [], .term 2⟩
  | 2 => some ⟨[.bound 0, .regular 1 ∅], [], .term 2⟩
  | 3 => some ⟨[.bound 0, .bound 0], [], .term 2⟩
  | 4 => some ⟨[.regular 1 ∅], [.var 0, .var 0], .var 0⟩
  | 5 => some ⟨[], [], .var 0⟩
  | _ => none

private def hypotheses : List Preterm := [.var 0, implies (.var 0) (.var 1)]
private def mp : ProofWitness := .theoremApp 0 [.var 0, .var 1] [.hyp 0, .hyp 1]

theorem local_hypothesis_lookup_accepts :
    check signature definitions theorems context hypotheses (.hyp 0) (.var 0) = true := by decide +kernel

theorem local_hypothesis_wrong_claim_rejected :
    check signature definitions theorems context hypotheses (.hyp 0) (.var 1) = false := by decide +kernel

theorem missing_local_hypothesis_rejected :
    proof? signature definitions theorems context hypotheses (.hyp 2) = none := by decide +kernel

theorem theorem_application_computes_hypotheses_and_conclusion :
    modusPonens.instantiate? signature context [.var 1, .var 0] =
      some ⟨[.var 1, implies (.var 1) (.var 0)], .var 0⟩ := by decide +kernel

theorem modus_ponens_accepts :
    check signature definitions theorems context hypotheses mp (.var 1) = true := by decide +kernel

theorem modus_ponens_wrong_conclusion_rejected :
    check signature definitions theorems context hypotheses mp (.var 0) = false := by decide +kernel

theorem missing_premise_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 0, .var 1] [.hyp 1]) = none := by decide +kernel

theorem extra_premise_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 0, .var 1] [.hyp 0, .hyp 1, .hyp 0]) = none := by decide +kernel

theorem reversed_premises_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) = none := by decide +kernel

theorem wrong_substitution_order_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 1, .var 0] [.hyp 0, .hyp 1]) = none := by decide +kernel

theorem missing_argument_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 0] [.hyp 0, .hyp 1]) = none := by decide +kernel

theorem extra_argument_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 0, .var 1, .var 0] [.hyp 0, .hyp 1]) = none := by decide +kernel

theorem wrong_argument_sort_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 0 [.var 2, .var 1] [.hyp 0, .hyp 1]) = none := by decide +kernel

theorem undefined_theorem_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 6 [] []) = none := by decide +kernel

theorem no_premise_axiom_accepts :
    check signature definitions theorems context hypotheses (.theoremApp 1 [] []) (.term 2) = true :=
  by decide +kernel

theorem duplicate_required_premise_keeps_two_children :
    check signature definitions theorems context hypotheses
      (.theoremApp 4 [.var 0] [.hyp 0, .hyp 0]) (.var 0) = true := by decide +kernel

theorem duplicate_premise_cannot_drop_child :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 4 [.var 0] [.hyp 0]) = none := by decide +kernel

theorem declared_dependency_independence_accepts :
    check signature definitions theorems context hypotheses
      (.theoremApp 2 [.var 2, .var 0] []) (.term 2) = true := by decide +kernel

theorem target_regular_dependency_capture_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 2 [.var 2, .var 3] []) = none := by decide +kernel

theorem occurrence_under_bound_slot_is_not_ignored :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 2 [.var 2, .app (.term 4) (.var 2)] []) = none := by decide +kernel

theorem bound_slot_refuses_same_sort_constant :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 2 [.term 5, .var 0] []) = none := by decide +kernel

theorem distinct_bound_images_accept :
    check signature definitions theorems context hypotheses
      (.theoremApp 3 [.var 2, .var 4] []) (.term 2) = true := by decide +kernel

theorem coincident_bound_images_rejected :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 3 [.var 2, .var 2] []) = none := by decide +kernel

theorem raw_declaration_with_unbound_conclusion_refused :
    proof? signature definitions theorems context hypotheses
      (.theoremApp 5 [] []) = none := by decide +kernel

theorem checked_conversion_transports_proof :
    check signature definitions theorems context hypotheses
      (.conversion (.symm (.unfold 1 [.var 0] [])) (.hyp 0))
      (.app (.term 1) (.var 0)) = true := by decide +kernel

theorem conversion_direction_is_checked :
    proof? signature definitions theorems context hypotheses
      (.conversion (.unfold 1 [.var 0] []) (.hyp 0)) = none := by decide +kernel

theorem unrelated_conversion_source_rejected :
    proof? signature definitions theorems context hypotheses
      (.conversion (.refl (.var 1)) (.hyp 0)) = none := by decide +kernel

theorem malformed_conversion_witness_rejected :
    proof? signature definitions theorems context hypotheses
      (.conversion (.trans (.refl (.var 0)) (.refl (.var 1))) (.hyp 0)) = none := by decide +kernel

private def reorderedTheorems : TheoremSignature
  | 0 => some ⟨modusPonens.arguments, modusPonens.hypotheses.reverse, modusPonens.conclusion⟩
  | index => theorems index

theorem premise_mutation_rejects_original_article :
    proof? signature definitions reorderedTheorems context hypotheses mp = none := by decide +kernel

theorem mutated_premises_accept_corresponding_ordered_article :
    check signature definitions reorderedTheorems context hypotheses
      (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) (.var 1) = true := by decide +kernel

private def foreignTheorems : TheoremSignature
  | 1 => some ⟨[], [], .term 3⟩
  | index => theorems index

theorem foreign_same_number_theorem_does_not_prove_original_goal :
    check signature definitions foreignTheorems context hypotheses
      (.theoremApp 1 [] []) (.term 2) = false := by decide +kernel

theorem derivable_goal_does_not_rescue_invalid_theorem_witness :
    Derives signature definitions theorems context hypotheses (.var 1) ∧
      check signature definitions theorems context hypotheses
        (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) (.var 1) = false := by
  exact ⟨ProofWitness.check_sound modus_ponens_accepts, by decide +kernel⟩

theorem derivable_goal_does_not_rescue_invalid_conversion_witness :
    Derives signature definitions theorems context hypotheses (.var 0) ∧
      check signature definitions theorems context hypotheses
        (.conversion (.refl (.var 1)) (.hyp 0)) (.var 0) = false := by
  exact ⟨.hypothesis (by simp [hypotheses]), by decide +kernel⟩

theorem raw_hypothesis_assumptions_require_separate_admission :
    check signature definitions theorems [] [.var 99] (.hyp 0) (.var 99) = true ∧
      infer signature [] (.var 99) = none := by decide +kernel

end Mettapedia.Languages.MM0.Kernel.ProofControls
