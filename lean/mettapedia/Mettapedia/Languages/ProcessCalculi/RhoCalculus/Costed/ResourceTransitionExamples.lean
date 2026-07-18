import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AuthorityObservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ReceiptReplayExamples

/-!
# Resource-transition examples for funded cost-rho

The positive example extracts an exact parameterised computation from a
receipt accepted by the executable checker.  The negative examples show both
that identity transitions cannot contain events and that the commutative raw
account forgets funding factorisation retained by the receipt.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
namespace ResourceTransitionExamples

open RuntimeExamples ReceiptReplayExamples

set_option maxRecDepth 100000

/-- The executable one-step fixture yields a genuine nonempty funded
computation, not merely an aggregate cost. -/
theorem exists_one_step_funded_execution :
    ∃ source target : FundedState,
      ∃ execution : FundedExecution source target Unit,
        execution.transition.rawEmission.length = 1 := by
  obtain ⟨finalComponents, path, emission_eq, _residual_eq⟩ :=
    validateReceipt_sound one_step_receipt_accepted
  refine ⟨path.sourceState, path.targetState,
    FundedExecution.ofPath path (), ?_⟩
  change path.rawEmission.length = 1
  rw [emission_eq]
  decide

/-- No parameterised identity computation can hide a funded event. -/
theorem no_nonempty_identity_execution (state : FundedState) :
    ¬∃ execution : FundedExecution state state Unit,
      execution.transition.rawEmission ≠ [] := by
  rintro ⟨execution, nonempty⟩
  rw [execution.endomorphism_transition_eq_identity] at nonempty
  exact nonempty (ResourceTransition.identity_rawEmission state)

/-- Equal aggregate raw spend does not determine how many purse occurrences
funded the event.  The exact receipt retains that distinction. -/
theorem raw_spend_forgets_funding_factorisation :
    splitPrefix.map (fun result => result.receipt.head?.map (·.rawSpend)) =
        combinedPrefix.map (fun result => result.receipt.head?.map (·.rawSpend)) ∧
      splitPrefix.map (fun result =>
          result.receipt.head?.map (·.funding.length)) ≠
        combinedPrefix.map (fun result =>
          result.receipt.head?.map (·.funding.length)) := by
  constructor
  · exact split_and_combined_raw_spend_agree
  · rw [split_heads_emit_two_contributions,
      combined_head_emits_one_contribution]
    decide

end ResourceTransitionExamples
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
