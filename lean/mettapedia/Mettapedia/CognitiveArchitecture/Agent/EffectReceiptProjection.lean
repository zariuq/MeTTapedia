import Mathlib

/-!
# Effect receipts and completion claims

Source provenance: adapted from GödelClaw commit
`906793a7cba9245ce4f7f9f5b479c77088fd1805`; only module packaging and
taxonomy-facing names were changed during integration.

A model proposal is an intention, not an observation that its effect happened.
The broker may return a result, withhold a suffix after a new stimulus, or
defer a suffix at a batch boundary.  Even a returned command needs result
evidence before a domain-level success claim is justified.

This file states the information boundary independently of any model or
effect implementation.  It belongs in the replaceable world-state projection,
not in the replace-or-stutter process kernel.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection

inductive Disposition where
  | returned
  | withheld
  | deferred
deriving Repr, DecidableEq

inductive ResultEvidence where
  | success
  | failure
  | unknown
deriving Repr, DecidableEq

structure Receipt where
  disposition : Disposition
  evidence : ResultEvidence
deriving Repr, DecidableEq

structure History where
  proposal : Nat
  receipt : Option Receipt
deriving Repr, DecidableEq

/-- A completion claim requires both a returned command and affirmative
result evidence.  Returned-with-failure and returned-with-unknown are not
silently promoted to success. -/
def Completed (history : History) : Prop :=
  history.receipt = some ⟨.returned, .success⟩

/-- The old projection: it remembers only which command was proposed. -/
def proposalOnly (history : History) : Nat :=
  history.proposal

/-- A still-insufficient projection: it remembers that the dispatcher
returned, but drops the result evidence. -/
def dispositionOnly (history : History) : Option Disposition :=
  history.receipt.map Receipt.disposition

def successful : History :=
  ⟨7, some ⟨.returned, .success⟩⟩

def withheld : History :=
  ⟨7, some ⟨.withheld, .unknown⟩⟩

def returnedFailure : History :=
  ⟨7, some ⟨.returned, .failure⟩⟩

theorem same_proposal_can_have_different_completion :
    proposalOnly successful = proposalOnly withheld ∧
      Completed successful ∧ ¬ Completed withheld := by
  simp [proposalOnly, successful, withheld, Completed]

/-- No deterministic completion classifier over proposals alone can be
correct for both an executed success and a withheld copy of that proposal. -/
theorem proposal_only_cannot_decide_completion :
    ¬ ∃ decideCompletion : Nat → Bool,
        decideCompletion (proposalOnly successful) = true ∧
          decideCompletion (proposalOnly withheld) = false := by
  rintro ⟨decideCompletion, successCorrect, withheldCorrect⟩
  have collision : proposalOnly successful = proposalOnly withheld := rfl
  have : true = false :=
    successCorrect.symm.trans <|
      (congrArg decideCompletion collision).trans withheldCorrect
  contradiction

theorem returned_disposition_can_have_different_completion :
    dispositionOnly successful = dispositionOnly returnedFailure ∧
      Completed successful ∧ ¬ Completed returnedFailure := by
  simp [dispositionOnly, successful, returnedFailure, Completed]

/-- Merely recording `returned` is also insufficient: the returned value may
be explicit failure evidence. -/
theorem disposition_only_cannot_decide_completion :
    ¬ ∃ decideCompletion : Option Disposition → Bool,
        decideCompletion (dispositionOnly successful) = true ∧
          decideCompletion (dispositionOnly returnedFailure) = false := by
  rintro ⟨decideCompletion, successCorrect, failureCorrect⟩
  have collision :
      dispositionOnly successful = dispositionOnly returnedFailure := rfl
  have : true = false :=
    successCorrect.symm.trans <|
      (congrArg decideCompletion collision).trans failureCorrect
  contradiction

/-- Completion factors through the receipt.  Proposal history is useful for
continuity, but is irrelevant to the truth of the completion claim. -/
theorem completion_factors_through_receipt (history : History) :
    Completed history ↔
      history.receipt = some ⟨.returned, .success⟩ := by
  rfl

theorem withheld_is_not_completed (proposal : Nat) :
    ¬ Completed ⟨proposal, some ⟨.withheld, .unknown⟩⟩ := by
  simp [Completed]

theorem deferred_is_not_completed (proposal : Nat) :
    ¬ Completed ⟨proposal, some ⟨.deferred, .unknown⟩⟩ := by
  simp [Completed]

theorem returned_failure_is_not_completed (proposal : Nat) :
    ¬ Completed ⟨proposal, some ⟨.returned, .failure⟩⟩ := by
  simp [Completed]

#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.proposal_only_cannot_decide_completion
#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.disposition_only_cannot_decide_completion
#print axioms Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.completion_factors_through_receipt

end Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection
