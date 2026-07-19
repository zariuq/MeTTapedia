import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudget
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

/-!
# Closed examples for concurrent event budgets

The examples use a genuinely contended branch: one event is admitted by one
unit of fuel and by every larger allowance, while zero fuel cannot admit it.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudgetExamples

open ParallelExamples

/-- One contested branch forms a one-event concurrent trace. -/
def aliceOneEventTrace :
    ParallelCostTrace contestedSource aliceBranch.receipt
      aliceBranch.target 1 := by
  simpa [aliceBranch, CostMatching.receipt, costWaveReceipt] using
    (ParallelCostTrace.cons contested_alice_branch_preserved
      (ParallelCostTrace.nil aliceBranch.target))

/-- One unit of event fuel admits the branch. -/
theorem alice_branch_within_one :
    ParallelRunsWithin 1 contestedSource aliceBranch.receipt
      aliceBranch.target :=
  ⟨1, aliceOneEventTrace, le_rfl⟩

/-- A larger allowance retains the same admitted branch. -/
theorem alice_branch_within_two :
    ParallelRunsWithin 2 contestedSource aliceBranch.receipt
      aliceBranch.target :=
  parallelRunsWithin_mono (by decide) alice_branch_within_one

/-- Zero event fuel cannot silently execute the contended branch. -/
theorem alice_branch_not_within_zero :
    ¬ParallelRunsWithin 0 contestedSource aliceBranch.receipt
      aliceBranch.target :=
  parallelStep_not_within_zero contested_alice_branch_preserved

/-- The example's receipt cardinality is the operational fuel charged. -/
theorem alice_branch_receipt_card : aliceBranch.receipt.card = 1 := by
  have exactCount := aliceOneEventTrace.count_eq_receipt_card
  simpa using exactCount.symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelBudgetExamples
