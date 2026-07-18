import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ReceiptReplay
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.RuntimeExamples

/-!
# Executable receipt-replay examples

The positive cases replay complete runtime evidence.  The negative cases alter
one occurrence-level claim at a time and are rejected without comparing only a
final aggregate cost.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
namespace ReceiptReplayExamples

open RuntimeExamples

set_option maxRecDepth 100000

def oneStepResult : RawCausalPrefix :=
  Option.get (boundedCausalPrefix 1 wholeCompoundSplit) (by decide)

theorem one_step_receipt_accepted :
    validateReceipt wholeCompoundSplit oneStepResult.receipt
      oneStepResult.residual = true := by
  decide

def corruptFirstId : RawReceipt → RawReceipt
  | [] => []
  | event :: rest => { event with id := event.id + 17 } :: rest

theorem altered_occurrence_id_rejected :
    validateReceipt wholeCompoundSplit
      (corruptFirstId oneStepResult.receipt) oneStepResult.residual = false := by
  decide

def corruptFirstFundingSurface : RawReceipt → RawReceipt
  | [] => []
  | event :: rest =>
      let funding := event.funding.map fun contribution =>
        { contribution with surface := wrong }
      { event with funding } :: rest

theorem altered_location_rejected :
    validateReceipt wholeCompoundSplit
      (corruptFirstFundingSurface oneStepResult.receipt)
      oneStepResult.residual = false := by
  decide

theorem altered_residual_rejected :
    validateReceipt wholeCompoundSplit oneStepResult.receipt .nil = false := by
  decide

/-- Reusing one purse serializes its two head consumptions.  The second event
therefore names the first event as the producer of the retained purse tail. -/
def chainedFunding : RawCostTerm :=
  parList [whole alice, whole alice, purse pay [alice, alice]]

def chainedResult : RawCausalPrefix :=
  Option.get (boundedCausalPrefix 2 chainedFunding) (by decide)

theorem chained_receipt_accepted :
    validateReceipt chainedFunding chainedResult.receipt
      chainedResult.residual = true := by
  decide

theorem chained_receipt_records_consumption_cause :
    chainedResult.receipt.map RawEmittedEvent.causes = [[], [0]] := by
  decide

def eraseSecondCauses : RawReceipt → RawReceipt
  | first :: second :: rest => first :: { second with causes := [] } :: rest
  | receipt => receipt

theorem erased_consumption_cause_rejected :
    validateReceipt chainedFunding (eraseSecondCauses chainedResult.receipt)
      chainedResult.residual = false := by
  decide

def malformedSource : RawCostTerm :=
  .purse pay [[]]

theorem malformed_source_rejected :
    validateReceipt malformedSource [] malformedSource = false := by
  decide

end ReceiptReplayExamples
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
