import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2Transformation

/-!
# Concrete normal-rule inventory for source-action execution

The ordered source-action GSLT is parameterized by a finite normal-proof rule
inventory.  This adapter supplies that inventory from the existing generic
normal MM2 verifier.  It introduces no alternate proof semantics and owns no
source data: it is solely the realization-selection boundary between the
generic verifier and the reusable action extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2Transformation

/-- The concrete inventory of the existing generic normal-proof MM2 machine.
It instantiates the source-action GSLT without changing its transition
presentation. -/
def normalProofMachineRuleInventory : NormalProofRuleInventory where
  dvPairBegin := normalDVPairBeginRule
  dvLeftConst := normalDVLeftConstRule
  dvLeftVariable := normalDVLeftVariableRule
  dvRightConst := normalDVRightConstRule
  dvRightVariable := normalDVRightVariableRule
  dvRightNil := normalDVRightNilRule
  dvLeftNil := normalDVLeftNilRule
  dvComplete := normalDVCompleteRule
  dispatchReload := normalDispatchReloadRule
  dispatchRuleRow := normalDispatchRuleRow
  accept := normalAcceptRule
  assertionStart := normalAssertionStartRule
  assertionBegin := normalAssertionBeginRule
  hypothesisStep := normalHypothesisStepRule
  assertionStartRequiresHeader := by decide +kernel
  assertionBeginRequiresHeader := by decide +kernel
  hypothesisStepDoesNotRequireHeader := by decide +kernel

end Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
