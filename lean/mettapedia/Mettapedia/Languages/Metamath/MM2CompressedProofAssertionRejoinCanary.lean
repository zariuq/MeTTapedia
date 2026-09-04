import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def rejoinContext : RejoinContext :=
  { scopeOwner := scopeOwner
    proofOwner := proofOwner
    wordPosition := 0
    remainingBytes := []
    index := 0
    heapNext := 1
    nodeNext := 0
    stackBase := 0
    assertionLabel := "ax"
    resultFormula := resultFormula }

/-- The normal kernel's exact result occurrence becomes one compact proof node
at the returned stack base. -/
theorem exact_normal_result_rejoins_compact_machine :
    resultNode ∈ rejoinFinal := by
  change rejoinContext.resultNodeRow ∈
    cFireReflectiveSourceExecFact rejoinContext.matchSlice
      compressedAssertionRejoinDirective
  apply canonical_rejoin_fire_adds_output_rows
  change rejoinContext.resultNodeRow ∈
    [rejoinContext.returnedMachineRow, rejoinContext.resultNodeRow,
     rejoinContext.resultStackRow, rejoinContext.resumeRow,
     compressedAssertionResumeRule]
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

/-- The normal stack cell is the synchronized normal-machine view used by
later compact assertion handoffs.  Rejoin publishes the compact result while
preserving that row. -/
theorem exact_normal_result_preserves_normal_stack :
    returnedStack ∈ rejoinFinal := by
  change rejoinContext.returnedStackRow ∈
    cFireReflectiveSourceExecFact rejoinContext.matchSlice
      compressedAssertionRejoinDirective
  exact canonical_rejoin_fire_preserves_returned_stack rejoinContext

#print axioms exact_normal_result_rejoins_compact_machine
#print axioms exact_normal_result_preserves_normal_stack

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCanary
