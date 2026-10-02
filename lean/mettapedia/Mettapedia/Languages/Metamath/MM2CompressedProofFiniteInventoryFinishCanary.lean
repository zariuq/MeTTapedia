import Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad1Canary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryFinishCanary

open Mettapedia.GSLT.FiniteInventoryLoader
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad0Canary
open Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad1Canary
open Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- With no row at cursor two, the self-reloading administrative shell is
consumed.  The loaded values and terminal cursor remain. -/
theorem exhaust_load_shell_exact :
    cReflectiveSourceWorkQueueStep .leaveInert afterLoad1 =
      some afterLoadExhausted := by
  decide +kernel

/-- The finish rule consumes the terminal cursor and releases the compressed
header and its owner-bound dispatch request, retaining exact staged code. -/
theorem finish_exact :
    cReflectiveSourceWorkQueueStep .leaveInert afterLoadExhausted =
      some afterFinish := by
  decide +kernel

/-- The four exact endpoint equalities form one proof-relevant continuous MM2
trace; no phase is reconstructed independently. -/
def concreteTwoRuleTrace :
    CReflectiveTrace .leaveInert 4 twoRuleProgram afterFinish :=
  .step load_occurrence_zero_exact
    (.step load_occurrence_one_exact
      (.step exhaust_load_shell_exact
        (.step finish_exact (.refl))))

/-- The concrete terminal observation stores every exact abstract rule value,
without premature executable release.  Only the exact end cursor releases the
source-bound header and its owner-bound dispatch request. -/
theorem concrete_terminal_observation_agrees_with_abstract :
    twoRulePresentation.loaderTerminal.loaded =
        [canaryOpaqueRule, secondOpaqueRule] ∧
      compressedDispatchRuleRow canaryOpaqueRule ∈ afterFinish ∧
      compressedDispatchRuleRow secondOpaqueRule ∈ afterFinish ∧
      canaryOpaqueRule ∉ afterFinish ∧ secondOpaqueRule ∉ afterFinish ∧
      canaryHeaderControl ∈ afterFinish ∧
      Atom.expression [Atom.symbol "mm-reload-compressed-dispatch", canarySource,
        canaryProofOwner] ∈ afterFinish ∧
      canaryLoading 2 ∉ afterFinish := by
  decide +kernel

#print axioms exhaust_load_shell_exact
#print axioms finish_exact
#print axioms concreteTwoRuleTrace
#print axioms concrete_terminal_observation_agrees_with_abstract

end Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryFinishCanary
