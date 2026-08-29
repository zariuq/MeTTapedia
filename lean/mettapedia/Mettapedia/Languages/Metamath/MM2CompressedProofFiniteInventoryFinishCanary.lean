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
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- With no row at cursor two, the self-reloading administrative shell is
consumed.  The loaded values and terminal cursor remain. -/
theorem exhaust_load_shell_exact :
    cReflectiveSourceWorkQueueStep .leaveInert afterLoad1 =
      some afterLoadExhausted := by
  rfl

/-- The finish rule then consumes exactly that terminal cursor and releases
the compressed header. -/
theorem finish_exact :
    cReflectiveSourceWorkQueueStep .leaveInert afterLoadExhausted =
      some afterFinish := by
  rfl

/-- The four exact endpoint equalities form one proof-relevant continuous MM2
trace; no phase is reconstructed independently. -/
def concreteTwoRuleTrace :
    CReflectiveTrace .leaveInert 4 twoRuleProgram afterFinish :=
  .step load_occurrence_zero_exact
    (.step load_occurrence_one_exact
      (.step exhaust_load_shell_exact
        (.step finish_exact (.refl))))

/-- The concrete terminal observation contains the exact abstract inventory,
and only the exact end cursor releases the source-bound header. -/
theorem concrete_terminal_observation_agrees_with_abstract :
    twoRulePresentation.loaderTerminal.loaded =
        [canaryOpaqueRule, secondOpaqueRule] ∧
      canaryOpaqueRule ∈ afterFinish ∧
      secondOpaqueRule ∈ afterFinish ∧
      canaryHeaderControl ∈ afterFinish ∧
      canaryLoading 2 ∉ afterFinish := by
  repeat' apply And.intro
  all_goals rfl

#print axioms exhaust_load_shell_exact
#print axioms finish_exact
#print axioms concreteTwoRuleTrace
#print axioms concrete_terminal_observation_agrees_with_abstract

end Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryFinishCanary
