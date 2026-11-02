import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestAdmission
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeProofEvaluation
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeBundleComponents
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeRightOuterComponents

/-!
# Independent source, bundle, target and refusal checks for the Vector branch.

The producer, checker, source requests and proof limits are unchanged.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem branchLeftAccepted :
    endpointAccepted branchContext branchLeft branchIotaType = true := by
  rw [ProofEvaluation.branch_endpoint_eq_termReplay, ProofEvaluation.choices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem branchBundleAccepted :
    endpointAccepted branchContext branchBundle branchBundleType = true := by
  exact BranchBundleComponents.bundle_accepted

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem branchRightAccepted :
    endpointAccepted branchContext branchRight branchIotaType = true := by
  exact BranchRightOuterComponents.right_accepted

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem unbundledBranchRefused :
    endpointAccepted branchContext
      (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0))
      branchIotaType = false := by
  rw [ProofEvaluation.branch_endpoint_eq_termReplay, ProofEvaluation.choices_exact]
  decide +kernel


#print axioms branchLeftAccepted
#print axioms branchBundleAccepted
#print axioms branchRightAccepted
#print axioms unbundledBranchRefused

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
