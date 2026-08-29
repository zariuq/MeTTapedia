import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- A compact assertion reference launches exactly one normal assertion
invocation through the shared assertion-control vocabulary. -/
theorem assertion_reference_launches_shared_normal_kernel :
    normalControl ∈ launchFinal := by
  decide +kernel

#print axioms assertion_reference_launches_shared_normal_kernel

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchCanary
