import Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
import Mettapedia.Languages.MeTTa.PrimeCandidates.TypedScheduler

/-!
# PLN evidence in the selected staged-reflective scheduler carrier

The independent PLN bridge supplies evidence-valued policies and their
quantale, fusion, and scalar-projection laws.  This downstream adapter places
its named Need reference policy in the families CwF carrier selected by
`TypedScheduler`.

The policy is reused unchanged.  Its semantic internalization does not choose
a language default scheduler or prove an authored syntax/elaboration theorem.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
open Mettapedia.Machines.BranchLocalNeed

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.PLNEvidenceScheduler

open Mettapedia.Languages.MeTTa.PrimeCandidates.TypedScheduler
open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Evidence.EvidenceQuantale

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

/-- The reference-machine evidence policy is a closed term in the selected
families CwF carrier.  This is semantic internalization, not a derivation that
the policy is expressible by authored candidate syntax. -/
noncomputable def internalNeedEvidencePolicy
    (score : NeedOccurrence Origin Local Resume Rule Value StableFault
      RetryableFault Effect → BinaryEvidence)
    (prefer : EvidenceHplus → EvidenceHplus → Bool) :
    Mettapedia.TypeTheory.Calculi.StagedScopedReflective.familiesCwF.Tm CandidateContext
      (policyTyFor (Origin := Origin) (Local := Local) (Resume := Resume)
        (Rule := Rule) (Value := Value) (StableFault := StableFault)
        (RetryableFault := RetryableFault) (Effect := Effect) EvidenceHplus) :=
  fun _ => needEvidencePolicy score prefer

@[simp] theorem internalNeedEvidencePolicy_apply
    (score : NeedOccurrence Origin Local Resume Rule Value StableFault
      RetryableFault Effect → BinaryEvidence)
    (prefer : EvidenceHplus → EvidenceHplus → Bool) :
    internalNeedEvidencePolicy score prefer PUnit.unit =
      needEvidencePolicy score prefer :=
  rfl


#print axioms internalNeedEvidencePolicy_apply

end Mettapedia.Languages.MeTTa.PrimeCandidates.PLNEvidenceScheduler
