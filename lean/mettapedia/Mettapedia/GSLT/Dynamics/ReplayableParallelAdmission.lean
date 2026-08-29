import Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority

/-!
# Replayable Boolean authority for parallel admission

A semantic `ParallelBackend` may state its admitted subset as a proposition.
That proposition is not yet an executable trust boundary.  This module gives
the exact bridge for backends that supply a Boolean decision together with a
two-sided reflection theorem.

The resulting certificate is `Unit`: all substantive evidence lives in the
replayed decision and its proof of exactness.  This is appropriate for a
finite or otherwise decidable admission policy.  Semidecidable policies may
instead retain proof-relevant certificates through the same
`AdmissionAuthority` interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ReplayableParallelAdmission

open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.ParallelExecutionAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uGrade

/-- Promote an exact Boolean characterization of one backend's admitted
subset to independently replayable admission authority. -/
def ofBooleanDecision {theory : QueryRevision.Theory}
    {backend : ParallelBackend.{uGrade} theory}
    (accept : EventClaim theory → Bool)
    (reflects : ∀ claim, accept claim = true ↔ Admitted backend claim) :
    AdmissionAuthority backend where
  Certificate := Unit
  checker := { check := fun claim _certificate => accept claim }
  authority := by
    constructor
    · intro claim certificate accepted
      exact (reflects claim).mp accepted
    · intro claim admitted
      exact ⟨(), (reflects claim).mpr admitted⟩

namespace Canary

open Mettapedia.GSLT.Dynamics.EventValuation.Canary

private instance : DecidableEq noOpTheory.Revision :=
  inferInstanceAs (DecidableEq Bool)

def sameClassDecision (claim : EventClaim noOpTheory) : Bool :=
  decide (claim.first = claim.second)

theorem sameClassDecision_reflects (claim : EventClaim noOpTheory) :
    sameClassDecision claim = true ↔ Admitted sameClassBackend claim := by
  simp [sameClassDecision, Admitted, sameClassBackend]

def sameClassAuthority : AdmissionAuthority sameClassBackend :=
  ofBooleanDecision sameClassDecision sameClassDecision_reflects

def equalClaim : EventClaim noOpTheory := ⟨true, true, (), ()⟩
def unequalClaim : EventClaim noOpTheory := ⟨true, false, (), ()⟩

theorem equal_claim_accepted :
    sameClassAuthority.checker.check equalClaim () = true := by
  decide

theorem unequal_claim_rejected :
    sameClassAuthority.checker.check unequalClaim () = false := by
  decide

end Canary

#print axioms ofBooleanDecision
#print axioms Canary.sameClassDecision_reflects
#print axioms Canary.equal_claim_accepted
#print axioms Canary.unequal_claim_rejected

end Mettapedia.GSLT.Dynamics.ReplayableParallelAdmission
