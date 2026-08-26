import Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
import Mettapedia.Logic.MarkovLogicSocialSmoking
import Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenInductionBridge

/-!
# Vanilla PeTTa typed calls around native probabilistic judgments

This module composes two authorities without collapsing them:

* the exact OSLF/NTT successor generated from vanilla PeTTa's typed-call GSLT;
* an independently proved probabilistic judgment or native `PLN.Derive` run.

The call guard establishes that the selected declaration accepts the argument
and result values at the current atomspace revision.  It does not establish a
probability.  Conversely, the probabilistic proof establishes its numeric or
evidential result but does not establish PeTTa call admissibility.

The three specimens cover a Tuffy-style social-smoking query, the raven
induction example, and the proof-producing `PLN.Derive` loop.  Negative cases
change only the typed boundary while leaving the independent probabilistic
authority untouched.
-/

namespace Mettapedia.PLN.Bridges.GSLT.PeTTaTypedPLNNativeBridge

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Logic.MarkovLogicSocialSmoking
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.RuleFamilies.FirstOrder
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAsymmetricInduction
open Mettapedia.PLN.RuleFamilies.FirstOrder.RavenInductionBridge

set_option autoImplicit false

abbrev CallMachine :=
  Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel.Machine

/-! ## Tuffy-style social smoking -/

namespace Tuffy

def queryType : Term := .atom "PLNQuery"

def smokesBob : Term := .atom "Smokes(bob)"

def declaration : ArrowDeclaration :=
  ⟨100, "PLN.QueryStrength", [queryType], numberType⟩

def snapshot : Snapshot :=
  ⟨100, [declaration], [⟨101, smokesBob, queryType⟩], ["PLN.QueryStrength"]⟩

def claim : Claim :=
  ⟨snapshot,
    ⟨"PLN.QueryStrength", [smokesBob], [smokesBob], .number "3/5"⟩⟩

/-- The generated NTT, rather than a separately asserted certificate, is the
typing premise for the social-smoking query. -/
theorem call_inhabits_generated_ntt :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred := by
  rw [satisfies_typedCallNTT_iff]
  decide

/-- Typed admission and the exact social-smoking probability are independent
conjuncts in the composed judgment. -/
theorem typed_smokes_bob_probability :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred ∧
      BinaryWorldModel.queryStrength
          (Mettapedia.Logic.MarkovLogicClauseWorldModel.clauseWMState
            socialGroundMLN socialFullSupport)
          smokesBobQuery =
        (3 : ENNReal) / 5 :=
  ⟨call_inhabits_generated_ntt,
    social_queryStrength_smokesBob_eq_three_fifths⟩

def wrongResultClaim : Claim :=
  { claim with call := { claim.call with result := .string "3/5" } }

/-- A semantically suggestive string is not a numeric result. -/
theorem wrong_result_type_rejected :
    ¬ (gsltOSLF callGuardGSLT).satisfies
        (⟨wrongResultClaim, .pending⟩ : CallMachine)
        (typedCallNTT wrongResultClaim declaration).pred := by
  rw [satisfies_typedCallNTT_iff]
  decide

end Tuffy

/-! ## Raven induction -/

namespace Raven

def declaration : ArrowDeclaration :=
  ⟨200, "PLN.RavenInduction", [numberType, numberType], numberType⟩

def snapshot : Snapshot :=
  ⟨200, [declaration], [], ["PLN.RavenInduction"]⟩

def claim : Claim :=
  ⟨snapshot,
    ⟨"PLN.RavenInduction", [.number "5", .number "95"],
      [.number "5", .number "95"], .number "1/20"⟩⟩

theorem call_inhabits_generated_ntt :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred := by
  rw [satisfies_typedCallNTT_iff]
  decide

/-- The typed call surrounds the existing guarded Bayes-inversion result; the
NTT does not manufacture the `1/20` equality. -/
theorem typed_bayes_inversion_values :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred ∧
      (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength
          (ravenBlackEvidence 5)).toReal = (1 : ℝ) ∧
      (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength
          (blackRavenEvidence 5 95)).toReal = (1 / 20 : ℝ) ∧
      ravenObservationBaseRate 5 95 = (1 / 20 : ℝ) ∧
      plnInversionBayesStrength
          (Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength
            (ravenBlackEvidence 5)).toReal
          (ravenObservationBaseRate 5 95)
          1 = (1 / 20 : ℝ) :=
  ⟨call_inhabits_generated_ntt,
    ravenInduction_bayesInversion_values_canary⟩

def wrongResultClaim : Claim :=
  { claim with call := { claim.call with result := .string "1/20" } }

theorem wrong_result_type_rejected :
    ¬ (gsltOSLF callGuardGSLT).satisfies
        (⟨wrongResultClaim, .pending⟩ : CallMachine)
        (typedCallNTT wrongResultClaim declaration).pred := by
  rw [satisfies_typedCallNTT_iff]
  decide

end Raven

/-! ## Proof-producing PLN.Derive -/

namespace Derive

def stateType : Term := .atom "PLNState"

def initialValue : Term := .atom "temporal-initial"
def finalValue : Term := .atom "temporal-final"

def declaration : ArrowDeclaration :=
  ⟨300, "PLN.Derive", [stateType], stateType⟩

def snapshot : Snapshot :=
  ⟨300, [declaration],
    [⟨301, initialValue, stateType⟩, ⟨302, finalValue, stateType⟩],
    ["PLN.Derive"]⟩

def claim : Claim :=
  ⟨snapshot,
    ⟨"PLN.Derive", [initialValue], [initialValue], finalValue⟩⟩

theorem call_inhabits_generated_ntt :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred := by
  rw [satisfies_typedCallNTT_iff]
  decide

/-- A native typed-call step composes with the independently checked
chronological `PLN.Derive` articles and their generated GSLT path. -/
theorem typed_temporal_derivation :
    (gsltOSLF callGuardGSLT).satisfies
        (⟨claim, .pending⟩ : CallMachine)
        (typedCallNTT claim declaration).pred ∧
      (Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.nativeKernel.toChecker).check
          Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.claim
          Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate = true ∧
      Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.deriveGSLT.MultiStep
          ⟨Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.initial,
            Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate⟩
          ⟨Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.final, []⟩ :=
  ⟨call_inhabits_generated_ntt,
    Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate_accepted,
    Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate_has_oslf_trace⟩

def untypedResultSnapshot : Snapshot :=
  ⟨300, [declaration], [⟨301, initialValue, stateType⟩], ["PLN.Derive"]⟩

def untypedResultClaim : Claim :=
  ⟨untypedResultSnapshot, claim.call⟩

/-- The PLN articles remain valid independently, but the typed call is
rejected when its result annotation is absent. -/
theorem missing_result_annotation_separates_authorities :
    ¬ (gsltOSLF callGuardGSLT).satisfies
        (⟨untypedResultClaim, .pending⟩ : CallMachine)
        (typedCallNTT untypedResultClaim declaration).pred ∧
      (Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.nativeKernel.toChecker).check
          Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.claim
          Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate = true := by
  constructor
  · rw [satisfies_typedCallNTT_iff]
    decide
  · exact Mettapedia.PLN.Bridges.GSLT.PLNDeriveNIKAuthority.TemporalCanary.certificate_accepted

end Derive

#print axioms Tuffy.typed_smokes_bob_probability
#print axioms Tuffy.wrong_result_type_rejected
#print axioms Raven.typed_bayes_inversion_values
#print axioms Raven.wrong_result_type_rejected
#print axioms Derive.typed_temporal_derivation
#print axioms Derive.missing_result_annotation_separates_authorities

end Mettapedia.PLN.Bridges.GSLT.PeTTaTypedPLNNativeBridge
