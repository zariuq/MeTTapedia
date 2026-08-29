import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.OSLF.Framework.ContextualModalProfileObservability

/-!
# Profile retention in selected native-type generation

A selected native-type demand contains two kinds of information: a grounded
stream of rewrite occurrences and one local `star`/`box` profile at every
contextual slot.  The contextual-modal signature compiler deliberately uses
only the first coordinate.  It constructs the shared telescope of formula
constructors, not the profile-sensitive native typing rules.

This module states that boundary as a factorization theorem.  It also gives
the exact obligation for a later full generator: its output must retain the
authored profile wire.  Any such generator necessarily fails to factor
through the profile-free foundation projection.
-/

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeProfileRetention

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework

abbrev source : ValidatedLanguageDef :=
  ContextualModalProfileObservability.source

abbrev Demand := SelectedNativeTypeDemand source

abbrev ProfileWire := List (List CarrierUniverseSignature.Code)

/-- Forget the local modal profile while retaining the grounded occurrence
stream. -/
def foundationShadow (demand : Demand) :
    SelectedNativeTypeFoundation.Demand source :=
  demand.foundation

/-- The current signature-only output. -/
def signatureOutput (demand : Demand) : CalculusLanguageDef :=
  ContextualModalSignatureCompiler.definition demand.foundation

/-- A generated artifact retains the profile coordinate when the complete
stable profile wire can be recovered from that artifact. -/
def RetainsProfileWire {Output : Type*} (generate : Demand → Output) : Prop :=
  Factors generate SelectedNativeTypeDemand.choices

abbrev allStar : Demand := ContextualModalProfileObservability.allStar
abbrev allBox : Demand := ContextualModalProfileObservability.allBox

/-- The foundation projection identifies two demands whose profile wires are
different. -/
def foundationProfileFiber :
    NonTrivialFiber foundationShadow SelectedNativeTypeDemand.choices where
  left := allStar
  right := allBox
  sameShadow := by
    simp [foundationShadow, allStar, allBox,
      ContextualModalProfileObservability.allStar,
      ContextualModalProfileObservability.allBox]
  differentValue :=
    ContextualModalProfileObservability.profile_wires_distinct

/-- The profile wire cannot be reconstructed from the profile-free
foundation. -/
theorem profileWire_not_factors_through_foundation :
    ¬ Factors foundationShadow SelectedNativeTypeDemand.choices :=
  foundationProfileFiber.not_factors

/-- The existing contextual-modal signature compiler factors completely
through the profile-free foundation. -/
theorem signatureOutput_factors_through_foundation :
    Factors foundationShadow signatureOutput := by
  refine ⟨ContextualModalSignatureCompiler.definition, ?_⟩
  intro demand
  rfl

/-- Recovering the profile wire from an output forces that output to separate
the two concrete endpoint profiles. -/
theorem retainedProfileWire_separates_endpoints {Output : Type*}
    {generate : Demand → Output}
    (retains : RetainsProfileWire generate) :
    generate allStar ≠ generate allBox := by
  intro sameOutput
  exact ContextualModalProfileObservability.profile_wires_distinct
    (retains.constantOnFibers allStar allBox sameOutput)

/-- Consequently the signature-only compiler is not a full profiled
native-type generator. -/
theorem signatureOutput_does_not_retain_profileWire :
    ¬ RetainsProfileWire signatureOutput := by
  intro retains
  exact retainedProfileWire_separates_endpoints retains
    ContextualModalProfileObservability.signature_projection_identifies_profiles

/-- Any output retaining the complete profile wire necessarily depends on
more than the profile-free foundation. -/
theorem retainingGenerator_not_factors_through_foundation
    {Output : Type*} {generate : Demand → Output}
    (retains : RetainsProfileWire generate) :
    ¬ Factors foundationShadow generate := by
  intro factors
  have sameOutput : generate allStar = generate allBox :=
    factors.constantOnFibers allStar allBox
      foundationProfileFiber.sameShadow
  exact retainedProfileWire_separates_endpoints retains sameOutput

/-! ## Positive control -/

/-- Retaining the complete demand trivially retains its profile wire.  This
is a control for the criterion, not a native-type generator. -/
theorem identity_retains_profileWire :
    RetainsProfileWire (fun demand : Demand => demand) := by
  exact ⟨SelectedNativeTypeDemand.choices, fun _ => rfl⟩

/-- The positive control also exhibits the required non-factorization through
the profile-free foundation. -/
theorem identity_not_factors_through_foundation :
    ¬ Factors foundationShadow (fun demand : Demand => demand) := by
  apply (NonTrivialFiber.mk
    (shadow := foundationShadow)
    (invariant := fun demand : Demand => demand)
    allStar allBox
    foundationProfileFiber.sameShadow
    ContextualModalProfileObservability.demands_distinct).not_factors

#print axioms foundationProfileFiber
#print axioms profileWire_not_factors_through_foundation
#print axioms signatureOutput_factors_through_foundation
#print axioms retainedProfileWire_separates_endpoints
#print axioms signatureOutput_does_not_retain_profileWire
#print axioms retainingGenerator_not_factors_through_foundation
#print axioms identity_retains_profileWire
#print axioms identity_not_factors_through_foundation

end Mettapedia.OSLF.Framework.SelectedNativeTypeProfileRetention
