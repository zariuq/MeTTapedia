import Mettapedia.Languages.VibeITP.Presentation.KernelFormation
import Mettapedia.Languages.VibeITP.Presentation.OSLFBridge

/-!
# Authored admitted Vibe checking and generated OSLF types

The fixed-initial declaration entry establishes the actual theory's hosting
invariant. The existing declarative calculus then supplies ordered obligation
behavior and its generated reachability type. Witness-specific checking stays
separate from existential derivability and behavioral type membership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.AdmittedOSLF

open ComputationalData ComputationalProofs ComputationalAdmission KernelFormation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem checked_entry_at_run {declarations : List Declaration} {after : AdmissionState}
    (admitted : AdmissionRun initialAdmission declarations after)
    (proof : ProofWitness) (claim : Spec.Term) :
    Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True") ↔
      ProofWitness.Checks after.theory proof claim := by
  rw [checked_entry]
  constructor
  · rintro ⟨other, otherRun, checked⟩
    have same := (admitRun_eq_some_iff _ _ _).mpr otherRun
    rw [(admitRun_eq_some_iff _ _ _).mpr admitted] at same
    cases Option.some.inj same
    exact checked
  · intro checked
    exact ⟨after, admitted, checked⟩

theorem admitted_nativeType_iff_checked {declarations : List Declaration} {after : AdmissionState}
    (admitted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after))) (claim : Spec.Term) :
    (gsltOSLF (proofSearchGSLT (kernelValidated after.theory after.nextFresh))).satisfies
      [jThm (encTerm after.theory.sig claim)]
      (derivableNativeType (kernelValidated after.theory after.nextFresh)).pred ↔
      ∃ proof, Applies admissionProgram dataEqualityHost "vibe:check-static"
        [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True") := by
  rw [kernel_nativeType_iff_derives (checked_start_hosted admitted)]
  have actualRun := (checked_start _ _).mp admitted
  constructor
  · intro derived
    obtain ⟨proof, checked⟩ := certificate_exists (checked_start_hosted admitted) derived
    exact ⟨proof, (checked_entry_at_run actualRun proof claim).mpr checked⟩
  · rintro ⟨proof, checked⟩
    exact ((checked_entry_at_run actualRun proof claim).mp checked).derives

theorem admitted_discharge_iff_checked {declarations : List Declaration} {after : AdmissionState}
    (admitted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after))) (claim : Spec.Term) :
    (proofSearchGSLT (kernelValidated after.theory after.nextFresh)).MultiStep
      [jThm (encTerm after.theory.sig claim)] [] ↔
      ∃ proof, Applies admissionProgram dataEqualityHost "vibe:check-static"
        [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True") := by
  rw [kernel_proofSearch_iff_derives (checked_start_hosted admitted)]
  exact (kernel_nativeType_iff_derives (checked_start_hosted admitted) claim).symm.trans
    (admitted_nativeType_iff_checked admitted claim)

theorem accepted_proof_has_nativeType {declarations : List Declaration} {after : AdmissionState}
    {proof : ProofWitness} {claim : Spec.Term}
    (admitted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after)))
    (accepted : Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True")) :
    (gsltOSLF (proofSearchGSLT (kernelValidated after.theory after.nextFresh))).satisfies
      [jThm (encTerm after.theory.sig claim)]
      (derivableNativeType (kernelValidated after.theory after.nextFresh)).pred :=
  (admitted_nativeType_iff_checked admitted claim).mpr ⟨proof, accepted⟩

theorem nativeType_has_finite_checked_execution {declarations : List Declaration} {after : AdmissionState}
    {claim : Spec.Term}
    (admitted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after)))
    (inhabited : (gsltOSLF (proofSearchGSLT (kernelValidated after.theory after.nextFresh))).satisfies
      [jThm (encTerm after.theory.sig claim)]
      (derivableNativeType (kernelValidated after.theory after.nextFresh)).pred) :
    ∃ proof fuel, apply admissionProgram dataEqualityHost fuel "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] = .value (.sym "True") :=
  (admitted_nativeType_iff_checked admitted claim).mp inhabited

end Mettapedia.Languages.VibeITP.Presentation.AdmittedOSLF
