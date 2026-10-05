import Mettapedia.Languages.VibeITP.Presentation.AdmissionCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Native Vibe proof identity and the checked computational entry

The proof object is the supplied static witness. Its judgment is the independent
`Checks` relation, while the executable kernel recomputes the witness's result.
Fuel belongs to execution, not to this proof object or its accepted fibre.

The entire authored admission program transports to the common data-equality
host without changing any outcome at any fuel. The public entry then binds the
same witness judgment to the theory constructed from the fixed initial state.
These laws concern the formal evaluator; realization of its primitives remains
a separate runtime obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.KernelFormation

open ComputationalData ComputationalShift ComputationalProofs ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.KernelAuthority

def nativeProofSystem (theory : Spec.Theory) : NativeProofSystem Spec.Term where
  ProofObject := ProofWitness
  Judges := ProofWitness.Checks theory

def nativeKernel (theory : Spec.Theory) : NativeProofKernel (nativeProofSystem theory) where
  decide claim proof := ProofWitness.check theory proof claim
  correct claim proof := ProofWitness.check_iff theory proof claim

theorem native_judgment_iff (theory : Spec.Theory) (proof : ProofWitness) (claim : Spec.Term) :
    (nativeKernel theory).toChecker.check claim proof = true ↔
      ProofWitness.Checks theory proof claim :=
  (nativeKernel theory).correct claim proof

def native_proof_fibre_exact (theory : Spec.Theory) :
    CertificateEquivalence (nativeKernel theory).toChecker (nativeProofSystem theory) :=
  (nativeKernel theory).certificateEquivalence

theorem native_authority {theory : Spec.Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) :
    (nativeKernel theory).toChecker.Authority (Spec.Derives theory) where
  sound := fun _ _ accepted => ProofWitness.check_sound accepted
  complete := fun claim derived => (derives_iff_checked hosted claim).mp derived

theorem common_host_agreement :
    productDivisionHost.AgreesOn dataEqualityHost admissionProgram.calledHeads := by
  apply dataEqualityHost_agrees
  decide +kernel

theorem common_host_apply (fuel : Nat) (head : String)
    (used : head ∈ admissionProgram.calledHeads) (arguments : List Term) :
    apply admissionProgram productDivisionHost fuel head arguments =
      apply admissionProgram dataEqualityHost fuel head arguments :=
  apply_host_eq admissionProgram common_host_agreement fuel head used arguments

theorem common_host_eval (fuel : Nat) (environment : Env) (term : Term)
    (confined : CallsWithin admissionProgram.calledHeads term) :
    eval admissionProgram productDivisionHost fuel environment term =
      eval admissionProgram dataEqualityHost fuel environment term :=
  eval_host_eq admissionProgram common_host_agreement
    (fun _ member => Program.calledHeads_body member) fuel environment term confined

theorem common_host_applies (head : String) (used : head ∈ admissionProgram.calledHeads)
    (arguments : List Term) (result : Term) :
    Applies admissionProgram productDivisionHost head arguments result ↔
      Applies admissionProgram dataEqualityHost head arguments result :=
  Applies.host_iff admissionProgram common_host_agreement head used arguments result

theorem checked_start (declarations : List Declaration) (after : AdmissionState) :
    Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after)) ↔
      AdmissionRun initialAdmission declarations after := by
  rw [← common_host_applies "vibe:admission-start" (by decide +kernel)]
  exact admissionStart_accepts_iff declarations after

theorem checked_start_hosted {declarations : List Declaration} {after : AdmissionState}
    (accepted : Applies admissionProgram dataEqualityHost "vibe:admission-start"
      [encodeDeclarations declarations] (encodeAdmissionResult (some after))) :
    Hosted after.theory after.nextFresh :=
  ((checked_start declarations after).mp accepted).hosted initialAdmission_hosted

theorem checked_entry (declarations : List Declaration) (proof : ProofWitness) (claim : Spec.Term) :
    Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True") ↔
      ∃ after, AdmissionRun initialAdmission declarations after ∧
        (nativeProofSystem after.theory).Judges proof claim := by
  rw [← common_host_applies "vibe:check-static" (by decide +kernel)]
  exact checkStatic_accepts_iff declarations proof claim

theorem checked_entry_refuses (declarations : List Declaration) (proof : ProofWitness) (claim : Spec.Term) :
    Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "False") ↔
      ¬ ∃ after, AdmissionRun initialAdmission declarations after ∧
        (nativeProofSystem after.theory).Judges proof claim := by
  rw [← common_host_applies "vibe:check-static" (by decide +kernel)]
  exact checkStatic_refuses_iff declarations proof claim

theorem checked_entry_completed (declarations : List Declaration) (proof : ProofWitness)
    (claim : Spec.Term) (fuel : Nat)
    (finished : apply admissionProgram dataEqualityHost fuel "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] ≠ .exhausted) :
    apply admissionProgram dataEqualityHost fuel "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] =
      .value (boolean (checkStatic declarations proof claim)) := by
  rw [← common_host_apply fuel "vibe:check-static" (by decide +kernel)] at finished ⊢
  exact checkStatic_completed_exact declarations proof claim fuel finished

theorem checked_entry_derivable (declarations : List Declaration) (claim : Spec.Term) :
    (∃ proof, Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness proof, encode claim] (.sym "True")) ↔
      ∃ after, AdmissionRun initialAdmission declarations after ∧ Spec.Derives after.theory claim := by
  constructor
  · rintro ⟨proof, accepted⟩
    obtain ⟨after, run, checked⟩ := (checked_entry declarations proof claim).mp accepted
    exact ⟨after, run, checked.derives⟩
  · rintro ⟨after, run, derived⟩
    obtain ⟨proof, checked⟩ := certificate_exists (run.hosted initialAdmission_hosted) derived
    exact ⟨proof, (checked_entry declarations proof claim).mpr ⟨after, run, checked⟩⟩

end Mettapedia.Languages.VibeITP.Presentation.KernelFormation
