import Mettapedia.Languages.MM0.Presentation.AdmissionCorrespondence
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Native MM0 proof identity and authored checked entries

The native proof object retains the supplied theorem arguments, ordered child
proofs and conversion witness. The judgment is independent of the checker.
The shared formal evaluator checks the same witness against the actual theory
tables. Fixed initial admission establishes logical well-formedness, while
alignment with an external fixed specification is a separate requirement.

Execution budgets are not proof decorations. The correspondence below retains
completed outcomes and finite witness identity, without asserting that the
native MeTTa runtime already realizes the formal primitive catalogue.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.KernelFormation

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions ComputationalProof
open ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.KernelAuthority

def nativeProofSystem (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    NativeProofSystem Preterm where
  ProofObject := ProofWitness
  Judges := ProofWitness.Checks theory.termSignature theory.definitionSignature
    theory.theoremSignature context hypotheses

def nativeKernel (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    NativeProofKernel (nativeProofSystem theory context hypotheses) where
  decide claim proof := ProofWitness.check theory.termSignature theory.definitionSignature
    theory.theoremSignature context hypotheses proof claim
  correct claim proof := ProofWitness.check_iff _ _ _ _ _ proof claim

theorem native_judgment_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    (nativeKernel theory context hypotheses).toChecker.check claim proof = true ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature
        theory.theoremSignature context hypotheses proof claim :=
  (nativeKernel theory context hypotheses).correct claim proof

def native_proof_fibre_exact (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    CertificateEquivalence (nativeKernel theory context hypotheses).toChecker
      (nativeProofSystem theory context hypotheses) :=
  (nativeKernel theory context hypotheses).certificateEquivalence

theorem native_authority (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    (nativeKernel theory context hypotheses).toChecker.Authority
      (Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses) where
  sound := fun _ _ accepted => ProofWitness.check_sound accepted
  complete := fun claim derived => (derives_iff_checked _ _ _ _ _ claim).mp derived

theorem checked_entry (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") ↔
      (nativeProofSystem theory context hypotheses).Judges proof claim :=
  supplied_proof_accepts_iff theory context hypotheses proof claim

theorem checked_entry_result (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) (result : Term) :
    Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] result ↔
      result = boolean ((nativeKernel theory context hypotheses).decide claim proof) := by
  constructor
  · exact fun computed => computed.deterministic (supplied_proof_computes theory context hypotheses proof claim)
  · rintro rfl
    exact supplied_proof_computes theory context hypotheses proof claim

theorem checked_entry_refuses (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "False") ↔
      ¬ (nativeProofSystem theory context hypotheses).Judges proof claim := by
  rw [checked_entry_result, ← (nativeKernel theory context hypotheses).correct claim proof]
  cases (nativeKernel theory context hypotheses).decide claim proof <;> simp [boolean]

theorem checked_entry_completed (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) (fuel : Nat)
    (finished : apply admissionProgram dataEqualityHost fuel "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] ≠ .exhausted) :
    apply admissionProgram dataEqualityHost fuel "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] =
      .value (boolean ((nativeKernel theory context hypotheses).decide claim proof)) :=
  (supplied_proof_computes theory context hypotheses proof claim).completed fuel finished

theorem checked_initial_theory {admissions : List Admission} {theory : Theory}
    (accepted : Applies admissionProgram dataEqualityHost "mm0:admission-start"
      [encodeAdmissions admissions] (encodeTheoryResult (some theory))) : Theory.WellFormed theory :=
  initial_run_wellFormed accepted

theorem checked_entry_derivable (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) :
    (∃ proof, Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True")) ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim :=
  (derives_iff_supplied_proof theory context hypotheses claim).symm

end Mettapedia.Languages.MM0.Presentation.KernelFormation
