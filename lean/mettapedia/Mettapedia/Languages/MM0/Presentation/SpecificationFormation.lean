import Mettapedia.Languages.MM0.Presentation.SpecificationCorrespondence
import Mettapedia.Languages.MM0.Presentation.KernelFormation
import Mettapedia.Languages.MM0.Presentation.ObligationGSLT

/-!
# MM0 specification authority, native proofs and computational obligations

These laws compose fixed-specification verification with the existing native
proof-system interface and the local computational obligation machine. The
same resulting theory supplies every signature. Behavioral membership means
that some proof exists; acceptance still validates the particular witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.SpecificationFormation

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalProof ComputationalConversion ComputationalAdmission ComputationalSpecification
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

theorem checked_native_entry (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies specificationProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") ↔
      (KernelFormation.nativeProofSystem theory context hypotheses).Judges proof claim :=
  ComputationalSpecification.supplied_proof_accepts_iff theory context hypotheses proof claim

theorem discharge_iff_checked (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) :
    (ComputationalObligations.obligationGSLT theory context hypotheses).MultiStep [claim] [] ↔
      ∃ proof, Applies specificationProgram dataEqualityHost "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") :=
  (ComputationalObligations.singleton_discharge_iff theory context hypotheses claim).trans
    (ComputationalSpecification.derives_iff_supplied_proof theory context hypotheses claim)

theorem nativeType_iff_checked (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) :
    (gsltOSLF (ComputationalObligations.obligationGSLT theory context hypotheses)).satisfies [claim]
      (ComputationalObligations.derivableNativeType theory context hypotheses).pred ↔
      ∃ proof, Applies specificationProgram dataEqualityHost "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") :=
  (ComputationalObligations.nativeType_iff_derives theory context hypotheses claim).trans
    (ComputationalSpecification.derives_iff_supplied_proof theory context hypotheses claim)

theorem verified_theory_unique {specification : List SpecificationEntry} {declarations : List ProofDeclaration}
    {first second : Theory}
    (left : Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some first)))
    (right : Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some second))) :
    first = second := Option.some.inj (encodeTheoryResult_injective (left.deterministic right))

theorem verified_proof_has_authorized_basis
    {specification : List SpecificationEntry} {declarations : List ProofDeclaration} {theory : Theory}
    (admitted : Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some theory)))
    {context : Context} {hypotheses : List Preterm} {proof : ProofWitness} {claim : Preterm}
    (checked : Applies specificationProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True")) :
    Theory.WellFormed theory ∧
      SpecificationAdmission.declarationAxioms declarations = SpecificationAdmission.specificationAxioms specification ∧
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim :=
  ⟨ComputationalSpecification.verified_wellFormed admitted,
    ComputationalSpecification.verified_axioms_exact admitted,
    ((checked_native_entry theory context hypotheses proof claim).mp checked).derives⟩

theorem verified_behavior_iff_checked (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (context : Context) (hypotheses : List Preterm) (claim : Preterm) :
    (∃ theory, Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some theory)) ∧
      (gsltOSLF (ComputationalObligations.obligationGSLT theory context hypotheses)).satisfies [claim]
        (ComputationalObligations.derivableNativeType theory context hypotheses).pred) ↔
    ∃ theory proof, Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some theory)) ∧
      Applies specificationProgram dataEqualityHost "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") := by
  constructor
  · rintro ⟨theory, admitted, inhabited⟩
    obtain ⟨proof, checked⟩ := (nativeType_iff_checked theory context hypotheses claim).mp inhabited
    exact ⟨theory, proof, admitted, checked⟩
  · rintro ⟨theory, proof, admitted, checked⟩
    exact ⟨theory, admitted, (nativeType_iff_checked theory context hypotheses claim).mpr ⟨proof, checked⟩⟩

theorem behavioral_membership_has_finite_checked_execution (theory : Theory) (context : Context)
    (hypotheses : List Preterm) (claim : Preterm)
    (inhabited : (gsltOSLF (ComputationalObligations.obligationGSLT theory context hypotheses)).satisfies [claim]
      (ComputationalObligations.derivableNativeType theory context hypotheses).pred) :
    ∃ proof fuel, apply specificationProgram dataEqualityHost fuel "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] = .value (.sym "True") :=
  (nativeType_iff_checked theory context hypotheses claim).mp inhabited

end Mettapedia.Languages.MM0.Presentation.SpecificationFormation
