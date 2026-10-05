import Mettapedia.Languages.MM0.Presentation.SpecificationFormation

/-! # Specification-bound behavior and supplied-witness separation -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.SpecificationFormation.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalProof ComputationalConversion ComputationalAdmission ComputationalSpecification
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private instance : DecidableEq Theory := fun left right =>
  decidable_of_iff (encodeTheory left = encodeTheory right) encodeTheory_injective.eq_iff

private def proposition : SortInfo := { provable := true }
private def constant : TermDecl := ⟨[], 0, ∅⟩
private def statement : TheoremDecl := ⟨[], [], .term 0⟩
private def theory : Theory :=
  { sorts := [(0, proposition)], terms := [(0, constant)], theorems := [(0, statement)] }
private def specification : List SpecificationEntry :=
  [.sort 0 proposition, .term 0 constant, .axiomDecl 0 statement]
private def declarations : List ProofDeclaration :=
  [⟨.sort 0 proposition, false⟩, ⟨.term 0 constant, false⟩, ⟨.axiomDecl 0 statement, false⟩]
private def proof : ProofWitness := .theoremApp 0 [] []

private theorem admitted :
    Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] (encodeTheoryResult (some theory)) := by
  have verified : SpecificationAdmission.verify? specification declarations = some theory := by decide +kernel
  simpa only [verified] using verify_computes specification declarations

private theorem checked :
    Applies specificationProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext [], encodeExpressions [], encodeProof proof, encode (.term 0)] (.sym "True") := by
  apply (ComputationalSpecification.supplied_proof_accepts_iff theory [] [] proof (.term 0)).mpr
  apply (ProofWitness.check_iff _ _ _ _ _ _ _).mp
  decide +kernel

theorem accepted_proof_retains_expected_assumptions :
    Theory.WellFormed theory ∧
      SpecificationAdmission.declarationAxioms declarations = SpecificationAdmission.specificationAxioms specification ∧
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature [] [] (.term 0) :=
  verified_proof_has_authorized_basis admitted checked

theorem proof_inhabits_the_generated_behavioral_type :
    (gsltOSLF (ComputationalObligations.obligationGSLT theory [] [])).satisfies [.term 0]
      (ComputationalObligations.derivableNativeType theory [] []).pred :=
  (nativeType_iff_checked theory [] [] (.term 0)).mpr ⟨proof, checked⟩

theorem derivable_claim_does_not_validate_a_bad_witness :
    (gsltOSLF (ComputationalObligations.obligationGSLT theory [] [])).satisfies [.term 0]
      (ComputationalObligations.derivableNativeType theory [] []).pred ∧
    ¬ Applies specificationProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext [], encodeExpressions [], encodeProof (.hyp 0), encode (.term 0)] (.sym "True") := by
  refine ⟨proof_inhabits_the_generated_behavioral_type, ?_⟩
  rw [ComputationalSpecification.supplied_proof_accepts_iff, ← ProofWitness.check_iff]
  decide +kernel

theorem missing_specification_axiom_removes_verified_authority :
    ¬ ∃ result, Applies specificationProgram dataEqualityHost "mm0:spec-verify"
      [encodeEntries (specification ++ [.axiomDecl 1 statement]), encodeProofDeclarations declarations]
      (encodeTheoryResult (some result)) ∧
      (gsltOSLF (ComputationalObligations.obligationGSLT result [] [])).satisfies [.term 0]
        (ComputationalObligations.derivableNativeType result [] []).pred := by
  rintro ⟨result, accepted, _⟩
  have refuses : SpecificationAdmission.verify? (specification ++ [.axiomDecl 1 statement]) declarations = none := by
    decide +kernel
  have same := (SpecificationAdmission.verify_eq_some_iff _ _ _).mpr
    ((verify_accepts_iff (specification ++ [.axiomDecl 1 statement]) declarations result).mp accepted)
  rw [refuses] at same
  cases same

end Mettapedia.Languages.MM0.Presentation.SpecificationFormation.Controls
