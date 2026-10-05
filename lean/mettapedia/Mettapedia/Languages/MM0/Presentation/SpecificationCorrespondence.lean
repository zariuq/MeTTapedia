import Mettapedia.Languages.MM0.Presentation.SpecificationExecution

/-!
# Exact authored MM0 verification against a fixed specification

The result includes the actual admitted theory. Successful runs preserve the
specification's complete ordered axiom list, and proved declarations use the
preceding theory. All statements concern resolved canonical inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSpecification

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalConversion ComputationalProof ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => specificationProgram
local notation "H" => dataEqualityHost

theorem step_result_exact (state : SpecificationAdmission.State) (declaration : ProofDeclaration)
    (result : Term) :
    Applies P H "mm0:spec-step" [encodeState state, encodeProofDeclaration declaration] result ↔
      result = encodeStateResult (SpecificationAdmission.step? state declaration) := by
  constructor
  · exact fun checked => checked.deterministic (step_computes state declaration)
  · rintro rfl; exact step_computes state declaration

theorem step_accepts_iff (before after : SpecificationAdmission.State) (declaration : ProofDeclaration) :
    Applies P H "mm0:spec-step" [encodeState before, encodeProofDeclaration declaration]
      (encodeStateResult (some after)) ↔ SpecificationAdmission.Step before declaration after := by
  rw [step_result_exact, encodeStateResult_injective.eq_iff, eq_comm, SpecificationAdmission.step_eq_some_iff]

theorem step_refuses_iff (state : SpecificationAdmission.State) (declaration : ProofDeclaration) :
    Applies P H "mm0:spec-step" [encodeState state, encodeProofDeclaration declaration] (.sym "None") ↔
      ¬ ∃ next, SpecificationAdmission.Step state declaration next := by
  change Applies P H _ _ (encodeStateResult none) ↔ _
  simp only [step_result_exact, encodeStateResult_injective.eq_iff, ← SpecificationAdmission.step_eq_some_iff]
  cases SpecificationAdmission.step? state declaration <;> simp

theorem run_result_exact (state : SpecificationAdmission.State) (declarations : List ProofDeclaration)
    (result : Term) :
    Applies P H "mm0:spec-run" [encodeState state, encodeProofDeclarations declarations] result ↔
      result = encodeStateResult (SpecificationAdmission.run? state declarations) := by
  constructor
  · exact fun checked => checked.deterministic (run_computes state declarations)
  · rintro rfl; exact run_computes state declarations

theorem run_accepts_iff (before after : SpecificationAdmission.State) (declarations : List ProofDeclaration) :
    Applies P H "mm0:spec-run" [encodeState before, encodeProofDeclarations declarations]
      (encodeStateResult (some after)) ↔ SpecificationAdmission.Runs before declarations after := by
  rw [run_result_exact, encodeStateResult_injective.eq_iff, eq_comm, SpecificationAdmission.run_eq_some_iff]

theorem verify_result_exact (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (result : Term) :
    Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations] result ↔
      result = encodeTheoryResult (SpecificationAdmission.verify? specification declarations) := by
  constructor
  · exact fun checked => checked.deterministic (verify_computes specification declarations)
  · rintro rfl; exact verify_computes specification declarations

theorem verify_accepts_iff (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (theory : Theory) :
    Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      (encodeTheoryResult (some theory)) ↔ SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, []⟩ := by
  rw [verify_result_exact, encodeTheoryResult_injective.eq_iff, eq_comm, SpecificationAdmission.verify_eq_some_iff]

theorem verify_refuses_iff (specification : List SpecificationEntry) (declarations : List ProofDeclaration) :
    Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations] (.sym "None") ↔
      ¬ ∃ theory, SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨theory, []⟩ := by
  change Applies P H _ _ (encodeTheoryResult none) ↔ _
  simp only [verify_result_exact, encodeTheoryResult_injective.eq_iff, ← SpecificationAdmission.verify_eq_some_iff]
  cases SpecificationAdmission.verify? specification declarations <;> simp

theorem verified_wellFormed {specification : List SpecificationEntry} {declarations : List ProofDeclaration}
    {theory : Theory}
    (accepted : Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      (encodeTheoryResult (some theory))) : Theory.WellFormed theory :=
  ((verify_accepts_iff specification declarations theory).mp accepted).theory_run.wellFormed Theory.empty_wellFormed

theorem verified_axioms_exact {specification : List SpecificationEntry} {declarations : List ProofDeclaration}
    {theory : Theory}
    (accepted : Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      (encodeTheoryResult (some theory))) :
    SpecificationAdmission.declarationAxioms declarations = SpecificationAdmission.specificationAxioms specification :=
  SpecificationAdmission.verified_axioms_exact
    ((SpecificationAdmission.verify_eq_some_iff _ _ _).mpr ((verify_accepts_iff _ _ _).mp accepted))

theorem accepted_axiom_is_next_specification_entry {before after : SpecificationAdmission.State}
    {index : Nat} {declaration : TheoremDecl} {localFlag : Bool}
    (accepted : Applies P H "mm0:spec-step"
      [encodeState before, encodeProofDeclaration ⟨.axiomDecl index declaration, localFlag⟩]
      (encodeStateResult (some after))) :
    localFlag = false ∧ before.pending = .axiomDecl index declaration :: after.pending :=
  ((step_accepts_iff _ _ _).mp accepted).axiom_from_specification

theorem admitted_theorem_uses_preceding_theory {before after : SpecificationAdmission.State}
    {index : Nat} {declaration : TheoremDecl} {dummies : List Nat} {proof : ProofWitness} {localFlag : Bool}
    (accepted : Applies P H "mm0:spec-step"
      [encodeState before, encodeProofDeclaration ⟨.theoremDecl index declaration dummies proof, localFlag⟩]
      (encodeStateResult (some after))) :
    Derives before.theory.termSignature before.theory.definitionSignature before.theory.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion :=
  ((step_accepts_iff _ _ _).mp accepted).theory_step.theorem_justified

theorem supplied_proof_computes (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim]
      (boolean (ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim)) :=
  admission_suffix_reused _ (by decide) _ _
    (ComputationalAdmission.supplied_proof_computes theory context hypotheses proof claim)

theorem supplied_proof_accepts_iff (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (proof : ProofWitness) (claim : Preterm) :
    Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") ↔
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim := by
  constructor
  · intro accepted
    have same := accepted.deterministic (supplied_proof_computes theory context hypotheses proof claim)
    apply (ProofWitness.check_iff _ _ _ _ _ _ _).mp
    cases computed : ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses proof claim with
    | false => simp [computed, boolean] at same
    | true => rfl
  · intro checked
    simpa [(ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked, boolean] using
      supplied_proof_computes theory context hypotheses proof claim

theorem derives_iff_supplied_proof (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (claim : Preterm) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature context hypotheses claim ↔
      ∃ proof, Applies P H "mm0:check-proof"
        [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
          encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True") := by
  constructor
  · intro derived
    obtain ⟨proof, checked⟩ := derived.certificate_exists
    exact ⟨proof, (supplied_proof_accepts_iff theory context hypotheses proof claim).mpr checked⟩
  · rintro ⟨proof, checked⟩
    exact ((supplied_proof_accepts_iff theory context hypotheses proof claim).mp checked).derives

theorem verified_proof_is_statement {specification : List SpecificationEntry} {declarations : List ProofDeclaration}
    {theory : Theory}
    (admitted : Applies P H "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      (encodeTheoryResult (some theory)))
    {context : Context} {hypotheses : List Preterm} {proof : ProofWitness} {claim : Preterm}
    (localStatements : ∀ hypothesis ∈ hypotheses,
      Preterm.IsStatement theory.sortSignature theory.termSignature context hypothesis)
    (checked : Applies P H "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode claim] (.sym "True")) :
    Preterm.IsStatement theory.sortSignature theory.termSignature context claim :=
  (verified_wellFormed admitted).derives_statement localStatements
    ((supplied_proof_accepts_iff theory context hypotheses proof claim).mp checked).derives

theorem verify_completed_result (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (fuel : Nat)
    (finished : apply P H fuel "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations] ≠ .exhausted) :
    apply P H fuel "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations] =
      .value (encodeTheoryResult (SpecificationAdmission.verify? specification declarations)) :=
  (verify_computes specification declarations).completed fuel finished

theorem verify_eventually_stable (specification : List SpecificationEntry) (declarations : List ProofDeclaration) :
    ∃ needed, ∀ fuel, needed ≤ fuel → apply P H fuel "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations] =
      .value (encodeTheoryResult (SpecificationAdmission.verify? specification declarations)) :=
  (verify_computes specification declarations).at_least

end Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
