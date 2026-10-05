import Mettapedia.Languages.MM0.Presentation.AdmissionProgram

/-! # Authorization is computed from the preceding MM0 theory -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmission

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalConversion ComputationalProof ComputationalDeclaration
open ComputationalDefinitionAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "A" => admissionEquations
local notation "H" => dataEqualityHost

theorem declaration_imported (head : String) (used : head ∈ declarationProgram.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies declarationProgram H head arguments result) :
    Applies P H head arguments result :=
  body_reused head (by
    simp only [bodyProgram, bodyBase, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl (Or.inl used)) arguments result
    (ComputationalDefinitionAdmission.declaration_reused head used arguments result computed)

theorem declaration_suffix_imported (head : String) (used : head ∈ declarationEquations.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies declarationProgram H head arguments result) :
    Applies P H head arguments result :=
  declaration_imported head (by
    simp only [declarationProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr used) arguments result computed

theorem body_suffix_imported (head : String) (used : head ∈ bodyEquations.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies bodyProgram H head arguments result) :
    Applies P H head arguments result :=
  body_reused head (by
    simp only [bodyProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr used) arguments result computed

theorem proof_suffix_imported (head : String) (used : head ∈ proofEquations.calledHeads)
    (arguments : List Term) (result : Term)
    (computed : Applies proofProgram H head arguments result) :
    Applies P H head arguments result := by
  have included : head ∈ proofProgram.calledHeads := by
    simp only [proofProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr used
  exact declaration_imported head (by
    simp only [declarationProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inl included) arguments result (ComputationalDeclaration.proof_reused head included _ _ computed)

theorem and_imported (left right : Bool) :
    Applies P H "mm0:form-and" [boolean left, boolean right] (boolean (left && right)) :=
  declaration_suffix_imported _ (by decide) _ _ (and_computes left right)

private theorem evaluates_and {environment : Env} {left right : Term} {first second : Bool}
    (leftRun : Evaluates P H environment left (boolean first))
    (rightRun : Evaluates P H environment right (boolean second)) :
    Evaluates P H environment (.expr [.sym "mm0:form-and", left, right]) (boolean (first && second)) :=
  .call (by simp [Special]) (.cons leftRun (.cons rightRun .nil)) (and_imported first second)

theorem missing_computes {α : Type} (encode : α → Term) (entry : Option α) :
    Applies P H "mm0:admission-missing" [encodeLookupResult (entry.map encode)] (boolean entry.isNone) := by
  cases entry <;> exact ⟨1, by rw [admission_apply _ (by decide)]; rfl⟩

theorem fresh_computes {α : Type} (encode : α → Term) (table : List (Nat × α)) (index : Nat) :
    Applies P H "mm0:admission-fresh" [encodeNaturalTable encode table, natural index]
      (boolean (table.lookup index).isNone) := by
  refine admission_equation (equation := A[0]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (missing_computes encode _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (declaration_suffix_imported _ (by decide) _ _ (lookup_reused encode table index))

theorem theorem_proof_computes (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : ProofWitness) :
    Applies P H "mm0:admission-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeTheorem declaration, encodeNaturals dummies, encodeProof proof]
      (boolean (ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion)) := by
  rw [← theory_signature theory]
  refine admission_equation (equation := A[8]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
    (proof_suffix_imported _ (by decide) _ _
      (ComputationalProof.check_computes theory.terms theory.definitions theory.theorems
        (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion))
  refine Evaluates.call
    (values := [encodeContext declaration.arguments, encodeContext (dummies.map Kernel.Binder.bound)])
    (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (body_suffix_imported _ (by decide) _ _ (dummy_context_computes dummies))
  · simpa only [Admission.proofContext, encodeContext, List.map_append] using
      declaration_suffix_imported _ (by decide) _ _
        (append_reused (declaration.arguments.map encodeBinder) ((dummies.map Kernel.Binder.bound).map encodeBinder))

theorem check_computes (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-check" [encodeTheory theory, encodeAdmission admission]
      (boolean (admission.check theory)) := by
  cases admission with
  | sort index info =>
      refine admission_equation (equation := A[3]) (by decide) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeSort theory.sorts index)
  | term index declaration =>
      refine admission_equation (equation := A[4]) (by decide) (by rfl) (by rfl) ?_
      apply evaluates_and
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeDeclaration theory.terms index)
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (declaration_suffix_imported _ (by decide) _ _ (term_computes theory.sorts declaration))
  | definition index declaration body =>
      refine admission_equation (equation := A[5]) (by decide) (by rfl) (by rfl) ?_
      apply evaluates_and
      · apply evaluates_and
        · apply evaluates_and
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeDeclaration theory.terms index)
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeBody theory.definitions index)
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
            (declaration_suffix_imported _ (by decide) _ _ (term_computes theory.sorts declaration))
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (body_suffix_imported _ (by decide) _ _ (by
            simpa only [theory_signature, theory_sorts] using body_computes theory.sorts theory.terms declaration body))
  | axiomDecl index declaration =>
      refine admission_equation (equation := A[6]) (by decide) (by rfl) (by rfl) ?_
      apply evaluates_and
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeTheorem theory.theorems index)
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (declaration_suffix_imported _ (by decide) _ _ (by
            simpa only [theory_signature, theory_sorts] using theorem_computes theory.sorts theory.terms declaration))
  | theoremDecl index declaration dummies proof =>
      refine admission_equation (equation := A[7]) (by decide) (by rfl) (by rfl) ?_
      apply evaluates_and
      · apply evaluates_and
        · apply evaluates_and
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (fresh_computes encodeTheorem theory.theorems index)
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
              (declaration_suffix_imported _ (by decide) _ _ (by
                simpa only [theory_signature, theory_sorts] using theorem_computes theory.sorts theory.terms declaration))
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
            (declaration_suffix_imported _ (by decide) _ _ (dummies_computes theory.sorts dummies))
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
          (theorem_proof_computes theory declaration dummies proof)

theorem check_accepts_iff (theory : Theory) (admission : Admission) :
    Applies P H "mm0:admission-check" [encodeTheory theory, encodeAdmission admission] (.sym "True") ↔
      Admission.Authorized theory admission := by
  constructor
  · intro run
    have same := run.deterministic (check_computes theory admission)
    apply (Admission.check_iff theory admission).mp
    cases checked : admission.check theory with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro authorized
    simpa [(Admission.check_iff theory admission).mpr authorized, boolean] using check_computes theory admission

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
